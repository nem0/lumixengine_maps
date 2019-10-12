#include "editor/render_interface.h"
#include "editor/studio_app.h"
#include "editor/utils.h"
#include "editor/world_editor.h"
#include "engine/engine.h"
#include "engine/log.h"
#include "engine/math.h"
#include "engine/mt/atomic.h"
#include "engine/mt/sync.h"
#include "engine/mt/task.h"
#include "engine/os.h"
#include "engine/path_utils.h"
#include "imgui/imgui.h"
#include "stb/stb_image.h"
#include <WinSock2.h>
#include <Windows.h>
#include <cmath>
#include <cstdlib>
#pragma comment(lib, "Ws2_32.lib")


using namespace Lumix;


namespace
{


double tilex2long(double x, int z)
{
	return x / pow(2.0, z) * 360.0 - 180;
}


double tiley2lat(double y, int z)
{
	double n = PI - 2.0 * PI * y / pow(2.0, z);
	return 180.0 / PI * atan(0.5 * (exp(n) - exp(-n)));
}


constexpr int TILE_SIZE = 256;
constexpr int MAX_ZOOM = 18;
constexpr float MAP_UI_SIZE = 512;


struct MapsPlugin final : public StudioApp::GUIPlugin
{
	struct MapsTask;


	struct ImageData
	{
		ImageData(int tiles_count, IAllocator& allocator) 
			: pixels(allocator)
		{
			pixels.resize(TILE_SIZE * TILE_SIZE * tiles_count);
			memset(pixels.begin(), 0xff, pixels.byte_size());
		}

		MT::CriticalSection mutex;
		ImTextureID texture = nullptr;
		Array<u32> pixels;
	};


	struct MapsTask : public MT::Task
	{
		MapsTask(IAllocator& _allocator)
			: Task(_allocator)
			, allocator(_allocator)
		{
		}


		static int getHTTPHeaderLength(const Array<u8>& data)
		{
			for (int i = 0; i < data.size() - 4; ++i)
			{
				if (data[i] == '\r' && data[i + 1] == '\n' && data[i + 2] == '\r' && data[i + 3] == '\n')
				{
					return i + 4;
				}
			}
			return 0;
		}


		static void sendHTTPHeader(SOCKET socket, const char* host, const char* path)
		{
			writeRawString(socket, "GET ");
			writeRawString(socket, path);
			writeRawString(socket, " HTTP/1.1\r\nHost: ");
			writeRawString(socket, host);
			writeRawString(socket, "\r\nConnection: close\r\n\r\n");
		}


		bool readAll(SOCKET socket, Array<u8>* data) const
		{
			data->reserve(256 * 256);
			u8 buf[1024];
			while (int r = ::recv(socket, (char*)buf, sizeof(buf), 0))
			{
				ASSERT(r != SOCKET_ERROR || canceled);
				if (canceled) {
					return false;
				}
				if (r > 0) {
					MT::atomicAdd(downloaded_bytes, r);
					data->resize(data->size() + r);
					copyMemory(&(*data)[data->size() - r], buf, r);
				}
			}
			return true;
		}


		SOCKET connect(const char* host)
		{
			SOCKET socket = ::socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);
			if (socket == INVALID_SOCKET) return INVALID_SOCKET;

			SOCKADDR_IN sin;
			setMemory(&sin, 0, sizeof(sin));
			sin.sin_family = AF_INET;
			sin.sin_port = htons(80);
			hostent* hostname = gethostbyname(host);
			if (!hostname) return INVALID_SOCKET;

			const char* ip = inet_ntoa(**(in_addr**)hostname->h_addr_list);
			sin.sin_addr.s_addr = ip ? ::inet_addr(ip) : INADDR_ANY;

			if (::connect(socket, (LPSOCKADDR)&sin, sizeof(sin)) != 0) {
				return INVALID_SOCKET;
			}
			return socket;
		}


		bool parseImage(const Array<u8>& data) const
		{
			int header_size = getHTTPHeaderLength(data);

			int channels, w, h;
			int image_size = data.size() - header_size;
			stbi_uc* pixels = stbi_load_from_memory(&data[header_size], image_size, &w, &h, &channels, 4);
			if (!pixels || canceled) return false;

			ASSERT(w == 256 && h == 256);
			mutex->enter();
			int row_size = w * sizeof(u32);
			for (int j = 0; j < h; ++j)
			{
				copyMemory(&out[j * stride_bytes], &pixels[j * row_size], row_size);
			}
			mutex->exit();
			stbi_image_free(pixels);
			return true;
		}


		int task() override
		{
			socket = connect(host);
			if (socket == INVALID_SOCKET) return -1;

			sendHTTPHeader(socket, host, path);

			Array<u8> data(allocator);
			if(!readAll(socket, &data)) return -1;
			
			return parseImage(data) ? 0 : -1;
		}

		SOCKET socket = INVALID_SOCKET;
		MT::CriticalSection* mutex;
		StaticString<MAX_PATH_LENGTH> host;
		StaticString<1024> path;
		u8* out;
		int stride_bytes;
		IAllocator& allocator;
		volatile i32* downloaded_bytes;
		volatile bool canceled = false;
	};


	MapsPlugin(StudioApp& app)
		: m_app(app)
		, m_open(false)
		, m_satellite_map(4, app.getWorldEditor().getAllocator())
		, m_height_map(4, app.getWorldEditor().getAllocator())
		, m_in_progress(app.getWorldEditor().getAllocator())
		, m_queue(app.getWorldEditor().getAllocator())
	{
		WORD sockVer;
		WSADATA wsaData;
		sockVer = 2 | (2 << 8);
		if (WSAStartup(sockVer, &wsaData) != 0) logError("Maps") << "Failed to init winsock.";

		Action* action = LUMIX_NEW(app.getWorldEditor().getAllocator(), Action)("Maps", "maps", "maps");
		action->func.bind<MapsPlugin, &MapsPlugin::toggleOpen>(this);
		action->is_selected.bind<MapsPlugin, &MapsPlugin::isOpen>(this);
		app.addWindowAction(action);
		m_out_path[0] = '\0';
	}


	~MapsPlugin()
	{
		finishAllTasks();
		WSACleanup();
		clear();
	}


	void finishAllTasks()
	{
		IAllocator& allocator = m_app.getWorldEditor().getEngine().getAllocator();
		for (MapsTask* task : m_in_progress) {
			task->canceled = true;
			closesocket(task->socket);

			task->destroy();
			LUMIX_DELETE(allocator, task);
		}
		for (MapsTask* task : m_queue) {
			LUMIX_DELETE(allocator, task);
		}
		m_queue.clear();
		m_in_progress.clear();
	}


	void toggleOpen() { m_open = !m_open; }
	bool isOpen() const { return m_open; }
	const char* getName() const override { return "maps"; }


	static bool writeRawString(SOCKET socket, const char* str)
	{
		int len = stringLength(str);
		int send = ::send(socket, str, len, 0);
		return send == len;
	}


	void clear()
	{
		if (m_satellite_map.texture)
		{
			m_app.getWorldEditor().getRenderInterface()->destroyTexture(m_satellite_map.texture);
			m_satellite_map.texture = nullptr;
		}
		if (m_height_map.texture)
		{
			m_app.getWorldEditor().getRenderInterface()->destroyTexture(m_height_map.texture);
			m_height_map.texture = nullptr;
		}
		m_satellite_map.pixels.clear();
		m_height_map.pixels.clear();
	}


	void getHeightmapPath(char* url, int x, int y, int scale)
	{
		int size = 1 << m_zoom;
		sprintf(url,
			"/elevation-tiles-prod/terrarium/%d/%d/%d.png",
			m_zoom,
			(m_x + x) % size,
			(m_y + y) % size);
	}


	void getSatellitePath(char* url, int x, int y, int scale)
	{
		int size = 1 << m_zoom;
		sprintf(url,
			"/wmts/1.0.0/s2cloudless-2017_3857/default/g/%d/%d/%d.jpg",
			m_zoom,
			(m_y + y) % size,
			(m_x + x) % size);
	}


	void download()
	{
		finishAllTasks();
		WorldEditor& editor = m_app.getWorldEditor();
		memset(m_satellite_map.pixels.begin(), 0xff, m_satellite_map.pixels.byte_size());
		memset(m_height_map.pixels.begin(), 0xff, m_height_map.pixels.byte_size());
		RenderInterface* ri = editor.getRenderInterface();
		const int map_size = TILE_SIZE * (1 << m_size);
		m_satellite_map.texture = ri->createTexture("maps", &m_satellite_map.pixels[0], map_size, map_size);
		m_height_map.texture = ri->createTexture("maps", &m_height_map.pixels[0], map_size, map_size);

		m_is_download_deferred = false;

		int world_size = 1 << m_zoom;
		m_x = (m_x + world_size) % world_size;
		m_y = (m_y + world_size) % world_size;

		IAllocator& allocator = m_app.getWorldEditor().getEngine().getAllocator();
		char url[1024];
		for (int j = 0; j < (1 << m_size); ++j)
		{
			for (int i = 0; i < (1 << m_size); ++i)
			{
				getSatellitePath(url, i, j, (1 << m_size) - 1);
				MapsTask* task = LUMIX_NEW(allocator, MapsTask)(allocator);
				// https://tiles.maps.eox.at/wmts/1.0.0/s2cloudless-2017_3857/default/g/2/1/1.jpg
				task->host = "tiles.maps.eox.at";
				task->path = url;
				task->downloaded_bytes = &m_downloaded_bytes;
				task->out = (u8*)&m_satellite_map.pixels[i * TILE_SIZE + j * 256 * map_size];
				task->stride_bytes = map_size * sizeof(u32);
				task->mutex = &m_satellite_map.mutex;
//				task->create("download_image", true);
				m_queue.push(task);
//				m_satellite_map.tasks.push(task);
			}
		}

		for (int j = 0; j < (1 << m_size); ++j)
		{
			for (int i = 0; i < (1 << m_size); ++i)
			{
				getHeightmapPath(url, i, j, (1 << m_size) - 1);
				MapsTask* task = LUMIX_NEW(allocator, MapsTask)(allocator);
				task->host = "s3.amazonaws.com";
				task->path = url;
				task->downloaded_bytes = &m_downloaded_bytes;
				task->out = (u8*)&m_height_map.pixels[i * 256 + j * 256 * map_size];
				task->stride_bytes = map_size * sizeof(u32);
				task->mutex = &m_height_map.mutex;
				//task->create("download_hm", true);
				m_queue.push(task);
				//m_height_map.tasks.push(task);
			}
		}
	}


	bool browse()
	{
		return OS::getSaveFilename(Span(m_out_path), "Raw Image\0*.raw\0", "raw");
	}


	void save()
	{
		if (m_height_map.pixels.empty()) return;
		if (m_satellite_map.pixels.empty()) return;
		if (m_out_path[0] == '\0' && !browse()) return;

		union RGBA
		{
			struct { u8 r, g, b, a; };
			u32 rgba;
		};

		Array<u16> raw(m_app.getWorldEditor().getAllocator());
		int map_size = TILE_SIZE * (1 << m_size);
		raw.resize(map_size * map_size);
		const RGBA* in = (const RGBA*)&m_height_map.pixels[0];

		u32 min = 0xffffFFFF;
		u32 max = 0;
		for (int i = 0; i < raw.size(); ++i)
		{
			RGBA rgba = in[i];
			u32 p = u32((rgba.r << 16) + (rgba.g << 8) + rgba.b);
			if (max < p) max = p;
			if (min > p) min = p;
		}

		double diff = max - min;

		for (int i = 0; i < raw.size(); ++i)
		{
			RGBA rgba = in[i];
			u32 p = u32((rgba.r << 16) + (rgba.g << 8) + rgba.b);
			raw[i] = u16((double(p - min) / diff) * 0xffff);
		}

		WorldEditor& editor = m_app.getWorldEditor();
		IAllocator& allocator = editor.getAllocator();
		OS::OutputFile file;
		if (!file.open(m_out_path)) {
			logError("Maps") << "Failed to save " << m_out_path;
			return;
		}
		file.write(&raw[0], raw.size() * 2);
		file.close();

		RenderInterface* ri = editor.getRenderInterface();
		PathUtils::FileInfo file_info(m_out_path);
		StaticString<MAX_PATH_LENGTH> tga_path(file_info.m_dir, "/", file_info.m_basename, ".tga");
		ri->saveTexture(editor.getEngine(), tga_path, &m_satellite_map.pixels[0], map_size, map_size, true);
	}


	void checkTasks()
	{
		IAllocator& allocator = m_app.getWorldEditor().getEngine().getAllocator();
		u8 finished = 0;

		for (int i = m_in_progress.size() - 1; i >= 0; --i) {
			MapsTask* task = m_in_progress[i];
			if (task->isFinished()) {
				const bool is_hm = task->out < (u8*)m_satellite_map.pixels.begin() || task->out >= (u8*)m_satellite_map.pixels.end();
				finished |= is_hm ? 1 : 2;
				m_in_progress.swapAndPop(i);
				closesocket(task->socket);
				task->destroy();
				LUMIX_DELETE(allocator, task);
			}
		}

		if (!finished) return;

		for(u32 i = 0; i < 2; ++i) {
			if ((finished & (1 << i)) == 0) continue;

			ImageData* data = i == 0 ? &m_height_map : &m_satellite_map;
			RenderInterface* ri = m_app.getWorldEditor().getRenderInterface();
			if (data->texture) ri->destroyTexture(data->texture);

			int map_size = TILE_SIZE * (1 << m_size);
			data->mutex.enter();
			data->texture = ri->createTexture("maps", &data->pixels[0], map_size, map_size);
			data->mutex.exit();
		}
	}


	void resize()
	{
		finishAllTasks();
		int map_size = TILE_SIZE * (1 << m_size);
		m_satellite_map.pixels.resize(map_size * map_size);
		m_height_map.pixels.resize(map_size * map_size);
		download();
	}


	void move(int dx, int dy)
	{
		m_x += dx;
		m_y += dy;
		download();
	}


	void zoom(int dz)
	{
		int new_zoom = clamp(m_zoom + dz, m_size, MAX_ZOOM);
		dz = new_zoom - m_zoom;
		if (dz > 0)
		{
			m_x <<= dz;
			m_y <<= dz;
		}
		else
		{
			m_x >>= -dz;
			m_y >>= -dz;
		}
		m_zoom = new_zoom;
		download();
	}


	void onWindowGUI() override
	{
		while (!m_queue.empty() && m_in_progress.size() < 8) {
			MapsTask* task = m_queue.back();
			m_queue.pop();
			task->create("download_maps_task", true);
			m_in_progress.push(task);
		}

		checkTasks();

		if (!ImGui::Begin("Maps", &m_open))
		{
			ImGui::End();
			return;
		}
		
		ImGui::Text("Running tasks: %d", m_queue.size() + m_in_progress.size());
		ImGui::Text("Downloaded: %dkB", m_downloaded_bytes / 1024);

		if (m_is_download_deferred) download();

		if (ImGui::Combo("Size", &m_size, "1x1\0" "2x2\0" "4x4\0" "8x8\0" "16x16\0")) resize();

		int current_zoom = m_zoom;
		if (ImGui::SliderInt("Zoom", &current_zoom, m_size, MAX_ZOOM)) zoom(current_zoom - m_zoom);

		ImGui::LabelText("Output", m_out_path);
		ImGui::SameLine();
		if (ImGui::Button("...")) browse();

		if (!m_satellite_map.pixels.empty() && ImGui::Button("Save")) save();

		ImGui::SameLine();
		if (ImGui::Button("+")) zoom(1);
		ImGui::SameLine();
		if (ImGui::Button("-")) zoom(-1);
		ImGui::SameLine();
		if (ImGui::Button("<")) move(-1, 0);
		ImGui::SameLine();
		if (ImGui::Button(">")) move(1, 0);
		ImGui::SameLine();
		if (ImGui::Button("up")) move(0, -1);
		ImGui::SameLine();
		if (ImGui::Button("down")) move(0, 1);

		ImGui::SameLine();
		static bool show_hm = false;
		ImGui::Checkbox("Show HeightMap", &show_hm);

		ImVec2 cursor_pos = ImGui::GetCursorScreenPos();
		if (m_satellite_map.texture && !show_hm) ImGui::ImageButton(m_satellite_map.texture, ImVec2(MAP_UI_SIZE, MAP_UI_SIZE));
		if (m_height_map.texture && show_hm) ImGui::ImageButton(m_height_map.texture, ImVec2(MAP_UI_SIZE, MAP_UI_SIZE));

		if(ImGui::IsMouseDown(0) && ImGui::IsItemHovered()) {
			ImDrawList* dl = ImGui::GetWindowDrawList();
			dl->AddRect(m_mouse_down_pos, ImGui::GetMousePos(), 0xff000000);
		}

		if (ImGui::IsMouseClicked(0) && ImGui::IsItemHovered()) m_mouse_down_pos = ImGui::GetMousePos();
		if (ImGui::IsMouseReleased(0) && ImGui::IsItemHovered())
		{
			ImVec2 up_pos = ImGui::GetMousePos();
			double diff = maximum(abs(up_pos.x - m_mouse_down_pos.x), abs(up_pos.y - m_mouse_down_pos.y));
			int new_zoom = m_zoom;
			while (diff * 2 < 256 && diff > 0)
			{
				++new_zoom;
				diff *= 2;
			}
			if (new_zoom != m_zoom)
			{
				double x = m_x / double(1 << m_zoom);
				double y = m_y / double(1 << m_zoom);
				double left = minimum(up_pos.x, m_mouse_down_pos.x) - cursor_pos.x;
				double up = minimum(up_pos.y, m_mouse_down_pos.y) - cursor_pos.y;
				x += (left / MAP_UI_SIZE) / (1 << (m_zoom - m_size));
				y += (up / MAP_UI_SIZE) / (1 << (m_zoom - m_size));
				m_x = int(x * (1 << new_zoom));
				m_y = int(y * (1 << new_zoom));
				m_zoom = new_zoom;
				m_is_download_deferred = true;
			}
		}

		double lat = double(tiley2lat(double(m_y + (1 << (m_size - 1))), m_zoom));
		double width = 256 * (1 << m_size) * 156543.03 * cos(degreesToRadians(lat)) / (1 << m_zoom);

		ImGui::Text("Width: %fkm", width / 1000);
		ImGui::Text("Uses https://aws.amazon.com/public-datasets/terrain/");
		ImGui::Text("http://s3.amazonaws.com/elevation-tiles-prod/terrarium/%d/%d/%d.png", m_zoom, m_x, m_y);
		ImGui::Text("Sentinel-2 cloudless - https://s2maps.eu by EOX IT Services GmbH (Contains modified Copernicus Sentinel data 2016 & 2017)");
		ImGui::End();
	}


	StudioApp& m_app;
	ImageData m_satellite_map;
	ImageData m_height_map;
	Array<MapsTask*> m_queue;
	Array<MapsTask*> m_in_progress;
	volatile i32 m_downloaded_bytes = 0;
	bool m_open = false;
	bool m_is_download_deferred = true;
	int m_zoom = 1;
	int m_x = 0;
	int m_y = 0;
	int m_size = 1;
	char m_out_path[MAX_PATH_LENGTH];
	ImVec2 m_mouse_down_pos;
};


} // anonoymous namespace


LUMIX_STUDIO_ENTRY(maps)
{
	WorldEditor& editor = app.getWorldEditor();

	auto* plugin = LUMIX_NEW(editor.getAllocator(), MapsPlugin)(app);
	app.addPlugin(*plugin);
	return nullptr;
}
