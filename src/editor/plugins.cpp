#define LUMIX_NO_CUSTOM_CRT
#include "editor/render_interface.h"
#include "editor/studio_app.h"
#include "editor/utils.h"
#include "editor/world_editor.h"
#include "engine/atomic.h"
#include "engine/engine.h"
#include "engine/geometry.h"
#include "engine/hash_map.h"
#include "engine/log.h"
#include "engine/math.h"
#include "engine/os.h"
#include "engine/path.h"
#include "engine/reflection.h"
#include "engine/sync.h"
#include "engine/thread.h"
#include "imgui/imgui.h"
#include "renderer/texture.h"
#include "stb/stb_image.h"
#include "pugixml/pugixml.hpp"

#ifdef _WIN32
	#include <WinSock2.h>
	#include <Windows.h>
#else
	#include <arpa/inet.h>
	#include <netdb.h>
	#include <netinet/in.h>
	#include <sys/socket.h>
 	#include <unistd.h>
 #endif

#include <cmath>
#include <cstdlib>
#pragma comment(lib, "Ws2_32.lib")


using namespace Lumix;


namespace
{

static const ComponentType MODEL_INSTANCE_TYPE = Reflection::getComponentType("model_instance");
static const ComponentType TERRAIN_TYPE = Reflection::getComponentType("terrain");

double long2tilex(double long lon, int z) {
	return (lon + 180) * (1 << z) / 360.0;
}

double tilex2long(double x, int z) {
	return x / pow(2.0, z) * 360.0 - 180;
}

double lat2tiley(double lat, int z) { 
    const double latrad = lat * PI / 180.0;
	return (1.0 - asinh(tan(latrad)) / PI) / 2.0 * (1 << z); 
}

double tiley2lat(double y, int z) {
	double n = PI - 2.0 * PI * y / pow(2.0, z);
	return 180.0 / PI * atan(0.5 * (exp(n) - exp(-n)));
}


constexpr int TILE_SIZE = 256;
constexpr int MAX_ZOOM = 18;
constexpr float MAP_UI_SIZE = 512;


struct OSMParser {
	OSMParser(StudioApp& app)
		: m_app(app) 
		, m_nodes(m_app.getAllocator())
		, m_ways(m_app.getAllocator())
	{}


	bool toPos(pugi::xml_node nd_ref, Ref<DVec3> p) {
			if (nd_ref.empty() || !equalStrings(nd_ref.name(), "nd")) return false;

			pugi::xml_attribute ref_attr = nd_ref.attribute("ref");
			if (ref_attr.empty()) return false;
			const char* ref_str = ref_attr.value();
			u64 node_id;
			fromCString(Span(ref_str, (u32)strlen(ref_str)), Ref(node_id));

			auto iter = m_nodes.find(node_id);
			if (!iter.isValid()) return false;

			pugi::xml_node n = iter.value();

			pugi::xml_attribute lat_attr = n.attribute("lat");
			pugi::xml_attribute lon_attr = n.attribute("lon");
			
			if (lat_attr.empty() || lon_attr.empty()) return false;

			const double lat = atof(lat_attr.value());
			const double lon = atof(lon_attr.value());

			p->x = (lon - m_min_lon) / m_lon_range * m_scale;
			p->y = 0;
			p->z = (m_min_lat + m_lat_range - lat) / m_lat_range * m_scale;

			return true;
	}
	
	pugi::xml_node getNode(const pugi::xml_node& nd_ref) {
		if (nd_ref.empty() || !equalStrings(nd_ref.name(), "nd")) return pugi::xml_node();
		
		pugi::xml_attribute ref_attr = nd_ref.attribute("ref");
		if (ref_attr.empty()) return pugi::xml_node();
		const char* ref_str = ref_attr.value();
		u64 node_id;
		fromCString(Span(ref_str, (u32)strlen(ref_str)), Ref(node_id));

		auto iter = m_nodes.find(node_id);
		if (!iter.isValid()) return pugi::xml_node();

		return iter.value();
	}

	static bool isRoad(const pugi::xml_node& w) {
		pugi::xml_node building_tag = w.find_child([](const pugi::xml_node& n){
			if (!equalStrings(n.name(), "tag")) return false;
			pugi::xml_attribute key_attr = n.attribute("k");
			if (key_attr.empty()) return false;
			const bool is_highway = equalStrings(key_attr.value(), "highway");
			if (!is_highway) return false;
			pugi::xml_attribute value_attr = n.attribute("v");
			if (key_attr.empty()) return true;

			const bool is_footway = equalStrings(value_attr.value(), "footway");
			return !is_footway;
		});
		return !building_tag.empty();
	}

	static bool isBuilding(const pugi::xml_node& w) {
		pugi::xml_node building_tag = w.find_child([](const pugi::xml_node& n){
			if (!equalStrings(n.name(), "tag")) return false;
			pugi::xml_attribute key_attr = n.attribute("k");
			if (key_attr.empty()) return false;
			return equalStrings(key_attr.value(), "building");
		});
		return !building_tag.empty();
	}

	void createBuilding(const pugi::xml_node& way) {
		pugi::xml_node nd_ref = way.first_child();
		DVec3 pos;
		if (!toPos(nd_ref, Ref(pos))) return;

		/*WorldEditor& editor = m_app.getWorldEditor();
		const EntityRef e = editor.addEntityAt(pos);
		editor.addComponent(Span(&e, 1), MODEL_INSTANCE_TYPE);
		editor.setEntitiesScale(&e, 1, 10);
		editor.setProperty(MODEL_INSTANCE_TYPE, -1, "Source", Span(&e, 1), Path("models/cube/cube.fbx"));*/
		
		// geom
		DVec3 min_pos(m_min_lon, 0, m_min_lat);
		DVec3 prev;
		pugi::xml_node n = nd_ref;
		if (!toPos(n, Ref(prev))) return;
		const DVec3 first = prev;
		for(;;) {
			pugi::xml_node next = n.next_sibling();
			if (next.empty() || !equalStrings(next.name(), "nd")) break;
			DVec3 p;
			if (!toPos(next, Ref(p))) break;

			m_tris->push((prev - min_pos).toFloat());
			m_tris->push((p - min_pos).toFloat());
			m_tris->push((p - min_pos).toFloat() + Vec3(0, 6, 0));

			m_tris->push((prev - min_pos).toFloat());
			m_tris->push((p - min_pos).toFloat() + Vec3(0, 6, 0));
			m_tris->push((prev - min_pos).toFloat() + Vec3(0, 6, 0));
			prev = p;
			n = next;
		}
	}

	void createRoad(const pugi::xml_node& way) {
		pugi::xml_node nd_ref = way.first_child();
		DVec3 pos;
		if (!toPos(nd_ref, Ref(pos))) return;

		DVec3 min_pos(m_min_lon, 0, m_min_lat);
		DVec3 prev;
		pugi::xml_node n = nd_ref;
		if (!toPos(n, Ref(prev))) return;
		const DVec3 first = prev;
		for(;;) {
			pugi::xml_node next = n.next_sibling();
			if (next.empty() || !equalStrings(next.name(), "nd")) break;
			DVec3 p;
			if (!toPos(next, Ref(p))) break;

			const Vec3 a = (prev - min_pos).toFloat();
			const Vec3 b = (p - min_pos).toFloat();
			Vec3 norm = crossProduct(a - b, Vec3(0, 1, 0)).normalized();
			m_tris->push(a - norm * 2);
			m_tris->push(b - norm * 2);
			m_tris->push(b + norm * 2);
			
			m_tris->push(a - norm * 2);
			m_tris->push(b + norm * 2);
			m_tris->push(a + norm * 2);
			
			prev = p;
			n = next;
		}
	}

	void parseOSM(double left, double bottom, double right, double top, float scale,  Ref<Array<Vec3>> lines, Ref<Array<Vec3>> tris) {
		m_lines = &lines.value;
		m_tris = &tris.value;
		pugi::xml_document doc;
		FILE* fp = fopen("map.osm", "rb");
		fseek(fp, 0, SEEK_END);
		Array<char> data(m_app.getAllocator());
		data.resize(ftell(fp) + 1);
		data.back() = '\0';
		fseek(fp, 0, SEEK_SET);
		fread(data.begin(), 1, data.size(), fp);
		fclose(fp);
		const pugi::xml_parse_result res = doc.load_string(data.begin());
		ASSERT(pugi::status_ok == res.status);

		pugi::xml_node osm_root = doc.root().first_child();

		m_min_lon = left;
		m_min_lat = bottom;
		m_lat_range = top - bottom;
		m_lon_range = right - left;
		m_scale = scale;

		for (pugi::xml_node n = osm_root.first_child(); !n.empty(); n = n.next_sibling()) {
			if (equalStrings(n.name(), "node")) {
				pugi::xml_attribute id_attr = n.attribute("id");
				if (id_attr.empty()) continue;

				const char* id_str = id_attr.value();
				u64 id;
				fromCString(Span(id_str, stringLength(id_str)), Ref(id));
				m_nodes.insert(id, n);
			}
			else if (equalStrings(n.name(), "way")) {
				pugi::xml_attribute id_attr = n.attribute("id");
				if (id_attr.empty()) continue;

				const char* id_str = id_attr.value();
				u64 id;
				fromCString(Span(id_str, stringLength(id_str)), Ref(id));
				m_ways.insert(id, n);
			}
		}
		
		for (pugi::xml_node w : m_ways) {
			if (isBuilding(w)) createBuilding(w);
			else if (isRoad(w)) createRoad(w);
		}

		m_nodes.clear();
		m_ways.clear();
	}

	StudioApp& m_app;
	HashMap<u64, pugi::xml_node> m_nodes;
	HashMap<u64, pugi::xml_node> m_ways;
	double m_min_lat = 0;
	double m_min_lon = 0;
	double m_lat_range = 0.5f;
	double m_lon_range = 0.5f;
	float m_scale = 1;

	Array<Vec3>* m_lines = nullptr;
	Array<Vec3>* m_tris = nullptr;
};


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

		Mutex mutex;
		ImTextureID texture = nullptr;
		Array<u32> pixels;
	};


	struct MapsTask : public Thread
	{
		#ifdef _WIN32
			using SocketType = SOCKET;
		#else
			using SocketType = int;
			using SOCKADDR_IN = sockaddr_in;
			static constexpr int INVALID_SOCKET = -1;
			static constexpr int SOCKET_ERROR = -1;
			#define closesocket close
		#endif
		SocketType socket = INVALID_SOCKET;

		MapsTask(IAllocator& _allocator)
			: Thread(_allocator)
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

		static bool writeRawString(SocketType socket, const char* str)
		{
			int len = stringLength(str);
			int send = ::send(socket, str, len, 0);
			return send == len;
		}

		static void sendHTTPHeader(SocketType socket, const char* host, const char* path)
		{
			writeRawString(socket, "GET ");
			writeRawString(socket, path);
			writeRawString(socket, " HTTP/1.1\r\nHost: ");
			writeRawString(socket, host);
			writeRawString(socket, "\r\nConnection: close\r\n\r\n");
		}


		bool readAll(SocketType socket, Array<u8>* data) const
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
					atomicAdd(downloaded_bytes, r);
					data->resize(data->size() + r);
					memcpy(&(*data)[data->size() - r], buf, r);
				}
			}
			return true;
		}


		SocketType connect(const char* host)
		{
			SocketType socket = ::socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);
			if (socket == INVALID_SOCKET) return INVALID_SOCKET;

			SOCKADDR_IN sin = {};
			sin.sin_family = AF_INET;
			sin.sin_port = htons(80);
			
			hostent* hostname = gethostbyname(host);
			if (!hostname) return INVALID_SOCKET;

			const char* ip = inet_ntoa(**(in_addr**)hostname->h_addr_list);
			sin.sin_addr.s_addr = ip ? ::inet_addr(ip) : INADDR_ANY;

			if (::connect(socket, (const sockaddr*)&sin, sizeof(sin)) != 0) {
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
				memcpy(&out[j * stride_bytes], &pixels[j * row_size], row_size);
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

		Mutex* mutex;
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
		, m_satellite_map(4, app.getAllocator())
		, m_height_map(4, app.getAllocator())
		, m_in_progress(app.getAllocator())
		, m_queue(app.getAllocator())
		, m_osm_parser(app)
		, m_osm_lines(app.getAllocator())
		, m_osm_tris(app.getAllocator())
	{
		#ifdef _WIN32
			WORD sockVer;
			WSADATA wsaData;
			sockVer = 2 | (2 << 8);
			if (WSAStartup(sockVer, &wsaData) != 0) logError("Maps") << "Failed to init winsock.";
		#endif

		Action* action = LUMIX_NEW(app.getAllocator(), Action)("Maps", "maps", "maps");
		action->func.bind<&MapsPlugin::toggleOpen>(this);
		action->is_selected.bind<&MapsPlugin::isOpen>(this);
		app.addWindowAction(action);
		m_out_path[0] = '\0';
	}


	~MapsPlugin()
	{
		finishAllTasks();
		#ifdef _WIN32
			WSACleanup();
		#endif
		clear();
	}

	void parseOSMData(double left, double bottom, double right, double top, float scale) {
		m_osm_parser.parseOSM(left, bottom, right, top, scale, Ref(m_osm_lines), Ref(m_osm_tris));
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


	void clear()
	{
		if (m_satellite_map.texture)
		{
			m_app.getRenderInterface()->destroyTexture(m_satellite_map.texture);
			m_satellite_map.texture = nullptr;
		}
		if (m_height_map.texture)
		{
			m_app.getRenderInterface()->destroyTexture(m_height_map.texture);
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
		RenderInterface* ri = m_app.getRenderInterface();
		const int map_size = TILE_SIZE * (1 << m_size);
		m_satellite_map.texture = ri->createTexture("maps", &m_satellite_map.pixels[0], map_size, map_size);
		m_height_map.texture = ri->createTexture("maps", &m_height_map.pixels[0], map_size, map_size);

		m_is_download_deferred = false;

		int world_size = 1 << m_zoom;
		m_x = (m_x + world_size) % world_size;
		m_y = (m_y + world_size) % world_size;

		IAllocator& allocator = editor.getEngine().getAllocator();
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

	void createMapEntity() {
		WorldEditor& editor = m_app.getWorldEditor();
		const EntityRef e = editor.addEntityAt({0, 0, 0});
		editor.addComponent(Span(&e, 1), TERRAIN_TYPE);
		const PathInfo file_info(m_out_path);
		StaticString<MAX_PATH_LENGTH> mat_path(file_info.m_dir, "/", file_info.m_basename, ".mat");
		char rel_mat_path[MAX_PATH_LENGTH];
		
		if (!editor.getEngine().getFileSystem().makeRelative(Span(rel_mat_path), mat_path)) {
			logError("Maps") << "Can not load " << mat_path << " because it's not in root directory.";
		}
		editor.setProperty(TERRAIN_TYPE, -1, "Material", Span(&e, 1), Path(rel_mat_path));

		const double lat = double(tiley2lat(double(m_y + (1 << (m_size - 1))), m_zoom));
		const double width = 256 * (1 << m_size) * 156543.03 * cos(degreesToRadians(lat)) / (1 << m_zoom);
		const float scale = float(width / ((1 << m_size) * 256));
		editor.setProperty(TERRAIN_TYPE, -1, "XZ scale", Span(&e, 1), scale);
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
		RawTextureHeader header;
		header.channels_count = 1;
		header.channel_type = RawTextureHeader::ChannelType::U16;
		header.depth = 1;
		header.is_array = false;
		header.width = map_size;
		header.height = map_size;
		file.write(&header, sizeof(header));
		file.write(&raw[0], raw.byte_size());
		file.close();

		RenderInterface* ri = m_app.getRenderInterface();
		PathInfo file_info(m_out_path);
		StaticString<MAX_PATH_LENGTH> tga_path(file_info.m_dir, "/", file_info.m_basename, ".tga");
		ri->saveTexture(editor.getEngine(), tga_path, &m_satellite_map.pixels[0], map_size, map_size, true);

		StaticString<MAX_PATH_LENGTH> mat_path(file_info.m_dir, "/", file_info.m_basename, ".mat");
		OS::OutputFile mat_file;
		if (mat_file.open(mat_path)) {
			mat_file << R"#(
				shader "pipelines/terrain.shd"
				backface_culling(true)
				layer "default"
				emission(0.000000)
				metallic(0.000000)
				roughness(1.000000)
				alpha_ref(0.300000)
				defines {}
				color { 1.000000, 1.000000, 1.000000, 1.000000 }
				texture ")#" << file_info.m_basename << R"#(.raw"
				texture ""
				texture ""
				texture ""
				texture ")#" << file_info.m_basename << R"#(.tga"
				texture ""
				layer "default"
				uniform("Detail distance", 0.000000)
				uniform("Detail scale", 0.000000)
			)#";
			mat_file.close();
		}
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
			RenderInterface* ri = m_app.getRenderInterface();
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
		if (!m_osm_lines.empty()) {
			UniverseView& view = m_app.getWorldEditor().getView();
			const Vec3 cam_pos = view.getViewport().pos.toFloat();
			UniverseView::Vertex* v = view.render(true, m_osm_lines.size());
			for (i32 i = 0; i < m_osm_lines.size(); ++i) {
				v[i].pos = m_osm_lines[i] - cam_pos;
				v[i].abgr = 0xff0000ff;
			}
		}

		if (!m_osm_tris.empty()) {
			UniverseView& view = m_app.getWorldEditor().getView();
			const Vec3 cam_pos = view.getViewport().pos.toFloat();
			UniverseView::Vertex* v = view.render(false, m_osm_tris.size());
			for (i32 i = 0; i < m_osm_tris.size(); ++i) {
				v[i].pos = m_osm_tris[i] - cam_pos;
				v[i].abgr = 0xff0000FF;
			}
		}

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

		
		double bottom = double(tiley2lat(double(m_y), m_zoom));
		double left = double(tilex2long(double(m_x), m_zoom));
		double top = double(tiley2lat(double(m_y + (1 << m_size)), m_zoom));
		double right = double(tilex2long(double(m_x + (1 << m_size)), m_zoom));
		if (bottom > top) swap(bottom, top);
		if (left > right) swap(left, right);

		const float scale = float(256 * (1 << m_size) * 156543.03 * cos(degreesToRadians(bottom)) / (1 << m_zoom));

		if (ImGui::Button("OSM test")) parseOSMData(left, bottom, right, top, scale);
		if (ImGui::Button("OSM download")) {
			const StaticString<1024> osm_download_path("https://api.openstreetmap.org/api/0.6/map?bbox=", left, ",", bottom, ",", right, ",", top);
			OS::shellExecuteOpen(osm_download_path);
		}
		static double go_lat = 0;
		static double go_lon = 0;
		ImGui::InputDouble("Lat", &go_lat);
		ImGui::InputDouble("Lon", &go_lon);
		if (ImGui::Button("Go")) {
			double y = lat2tiley(go_lat, m_zoom);
			double x = long2tilex(go_lon, m_zoom);
			m_x = (int)x;
			m_y = (int)y;
			download();
		}
		ImGui::Text("Running tasks: %d", m_queue.size() + m_in_progress.size());
		ImGui::Text("Downloaded: %dkB", m_downloaded_bytes / 1024);

		if (m_is_download_deferred) download();

		if (ImGui::Combo("Size", &m_size, "1x1\0" "2x2\0" "4x4\0" "8x8\0" "16x16\0")) resize();

		int current_zoom = m_zoom;
		if (ImGui::SliderInt("Zoom", &current_zoom, m_size, MAX_ZOOM)) zoom(current_zoom - m_zoom);
		if (m_zoom > 12) {
			ImGui::Text("Heightmap might have artifacts at this level.");
		}

		ImGui::LabelText("Output", "%s", m_out_path);
		ImGui::SameLine();
		if (ImGui::Button("...")) browse();

		if (!m_satellite_map.pixels.empty() && ImGui::Button("Save")) save();
		if (m_out_path[0] && ImGui::Button("Create entity")) createMapEntity();

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
	OSMParser m_osm_parser;
	Array<Vec3> m_osm_lines;
	Array<Vec3> m_osm_tris;
};


} // anonoymous namespace


LUMIX_STUDIO_ENTRY(maps)
{
	WorldEditor& editor = app.getWorldEditor();

	auto* plugin = LUMIX_NEW(editor.getAllocator(), MapsPlugin)(app);
	app.addPlugin(*plugin);
	return nullptr;
}
