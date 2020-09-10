#define LUMIX_NO_CUSTOM_CRT
#include "editor/asset_browser.h"
#include "editor/prefab_system.h"
#include "editor/render_interface.h"
#include "editor/studio_app.h"
#include "editor/utils.h"
#include "editor/world_editor.h"
#include "editor/settings.h"
#include "engine/atomic.h"
#include "engine/crc32.h"
#include "engine/engine.h"
#include "engine/geometry.h"
#include "engine/hash_map.h"
#include "engine/log.h"
#include "engine/math.h"
#include "engine/os.h"
#include "engine/path.h"
#include "engine/prefab.h"
#include "engine/reflection.h"
#include "engine/resource_manager.h"
#include "engine/sync.h"
#include "engine/thread.h"
#include "imgui/imgui.h"
#include "renderer/material.h"
#include "renderer/render_scene.h"
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
#pragma warning(disable : 4996)



using namespace Lumix;


namespace
{

struct BoundingBox {
	DVec3 center;
	float yaw;
};

struct DVec2 {
	double x, y;
	DVec2 operator -(const DVec2& rhs) const { return {x - rhs.x, y - rhs.y}; }
};

struct TileLoc {
	TileLoc() {}
	TileLoc(int _x, int _y, int z) 
		: z(z)
	{
		const int size = 1 << z;
		x = (_x + size) % size;
		y = (_y + size) % size;
	}
	bool operator==(const TileLoc& rhs) {
		return x == rhs.x && y == rhs.y && z == rhs.z;
	}
	int x, y, z;
};

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

	bool getLatLon(pugi::xml_node nd_ref, Ref<DVec2> p) const {
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

		p = {lat, lon};
		return true;
	}

	bool toPos(pugi::xml_node nd_ref, Ref<DVec3> p) const {
		DVec2 lat_lon;
		if (!getLatLon(nd_ref, Ref(lat_lon))) return false;
		p->x = (lat_lon.y - m_min_lon) / m_lon_range * m_scale;
		p->y = 0;
		p->z = (m_min_lat + m_lat_range - lat_lon.x) / m_lat_range * m_scale;

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
		pugi::xml_node road_tag = w.find_child([](const pugi::xml_node& n){
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
		return !road_tag.empty();
	}

	static bool hasTag(const pugi::xml_node& w, const char* tag, const char* value = "") {
		pugi::xml_node building_tag = w.find_child([&](const pugi::xml_node& n){
			if (!equalStrings(n.name(), "tag")) return false;
			pugi::xml_attribute key_attr = n.attribute("k");
			if (key_attr.empty()) return false;
			if (equalStrings(key_attr.value(), tag)) {
				if (!value[0]) return true;
				
				pugi::xml_attribute value_attr = n.attribute("v");
				if (value_attr.empty()) return false;
				
				return equalStrings(value_attr.value(), value);
			}
			return false;
		});
		return !building_tag.empty();
		
	}

	void getWay(const pugi::xml_node& way, Ref<Array<DVec3>> out) const {
		RenderInterface* ri = m_app.getRenderInterface();
		Universe* universe = m_app.getWorldEditor().getUniverse();
		
		for (pugi::xml_node& c : way.children()) {
			if (equalStrings(c.name(), "nd")) {
				DVec2 lat_lon;
				getLatLon(c, Ref(lat_lon));
				DVec3 p;
				p.x = (lat_lon.y - m_min_lon) / m_lon_range * m_scale;
				p.y = 9'001;
				p.z = (m_min_lat + m_lat_range - lat_lon.x) / m_lat_range * m_scale;
				const UniverseView::RayHit hit = ri->castRay(*universe, p, Vec3(0, -1, 0), INVALID_ENTITY);
				p.y = hit.is_hit ? p.y - hit.t : 0;
				out->push(p);
			}
		}		
	}


	static bool inside(const DVec3& p, const DVec3& a, const DVec3& b, const DVec3& c) {
		const DVec3 v0 = b - a, v1 = c - a, v2 = p - a;
		const double den = v0.x * v1.z - v1.x * v0.z;
		const double v = (v2.x * v1.z - v1.x * v2.z) / den;
		const double w = (v0.x * v2.z - v2.x * v0.z) / den;
		const double u = 1.0f - v - w;
		return u >= 0 && v >= 0 && w >= 0;
	}

	static bool isEar(const Array<DVec3>& polygon, i32 i1, bool side_negative) {
		const i32 s = polygon.size();
		i32 i0 = (i1- 1 + s) % s;
		i32 i2 = (i1 + 1) % s;
		const DVec3 a = polygon[i0];
		const DVec3 b = polygon[i1];
		const DVec3 c = polygon[i2];
		
		const DVec3 ba = b - a;
		const DVec3 ca = c - a;
		const bool side_negative_2 = ba.x * ca.z - ba.z * ca.x < 0;
		if (side_negative != side_negative_2) return false;

		for (i32 i = 0; i < s; ++i) {
			if (i == i0 || i == i1 || i == i2) continue;
			if (inside(polygon[i], a, b, c)) return false;
		}
		return true;
	}

	BoundingBox createArea(const pugi::xml_node& way, u32 abgr, Ref<Array<UniverseView::Vertex>> out, IAllocator& allocator) const {
		Array<DVec3> polygon(allocator);
		getWay(way, Ref(polygon));
		if (polygon.size() < 3) return {};

		polygon.pop();

		BoundingBox res;
		res.center = DVec3(0);
		for (i32 i = 0, c = polygon.size(); i < c; ++i) {
			res.center += polygon[i];
		}
		res.center /= polygon.size();
		Vec3 dir = (polygon[0] - polygon[1]).toFloat();
		dir.y = 0;
		dir.normalize();
		res.yaw = atan2(dir.x, dir.z);

		i32 max = 0;
		i32 s = polygon.size();
		for (i32 i = 1, c = polygon.size(); i < c; ++i) {
			if (polygon[i].x > polygon[max].x) max = i;
		}

		const DVec3 a = polygon[(max - 1 + s) % s];
		const DVec3 b = polygon[max];
		const DVec3 c = polygon[(max + 1) % s];
		const DVec3 ba = b - a;
		const DVec3 ca = c - a;
		const bool side_negative = ba.x * ca.z - ba.z * ca.x < 0;
		RenderInterface* ri = m_app.getRenderInterface();
		Universe* universe = m_app.getWorldEditor().getUniverse();

		while (polygon.size() > 2) {
			for (i32 i = 0, c = polygon.size() - 1; i < c; ++i) {
				if (isEar(polygon, i, side_negative)) {
					const i32 s = polygon.size();
					DVec3 a = polygon[(i - 1 + s) % s];
					DVec3 b = polygon[i];
					DVec3 c = polygon[(i + 1) % s];
				
					polygon.erase(i);
					
					out->push({a.toFloat(), abgr});
					out->push({b.toFloat(), abgr});
					out->push({c.toFloat(), abgr});
					
					break;
				}
			}
		}
		return res;
/*		
		pugi::xml_node nd_ref = way.first_child();
		DVec3 pos;
		if (!toPos(nd_ref, Ref(pos))) return;

		// geom
		DVec3 min_pos(m_min_lon, 0, m_min_lat);
		DVec3 prev;
		pugi::xml_node n = nd_ref;
		if (!toPos(n, Ref(prev))) return;
		const DVec3 first = prev;
		Array<DVec3> vertices(allocator);
		for(;;) {
			pugi::xml_node next = n.next_sibling();
			if (next.empty() || !equalStrings(next.name(), "nd")) break;
			DVec3 p;
			if (!toPos(next, Ref(p))) break;
			vertices.push(p);

			prev = p;
			n = next;
		}*/
	}

	void clip(Ref<Vec3> a, Ref<Vec3> b, float max) const {
		const Vec3 v = b.value - a.value;
		if (a->x < 0) {
			a->z -= a->x * v.z / v.x;
			a->x = 0;
		}
		if (a->z < 0) {
			a->x -= a->z * v.x / v.z;
			a->z = 0;
		}
		if (a->x > max) {
			a->z -= (a->x - max) * v.z / v.x;
			a->x = max;
		}
		if (a->z > max) {
			a->x -= (a->z - max) * v.x / v.z;
			a->z = max;
		}
	}


	void createPolyline(const Array<DVec3>& points, u32 color, Ref<Array<UniverseView::Vertex>> out) {
		if (points.empty()) return;

		for(i32 i = 0; i < points.size() - 1; ++i) {	
			Vec3 a = points[i].toFloat();
			Vec3 b = points[i + 1].toFloat();
			clip(Ref(a), Ref(b), m_scale);
			clip(Ref(b), Ref(a), m_scale);

			if ((a-b).squaredLength() < 0.01f) continue;

			Vec3 norm = crossProduct(a - b, Vec3(0, 1, 0)).normalized();
			out->push({a - norm * 2, color});
			out->push({b - norm * 2, color});
			out->push({b + norm * 2, color});
			
			out->push({a - norm * 2, color});
			out->push({b + norm * 2, color});
			out->push({a + norm * 2, color});
		}
	}

	void parseOSM(double left, double bottom, double right, double top, float scale) {
		m_nodes.clear();
		m_ways.clear();
		FILE* fp = fopen("map.osm", "rb");
		fseek(fp, 0, SEEK_END);
		Array<char> data(m_app.getAllocator());
		data.resize(ftell(fp) + 1);
		data.back() = '\0';
		fseek(fp, 0, SEEK_SET);
		fread(data.begin(), 1, data.size(), fp);
		fclose(fp);
		const pugi::xml_parse_result res = m_doc.load_string(data.begin());
		ASSERT(pugi::status_ok == res.status);

		pugi::xml_node osm_root = m_doc.root().first_child();

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
		
		/*for (pugi::xml_node w : m_ways) {
			if (hasTag(w, "building")) createArea(w);
			else if (isRoad(w)) createRoad(w);
		}*/
	}

	StudioApp& m_app;
	pugi::xml_document m_doc;
	HashMap<u64, pugi::xml_node> m_nodes;
	HashMap<u64, pugi::xml_node> m_ways;
	double m_min_lat = 0;
	double m_min_lon = 0;
	double m_lat_range = 0.5f;
	double m_lon_range = 0.5f;
	float m_scale = 1;
};


struct MapsPlugin final : public StudioApp::GUIPlugin
{
	struct MapsTask;

	struct TileData 
	{
		TileData(int x, int y, int zoom, IAllocator& allocator) 
			: imagery_data(allocator)
			, hm_data(allocator)
		{
			const int size = 1 << zoom;
			loc.x = (x + size) % size;
			loc.y = (y + size) % size;
			loc.z = zoom;

			imagery_data.resize(TILE_SIZE * TILE_SIZE);
			hm_data.resize(TILE_SIZE * TILE_SIZE);
			memset(imagery_data.begin(), 0xff, imagery_data.byte_size());
			memset(hm_data.begin(), 0xff, hm_data.byte_size());
		}

		TileLoc loc;
		ImTextureID imagery = (ImTextureID)(intptr_t)0xffFFffFF;
		ImTextureID hm = (ImTextureID)(intptr_t)0xffFFffFF;
		Array<u32> imagery_data;
		Array<u32> hm_data;
		MapsTask* hm_task = nullptr;
		MapsTask* imagery_task = nullptr;
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

		MapsTask(StudioApp& app, TileData* tile, IAllocator& _allocator)
			: Thread(_allocator)
			, app(&app)
			, allocator(_allocator)
			, tile(*tile)
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
			int row_size = w * sizeof(u32);
			u8* out = is_heightmap ? (u8*)tile.hm_data.begin() : (u8*)tile.imagery_data.begin();
			for (int j = 0; j < h; ++j) {
				memcpy(&out[j * row_size], &pixels[j * row_size], row_size);
			}
			stbi_image_free(pixels);
			return true;
		}


		bool loadFromCache() {
			FileSystem& fs = app->getWorldEditor().getEngine().getFileSystem();
			const StaticString<MAX_PATH_LENGTH> path(fs.getBasePath(), "_maps_cache", "/", is_heightmap ? "hm" : "im", tile.loc.z, "_", tile.loc.x, "_", tile.loc.y);
			
			OS::InputFile file;
			if (file.open(path)) {
				u8* out = is_heightmap ? (u8*)tile.hm_data.begin() : (u8*)tile.imagery_data.begin();
				const bool res = file.read(out, TILE_SIZE * TILE_SIZE * sizeof(u32));
				file.close();
				return res;
			}
			return false;
		}


		void saveToCache() {
			FileSystem& fs = app->getWorldEditor().getEngine().getFileSystem();
			const StaticString<MAX_PATH_LENGTH> dir(fs.getBasePath(), "_maps_cache");
			OS::makePath(dir);
			const StaticString<MAX_PATH_LENGTH> path(dir, "/", is_heightmap ? "hm" : "im", tile.loc.z, "_", tile.loc.x, "_", tile.loc.y);
			OS::OutputFile file;
			if (file.open(path)) {
				u8* out = is_heightmap ? (u8*)tile.hm_data.begin() : (u8*)tile.imagery_data.begin();
				file.write(out, TILE_SIZE * TILE_SIZE * sizeof(u32));
				file.close();
			}
			else {
				logError("Maps") << "Fail to create " << path;
			}
		}


		int task() override
		{
			if (loadFromCache()) return 0;

			socket = connect(host);
			if (socket == INVALID_SOCKET) return -1;

			sendHTTPHeader(socket, host, path);

			Array<u8> data(allocator);
			if(!readAll(socket, &data)) return -1;
			
			const bool res = parseImage(data);
			if (res) saveToCache();
			return res ? 0 : -1;
		}

		StaticString<MAX_PATH_LENGTH> host;
		StaticString<1024> path;
		IAllocator& allocator;
		volatile i32* downloaded_bytes;
		volatile bool canceled = false;
		StudioApp* app;
		TileData& tile;
		bool is_heightmap;
	};


	MapsPlugin(StudioApp& app)
		: m_app(app)
		, m_open(false)
		, m_tiles(app.getAllocator())
		, m_cache(app.getAllocator())
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
	
	void onBeforeSettingsSaved() override {
		m_app.getSettings().setValue("is_maps_plugin_open", m_open);
	}

	void onSettingsLoaded() override {
		m_open = m_app.getSettings().getValue("is_maps_plugin_open", false);
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
		m_osm_parser.parseOSM(left, bottom, right, top, scale);
	}

	void finishAllTasks()
	{
		IAllocator& allocator = m_app.getWorldEditor().getEngine().getAllocator();
		for (MapsTask* task : m_in_progress) {
			task->canceled = true;
			closesocket(task->socket);
			task->tile.hm_task = nullptr;
			task->tile.imagery_task = nullptr;

			task->destroy();
			LUMIX_DELETE(allocator, task);
		}
		for (MapsTask* task : m_queue) {
			task->tile.hm_task = nullptr;
			task->tile.imagery_task = nullptr;
			LUMIX_DELETE(allocator, task);
		}
		m_queue.clear();
		m_in_progress.clear();
	}


	void toggleOpen() { m_open = !m_open; }
	bool isOpen() const { return m_open; }
	const char* getName() const override { return "maps"; }

	DVec2 getCenter() {
		int size = 1 << m_zoom;
		DVec2 res;
		res.x = ((m_x + size) % size + (1 << (m_size - 1))) / double(size);
		res.y = ((m_y + size) % size + (1 << (m_size - 1))) / double(size);
		res.x -= m_offset.x * pixelToWorld();
		res.y -= m_offset.y * pixelToWorld();
		return res;
	}


	void clear()
	{
		for (TileData* tile : m_tiles) {
			m_app.getRenderInterface()->destroyTexture(tile->imagery);
			m_app.getRenderInterface()->destroyTexture(tile->hm);
		}
		for (TileData* tile : m_cache) {
			m_app.getRenderInterface()->destroyTexture(tile->imagery);
			m_app.getRenderInterface()->destroyTexture(tile->hm);
		}
		m_tiles.clear();
		m_cache.clear();
	}


	static void getHeightmapPath(char* url, const TileLoc& loc)
	{
		int size = 1 << loc.z;
		sprintf(url,
			"/elevation-tiles-prod/terrarium/%d/%d/%d.png",
			loc.z,
			loc.x % size,
			loc.y % size);
	}


	static void getSatellitePath(char* url, const TileLoc& loc)
	{
		const int size = 1 << loc.z;
		sprintf(url,
			"/wmts/1.0.0/s2cloudless-2017_3857/default/g/%d/%d/%d.jpg",
			loc.z,
			loc.y % size,
			loc.x % size);
	}

	void createTile(const TileLoc& loc) {
		for (TileData* tile : m_cache) {
			if (tile->loc == loc) {
				m_tiles.push(tile);
				m_cache.eraseItem(tile);
				return;
			}
		}
		for (TileData* tile : m_tiles) {
			if (tile->loc == loc) return;
		}
		
		WorldEditor& editor = m_app.getWorldEditor();
		RenderInterface* ri = m_app.getRenderInterface();
		IAllocator& allocator = editor.getEngine().getAllocator();
		TileData& tile = *m_tiles.emplace(LUMIX_NEW(allocator, TileData)(loc.x, loc.y, loc.z, allocator));
		
		const int map_size = TILE_SIZE * (1 << m_size);

		char url[1024];
		getSatellitePath(url, loc);
		MapsTask* task = LUMIX_NEW(allocator, MapsTask)(m_app, &tile, allocator);
		// https://tiles.maps.eox.at/wmts/1.0.0/s2cloudless-2017_3857/default/g/2/1/1.jpg
		task->host = "tiles.maps.eox.at";
		task->path = url;
		task->downloaded_bytes = &m_downloaded_bytes;
		task->is_heightmap = false;
		tile.imagery_task = task;
		m_queue.push(task);

		{
			getHeightmapPath(url, loc);
			MapsTask* task = LUMIX_NEW(allocator, MapsTask)(m_app, &tile, allocator);
			task->host = "s3.amazonaws.com";
			task->path = url;
			task->downloaded_bytes = &m_downloaded_bytes;
			task->is_heightmap = true;
			tile.hm_task = task;
			m_queue.push(task);
		}
	}

	bool shouldLoad(const TileLoc& loc) const {
		if (loc.z != m_zoom) return false;

		int x = m_x;
		int y = m_y;
		int size = 1 << m_zoom;
		if (loc.x - x > size) x += size;
		if (loc.y - y > size) y += size;
		if (loc.x - x < -size) x -= size;
		if (loc.y - y < -size) y -= size;

		const int right_edge = m_offset.x < 0;
		const int left_edge = m_offset.x > 0;
		const int bottom_edge = m_offset.y < 0;
		const int top_edge = m_offset.y > 0;
		if (loc.x < m_x - left_edge) return false;
		if (loc.y < m_y - top_edge) return false;
		if (loc.x > m_x + ((1 << m_size) - 1) + right_edge) return false;
		if (loc.y > m_y + ((1 << m_size) - 1) + bottom_edge) return false;
		return true;
	}

	void download()
	{
		m_is_download_deferred = false;
		
		for (i32 i = m_tiles.size() - 1; i >= 0; --i) {
			if (!shouldLoad(m_tiles[i]->loc)) {
				m_cache.push(m_tiles[i]);
				m_tiles.swapAndPop(i);
			}
		}

		for (int j = -1; j < (1 << m_size) + 1; ++j) {
			for (int i = -1; i < (1 << m_size) + 1; ++i) {
				const TileLoc loc(m_x + i, m_y + j, m_zoom);
				if (shouldLoad(loc)) {
					createTile(loc);
				}
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
		editor.setProperty(TERRAIN_TYPE, "", -1, "Material", Span(&e, 1), Path(rel_mat_path));

		const double lat = double(tiley2lat(double(m_y + (1 << (m_size - 1))), m_zoom));
		const double width = 256 * (1 << m_size) * 156543.03 * cos(degreesToRadians(lat)) / (1 << m_zoom);
		const float scale = float(width / ((1 << m_size) * 256));
		editor.setProperty(TERRAIN_TYPE, "", -1, "XZ scale", Span(&e, 1), scale);
	}

	bool createHeightmap(const char* material_path, int size)
	{
		
		return true;
	}

	void save()
	{
		ASSERT(m_out_path[0]);
		union RGBA
		{
			struct { u8 r, g, b, a; };
			u32 rgba;
		};

		Array<u16> raw(m_app.getWorldEditor().getAllocator());
		int map_size = TILE_SIZE * (1 << m_size);
		raw.resize(map_size * map_size);

		auto for_each = [&](auto f){
			for (TileData* tile : m_tiles) {
				const RGBA* in = (const RGBA*)tile->hm_data.begin();

				const ImVec2 p = getPos(*tile);

				for (u32 j = 0; j < TILE_SIZE; ++j) {
					for (u32 i = 0; i < TILE_SIZE; ++i) {
						const i32 x = i32(p.x) + i;
						const i32 y = i32(p.y) + j;

						if (x < 0) continue;
						if (y < 0) continue;
						if (x >= map_size) continue;
						if (y >= map_size) continue;

						const RGBA rgba = in[i + j * TILE_SIZE];
						f(x, y, rgba);
					}
				}
			}
		};

		u32 min = 0xffffFFFF;
		u32 max = 0;

		for_each([&](i32 x, i32 y, const RGBA rgba){
			const u32 p = u32((rgba.r << 16) + (rgba.g << 8) + rgba.b);
			if (max < p) max = p;
			if (min > p) min = p;
		});

		double diff = max - min;
		for_each([&](i32 x, i32 y, const RGBA rgba){
			const i32 o = x + y * map_size;
			u32 p = u32((rgba.r << 16) + (rgba.g << 8) + rgba.b);
			raw[o] = u16((double(p - min) / diff) * 0xffff);
		});

		Array<u32> imagery(m_app.getWorldEditor().getAllocator());
		imagery.resize(map_size * map_size);
		for (TileData* tile : m_tiles) {
			const u32* in = tile->imagery_data.begin();

			const ImVec2 p = getPos(*tile);

			for (u32 j = 0; j < TILE_SIZE; ++j) {
				for (u32 i = 0; i < TILE_SIZE; ++i) {
					const i32 x = i32(p.x) + i;
					const i32 y = i32(p.y) + j;

					if (x < 0) continue;
					if (y < 0) continue;
					if (x >= map_size) continue;
					if (y >= map_size) continue;
						
					const i32 o = x + y * map_size;
					imagery[o] = in[i + j * TILE_SIZE];
				}
			}
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
		ri->saveTexture(editor.getEngine(), tga_path, imagery.begin(), map_size, map_size, true);

		const StaticString<MAX_PATH_LENGTH> albedo_path(file_info.m_dir, "albedo_detail.ltc");
		const StaticString<MAX_PATH_LENGTH> normal_path(file_info.m_dir, "normal_detail.ltc");
		const StaticString<MAX_PATH_LENGTH> splatmap_meta_path(file_info.m_dir, file_info.m_basename, ".tga.meta");
		
		if (!file.open(splatmap_meta_path)) {
			logError("Editor") << "Failed to create " << splatmap_meta_path;
		}
		else {
			file << "filter = \"point\"";
			file.close();
		}

		if (!file.open(albedo_path)) {
			logError("Editor") << "Failed to create " << albedo_path;
		}
		else {
			file << R"#(
				layer {
					red = { "/textures/common/red.tga", 0 },
					green = { "/textures/common/red.tga", 1 },
					blue = { "/textures/common/red.tga", 2 },
					alpha = { "/textures/common/red.tga", 3 }
				}
				layer {
					red = { "/textures/common/green.tga", 0 },
					green = { "/textures/common/green.tga", 1 },
					blue = { "/textures/common/green.tga", 2 },
					alpha = { "/textures/common/green.tga", 3 }
				}
			)#";
			file.close();
		}

		if (!file.open(normal_path)) {
			logError("Editor") << "Failed to create " << normal_path;
		}
		else {
			file << R"#(
				layer {
					red = { "/textures/common/default_normal.tga", 0 },
					green = { "/textures/common/default_normal.tga", 1 },
					blue = { "/textures/common/default_normal.tga", 2 },
					alpha = { "/textures/common/default_normal.tga", 3 }
				}
				layer {
					red = { "/textures/common/default_normal.tga", 0 },
					green = { "/textures/common/default_normal.tga", 1 },
					blue = { "/textures/common/default_normal.tga", 2 },
					alpha = { "/textures/common/default_normal.tga", 3 }
				}
			)#";
			file.close();
		}

		StaticString<MAX_PATH_LENGTH> mat_path(file_info.m_dir, "/", file_info.m_basename, ".mat");
		OS::OutputFile mat_file;
		if (mat_file.open(mat_path)) {
			mat_file << R"#(
				shader "/pipelines/terrain.shd"
				texture ")#";
			mat_file << file_info.m_basename;
			mat_file << R"#(.raw"
				texture "albedo_detail.ltc"
				texture "normal_detail.ltc"
				texture "/textures/common/white.tga"
				texture ")#" << file_info.m_basename << R"#(.tga"
				uniform("Detail distance", 50.000000)
				uniform("Detail scale", 1.000000)
				uniform("Noise UV scale", 0.200000)
				uniform("Detail diffusion", 0.500000)
				uniform("Detail power", 16.000000)
			)#";

			mat_file.close();
		}

		StaticString<MAX_PATH_LENGTH> raw_meta_path(file_info.m_dir, "/", file_info.m_basename, ".raw.meta");
		OS::OutputFile raw_meta_file;
		if (raw_meta_file.open(raw_meta_path)) {
			raw_meta_file << "wrap_mode_u = \"clamp\"\n";
			raw_meta_file << "wrap_mode_v = \"clamp\"\n";
			raw_meta_file.close();
		}

		StaticString<MAX_PATH_LENGTH> tga_meta_path(file_info.m_dir, "/", file_info.m_basename, ".tga.meta");
		OS::OutputFile tga_meta_file;
		if (tga_meta_file.open(tga_meta_path)) {
			tga_meta_file << "srgb = true\n";
			tga_meta_file << "wrap_mode_u = \"clamp\"\n";
			tga_meta_file << "wrap_mode_v = \"clamp\"\n";
			tga_meta_file.close();
		}
	}


	void checkTasks()
	{
		IAllocator& allocator = m_app.getWorldEditor().getEngine().getAllocator();
		RenderInterface* ri = m_app.getRenderInterface();

		for (int i = m_in_progress.size() - 1; i >= 0; --i) {
			MapsTask* task = m_in_progress[i];
			if (task->isFinished()) {
				m_in_progress.swapAndPop(i);
				closesocket(task->socket);
				
				TileData& tile = task->tile;
				const u8* data = task->is_heightmap ? (u8*)tile.hm_data.begin() : (u8*)tile.imagery_data.begin();
				ImTextureID& tex = task->is_heightmap ? tile.hm : tile.imagery;
				tex = ri->createTexture("maps", data, TILE_SIZE, TILE_SIZE);
				ASSERT(tex != (void*)(intptr_t)0xffFFffFF);

				task->destroy();
				LUMIX_DELETE(allocator, task);

				if (tile.imagery_task == task) tile.imagery_task = nullptr;
				if (tile.hm_task == task) tile.hm_task = nullptr;
			}
		}
	}


	void resize()
	{
		download();
	}


	void move(int dx, int dy)
	{
		m_x += dx;
		m_y += dy;
		download();
	}


	double pixelToWorld() const {
		return 1.0 / ((1 << m_zoom) * 256);
	}


	void zoom(int dz)
	{
		const DVec2 center = getCenter();
		
		int new_zoom = clamp(m_zoom + dz, m_size, MAX_ZOOM);
		dz = new_zoom - m_zoom;
		m_zoom = new_zoom;
		const int size = 1 << m_zoom;
		m_x = int(center.x * size) - 1;
		m_y = int(center.y * size) - 1;
		IVec2 offset = m_offset;
		m_offset = IVec2(0);
		const DVec2 new_center = getCenter();
		m_offset.x += int((new_center.x - center.x) / pixelToWorld());
		m_offset.y += int((new_center.y - center.y) / pixelToWorld());
		const DVec2 check = getCenter();

		download();
	}

	ImVec2 getPos(const TileData& tile) const {
		ImVec2 res;
		res.x = float(256 * (tile.loc.x - m_x)) + m_offset.x;
		res.y = float(256 * (tile.loc.y - m_y)) + m_offset.y;
		return res;
	}

	void erosionGUI() {
		static i32 iterations = 1;
		static i32 drops_count = 1024 * 1024;
		static float power = 0.01f;

		ImGuiEx::Label("Iterations");
		ImGui::InputInt("##iters", &iterations);
		ImGuiEx::Label("Drops count");
		ImGui::InputInt("##drps_cnt", &drops_count);
		ImGuiEx::Label("Power");
		ImGui::SliderFloat("##pwr", &power, 0.f, 1.f);
		WorldEditor& editor = m_app.getWorldEditor();
		const Array<EntityRef>& entities = editor.getSelectedEntities();
		if (entities.empty()) {
			ImGui::TextUnformatted("No entity selected");
			return;
		}
		Universe* universe = editor.getUniverse();
		if (!universe->hasComponent(entities[0], TERRAIN_TYPE)) {
			ImGui::TextUnformatted("Selected entity does not have terrain component");
			return;
		}
		RenderScene* scene = (RenderScene*)universe->getScene(crc32("renderer"));
		Material* mat = scene->getTerrainMaterial(entities[0]);
		if (!mat->isReady()) {
			ImGui::Text("Material %s not ready", mat->getPath().c_str());
			return;
		}
		Texture* tex = mat->getTextureByName("Heightmap");
		if (!tex) {
			ImGui::TextUnformatted("Missing heightmap");
			return;
		}
		if (!tex->isReady()) {
			ImGui::TextUnformatted("Heightmap not ready");
			return;
		}
		
		if (ImGui::Button("Erode")) {
			Array<IVec2> drops(m_app.getAllocator());
			Array<IVec2> drops2(m_app.getAllocator());
			Array<float> hmf(m_app.getAllocator());
			
			drops2.reserve(drops_count);
			const u32 w = tex->width;
			const u32 h = tex->height;
			hmf.resize(w * h);
			u16* hm = (u16*)tex->data.getMutableData();
			ASSERT(tex->data.size() == w * h * 2);
			for (u32 i = 0; i < w * h; ++i) {
				hmf[i] = hm[i];
			}

			for (i32 iter = 0; iter < iterations; ++iter) {
				drops.resize(drops_count);
				drops2.clear();
				for (IVec2& drop : drops) {
					drop.x = rand(0, w - 1);
					drop.y = rand(0, h - 1);
				}

				Array<IVec2>* from = &drops;
				Array<IVec2>* to = &drops2;
			
				auto find_low = [&](const IVec2 p){
					const IVec2 offsets[] = {
						IVec2(-1, -1),
						IVec2(-1, 0),
						IVec2(-1, 1),
						IVec2(0, -1),
						IVec2(0, 1),
						IVec2(1, -1),
						IVec2(1, 0),
						IVec2(1, 1)
					};

					float min = hmf[p.x + p.y * w];
					IVec2 min_p = p;
					for (const IVec2& o : offsets){
						IVec2 tmp = p + o;
						if (tmp.x < 0 || tmp.y < 0 || tmp.x >= (i32)w || tmp.y >= (i32)h) continue;

						if (min > hmf[tmp.x + tmp.y * w]) {
							min = hmf[tmp.x + tmp.y * w];
							min_p = tmp;
						}
					}
					return min_p;
				};

				while (!from->empty()) {
					const IVec2 drop = from->back();
					from->pop();
					const IVec2 low = find_low(drop);
					if (low != drop) {
						const u32 id = drop.x + drop.y * w;
						const u32 il = low.x + low.y * w;
						const float d = hmf[id] - hmf[il];
						const float steep = clamp(d * d, 0.f, 1.f);
						hmf[id] -= d * power * steep;
						hmf[il] += d * power * steep;
						to->push(low);
					}
				}
			}
			for (u32 i = 0; i < w * h; ++i) {
				hm[i] = (u16)hmf[i];
			}

			tex->onDataUpdated(0, 0, w, h);
		}
	}

	void onWindowGUI() override {
		while (!m_queue.empty() && m_in_progress.size() < 8) {
			MapsTask* task = m_queue.back();
			m_queue.pop();
			task->create("download_maps_task", true);
			m_in_progress.push(task);
		}
		checkTasks();

		if (!m_open) return;
		if (!ImGui::Begin(ICON_FA_MAP "Maps##maps", &m_open))
		{
			ImGui::End();
			return;
		}

		if (ImGui::BeginTabBar("tabs")) {
			if (ImGui::BeginTabItem("Map")) {
				mapGUI();
				ImGui::EndTabItem();
			}
			if (ImGui::BeginTabItem("OSM")) {
				OSMGUI();
				ImGui::EndTabItem();
			}
			if (ImGui::BeginTabItem("Erosion")) {
				erosionGUI();
				ImGui::EndTabItem();
			}
			ImGui::EndTabBar();
		}
		ImGui::End();
	}
	
	void raster(const Array<IVec2>& points, u32 w, u32 h, Ref<Array<u8>> out) {
		// naive polygon rasterization
		if (points.empty()) return;

		for (u32 pixelY = 0; pixelY < h; ++pixelY) {
			i32 nodeX[256];
			u32 nodes = 0;
			for (i32 i = 0; i < points.size() - 1; i++) {
				if (points[i].y < (double)pixelY && points[i + 1].y >= (double)pixelY ||
					points[i + 1].y < (double)pixelY && points[i].y >= (double)pixelY)
				{
					nodeX[nodes] = (i32)(points[i].x + (pixelY - (float)points[i].y) / (points[i + 1].y - (float)points[i].y) * (points[i + 1].x - (float)points[i].x));
					++nodes;
				}
			}

			qsort(nodeX, nodes, sizeof(nodeX[0]), [](const void* a, const void* b){ 
				int m = *(int*)a;
				int n = *(int*)b;
				return m == n ? 0 : (m < n ? -1 : 1); 
			});

			for (u32 i = 0; i < nodes; i += 2) {
				nodeX[i] = clamp(nodeX[i], 0, w);
				nodeX[i + 1] = clamp(nodeX[i + 1], 0, w);
				for (i32 pixelX = nodeX[i]; pixelX < nodeX[i + 1]; pixelX++) {
					out.value[pixelX + pixelY * w] = 0xff;
				}
			}
		}
	}

	static Color randomColor() {
		// HSV to RGB with S=1,V=1,H=random
		const i32 H = rand(0, 360);
		const u8 X = u8(clamp(255 * (1 - abs(fmodf(H / 60.0f, 2) - 1)), 0.f, 255.f) + 0.5);

		Color res(0);
		res.a = 0xff;

		if(H >= 0 && H < 60) {
			res.r = 255;
			res.g = X;
		}
		else if(H >= 60 && H < 120) {	
			res.r = X;
			res.g = 255;
		}
		else if(H >= 120 && H < 180) {
			res.g = 255;
			res.b = X;	
		}
		else if(H >= 180 && H < 240) {
			res.g = X;
			res.b = 255;	
		}
		else if(H >= 240 && H < 300) {
			res.r = X;
			res.b = 255;	
		}
		else {
			res.r = 255;
			res.b = X;	
		}
		return res;
	}

	static void tagInput(Span<char> key, Span<char> value, Span<const char*> values) {
		ImGuiEx::Label("Tag");
		const float w = (ImGui::GetContentRegionAvail().x - 20) * 0.5f;
		ImGui::SetNextItemWidth(w);
		ImGui::InputText("##tag_key", key.begin(), key.length());
		ImGui::SameLine();
		ImGui::SetNextItemWidth(w);
		ImGui::InputText("##tag_value", value.begin(), value.length());
		ImGui::SameLine();
		if (ImGuiEx::IconButton(ICON_FA_ELLIPSIS_H, "Common values")) {
			ImGui::OpenPopup("tag_list");
		}
		if (ImGui::BeginPopup("tag_list")) {
			for (const char* tag : values) {
				const char* tag2 = tag + stringLength(tag) + 1;
				if (ImGui::Selectable(tag[0] ? tag : tag2)) {
					copyString(value, tag);
					copyString(key, tag2);
				}
			}
			ImGui::EndPopup();
		}
	}


	void OSMGUI() {
		double bottom = double(tiley2lat(double(m_y - m_offset.y / 256.0), m_zoom));
		double left = double(tilex2long(double(m_x - m_offset.x / 256.0), m_zoom));
		double top = double(tiley2lat(double(m_y - m_offset.y / 256.0 + (1 << m_size)), m_zoom));
		double right = double(tilex2long(double(m_x - m_offset.x / 256.0 + (1 << m_size)), m_zoom));
		if (bottom > top) swap(bottom, top);
		if (left > right) swap(left, right);

		const float scale = float(256 * (1 << m_size) * 156543.03 * cos(degreesToRadians(bottom)) / (1 << m_zoom));

		if (ImGui::Button("Load map.osm")) parseOSMData(left, bottom, right, top, scale);
		ImGui::SameLine();
		if (ImGui::Button(ICON_FA_FILE_DOWNLOAD "download OSM data")) {
			const StaticString<1024> osm_download_path("https://api.openstreetmap.org/api/0.6/map?bbox=", left, ",", bottom, ",", right, ",", top);
			OS::shellExecuteOpen(osm_download_path);
		}
		if (!m_osm_tris.empty()) {
			ImGui::SameLine();
			if (ImGui::Button(ICON_FA_TRASH "clear shapes")) {
				m_osm_tris.clear();
			}
		}


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
				v[i].pos = m_osm_tris[i].pos - cam_pos;
				v[i].abgr = m_osm_tris[i].abgr;
			}
		}
		
		if (m_osm_parser.m_nodes.empty()) return;

		WorldEditor& editor = m_app.getWorldEditor();
		
		if (ImGui::CollapsingHeader("Area")) {
			ImGui::PushID("Area");
			ImGuiEx::Label("Prefab");
			static char prefab[MAX_PATH_LENGTH] = ""; 
			m_app.getAssetBrowser().resourceInput("##area_prefab", Span(prefab), PrefabResource::TYPE);
			
			static char tag_key[64] = "";
			static char tag_value[64] = "";
			const char* values[] = { 
				"forest\0landuse", 
				"residential\0landuse",
				"industrial\0landuse",
				"farmland\0landuse",
				"farmyard\0landuse",
				"cemetery\0landuse",
				"reservoir\0landuse",
				"water\0natural",
				"\0building"
			};
			tagInput(Span(tag_key), Span(tag_value), Span(values));
			static float spacing = 1.f;
			ImGuiEx::Label("Spacing");
			ImGui::DragFloat("##dens", &spacing, 0.01f);
			ImGuiEx::Label("Invert create");
			static bool invert_create = false;
			ImGui::Checkbox("##inv", &invert_create);

			if (prefab[0] && ImGui::Button("Create")) {
				Array<DVec3> polygon(m_app.getAllocator());
				Array<IVec2> points(m_app.getAllocator());
				Array<u8> bitmap(m_app.getAllocator());
				const u32 size = 256 * (1 << m_size);
				bitmap.resize(size * size);
				memset(bitmap.begin(), 0, bitmap.byte_size());
				const DVec2 from = {m_osm_parser.m_min_lat, m_osm_parser.m_min_lon};
				const DVec2 range = {m_osm_parser.m_lat_range, m_osm_parser.m_lon_range};
				
				PrefabResource* prefab_res = editor.getEngine().getResourceManager().load<PrefabResource>(Path(prefab));
				Universe* universe = m_app.getWorldEditor().getUniverse();
				for (pugi::xml_node& w : m_osm_parser.m_ways) {
					if (!OSMParser::hasTag(w, tag_key, tag_value)) continue;

					polygon.clear();
					points.clear();
					m_osm_parser.getWay(w, Ref(polygon));

					for (const DVec3 p : polygon) {
						DVec2 tmp;
						tmp.x = p.x  / m_osm_parser.m_scale * (float)size;
						tmp.y = (1 - p.z  / m_osm_parser.m_scale) * (float)size;
						points.push(IVec2((i32)tmp.x, (i32)tmp.y));
					}
					raster(points, size, size, Ref(bitmap));
				}

				RenderInterface* ri = m_app.getRenderInterface();
				const u8 ref = invert_create ? 0 : 0xff;
				Array<Transform> trs(m_app.getAllocator());
				for (float y = 0; y < size; y += spacing) {
					for (float x = 0; x < size; x += spacing) {
						if (bitmap[i32(x) + i32(y) * size] == ref) {
							DVec3 pos;
							pos.x = (x + spacing * randFloat() * 0.9f - 0.45f) / (float)size * m_osm_parser.m_scale;
							pos.y = 9'001;
							pos.z = (1 - (y + spacing * randFloat() * 0.9f - 0.45f) / (float)size) * m_osm_parser.m_scale;

							auto hit = ri->castRay(*universe, pos, Vec3(0, -1, 0), INVALID_ENTITY);
							if (hit.is_hit) {
								pos += Vec3(0, -hit.t, 0);
							}
							trs.push({pos, Quat(Vec3(0, 1, 0), randFloat() * 2 * PI), 1});
						}
					}
				}
				editor.getPrefabSystem().instantiatePrefabs(*prefab_res, trs);
			}
			
			if (prefab[0]) ImGui::SameLine();
			if (ImGui::Button("Show")) {
				const ComponentType model_instance_type = Reflection::getComponentType("model_instance");
				for (pugi::xml_node& w : m_osm_parser.m_ways) {
					if (!OSMParser::hasTag(w, tag_key, tag_value)) continue;
					const BoundingBox bb = m_osm_parser.createArea(w, randomColor().abgr(), Ref(m_osm_tris), m_app.getAllocator());
					//const EntityRef e = editor.addEntity();
					//const Quat rot(Vec3(0, 1, 0), bb.yaw);
					//editor.setEntitiesPositionsAndRotations(&e, &bb.center, &rot, 1);
					//editor.addComponent(Span(&e, 1), model_instance_type);
					//editor.setProperty(model_instance_type, "", -1, "Source", Span(&e, 1), Path("models/shapes/cube.fbx"));
				}
			}

			ImGui::PopID();
		}

		if (ImGui::CollapsingHeader("Polylines")) {
			ImGui::PushID("polyline");
			ImGuiEx::Label("Prefab");
			static char prefab[MAX_PATH_LENGTH] = ""; 
			m_app.getAssetBrowser().resourceInput("##polyline_prefab", Span(prefab), PrefabResource::TYPE);
			
			static char tag_key[64] = "";
			static char tag_value[64] = "";
			const char* values[] = { "footway\0highway", "track\0highway", "path\0highway", "tree_row\0natural", "stream\0waterway" };
			tagInput(Span(tag_key), Span(tag_value), Span(values));
			static float spacing = 1.f;
			ImGuiEx::Label("Spacing");
			ImGui::DragFloat("##spac", &spacing, 0.01f);

			if (prefab[0] && ImGui::Button("Create")) {
				PrefabResource* prefab_res = editor.getEngine().getResourceManager().load<PrefabResource>(Path(prefab));
				RenderInterface* ri = m_app.getRenderInterface();
				Universe* universe = m_app.getWorldEditor().getUniverse();
				Array<DVec3> polyline(m_app.getAllocator());
				Array<Transform> transforms(m_app.getAllocator());
				for (pugi::xml_node& w : m_osm_parser.m_ways) {
					if (!OSMParser::hasTag(w, tag_key, tag_value)) continue;

					DVec3 pos;
					DVec3 prev;
					bool first = true;
					double t = 0;
					polyline.clear();
					m_osm_parser.getWay(w, Ref(polyline));
					for (i32 i = 0; i < polyline.size() - 1; ++i) {
						DVec3 a = polyline[i];
						DVec3 b = polyline[i + 1];

						const double len = (b - a).length();

						for (; t < len; t += spacing) {
							DVec3 p = lerp(a, b, float(t / len));
							p.x += spacing * randFloat() * 0.9f - 0.45f;
							p.z += spacing * randFloat() * 0.9f - 0.45f;
							auto hit = ri->castRay(*universe, p, Vec3(0, -1, 0), INVALID_ENTITY);
							if (hit.is_hit) {
								p += Vec3(0, -hit.t, 0);
							}
							transforms.push({p, Quat(Vec3(0, 1, 0), randFloat() * 2 * PI), 1});
						}
						t -= len;
					}
				}
				editor.getPrefabSystem().instantiatePrefabs(*prefab_res, transforms);
			}

			if (ImGui::Button("Show")) {
				Array<DVec3> polyline(m_app.getAllocator());
				for (pugi::xml_node& w : m_osm_parser.m_ways) {
					if (!OSMParser::hasTag(w, tag_key, tag_value)) continue;
					polyline.clear();
					m_osm_parser.getWay(w, Ref(polyline));

					m_osm_parser.createPolyline(polyline, randomColor().abgr(), Ref(m_osm_tris));
				}
			}

			ImGui::PopID();
		}
	}

	void mapGUI() {

		if (m_is_download_deferred) download();

		ImGuiEx::Label("Size");
		if (ImGui::Combo("##size", &m_size, "256\0" "512\0" "1024\0" "2048\0" "4096\0")) resize();

		int current_zoom = m_zoom;
		ImGuiEx::Label("Zoom");
		ImGui::SetNextItemWidth(-50);
		if (ImGui::SliderInt("##zoom", &current_zoom, m_size, MAX_ZOOM)) zoom(current_zoom - m_zoom);
		ImGui::SameLine();
		if (ImGui::Button("+")) zoom(1);
		ImGui::SameLine();
		if (ImGui::Button("-")) zoom(-1);


		if (m_zoom > 12) {
			ImGui::Text("Heightmap might have artifacts at this level.");
		}

		ImGuiEx::Label("Output");
		if (ImGui::Button(StaticString<MAX_PATH_LENGTH + 128>(m_out_path[0] ? m_out_path : "Click to set"), ImVec2(-1, 0))) {
			browse();
		}

		if (m_out_path[0]) {
			if (ImGui::Button(ICON_FA_SAVE "Save textures")) save();
			ImGui::SameLine();
			if (ImGui::Button("Create entity")) createMapEntity();
		}

		ImVec2 cursor_pos = ImGui::GetCursorScreenPos();
		ImGui::PushStyleVar(ImGuiStyleVar_FramePadding, ImVec2(0, 0));
		bool hovered = false;
		if (ImGui::BeginChild("img", ImVec2(512, 512), false, ImGuiWindowFlags_NoScrollbar | ImGuiWindowFlags_NoScrollWithMouse)) {
			const ImVec2 cp = ImGui::GetCursorPos();

			for (TileData* tile : m_tiles) {
				ImVec2 p = getPos(*tile);
				float scale = 2.f / (1 << m_size);
				p = p * ImVec2(scale, scale);
				ImGui::SetCursorPos(p + cp);
				if (tile->hm != (void*)(intptr_t)0xffFFffFF && m_show_hm) ImGui::ImageButton(tile->hm, ImVec2(TILE_SIZE * scale, TILE_SIZE* scale));
				if (tile->imagery != (void*)(intptr_t)0xffFFffFF && !m_show_hm) ImGui::ImageButton(tile->imagery, ImVec2(TILE_SIZE* scale, TILE_SIZE* scale));
				hovered = hovered || ImGui::IsItemHovered();
			}
		}
		ImGui::PopStyleVar();
		ImGui::EndChild();

		if(ImGui::IsMouseDragging(0) && m_is_dragging) {
			m_offset.x = m_drag_start_offset.x + int(ImGui::GetMouseDragDelta().x) * (1 << (m_size - 1));
			m_offset.y = m_drag_start_offset.y + int(ImGui::GetMouseDragDelta().y) * (1 << (m_size - 1));
			
			const int size = 1 << m_zoom;
			if (m_offset.x > 256) {
				m_drag_start_offset.x -= 256;
				m_offset.x -= 256;
				--m_x;
			} 
			if (m_offset.x < -256) {
				m_drag_start_offset.x += 256;
				m_offset.x += 256;
				++m_x;
			} 
			if (m_offset.y > 256) {
				m_drag_start_offset.y -= 256;
				m_offset.y -= 256;
				--m_y;
			} 
			if (m_offset.y < -256) {
				m_drag_start_offset.y += 256;
				m_offset.y += 256;
				++m_y;
			} 
			download();
		}

		if (ImGui::GetIO().MouseWheel && hovered) {
			zoom(ImGui::GetIO().MouseWheel > 0 ? 1 : -1);
		}

		if (ImGui::IsMouseClicked(0) && hovered) {
			m_is_dragging = true;
			m_drag_start_offset = m_offset;
		}

		if (ImGui::IsMouseReleased(0) && m_is_dragging) {
			m_is_dragging = false;
		}

		static double go_lat_lon[2] = {};
		ImGuiEx::Label("Lat, Lon");
		ImGui::SetNextItemWidth(-30);
		ImGui::InputScalarN("##nav", ImGuiDataType_Double, &go_lat_lon, 2);
		ImGui::SameLine();
		if (ImGui::Button("Go")) {
			double y = lat2tiley(go_lat_lon[0], m_zoom);
			double x = long2tilex(go_lat_lon[1], m_zoom);
			m_x = (int)x;
			m_y = (int)y;
			download();
		}
		
		ImGuiEx::Label("Location");
		static char loc[256] = "9005;5653;14;38;-158";
		if (ImGuiEx::IconButton(ICON_FA_MAP_MARKER_ALT, "Get current location")) {
			StaticString<sizeof(loc)> tmp(m_x, ";", m_y, ";", m_zoom, ";", m_offset.x, ";", m_offset.y);
			copyString(loc, tmp);
		}
		ImGui::SameLine();
		if (ImGuiEx::IconButton(ICON_FA_COPY, "Copy to clipboard")) {
			OS::copyToClipboard(loc);
		}
		ImGui::SameLine();
		if (ImGuiEx::IconButton(ICON_FA_BULLSEYE, "View")) {
			sscanf(loc, "%d;%d;%d;%d;%d", &m_x, &m_y, &m_zoom, &m_offset.x, &m_offset.y);
			download();
		}
		ImGui::SameLine();
		ImGui::InputText("##loc", loc, sizeof(loc));

		ImGui::Checkbox("Show HeightMap", &m_show_hm);

		ImGui::Text("Running tasks: %d, Downloaded: %dkB", m_queue.size() + m_in_progress.size(), m_downloaded_bytes / 1024);
		ImGui::Text("Uses https://aws.amazon.com/public-datasets/terrain/");
		ImGui::Text("http://s3.amazonaws.com/elevation-tiles-prod/terrarium/%d/%d/%d.png", m_zoom, m_x, m_y);
		ImGui::Text("Sentinel-2 cloudless - https://s2maps.eu by EOX IT Services GmbH (Contains modified Copernicus Sentinel data 2016 & 2017)");
	}


	bool m_show_hm = false;
	StudioApp& m_app;
	Array<TileData*> m_tiles;
	Array<TileData*> m_cache;
	Array<MapsTask*> m_queue;
	Array<MapsTask*> m_in_progress;
	volatile i32 m_downloaded_bytes = 0;
	bool m_open = false;
	bool m_is_download_deferred = true;
	int m_zoom = 1;
	int m_x = 0;
	int m_y = 0;
	IVec2 m_offset{0, 0};
	// TODO handle values other than 1
	int m_size = 1;
	char m_out_path[MAX_PATH_LENGTH];
	IVec2 m_drag_start_offset;
	bool m_is_dragging = false;
	OSMParser m_osm_parser;
	Array<Vec3> m_osm_lines;
	Array<UniverseView::Vertex> m_osm_tris;
};


} // anonoymous namespace


LUMIX_STUDIO_ENTRY(maps)
{
	WorldEditor& editor = app.getWorldEditor();

	auto* plugin = LUMIX_NEW(editor.getAllocator(), MapsPlugin)(app);
	app.addPlugin(*plugin);
	return nullptr;
}
