#define LUMIX_NO_CUSTOM_CRT
#include "editor/asset_browser.h"
#include "editor/prefab_system.h"
#include "editor/render_interface.h"
#include "editor/spline_editor.h"
#include "editor/studio_app.h"
#include "editor/utils.h"
#include "editor/world_editor.h"
#include "editor/settings.h"
#include "engine/atomic.h"
#include "engine/core.h"
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
#include "engine/stack_array.h"
#include "engine/sync.h"
#include "engine/thread.h"
#include "imgui/imgui.h"
#include "renderer/editor/composite_texture.h"
#include "renderer/editor/terrain_editor.h"
#include "renderer/material.h"
#include "renderer/model.h"
#include "renderer/render_module.h"
#include "renderer/terrain.h"
#include "renderer/texture.h"
#include "stb/stb_image.h"
#include "pugixml/pugixml.hpp"

#ifdef _WIN32
	#define NOGDI
	#define WIN32_LEAN_AND_MEAN
	#include <WinSock2.h>
	#include <Windows.h>
	#include <urlmon.h>
	#pragma comment(lib, "urlmon.lib")
 #endif

#include <math.h>
#include <stdlib.h>
#pragma warning(disable : 4996)

using namespace Lumix;

namespace
{

bool download(const char* url, OutputMemoryStream& blob, u32& downloaded_bytes) {
	IStream* stream = nullptr;
	if (S_OK != URLOpenBlockingStream(nullptr, url, &stream, 0, nullptr)) {
		return false;
	}
	char buffer[4096];
	ULONG read = 0;
	HRESULT hr;
	do {
		DWORD bytesRead = 0;
		hr = stream->Read(buffer, sizeof(buffer), &bytesRead);

		if (bytesRead > 0)
		{
			blob.write(buffer, bytesRead);
		}
	} while (SUCCEEDED(hr) && hr != S_FALSE);

	return true;
}

static const ComponentType SPLINE_TYPE = reflection::getComponentType("spline");
static const ComponentType MODEL_INSTANCE_TYPE = reflection::getComponentType("model_instance");
static const ComponentType TERRAIN_TYPE = reflection::getComponentType("terrain");
static const ComponentType INSTANCED_MODEL_TYPE = reflection::getComponentType("instanced_model");
static const ComponentType CURVE_DECAL_TYPE = reflection::getComponentType("curve_decal");

enum class NodeType : u32 {
	MASK_POLYGONS,
	MASK_POLYLINES,
	PAINT_GROUND,
	INVERT,
	GRASS,
	NOISE,
	MASK_TEXTURE,
	MERGE_MASKS,
	MERGE_DISTANCE_FIELDS,
	DISTANCE_FIELD,
	PLACE_INSTANCES,
	ADJUST_HEIGHT,
	PLACE_SPLINES,
	FLATTEN_POLYLINES,
	MASK_DISTANCE
};

static const struct {
	char key;
	const char* label;
	NodeType type;
} TYPES[] = {
	{ 'H', "Adjust height", NodeType::ADJUST_HEIGHT },
	{ 'D', "Distance field", NodeType::DISTANCE_FIELD },
	{ 'F', "Flatten polylines", NodeType::FLATTEN_POLYLINES },
	{ 'R', "Grass", NodeType::GRASS },
	{ 'I', "Invert", NodeType::INVERT },
	{ 0, "Mask distance", NodeType::MASK_DISTANCE },
	{ 'P', "Mask polygons", NodeType::MASK_POLYGONS },
	{ 'L', "Mask polylines", NodeType::MASK_POLYLINES },
	{ 0, "Mask texture", NodeType::MASK_TEXTURE },
	{ 'M', "Merge distance ", NodeType::MERGE_DISTANCE_FIELDS },
	{ 0, "Merge masks", NodeType::MERGE_MASKS },
	{ 'N', "Noise", NodeType::NOISE },
	{ 'G', "Paint ground", NodeType::PAINT_GROUND },
	{ 0, "Place instances", NodeType::PLACE_INSTANCES },
	{ 'S', "Place splines", NodeType::PLACE_SPLINES },
};
	
static stbi_uc* loadTexture(const char* texture, u32& mask_w, u32& mask_h, StudioApp& app) {
	FileSystem& fs = app.getEngine().getFileSystem();
	OutputMemoryStream blob(app.getAllocator());
	if (!fs.getContentSync(Path(texture), blob)) {
		logError("Failed to read ", texture);
		return nullptr;
	}

	int w, h, ch;
	stbi_uc* rgba = stbi_load_from_memory(blob.data(), (int)blob.size(), &w, &h, &ch, 1);
	if (!rgba) {
		logError("Failed to parse ", texture);
		return nullptr;
	}
	mask_w = w;
	mask_h = h;
	return rgba;
}
	
template <typename T>
static u32 getRandomItem(float distance, const Array<T>& probs) {
	float sum = 0;

	auto get = [](float distance, const T& prob){
		if (distance < prob.distances.x) return 0.f;
		if (distance > prob.distances.w) return 0.f;
		
		if (distance < prob.distances.y) {
			return prob.multiplier * (distance - prob.distances.x) / (prob.distances.y - prob.distances.x);
		}
		else if (distance < prob.distances.z) {
			return prob.multiplier;
		}
		return prob.multiplier * (1 - (distance - prob.distances.z) / (prob.distances.w - prob.distances.z));
	};

	for (const T& prob : probs) {
		sum += get(distance, prob);
	}
	if (sum == 0) return 0;
	
	float r = randFloat() * sum;

	for (i32 i = 0; i < probs.size(); ++i) {
		const T& prob = probs[i];
		float p = get(distance, prob);
		if (r < p) return i;
		r -= p;
	}
	
	ASSERT(false);
	return 0;
}

static bool tagInput(Span<char> key, Span<char> value, Span<const char*> values, float width) {
	ImGui::TextUnformatted("Tag"); ImGui::SameLine();
	const float w = (width - 20) * 0.5f;
	ImGui::SetNextItemWidth(w);
	bool res = ImGui::InputText("##tag_key", key.begin(), key.length());
	ImGui::SameLine();
	ImGui::SetNextItemWidth(w);
	res = ImGui::InputText("##tag_value", value.begin(), value.length()) || res;
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
				res = true;
			}
		}
		ImGui::EndPopup();
	}
	return res;
}

static bool tagInput(Span<char> key, Span<char> value, float width) {
	const char* values[] = {
		"\0landuse",
		"forest\0landuse",
		"farmland\0landuse",
		"farmyard\0landuse",
		"meadow\0landuse",
		"residential\0landuse",
		"industrial\0landuse",
		"cemetery\0landuse",
		"reservoir\0landuse",
		"water\0natural",
		"\0building",
		"\0man_made",
		"\0natural",
		"\0leisure",
		"\0barrier",
		"\0tourism",
		"\0amenity",
		"\0highway",
		"footway\0highway",
		"track\0highway",
		"path\0highway",
		"tree_row\0natural",
		"stream\0waterway",
	};
	return tagInput(key, value, Span(values), width);
}

enum class OutputType {
	MASK,
	DISTANCE_FIELD
};

struct OutputValue {
	virtual ~OutputValue() {}
	virtual OutputType getType() = 0;
};

struct DistanceFieldOutput : OutputValue {
	DistanceFieldOutput(IAllocator& allocator) : m_field(allocator) {}
	OutputType getType() override { return OutputType::DISTANCE_FIELD; }
	
	float sample(float u, float v) const {
		const float x = u * (m_size - 1);
		const float y = v * (m_size - 1);
		
		const i32 i = i32(x);
		const i32 j = i32(y);

		i32 idx = i + j * m_size;
		float rx = x - i;
		float ry = y - j;

		auto get = [this](i32 i, i32 j){
			i32 idx = clamp(i, 0, m_size - 1) + clamp(j, 0, m_size - 1) * m_size;
			return m_field[idx];
		};

		const float v00 = get(i, j);
		const float v10 = get(i + 1, j);
		const float v01 = get(i, j + 1);
		const float v11 = get(i + 1, j + 1);

		return lerp(
			lerp(v00, v01, rx),
			lerp(v01, v11, rx),
			ry
		);
	}

	u32 m_size;
	Array<float> m_field;
};

struct MaskOutput : OutputValue {
	MaskOutput(IAllocator& allocator) : m_bitmap(allocator) {}
	OutputType getType() override { return OutputType::MASK; }

	u32 m_size;
	Array<u8> m_bitmap;
};

using Polygon = Array<DVec3>;
using Polygon2D = Array<DVec2>;

struct Multipolygon {
	Multipolygon(IAllocator& allocator)
		: outer_polygons(allocator)
		, inner_polygons(allocator)
	{} 

	Array<Polygon> outer_polygons;
	Array<Polygon> inner_polygons;
};

struct Multipolygon2D {
	Multipolygon2D(IAllocator& allocator)
		: outer_polygons(allocator)
		, inner_polygons(allocator)
	{} 

	Array<Polygon2D> outer_polygons;
	Array<Polygon2D> inner_polygons;
};

struct OSMParser {
	static bool samePoint(const DVec3& a, const DVec3& b) {
		if (abs(a.x - b.x) > 1e-5) return false;
		if (abs(a.y - b.y) > 1e-5) return false;
		if (abs(a.z - b.z) > 1e-5) return false;

		return true;
	}

	static bool samePoint(const DVec2& a, const DVec2& b) {
		if (abs(a.x - b.x) > 1e-5) return false;
		if (abs(a.y - b.y) > 1e-5) return false;

		return true;
	}

	static void mergePolylines(Array<Polygon>& polylines, Polygon& merged) {
		merged = polylines.back().move();
		polylines.pop();
		while (!polylines.empty()) {
			const DVec3 end = merged.back();
			bool found = false;
			for (Polygon& i : polylines) {
				if (samePoint(i[0], end)) {
					for (int j = 1; j < i.size(); ++j) {
						merged.push(i[j]);
					}
					polylines.erase(u32(&i - polylines.begin()));
					found = true;
					break;
				}
				else if (samePoint(i.back(), end)) {
					for (int j = i.size() - 2; j >= 0; --j) {
						merged.push(i[j]);
					}
					polylines.erase(u32(&i - polylines.begin()));
					found = true;
					break;
				}
			}
			if (!found) return;
		}
	}

	static void mergePolylines(Array<Polygon2D>& polylines, Polygon2D& merged) {
		merged = polylines.back().move();
		polylines.pop();
		while (!polylines.empty()) {
			const DVec2 end = merged.back();
			bool found = false;
			for (Polygon2D& i : polylines) {
				if (samePoint(i[0], end)) {
					for (int j = 1; j < i.size(); ++j) {
						merged.push(i[j]);
					}
					polylines.erase(u32(&i - polylines.begin()));
					found = true;
					break;
				}
				else if (samePoint(i.back(), end)) {
					for (int j = i.size() - 2; j >= 0; --j) {
						merged.push(i[j]);
					}
					polylines.erase(u32(&i - polylines.begin()));
					found = true;
					break;
				}
			}
			if (!found) return;
		}
	}

	static bool hasAttributeValue(pugi::xml_node n, const char* key, const char* value) {
		pugi::xml_attribute attr = n.attribute(key);
		if (attr.empty()) return false;

		const char* str = attr.value();
		return equalStrings(str, value);
	}

	template <typename T>
	static bool getAttributeValue(pugi::xml_node n, const char* key, T& out) {
		pugi::xml_attribute attr = n.attribute(key);
		if (attr.empty()) return false;
		const char* str = attr.value();
		fromCString(Span(str, stringLength(str)), out);
		return true;
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

	OSMParser(StudioApp& app)
		: m_app(app) 
		, m_nodes(m_app.getAllocator())
		, m_ways(m_app.getAllocator())
		, m_relations(m_app.getAllocator())
	{
	}

	bool getLatLon(pugi::xml_node nd_ref, DVec2& p) const {
		if (nd_ref.empty() || !equalStrings(nd_ref.name(), "nd")) return false;

		pugi::xml_attribute ref_attr = nd_ref.attribute("ref");
		if (ref_attr.empty()) return false;
		const char* ref_str = ref_attr.value();
		u64 node_id;
		fromCString(Span(ref_str, (u32)strlen(ref_str)), node_id);

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
	
	template <typename F>
	void forEachWayInRelation(pugi::xml_node relation, F& f) const {
		for (pugi::xml_node n = relation.first_child(); !n.empty(); n = n.next_sibling()) {
			if (!equalStrings(n.name(), "member")) continue;
			if (!hasAttributeValue(n, "type", "way")) continue;

			u64 ref;
			if (!getAttributeValue(n, "ref", ref)) continue;
		
			auto iter = m_ways.find(ref);
			if (!iter.isValid()) continue;

			pugi::xml_attribute role_attr = n.attribute("role");
			const char* role = role_attr.empty() ? "" : role_attr.value();

			f(iter.value(), role);
		}
	}

	void getMultipolygon(pugi::xml_node relation, Multipolygon& multipolygon, EntityRef terrain) {
		Array<Polygon> polylines(m_app.getAllocator());
		forEachWayInRelation(relation, [&](const pugi::xml_node& w, const char* role){
			if (!equalStrings(role, "outer")) return;

			Polygon& polygon = polylines.emplace(m_app.getAllocator());
			getWay(w, terrain, polygon);
		});
		
		multipolygon.outer_polygons.clear();
		while(!polylines.empty()) {
			mergePolylines(polylines, multipolygon.outer_polygons.emplace(m_app.getAllocator()));
		}

		polylines.clear();
		forEachWayInRelation(relation, [&](const pugi::xml_node& w, const char* role){
			if (!equalStrings(role, "inner")) return;

			Polygon& polygon = polylines.emplace(m_app.getAllocator());
			getWay(w, terrain, polygon);
		});
		
		multipolygon.inner_polygons.clear();
		while(!polylines.empty()) {
			mergePolylines(polylines, multipolygon.inner_polygons.emplace(m_app.getAllocator()));
		}
	}

	void getMultipolygon(pugi::xml_node relation, Multipolygon2D& multipolygon) {
		Array<Polygon2D> polylines(m_app.getAllocator());
		forEachWayInRelation(relation, [&](const pugi::xml_node& w, const char* role){
			if (!equalStrings(role, "outer")) return;

			Polygon2D& polygon = polylines.emplace(m_app.getAllocator());
			getWay(w, polygon);
		});
		
		multipolygon.outer_polygons.clear();
		while(!polylines.empty()) {
			Polygon2D& merged = multipolygon.outer_polygons.emplace(m_app.getAllocator());
			mergePolylines(polylines, merged);
			if (!samePoint(merged[0], merged.back())) {
				merged.push(merged[0]);
			}
		}

		polylines.clear();
		forEachWayInRelation(relation, [&](const pugi::xml_node& w, const char* role){
			if (!equalStrings(role, "inner")) return;

			Polygon2D& polygon = polylines.emplace(m_app.getAllocator());
			getWay(w, polygon);
		});
		
		multipolygon.inner_polygons.clear();
		while(!polylines.empty()) {
			mergePolylines(polylines, multipolygon.inner_polygons.emplace(m_app.getAllocator()));
		}
	}

	pugi::xml_node getNode(const pugi::xml_node& nd_ref) {
		if (nd_ref.empty() || !equalStrings(nd_ref.name(), "nd")) return pugi::xml_node();
		
		pugi::xml_attribute ref_attr = nd_ref.attribute("ref");
		if (ref_attr.empty()) return pugi::xml_node();
		const char* ref_str = ref_attr.value();
		u64 node_id;
		fromCString(Span(ref_str, (u32)strlen(ref_str)), node_id);

		auto iter = m_nodes.find(node_id);
		if (!iter.isValid()) return pugi::xml_node();

		return iter.value();
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

	void getWay(const pugi::xml_node& way, EntityRef terrain, Array<DVec3>& out) const {
		WorldEditor& editor = m_app.getWorldEditor();
		World* world = editor.getWorld();
		RenderModule* module = (RenderModule*)world->getModule(TERRAIN_TYPE);
		const double y_base = world->getPosition(terrain).y;
		
		for (pugi::xml_node& c : way.children()) {
			if (equalStrings(c.name(), "nd")) {
				DVec2 lat_lon;
				getLatLon(c, lat_lon);
				DVec3 p;
				p.x = (lat_lon.y - m_min_lon) / m_lon_range * m_scale;
				p.z = (m_min_lat + m_lat_range - lat_lon.x) / m_lat_range * m_scale;
				p.y = module->getTerrainHeightAt(terrain, (float)p.x, (float)p.z) + y_base;
				p.x -= m_scale * 0.5f;
				p.z -= m_scale * 0.5f;
				out.push(p);
			}
		}		
	}

	void getWay(const pugi::xml_node& way, Array<DVec2>& out) const {
		for (pugi::xml_node& c : way.children()) {
			if (equalStrings(c.name(), "nd")) {
				DVec2 lat_lon;
				getLatLon(c, lat_lon);
				DVec2 p;
				p.x = (lat_lon.y - m_min_lon) / m_lon_range * m_scale - m_scale * 0.5f;
				p.y = (m_min_lat + m_lat_range - lat_lon.x) / m_lat_range * m_scale - m_scale * 0.5f;
				out.push(p);
			}
		}		
	}

	void createPolyline(const Array<DVec3>& points, u32 color, Array<WorldView::Vertex>& out) {
		if (points.empty()) return;

		const float half_extents = m_scale * 0.5f;
		for(i32 i = 0; i < points.size() - 1; ++i) {	
			Vec3 a = Vec3(points[i]) + Vec3(0, 1, 0);
			Vec3 b = Vec3(points[i + 1]) + Vec3(0, 1, 0);

			if (squaredLength(a-b) < 0.01f) continue;

			Vec3 norm = normalize(cross(a - b, Vec3(0, 1, 0)));
			out.push({a - norm * 2, color});
			out.push({b - norm * 2, color});
			out.push({b + norm * 2, color});
			
			out.push({a - norm * 2, color});
			out.push({b + norm * 2, color});
			out.push({a + norm * 2, color});
		}
	}

	[[nodiscard]] bool parseOSM(double left, double bottom, double right, double top, float scale, const OutputMemoryStream& data) {
		m_nodes.clear();
		m_ways.clear();
		m_relations.clear();
		
		const pugi::xml_parse_result res = m_doc.load_buffer(data.data(), data.size());
		if (pugi::status_ok != res.status) return false;

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
				fromCString(Span(id_str, stringLength(id_str)), id);
				m_nodes.insert(id, n);
			}
			else if (equalStrings(n.name(), "way")) {
				pugi::xml_attribute id_attr = n.attribute("id");
				if (id_attr.empty()) continue;

				const char* id_str = id_attr.value();
				u64 id;
				fromCString(Span(id_str, stringLength(id_str)), id);
				m_ways.insert(id, n);
			}
			else if (equalStrings(n.name(), "relation")) {
				pugi::xml_attribute id_attr = n.attribute("id");
				if (id_attr.empty()) continue;

				const char* id_str = id_attr.value();
				u64 id;
				fromCString(Span(id_str, stringLength(id_str)), id);
				m_relations.insert(id, n);
			}
		}
		
		return true;
	}

	StudioApp& m_app;
	pugi::xml_document m_doc;
	HashMap<u64, pugi::xml_node> m_nodes;
	HashMap<u64, pugi::xml_node> m_ways;
	HashMap<u64, pugi::xml_node> m_relations;
	double m_min_lat = 0;
	double m_min_lon = 0;
	double m_lat_range = 0.5f;
	double m_lon_range = 0.5f;
	float m_scale = 1;
};

static double long2tilex(double long lon, int z) {
	return (lon + 180) * (1 << z) / 360.0;
}

static double tilex2long(double x, int z) {
	return x / pow(2.0, z) * 360.0 - 180;
}

static double lat2tiley(double lat, int z) { 
	const double latrad = lat * PI / 180.0;
	return (1.0 - asinh(tan(latrad)) / PI) / 2.0 * (1 << z); 
}

static double tiley2lat(double y, int z) {
	double n = PI - 2.0 * PI * y / pow(2.0, z);
	return 180.0 / PI * atan(0.5 * (exp(n) - exp(-n)));
}

struct OSMNodeEditor : NodeEditor {
	struct Node : NodeEditorNode {
		Node(OSMNodeEditor& editor) 
			: m_editor(editor)
			, m_error(editor.m_allocator)
		{}

		virtual NodeType getType() const = 0;
		virtual void serialize(OutputMemoryStream& blob) = 0;
		virtual void deserialize(InputMemoryStream& blob) = 0;
		virtual bool gui() = 0;
		virtual UniquePtr<OutputValue> getOutputValue(u16 output_idx) = 0;

		bool nodeGUI() override {
			ImGuiEx::BeginNode(m_id, m_pos, &m_selected);
			m_input_counter = 0;
			m_output_counter = 0;
			bool res = gui();
			
			if (m_error.length() > 0) {
				ImGui::PushStyleColor(ImGuiCol_Border, IM_COL32(0xff, 0, 0, 0xff));
			}
			ImGuiEx::EndNode();
			if (m_error.length() > 0) {
				ImGui::PopStyleColor();
				if (ImGui::IsItemHovered()) ImGui::SetTooltip("%s", m_error.c_str());
			}

			return res;
		}

		ImGuiEx::PinShape toShape(OutputType type) {
			switch (type) {
				case OutputType::MASK: return ImGuiEx::PinShape::CIRCLE;
				case OutputType::DISTANCE_FIELD: return ImGuiEx::PinShape::SQUARE;
			}
			return ImGuiEx::PinShape::CIRCLE;
		}

		void inputSlot(OutputType type = OutputType::MASK) {
			ImGuiEx::Pin(m_id | ((u32)m_input_counter << 16), true, toShape(type));
			++m_input_counter;
		}
	
		void outputSlot(OutputType type = OutputType::MASK) {
			ImGuiEx::Pin(m_id | ((u32)m_output_counter << 16) | OUTPUT_FLAG, false, toShape(type));
			++m_output_counter;
		}

		struct Input {
			Node* node = nullptr;
			u16 output_idx;
			operator bool() const { return node; }
		};

		void nodeTitle(const char* label) {
			ImGuiEx::BeginNodeTitleBar();
			ImGui::TextUnformatted(label);
			previewButton();
			ImGuiEx::EndNodeTitleBar();
		}

		UniquePtr<OutputValue> outputError(const char* msg) { m_error = msg; return {}; }
		void error(const char* msg) { m_error = msg; }

		template <int N>
		bool textureMaskInput(StaticString<N>& texture) {
			char basename[LUMIX_MAX_PATH];
			copyString(Span(basename), Path::getBasename(texture));
			bool res = false;
			if (ImGui::Button(basename[0] ? basename : "Click to select", ImVec2(150, 0))) m_show_mask_open = true;
			ImGui::SameLine();
			if (ImGuiEx::IconButton(ICON_FA_TIMES, "Clear")) {
				texture = "";
				return true;
			}
			FileSelector& fs = m_editor.m_app.getFileSelector();
			if (fs.gui("Select mask texture", &m_show_mask_open, "tga", false)) {
				texture = fs.getPath();
				res = true;
			}
			return false;
		}

		void clearErrors() {
			for (Node* n : m_editor.m_nodes) {
				n->m_error = "";
			}
		}

		void previewButton() {
			ImGui::SameLine();
			if (ImGui::Button(ICON_FA_SEARCH) && ensureOSMData()) {
				clearErrors();

				UniquePtr<OutputValue> out = getOutputValue(0);
				if (out) {
					switch(out->getType()) {
						case OutputType::MASK: m_editor.visualize((MaskOutput*)out.get()); break;
						case OutputType::DISTANCE_FIELD: m_editor.visualize((DistanceFieldOutput*)out.get()); break;
					}
				}
			}
		}

		bool ensureOSMData() {
			if (m_editor.m_osm_parser.m_nodes.size() == 0 && m_editor.m_osm_parser.m_ways.size() == 0) {
				m_editor.m_show_osm_download_dialog = true;
				return false;
			}
			return true;
		}

		UniquePtr<OutputValue> getInput(u16 input_idx);

		OSMNodeEditor& m_editor;
		String m_error;
		u32 m_input_counter;
		u32 m_output_counter;
		bool m_selected = false;
		bool m_show_mask_open = false;
	};

	OSMNodeEditor(struct MapsPlugin& plugin, StudioApp& app)
		: NodeEditor(app.getAllocator())
		, m_app(app)
		, m_allocator(app.getAllocator())
		, m_links(app.getAllocator())
		, m_nodes(app.getAllocator())
		, m_recent_paths(app.getAllocator())
		, m_osm_parser(app)
	{
		pushUndo(NO_MERGE_UNDO);

		m_delete_action.init(ICON_FA_TRASH "Delete", "Maps node delete", "maps_nodes_delete", ICON_FA_TRASH, os::Keycode::DEL, Action::Modifiers::NONE, true);
		m_delete_action.func.bind<&OSMNodeEditor::deleteSelectedNodes>(this);
		m_delete_action.plugin = &plugin;*this, 

		m_save_action.init(ICON_FA_SAVE "Save", "Maps nodes save", "maps_nodes_save", ICON_FA_SAVE, os::Keycode::S, Action::Modifiers::CTRL, true);
		m_save_action.func.bind<&OSMNodeEditor::save>(this);
		m_save_action.plugin = &plugin;*this, 

		m_run_action.init(ICON_FA_PLAY "Run", "Maps nodes run", "maps_nodes_run", ICON_FA_PLAY, (os::Keycode)'P', Action::Modifiers::CTRL, true);
		m_run_action.func.bind<&OSMNodeEditor::run>(this);
		m_run_action.plugin = &plugin;*this, 

		m_undo_action.init(ICON_FA_UNDO "Undo", "Maps nodes undo", "maps_nodes_undo", ICON_FA_UNDO, os::Keycode::Z, Action::Modifiers::CTRL, true);
		m_undo_action.func.bind<&OSMNodeEditor::undo>((SimpleUndoRedo*)this);
		m_undo_action.plugin = &plugin;*this, 

		m_redo_action.init(ICON_FA_REDO "Redo", "Maps nodes redo", "maps_nodes_redo", ICON_FA_REDO, os::Keycode::Z, Action::Modifiers::CTRL | Action::Modifiers::SHIFT, true);
		m_redo_action.func.bind<&OSMNodeEditor::redo>((SimpleUndoRedo*)this);
		m_redo_action.plugin = &plugin;

		app.addAction(&m_delete_action);
		app.addAction(&m_save_action);
		app.addAction(&m_run_action);
		app.addAction(&m_undo_action);
		app.addAction(&m_redo_action);
	}

	~OSMNodeEditor() {
		m_app.removeAction(&m_delete_action);
		m_app.removeAction(&m_save_action);
		m_app.removeAction(&m_run_action);
		m_app.removeAction(&m_undo_action);
		m_app.removeAction(&m_redo_action);
		destroyPreviewTexture();
	}

	void run();

	void colorLinks() {
		const ImU32 colors[] = {
			IM_COL32(0x20, 0x20, 0xA0, 0xFF),
			IM_COL32(0x20, 0xA0, 0x20, 0xFF),
			IM_COL32(0x20, 0xA0, 0xA0, 0xFF),
			IM_COL32(0xA0, 0x20, 0x20, 0xFF),
			IM_COL32(0xA0, 0x20, 0xA0, 0xFF),
			IM_COL32(0xA0, 0xA0, 0x20, 0xFF),
			IM_COL32(0xA0, 0xA0, 0xA0, 0xFF),
		};
	
		for (i32 i = 0, c = m_links.size(); i < c; ++i) {
			NodeEditorLink& l = m_links[i];
			l.color = colors[i % lengthOf(colors)];
		}
	}

	void pushUndo(u32 tag) override {
		colorLinks();
		SimpleUndoRedo::pushUndo(tag);
	}

	TerrainEditor* getTerrainEditor() {
		for (StudioApp::MousePlugin* p : m_app.getMousePlugins()) {
			if (equalStrings(p->getName(), "terrain_editor")) {
				return static_cast<TerrainEditor*>(p);
			}
		}
		return nullptr;
	}

	void onBeforeSettingsSaved(Settings& settings) {
		for (const String& p : m_recent_paths) {
			const u32 i = u32(&p - m_recent_paths.begin());
			const StaticString<32> key("maps_plugin_recent_", i);
			settings.setValue(Settings::LOCAL, key, p.c_str());
		}
	}

	void onSettingsLoaded(Settings& settings) {
		m_recent_paths.clear();
		char tmp[LUMIX_MAX_PATH];
		FileSystem& fs = m_app.getEngine().getFileSystem();
		for (u32 i = 0; ; ++i) {
			const StaticString<32> key("maps_plugin_recent_", i);
			const u32 len = settings.getValue(Settings::LOCAL, key, Span(tmp));
			if (len == 0) break;
			if (fs.fileExists(tmp)) {
				m_recent_paths.emplace(tmp, m_app.getAllocator());
			}
		}
	}

	void deleteSelectedNodes() {
		if (m_is_any_item_active) return;
		for (i32 i = m_nodes.size() - 1; i >= 0; --i) {
			Node* node = m_nodes[i];
			if (node->m_selected) {
				for (i32 j = m_links.size() - 1; j >= 0; --j) {
					if (m_links[j].getFromNode() == node->m_id || m_links[j].getToNode() == node->m_id) {
						m_links.erase(j);
					}
				}

				LUMIX_DELETE(m_allocator, node);
				m_nodes.swapAndPop(i);
			}
		}		
		pushUndo(NO_MERGE_UNDO);
	}

	void destroyPreviewTexture() {
		RenderInterface* ri = m_app.getRenderInterface();
		if (!ri) return;
		if (m_preview_texture == (ImTextureID)(intptr_t)0xffFFffFF) return;
		ri->destroyTexture(m_preview_texture);
		m_preview_texture = (ImTextureID)(intptr_t)0xffFFffFF;
	}

	void visualize(DistanceFieldOutput* df) {
		destroyPreviewTexture();
		
		RenderInterface* ri = m_app.getRenderInterface();
		Array<u32> tmp(m_app.getAllocator());
		tmp.resize(df->m_field.size());
		for (u32 i = 0, c = df->m_field.size(); i < c; ++i) {
			u8 vp = u8(clamp(df->m_field[i], 0.f, 255.f));
			u8 vn = u8(clamp(-df->m_field[i], 0.f, 255.f));
			tmp[i] = Color(vn, vp, 0, 0xff).abgr();
		}
		m_preview_texture = ri->createTexture("maps_debug", tmp.begin(), df->m_size, df->m_size);
		m_preview_size = df->m_size;
		m_show_preview = true;
	}	

	void visualize(MaskOutput* mask) {
		destroyPreviewTexture();
		RenderInterface* ri = m_app.getRenderInterface();
		Array<u32> tmp(m_app.getAllocator());
		tmp.resize(mask->m_bitmap.size());
		for (u32 i = 0, c = mask->m_bitmap.size(); i < c; ++i) {
			u32 v = mask->m_bitmap[i] > 0 ? 0xff : 0;
			tmp[i] = Color(v, v, v, 0xff).abgr();
		}
		m_preview_texture = ri->createTexture("maps_debug", tmp.begin(), mask->m_size, mask->m_size);
		m_preview_size = mask->m_size;
		m_show_preview = true;
	}

	void pushRecent(const char* path) {
		Path p(path);
		m_recent_paths.eraseItems([&](const String& s) { return s == path; });
		m_recent_paths.emplace(p.c_str(), m_app.getAllocator());
	}

	Node* addNode(NodeType type, ImVec2 pos);

	struct Header {
		static const u32 MAGIC = 'LMAP';
		u32 magic = MAGIC;
		u32 version = 0;
	};

	void deserialize(InputMemoryStream& blob) override {
		for (Node* n : m_nodes) LUMIX_DELETE(m_app.getAllocator(), n);
		m_nodes.clear();
		m_links.clear();

		Header header;
		blob.read(header);
		u32 count;
		blob.read(count);
		m_links.resize(count);
		for (NodeEditorLink& link : m_links) {
			blob.read(link.from);
			blob.read(link.to);
		}
		blob.read(count);
		for (u32 i = 0; i < count; ++i) {
			NodeType type;
			blob.read(type);
			Node* n = addNode(type, Vec2(0, 0));
			blob.read(n->m_id);
			blob.read(n->m_pos);
			n->deserialize(blob);
		}
	}
	
	void serialize(OutputMemoryStream& blob) override {
		Header header;
		blob.write(header);
		blob.write(m_links.size());
		for (const NodeEditorLink& link : m_links) {
			blob.write(link.from);
			blob.write(link.to);
		}
		blob.write(m_nodes.size());
		for (Node* node : m_nodes) {
			blob.write(node->getType());
			blob.write(node->m_id);
			blob.write(node->m_pos);
			node->serialize(blob);
		}
	}
	
	void onCanvasClicked(ImVec2 pos, i32 hovered_link) override {
		for (const auto& t : TYPES) {
			if (t.key && os::isKeyDown((os::Keycode)t.key)) {
				Node* node = addNode(t.type, pos);
				if (hovered_link >= 0) splitLink(m_nodes.back(), m_links, hovered_link);
				pushUndo(NO_MERGE_UNDO);
				break;
			}
		}
	}

	void onLinkDoubleClicked(NodeEditorLink& link, ImVec2 pos) override {}

	void onContextMenu(ImVec2 pos) override {
		static char filter[64] = "";
		ImGuiEx::filter("Filter", filter, sizeof(filter), 150, ImGui::IsWindowAppearing());
		Node* new_node = nullptr;
		for (const auto& t : TYPES) {
			StaticString<64> label(t.label);
			if (t.key) {
				label.append(" (LMB + ", t.key, ")");
			}
			if ((!filter[0] || stristr(t.label, filter) != nullptr) && (ImGui::IsKeyPressed(ImGuiKey_Enter) || ImGui::MenuItem(label))){
				new_node = addNode(t.type, pos);
				pushUndo(NO_MERGE_UNDO);
				filter[0] = '\0';
				ImGui::CloseCurrentPopup();
				break;
			}
		}
	}

	void open(const char* path) {
		m_show_welcome_screen = false;
		FileSystem& fs = m_app.getEngine().getFileSystem();
		
		OutputMemoryStream blob(m_app.getAllocator());
		if (!fs.getContentSync(Path(path), blob)) {
			logError("Could not load ", path);
			return;
		}
		InputMemoryStream tmp(blob);
		deserialize(tmp);
		pushUndo(NO_MERGE_UNDO);
		m_path = path;
		pushRecent(path);
	}

	void saveAs(const char* path) {
		OutputMemoryStream blob(m_app.getAllocator());
		serialize(blob);
		
		FileSystem& fs = m_app.getEngine().getFileSystem();
		if (!fs.saveContentSync(Path(path), blob)) {
			logError("Could not save ", path);
			return;
		}
		
		m_path = path;
		pushRecent(path);
	}

	void save() {
		if (m_path.isEmpty()) m_show_save_as = true;
		else saveAs(m_path.c_str());
	}

	void gui(i32 x, i32 y, IVec2 pixel_offset, i32 zoom, float scale, i32 size) {
		if (m_show_preview) {
			ImGui::OpenPopup("Preview");
			m_show_preview = false;
			m_preview_size = minimum(512, m_preview_size);
		}
		if (ImGui::BeginPopup("Preview")) {
			ImGui::Image(m_preview_texture, ImVec2((float)m_preview_size, (float)m_preview_size));
			ImGui::EndPopup();
		}
		ImGui::BeginChild("osm", ImVec2(0, 0), false, ImGuiWindowFlags_MenuBar);

		double dl_bottom = double(tiley2lat(double(y - (pixel_offset.y - m_area_edge) / 256.0), zoom));
		double dl_left = double(tilex2long(double(x - (pixel_offset.x - m_area_edge) / 256.0), zoom));
		double dl_top = double(tiley2lat(double(y - m_area_edge / 256.0 - pixel_offset.y / 256.0 + (1 << size)), zoom));
		double dl_right = double(tilex2long(double(x - m_area_edge / 256.0 - pixel_offset.x / 256.0 + (1 << size)), zoom));

		double bottom = double(tiley2lat(double(y - pixel_offset.y / 256.0), zoom));
		double left = double(tilex2long(double(x - pixel_offset.x / 256.0), zoom));
		double top = double(tiley2lat(double(y - pixel_offset.y / 256.0 + (1 << size)), zoom));
		double right = double(tilex2long(double(x - pixel_offset.x / 256.0 + (1 << size)), zoom));
		if (bottom > top) swap(bottom, top);
		if (left > right) swap(left, right);
		if (dl_bottom > dl_top) swap(dl_bottom, dl_top);
		if (dl_left > dl_right) swap(dl_left, dl_right);

		const float level_scale = scale * float(256 * (1 << size) * 156543.03 * cos(degreesToRadians(bottom)) / (1 << zoom));

		auto downloadOSMData = [&](){
			const StaticString<1024> osm_download_path("https://api.openstreetmap.org/api/0.6/map?bbox=", dl_left, ",", dl_bottom, ",", dl_right, ",", dl_top);
			const StableHash url_hash(osm_download_path.data, stringLength(osm_download_path.data));
			const Path cache_path(".lumix/maps_cache/osm_", url_hash.getHashValue());
			FileSystem& fs = m_app.getEngine().getFileSystem();
			OutputMemoryStream blob(m_allocator);
			u32 downloaded_bytes;
			if (fs.fileExists(cache_path) && fs.getContentSync(cache_path, blob)) {
				if (!m_osm_parser.parseOSM(left, bottom, right, top, level_scale, blob)) {
					logError("Failed to parse ", osm_download_path);
				}
				else {
					logInfo(osm_download_path, " loaded from cache - ", cache_path);
				}
			}
			else if (download(osm_download_path, blob, downloaded_bytes)) {
				logInfo("Downloaded ", osm_download_path, " (", downloaded_bytes / 1024, "kB)");
				if (!fs.saveContentSync(cache_path, blob)) {
					logWarning("Could not save ", cache_path);
				}
				if (!m_osm_parser.parseOSM(left, bottom, right, top, level_scale, blob)) {
					logError("Failed to parse ", osm_download_path);
				}
			}
			else {
				logError("Failed to download ", osm_download_path);
			}
		};

		if (ImGui::BeginMenuBar()) {
			if (ImGui::BeginMenu("File")) {
				menuItem(m_save_action, true);
				if (ImGui::MenuItem("Save As")) m_show_save_as = true;
				if (ImGui::MenuItem("Open")) m_show_open = true;
				if (ImGui::BeginMenu("Recent", !m_recent_paths.empty())) {
					for (const String& s : m_recent_paths) {
						if (ImGui::MenuItem(s.c_str())) open(s.c_str());
					}
					ImGui::EndMenu();
				}
				menuItem(m_run_action, true);
				ImGui::EndMenu();
			}
			if (ImGui::BeginMenu("OSM data")) {
				if (ImGui::MenuItem(ICON_FA_FILE_DOWNLOAD "Download")) {
					downloadOSMData();
				}
				ImGui::DragInt("Area edge", &m_area_edge);
				ImGui::EndMenu();
			}
			if (ImGui::BeginMenu("Edit")) {
				menuItem(m_undo_action, canUndo());
				menuItem(m_redo_action, canRedo());
				ImGui::EndMenu();
			}
			ImGui::EndMenuBar();
		}

		FileSelector& fs = m_app.getFileSelector();
		if (fs.gui("Open", &m_show_open, "mgr", false)) open(fs.getPath());
		if (fs.gui("Save As", &m_show_save_as, "mgr", true)) saveAs(fs.getPath());

		if (m_show_welcome_screen) {
			if (ImGui::Button("New graph")) m_show_welcome_screen = false;
			ImGui::SameLine();
			if (ImGui::Button("Open")) {
				m_show_open = true;
				m_show_welcome_screen = false;
			}

			if (!m_recent_paths.empty()) {
				ImGui::TextUnformatted("Recent:");
				for (const String& s : m_recent_paths) {
					if (ImGui::Selectable(s.c_str())) {
						m_show_welcome_screen = false;
						open(s.c_str());
					}
				}
			}
		}
		else {
			nodeEditorGUI(m_nodes, m_links);
		}
		ImGui::EndChild();

		if (m_show_osm_download_dialog) {
			m_show_osm_download_dialog = false;
			ImGui::OpenPopup("Download OSM data");
		}
		if (ImGui::BeginPopupModal("Download OSM data")) {
			ImGui::TextUnformatted("OSM data empty");
			if (ImGui::Button("Download")) {
				downloadOSMData();
				ImGui::CloseCurrentPopup();
			}
			ImGui::SameLine();
			if (ImGui::Button("Close")) ImGui::CloseCurrentPopup();
			ImGui::EndPopup();
		}
	}

	OSMParser m_osm_parser;
	StudioApp& m_app;
	IAllocator& m_allocator;
	Array<NodeEditorLink> m_links;
	Array<Node*> m_nodes;
	u32 m_node_id_genereator = 1;
	Array<String> m_recent_paths;
	Action m_run_action;
	Action m_delete_action;
	Action m_save_action;
	Action m_undo_action;
	Action m_redo_action;
	i32 m_area_edge = 0;
	bool m_show_save_as = false;
	bool m_show_open = false;
	bool m_show_osm_download_dialog = false;
	bool m_show_welcome_screen = true;
	Path m_path;
	ImTextureID m_preview_texture = (ImTextureID)(intptr_t)0xffFFffFF;
	bool m_show_preview = false;
	u32 m_preview_size = 0;
};

template <typename F>
static void	forEachInput(const OSMNodeEditor& resource, int node_id, const F& f) {
	for (const NodeEditorLink& link : resource.m_links) {
		if (link.getToNode() == node_id) {
			const int iter = resource.m_nodes.find([&](const OSMNodeEditor::Node* node) { return node->m_id == link.getFromNode(); }); 
			OSMNodeEditor::Node* from = resource.m_nodes[iter];
			const u16 from_attr = link.getFromPin();
			const u16 to_attr = link.getToPin();
			f(from, from_attr, to_attr, u32(&link - resource.m_links.begin()));
		}
	}
}

UniquePtr<OutputValue> OSMNodeEditor::Node::getInput(u16 input_idx) {
	Node* node = nullptr;
	u16 output_idx = 0;
	forEachInput(m_editor, m_id, [&](Node* from, u16 from_attr, u16 to_attr, u32 link_idx){
		if (to_attr == input_idx) {
			output_idx = from_attr;
			node = from;
		}
	});

	if (!node) return {};
	return node->getOutputValue(output_idx);
}

static void raster(u8 value, const IVec2& p0, const IVec2& p1, u32 size, Array<u8>& out) {
	// naive line rasterization
	IVec2 a = p0;
	IVec2 b = p1;

	IVec2 d = b - a;
	if (abs(d.x) > abs(d.y)) {
		if (d.x < 0) swap(a, b);
		d = b - a;

		for (i32 i = a.x; i <= b.x; ++i) {
			i32 j = int(a.y + d.y * float(i - a.x) / d.x);
			if (i < 1 || i >= (i32)size - 1) continue;
			if (j < 1 || j >= (i32)size - 1) continue;

			for (i32 k = -1; k <= 1; ++k) {
				for (i32 l = -1; l <= 1; ++l) {
					out[i + k + (j + l) * size] = value;
				}
			}
		}
	}
	else {
		if (d.y < 0) swap(a, b);
		d = b - a;

		for (i32 j = a.y; j <= b.y; ++j) {
			i32 i = int(a.x + d.x * float(j - a.y) / d.y);
			if (i < 1 || i >= (i32)size - 1) continue;
			if (j < 1 || j >= (i32)size - 1) continue;

			for (i32 k = -1; k <= 1; ++k) {
				for (i32 l = -1; l <= 1; ++l) {
					out[i + k + (j + l) * size] = value;
				}
			}
		}
	}
}

static void raster(Span<const Vec2> points, u32 w, i32 change, Array<u8>& out) {
	// naive polygon rasterization
	if (points.length() == 0) return;

	float miny = FLT_MAX;
	float maxy = -FLT_MAX;
	for (Vec2 v : points) {
		miny = minimum(v.y, miny);
		maxy = maximum(v.y, maxy);
	}
	const i32 h = (i32)w;
	const i32 from_y = clamp(i32(miny - 1), 0, h - 1);
	const i32 to_y = clamp(i32(maxy + 1), 0, h - 1);

	for (i32 pixelY = from_y; pixelY < to_y; ++pixelY) {
		float nodeX[256];
		u32 nodes = 0;
		const float y = (float)pixelY;
		for (i32 i = 0; i < (i32)points.length() - 1; i++) {
			const float y0 = points[i].y;
			const float y1 = points[i + 1].y;
			if (y1 >= y && y0 < y || y1 < y && y0 >= y) {
				ASSERT(nodes < lengthOf(nodeX));
				const float t = (y - y0) / (y1 - y0);
				ASSERT(t >= 0);
				nodeX[nodes] = lerp(points[i].x, points[i + 1].x, t);
				++nodes;
			}
		}

		if ((nodes & 1) != 0) {
			ASSERT(false);
			logError("nodes == 1 ", points[0].x, ", ", points[0].y, " - ", points[2].x, ", ", points[2].y);
			continue;
		}

		qsort(nodeX, nodes, sizeof(nodeX[0]), [](const void* a, const void* b){ 
			float m = *(float*)a;
			float n = *(float*)b;
			return m == n ? 0 : (m < n ? -1 : 1); 
		});

		for (u32 i = 0; i < nodes; i += 2) {
			const i32 from = i32(clamp(nodeX[i] - 1, 0.f, (float)w - 1));
			const i32 to = i32(clamp(nodeX[i + 1] + 1, 0.f, (float)w - 1));

			for (i32 pixelX = from; pixelX < to; ++pixelX) {
				if (pixelX < nodeX[i]) continue;
				if (pixelX > nodeX[i + 1]) continue;
				u8& v = out[pixelX + pixelY * w];
				v = (u8)clamp(i32(v) + change, 0, 255);
			}
		}
	}
}

static Terrain* getTerrain(StudioApp& app) {
	WorldEditor& editor = app.getWorldEditor();
	World* world = app.getWorldEditor().getWorld();

	RenderModule* module = (RenderModule*)world->getModule("renderer");
	EntityPtr entity = module->getFirstTerrain();
	if (!entity.isValid()) return nullptr;
	if (module->getNextTerrain(*entity).isValid()) return nullptr;
	
	return module->getTerrain(*entity);
}

static u32 getSplatmapSize(StudioApp& app) {
	const Terrain* terrain = getTerrain(app);
	if (!terrain) return 1024;
	Texture* splatmap = terrain->getSplatmap();
	if (!splatmap || !splatmap->isReady()) return 1024;
	return splatmap->width;
}

struct GrassNode : OSMNodeEditor::Node {
	GrassNode(OSMNodeEditor& editor)
		: Node(editor)
	{}

	NodeType getType() const override { return NodeType::GRASS; }
	bool hasInputPins() const override { return true; }
	bool hasOutputPins() const override { return false; }
	void serialize(OutputMemoryStream& blob) override {}
	void deserialize(InputMemoryStream& blob) override {}

	UniquePtr<OutputValue> getOutputValue(u16 output_idx) override { ASSERT(false); return {}; }

	void run() {
		clearErrors();
		if (!ensureOSMData()) return;

		UniquePtr<OutputValue> input = getInput(0);
		if (!input) return error("Invalid input");
		if (input->getType() != OutputType::MASK) return error("Invalid input");
		const MaskOutput* mask = (MaskOutput*)input.get();

		TerrainEditor* terrain_editor = m_editor.getTerrainEditor();
		if (!terrain_editor) return error("Terrain editor not found");

		Terrain* terrain = getTerrain(m_editor.m_app);
		if (!terrain) return error("Terrain not found");

		Texture* splatmap = terrain->getSplatmap();
		if (!splatmap) return error("Missing splatmap");
		if (!splatmap->isReady()) return error("Splatmap not ready");

		auto is_masked = [&](u32 x, u32 y){
			u32 i = u32(x / float(splatmap->width) * mask->m_size + 0.5f);
			u32 j = u32(y / float(splatmap->height) * mask->m_size + 0.5f);
			i = clamp(i, 0, mask->m_size - 1);
			j = clamp(j, 0, mask->m_size - 1);
			
			return mask->m_bitmap[i + j * mask->m_size] != 0;
		};

		OutputMemoryStream new_data(m_editor.m_allocator);
		new_data.resize(splatmap->height * splatmap->width * 4);
		u8* data = new_data.getMutableData();
		memcpy(data, splatmap->getData(), new_data.size());
		for (u32 y = 0; y < splatmap->height; ++y) {
			for (u32 x = 0; x < splatmap->width; ++x) {
				if (is_masked(x, y)) {
					u8* pixel = data + (x + (splatmap->height - y - 1) * splatmap->width) * 4;
					if (m_additive) {
						u16* tmp = (u16*)(pixel + 2);
						*tmp |= m_grass;
					}
					else {
						memcpy(pixel + 2, &m_grass, sizeof(m_grass));
					}
				}
			}
		}

		terrain_editor->updateSplatmap(terrain, static_cast<OutputMemoryStream&&>(new_data), 0, 0, splatmap->width, splatmap->height, true);
	}

	bool gui() override {
		ImGuiEx::NodeTitle("Grass", ImGui::GetColorU32(ImGuiCol_PlotLinesHovered));
		inputSlot();
		bool res = ImGui::Checkbox("Additive", &m_additive);
		i32 g = m_grass;
		if (ImGui::InputInt("Grass", &g)) {
			m_grass = g;
			res = true;
		}
		return res;
	}

	u16 m_grass = 0;
	bool m_additive = false;
};

struct MergeDistanceFieldsNode : OSMNodeEditor::Node {
	MergeDistanceFieldsNode(OSMNodeEditor& editor)
		: Node(editor)
	{}

	NodeType getType() const override { return NodeType::MERGE_DISTANCE_FIELDS; }
	bool hasInputPins() const override { return true; }
	bool hasOutputPins() const override { return true; }
	
	void serialize(OutputMemoryStream& blob) override {}
	void deserialize(InputMemoryStream& blob) override {}

	UniquePtr<OutputValue> getOutputValue(u16 output_idx) override {
		UniquePtr<OutputValue> input0 = getInput(0);
		UniquePtr<OutputValue> input1 = getInput(1);
		if (!input0) return outputError("Invalid input");
		if (!input1) return outputError("Invalid input");
		if (input0->getType() != OutputType::DISTANCE_FIELD) return outputError("Invalid input");
		if (input1->getType() != OutputType::DISTANCE_FIELD) return outputError("Invalid input");
		DistanceFieldOutput* df0 = (DistanceFieldOutput*)input0.get();
		DistanceFieldOutput* df1 = (DistanceFieldOutput*)input1.get();
		if (df0->m_size != df1->m_size) return outputError("Distance fields have different size");

		for (u32 i = 0, c = df0->m_field.size(); i < c; ++i) {
			df0->m_field[i] = minimum(df0->m_field[i], df1->m_field[i]);
		}

		return input0.move();
	}
	
	bool gui() override {
		nodeTitle("Merge");
		ImGui::BeginGroup();
		inputSlot(OutputType::DISTANCE_FIELD); ImGui::TextUnformatted("A");
		inputSlot(OutputType::DISTANCE_FIELD); ImGui::TextUnformatted("B");
		ImGui::EndGroup();
		ImGui::SameLine();
		outputSlot(OutputType::DISTANCE_FIELD);
		return false;
	}
};

struct MergeMasksNode : OSMNodeEditor::Node {
	MergeMasksNode(OSMNodeEditor& editor)
		: Node(editor)
	{}

	NodeType getType() const override { return NodeType::MERGE_MASKS; }
	bool hasInputPins() const override { return true; }
	bool hasOutputPins() const override { return true; }
	
	void serialize(OutputMemoryStream& blob) override {
		blob.write(m_mode);
	}
	
	void deserialize(InputMemoryStream& blob) override {
		blob.read(m_mode);
	}

	UniquePtr<OutputValue> getOutputValue(u16 output_idx) override {
		UniquePtr<OutputValue> input0 = getInput(0);
		UniquePtr<OutputValue> input1 = getInput(1);
		if (!input0) return outputError("Invalid input");
		if (!input1) return outputError("Invalid input");
		if (input0->getType() != OutputType::MASK) return outputError("Invalid input");
		if (input1->getType() != OutputType::MASK) return outputError("Invalid input");
		MaskOutput* mask0 = (MaskOutput*)input0.get();
		MaskOutput* mask1 = (MaskOutput*)input1.get();

		switch (m_mode) {
			case DIFFERENECE:
				for (u32 i = 0, c = mask0->m_bitmap.size(); i < c; ++i) {
					mask0->m_bitmap[i] = mask0->m_bitmap[i] != 0 && mask1->m_bitmap[i] == 0;
				}
				break;
			case INTERSECTION:
				for (u32 i = 0, c = mask0->m_bitmap.size(); i < c; ++i) {
					mask0->m_bitmap[i] = mask0->m_bitmap[i] != 0 && mask1->m_bitmap[i] != 0;
				}
				break;
			case UNION:
				for (u32 i = 0, c = mask0->m_bitmap.size(); i < c; ++i) {
					mask0->m_bitmap[i] = mask0->m_bitmap[i] != 0 || mask1->m_bitmap[i] != 0;
				}
				break;
		}

		return input0.move();
	}

	bool gui() override {
		nodeTitle("Merge");
		ImGui::BeginGroup();
		inputSlot(); ImGui::TextUnformatted("A");
		inputSlot(); ImGui::TextUnformatted("B");
		ImGui::EndGroup();
		ImGui::SameLine();
		ImGui::Combo("Mode", (i32*)&m_mode, "Union\0Intersection\0Difference\0");
		ImGui::SameLine();
		outputSlot();
		return false;
	}

	enum Mode : u32 {
		UNION,
		INTERSECTION,
		DIFFERENECE
	};
	
	Mode m_mode = UNION;
};

struct DistanceFieldNode : OSMNodeEditor::Node {
	DistanceFieldNode(OSMNodeEditor& editor)
		: Node(editor)
	{}

	UniquePtr<OutputValue> getOutputValue(u16 output_idx) override {
		UniquePtr<OutputValue> input = getInput(0);
		if (!input) return outputError("Invalid input");
		if (input->getType() != OutputType::MASK) return outputError("Invalid input");
		MaskOutput* mask = (MaskOutput*)input.get();

		IAllocator& allocator = m_editor.m_app.getAllocator();
		UniquePtr<DistanceFieldOutput> df = UniquePtr<DistanceFieldOutput>::create(allocator, allocator);
		df->m_size = mask->m_size;
		df->m_field.resize(df->m_size * df->m_size);
		
		Array<IVec2> data_ar(m_editor.m_app.getAllocator());

		const u32 w = df->m_size;
		const u32 h = df->m_size;
		data_ar.resize(w * h);
		IVec2* data = data_ar.begin();

		auto check_neighbour = [](const IVec2& p, IVec2* n, IVec2 ij) {
			IVec2 a = p - ij;
			IVec2 b = *n - ij;
			if (a.x * a.x + a.y * a.y < b.x * b.x + b.y * b.y) {
				*n = p;
			}
		};

		const u8* bitmap = mask->m_bitmap.begin();
		for (i32 j = 0; j < (i32)h; ++j) {
			for (i32 i = 0; i < (i32)w; ++i) {
				if (bitmap[i + j * w] != 0) {
					data[i + j * w] = IVec2(i, j);
				}
				else {
					data[i + j * w] = IVec2(INT_MIN, INT_MIN);
				}
			}
		}

		auto compute = [&](){
			for (i32 j = 0; j < (i32)h; ++j) {
				const int j0 = maximum(j - 1, 0);
				for (i32 i = 0; i < (i32)w; ++i) {
					const int i0 = maximum(i - 1, 0);
					const int i1 = minimum(i + 1, w - 1);

					IVec2* n = &data[i + j * w];
					IVec2 ij(i, j);
					check_neighbour(data[i0 + j0 * w], n, ij);
					check_neighbour(data[i + j0 * w], n, ij);
					check_neighbour(data[i1 + j0 * w], n, ij);
					check_neighbour(data[i0 + j * w], n, ij);
				}

				for (int i = w - 1; i >= 0; --i) {
					const int i1 = minimum(i + 1, w - 1);

					IVec2* n = &data[j * w + i];
					IVec2 ij(i, j);
					check_neighbour(data[j * w + i1], n, ij);
				}
			}

			for (int j = h - 1; j >= 0; --j) {
				const int j0 = minimum(j + 1, h - 1);
				for (int i = w - 1; i >= 0; --i) {
					const int i0 = maximum(i - 1, 0);
					const int i1 = minimum(i + 1, w - 1);

					IVec2* n = &data[i + j * w];
					IVec2 ij(i, j);
					check_neighbour(data[i1 + j0 * w], n, ij);
					check_neighbour(data[i + j0 * w], n, ij);
					check_neighbour(data[i0 + j0 * w], n, ij);
					check_neighbour(data[i1 + j * w], n, ij);
				}

				for (int i = w - 1; i >= 0; --i) {
					const int i0 = maximum(i - 1, 0);

					IVec2* n = &data[j * w + i];
					IVec2 ij(i, j);
					check_neighbour(data[j * w + i0], n, ij);
				}
			}
		};
		compute();

		for (u32 j = 0; j < h; ++j) {
			for (u32 i = 0; i < w; ++i) {
				const float d = length(Vec2(data[i + j * w] - IVec2(i, j)));
				df->m_field[i + (h - j - 1) * w] = d;
			}
		}

		// negative distance
		for (i32 j = 0; j < (i32)h; ++j) {
			for (i32 i = 0; i < (i32)w; ++i) {
				if (bitmap[i + j * w] == 0) {
					data[i + j * w] = IVec2(i, j);
				}
				else {
					data[i + j * w] = IVec2(INT_MIN, INT_MIN);
				}
			}
		}

		compute();

		for (u32 j = 0; j < h; ++j) {
			for (u32 i = 0; i < w; ++i) {
				if (bitmap[i + j * w] != 0) {
					const float d = length(Vec2(data[i + j * w] - IVec2(i, j)));
					df->m_field[i + (h - j - 1) * w] = -d;
				}
			}
		}
		return df.move();
	}

	NodeType getType() const override { return NodeType::DISTANCE_FIELD; }
	bool hasInputPins() const override { return true; }
	bool hasOutputPins() const override { return true; }
	void serialize(OutputMemoryStream& blob) override {}
	void deserialize(InputMemoryStream& blob) override {}

	bool gui() override {
		nodeTitle("Distance field");
		inputSlot();
		outputSlot(OutputType::DISTANCE_FIELD);
		ImGui::TextUnformatted("Input mask");
		return false;
	}
};

struct AdjustHeightNode  : OSMNodeEditor::Node {
	AdjustHeightNode(OSMNodeEditor& editor)
		: Node(editor)
	{}

	NodeType getType() const override { return NodeType::ADJUST_HEIGHT; }
	bool hasInputPins() const override { return true; }
	bool hasOutputPins() const override { return false; }

	void serialize(OutputMemoryStream& blob) override {
		blob.writeString(m_texture);
		blob.write(m_texture_scale);
		blob.write(m_multiplier);
		blob.write(m_distance_range);
	}

	void deserialize(InputMemoryStream& blob) override {
		m_texture = blob.readString();
		blob.read(m_texture_scale);
		blob.read(m_multiplier);
		blob.read(m_distance_range);
	}

	UniquePtr<OutputValue> getOutputValue(u16 output_idx) override { return {}; }
	
	bool gui() override {
		ImGuiEx::BeginNodeTitleBar(ImGui::GetColorU32(ImGuiCol_PlotLinesHovered));
		ImGui::AlignTextToFramePadding();
		ImGui::TextUnformatted("Adjust height");
		ImGui::SameLine();
		if (ImGui::Button(ICON_FA_PLAY)) run();
		ImGuiEx::EndNodeTitleBar();
		inputSlot(OutputType::DISTANCE_FIELD);
		
		bool res = textureMaskInput(m_texture);
		res = ImGui::DragFloat("Texture scale", &m_texture_scale) || res;
		res = ImGui::DragFloat("Multiplier", &m_multiplier) || res;
		res = ImGui::DragFloat("Minimal distance", &m_distance_range.x, 1.f, -FLT_MAX, FLT_MAX) || res;
		res = ImGui::DragFloat("Maximal distance", &m_distance_range.y, 1.f, -FLT_MAX, FLT_MAX) || res;
		ImGui::TextUnformatted("(?)");
		if (ImGui::IsItemHovered()) {
			ImGui::SetTooltip(
				"Everything below minimal distance is not affected.\n"
				"Everything above maximal distance is fully affected.\n"
				"Quadratic interpolation between min and max."
			);
		}
		return false;
	}

	void run() {
		clearErrors();
		if (!ensureOSMData()) return;

		UniquePtr<OutputValue> input =  getInput(0);
		if (!input) return error("Invalid input");
		if (input->getType() != OutputType::DISTANCE_FIELD) return error("Invalid input");

		Terrain* terrain = getTerrain(m_editor.m_app);
		if (!terrain) return error("Terrain not found");

		TerrainEditor* terrain_editor = m_editor.getTerrainEditor();
		if (!terrain_editor) return error("Terrain editor not found");

		DistanceFieldOutput* df = (DistanceFieldOutput*)input.get();
		
		Texture* hm = terrain->getHeightmap();
		if (!hm) return error("Missing heightmap");
		if (!hm->isReady()) return error("Heightmap not ready");
		if (hm->format != gpu::TextureFormat::R16) return error("Heightmap format not supported - it has to be 16bit");
		
		const u16* src_data = (const u16*)hm->getData();
		if (!src_data) return error("Could not read heightmap data");

		u32 w, h;
		stbi_uc* rgba = nullptr;
		if (m_texture.data[0]) {
			rgba = loadTexture(m_texture, w, h, m_editor.m_app);
			if (!rgba) return error("Failed to load the texture");
		}

		OutputMemoryStream new_data(m_editor.m_allocator);
		new_data.resize(hm->width * hm->height * 2);
		u16* hm_data = (u16*)new_data.getMutableData();
		memcpy(hm_data, src_data, new_data.size());

		auto mix = [](float a, float b, float t) {
			return a * (1 - t) + b * t;
		};

		auto sample = [&](u32 i, u32 j) {
			if (!rgba) return 1.f;

			const float x = i * float(m_texture_scale / hm->width);
			const float y = j * float(m_texture_scale / hm->height);
			const float a = x * w;
			const float b = y * h;
			
			u32 a0 = u32(a);
			u32 b0 = u32(b);
			const float tx = a - a0;
			const float ty = b - b0;
			a0 = a0 % w;
			b0 = b0 % w;

			const float v00 = rgba[a0 + b0 * w] / float(0xff);
			const float v10 = rgba[a0 + 1 + b0 * w] / float(0xff);
			const float v11 = rgba[a0 + 1 + b0 * w + w] / float(0xff);
			const float v01 = rgba[a0 + b0 * w + w] / float(0xff);

			return mix(
				mix(v00, v10, tx),
				mix(v01, v11, tx),
				ty
			);
		};

		const float range = m_distance_range.y - m_distance_range.x;
		
		for (u32 j = 0; j < hm->height; ++j) {
			for (u32 i = 0; i < hm->width; ++i) {
				const float u = float(i) / (hm->width - 1);
				const float v = float(j) / (hm->height - 1);
				const float dist = df->sample(u, 1 - v);
				if (dist > m_distance_range.x) {
					float distance_weight = clamp((dist - m_distance_range.x) / range, 0.f, 1.f);
					distance_weight *= distance_weight;
					const u32 idx = i + (hm->height - j - 1) * hm->width;
					float height = (hm_data[idx] / float(0xffFF));
					height += sample(i, j) * m_multiplier * distance_weight;
					hm_data[idx] = (u16)clamp(height * float(0xffFF), 0.f, (float)0xffFF);
				}
			}
		}

		terrain_editor->updateHeightmap(terrain, static_cast<OutputMemoryStream&&>(new_data), 0, 0, hm->width, hm->height);
		stbi_image_free(rgba);
	}

	StaticString<LUMIX_MAX_PATH> m_texture;
	float m_texture_scale = 1.f;
	float m_multiplier = 1.f;
	Vec2 m_distance_range = Vec2(0, 1);
};

struct FlattenPolylinesNode : OSMNodeEditor::Node {
	FlattenPolylinesNode(OSMNodeEditor& editor)
		: Node(editor)
		, m_height(editor.m_allocator)
		, m_weight_sum(editor.m_allocator)
		, m_max_weight(editor.m_allocator)
	{}

	NodeType getType() const override { return NodeType::FLATTEN_POLYLINES; }
	bool hasInputPins() const override { return false; }
	bool hasOutputPins() const override { return false; }
	
	void serialize(OutputMemoryStream& blob) override {
		blob.write(m_line_width);
		blob.write(m_boundary_width);
		blob.writeString(m_key);
		blob.writeString(m_value);
	}
	
	void deserialize(InputMemoryStream& blob) override {
		blob.read(m_line_width);
		blob.read(m_boundary_width);
		m_key = blob.readString();
		m_value = blob.readString();
	}
	
	UniquePtr<OutputValue> getOutputValue(u16 output_idx) override { return {}; }

	bool gui() override {
		ImGuiEx::BeginNodeTitleBar(ImGui::GetColorU32(ImGuiCol_PlotLinesHovered));
		ImGui::TextUnformatted("Flatten polylines");
		ImGui::SameLine();
		if (ImGui::Button(ICON_FA_PLAY)) run();
		ImGuiEx::EndNodeTitleBar();
		bool res = ImGui::DragFloat("Width", &m_line_width);
		res = ImGui::DragFloat("Boundary", &m_boundary_width) || res;
		res = tagInput(Span(m_key.data), Span(m_value.data), 150) || res;
		return res;
	}
	
	Vec2 toHeightmap(const Vec2& p) const {
		Vec2 tmp;
		tmp = p;
		const Terrain* terrain = getTerrain(m_editor.m_app);
		const Vec2 s = terrain->getSize();
		const u32 size = terrain->getHeightmap()->width;
		tmp.x += s.x * 0.5f; 
		tmp.y += s.y * 0.5f; 
	
		tmp.x = tmp.x  / s.x * (float)size;
		tmp.y = (1 - tmp.y  / s.y) * (float)size;
		return tmp;
	}

	void flattenQuad(const Vec2* points, float h0, float h1, const Terrain& terrain, float line_width, float boundary_width) {
		u16* ptr = (u16*)terrain.m_heightmap->data.getMutableData();
		const u32 pixw = terrain.m_heightmap->width;
		const u32 pixh = terrain.m_heightmap->height;

		const Vec2 c0 = (points[0] + points[1]) * 0.5f;
		const Vec2 c1 = (points[2] + points[3]) * 0.5f;
		const Vec2 dir = normalize(c1 - c0);
		const Vec2 n(-dir.y, dir.x);

		const Vec2 min = minimum(points[0], minimum(points[1], minimum(points[2], points[3])));
		const Vec2 max = maximum(points[0], maximum(points[1], maximum(points[2], points[3])));
		const float heights[] = {h0, h0, h1, h1};

		const i32 from_y = clamp(i32(min.y - 1), 0, pixh);
		const i32 to_y = clamp(i32(max.y + 1), 0, pixh);
		for (i32 pixelY = from_y; pixelY < to_y; ++pixelY) {
			Vec2 nodeXY[4];
			u32 nodes = 0;
			const float y = (float)pixelY;
			for (i32 i = 0; i < 4; i++) {
				const float y0 = points[i].y;
				const float y1 = points[(i + 1) % 4].y;
				if (y0 < y && y1 >= y || y1 < y && y0 >= y) {
					const float t = (y - y0) / (y1 - y0);
					nodeXY[nodes].x = lerp(points[i].x, points[(i + 1) % 4].x, t);
					nodeXY[nodes].y = lerp(heights[i], heights[(i + 1) % 4], t);
					++nodes;
				}
			}

			if ((nodes & 1) != 0) {
				ASSERT(false);
				logError("nodes == 1 ", points[0].x, ", ", points[0].y, " - ", points[2].x, ", ", points[2].y);
				continue;
			}

			qsort(nodeXY, nodes, sizeof(nodeXY[0]), [](const void* a, const void* b){ 
				const Vec2 m = *(const Vec2*)a;
				const Vec2 n = *(const Vec2*)b;
				return m.x == n.x ? 0 : (m.x < n.x ? -1 : 1); 
			});

			for (u32 i = 0; i < nodes; i += 2) {
				const i32 from = clamp(i32(nodeXY[i].x), 0, pixw);
				const i32 to = clamp(i32(nodeXY[i + 1].x), 0, pixw);
				const float rcp_xd = 1.f / (nodeXY[i + 1].x - nodeXY[i].x);
				for (i32 pixelX = from; pixelX < to; ++pixelX) {
					const float x = (float)pixelX;
					const u32 idx = u32(pixelX + (pixh - pixelY - 1) * pixw);
					const float t = (x - nodeXY[i].x) * rcp_xd;
					const float h = lerp(nodeXY[i].y, nodeXY[i + 1].y, t);
					const Vec2 p(x, y);
					const float center_dist = abs(dot(p - c0, n));
					float weight = boundary_width < 0.001f
						? 1.f
						: 1.f - clamp((center_dist - line_width * 0.5f) / boundary_width, 0.f, 1.f);
					weight *= weight;

					if (weight > 0.001f) {
						m_height[idx] = (m_weight_sum[idx] * m_height[idx] + h * weight) / (m_weight_sum[idx] + weight);
						m_weight_sum[idx] += weight;
						m_max_weight[idx] = maximum(m_max_weight[idx], weight);
					}
				}
			}
		}
	}

	void flattenLine(const DVec3& prev, const DVec3& a, const DVec3& b, const DVec3& next, const Terrain& terrain, float line_width, float boundary_width) {
		ASSERT(terrain.m_heightmap->format == gpu::TextureFormat::R16);
		ASSERT(terrain.m_splatmap);

		const float base_y = (float)m_editor.m_app.getWorldEditor().getWorld()->getPosition(terrain.m_entity).y;

		const Vec2 a2d = Vec3(a).xz();
		const Vec2 b2d = Vec3(b).xz();
		const Vec2 prev2d = Vec3(prev).xz();
		const Vec2 next2d = Vec3(next).xz();
		const Vec2 dir = b2d - a2d;
		const Vec2 n0 = normalize(Vec2(dir.y, -dir.x));

		Vec2 n1 = next2d - b2d;
		if (squaredLength(n1) < 1e-3) {
			n1 = dir;
		}
		n1 = normalize(Vec2(n1.y, -n1.x));

		const float half_size = line_width * 0.5f + boundary_width;

		Vec2 points[] = { a2d - n0 * half_size
			, a2d + n0 * half_size
			, b2d + n1 * half_size
			, b2d - n1 * half_size
		};

		ASSERT(terrain.m_heightmap->width == terrain.m_heightmap->height);
		const float s = terrain.m_heightmap->height / terrain.getSize().x;
		for (int i = 0; i < 4; ++i) {
			points[i] = toHeightmap(points[i]) - Vec2(0.5f);
		}

		flattenQuad(points, (float)a.y - base_y, (float)b.y - base_y, terrain, line_width * s, boundary_width * s);
	}

	void run() {
		clearErrors();
		if (!ensureOSMData()) return;

		Terrain* terrain = getTerrain(m_editor.m_app);
		if (!terrain) return error("Terrain not found");

		Texture* hm = terrain->m_heightmap;
		if (!hm) return error("Missing heightmap");
		if (!hm->isReady()) return error("Heightmap not ready");

		TerrainEditor* terrain_editor = m_editor.getTerrainEditor();
		if (!terrain_editor) return error("Terrain editor not found");

		m_height.resize(hm->height * hm->width);
		m_weight_sum.resize(m_height.size());
		m_max_weight.resize(m_height.size());
		memset(m_max_weight.begin(), 0, m_max_weight.byte_size());
		memset(m_weight_sum.begin(), 0, m_weight_sum.byte_size());
		Array<DVec3> polyline(m_editor.m_app.getAllocator());

		for (pugi::xml_node& w : m_editor.m_osm_parser.m_ways) {
			if (!OSMParser::hasTag(w, m_key, m_value)) continue;

			polyline.clear();
			m_editor.m_osm_parser.getWay(w, terrain->m_entity, polyline);

			for (i32 i = 0; i < polyline.size() - 1; ++i) {
				flattenLine(polyline[i > 0 ? i - 1 : 0],
					polyline[i],
					polyline[i + 1],
					polyline[i + 2 < polyline.size() ? i + 2 : i + 1],
					*terrain,
					m_line_width,
					m_boundary_width);
			}
		}

		OutputMemoryStream new_data(m_editor.m_allocator);
		new_data.resize(hm->width * hm->height * 2);
		u16* hm_data = (u16*)new_data.getMutableData();
		memcpy(hm_data, hm->getData(), new_data.size());
		
		for (u32 j = 0; j < hm->height; ++j) {
			for (u32 i = 0; i < hm->width; ++i) {
				const u32 idx = i + j * hm->width;
				if (m_max_weight[idx] > 0.01f) {
					float h = float(hm_data[idx]) * terrain->m_scale.y / 0xffFF;
					h = lerp(h, m_height[idx], m_max_weight[idx]);
					hm_data[idx] = u16(clamp(h * 0xffFF / terrain->m_scale.y, 0.f, 65535.f) + 0.5f);
				}
			}
		}

		terrain_editor->updateHeightmap(terrain, static_cast<OutputMemoryStream&&>(new_data), 0, 0, hm->width, hm->height);
	}

	StaticString<128> m_key;
	StaticString<128> m_value;
	Array<float> m_weight_sum;
	Array<float> m_max_weight;
	Array<float> m_height; // weighted average
	float m_line_width = 3.f;
	float m_boundary_width = 3.f;
};

struct PlaceSplinesNode : OSMNodeEditor::Node {
	PlaceSplinesNode(OSMNodeEditor& editor)
		: Node(editor)
	{}

	NodeType getType() const override { return NodeType::PLACE_SPLINES; }
	bool hasInputPins() const override { return false; }
	bool hasOutputPins() const override { return false; }
	void serialize(OutputMemoryStream& blob) override {}
	void deserialize(InputMemoryStream& blob) override {}
	UniquePtr<OutputValue> getOutputValue(u16 output_idx) override { return {}; }
	
	bool gui() override {
		ImGuiEx::BeginNodeTitleBar(ImGui::GetColorU32(ImGuiCol_PlotLinesHovered));
		ImGui::TextUnformatted("Place splines");
		ImGui::SameLine();
		if (ImGui::Button(ICON_FA_PLAY)) run();
		ImGuiEx::EndNodeTitleBar();
		return tagInput(Span(m_key.data), Span(m_value.data), 150);
	}

	void run() {
		clearErrors();
		if (!ensureOSMData()) return;

		StudioApp& app = m_editor.m_app;

		Array<DVec3> polyline(app.getAllocator());

		const Terrain* terrain = getTerrain(app);
		if (!terrain) return error("Terrain not found");
		if (!terrain->m_heightmap) return error("Missing heightmap");
		if (!terrain->m_heightmap->isReady()) return error("Heightmap not ready");

		WorldEditor& editor = app.getWorldEditor();
		
		editor.beginCommandGroup("place_splines");
		SplineEditor* spline_editor = static_cast<SplineEditor*>(app.getIPlugin("spline_editor"));
		Array<Vec3> points(app.getAllocator());
		for (pugi::xml_node& w : m_editor.m_osm_parser.m_ways) {
			if (!OSMParser::hasTag(w, m_key, m_value)) continue;
	
			polyline.clear();
			m_editor.m_osm_parser.getWay(w, terrain->m_entity, polyline);
			if (polyline.size() < 3) continue;
	
			const EntityRef entity = editor.addEntityAt(polyline[0]);
			editor.makeParent(terrain->m_entity, entity);
			editor.addComponent(Span(&entity, 1), SPLINE_TYPE);

			points.clear();
			for (const DVec3& p : polyline) {
				points.push(Vec3(p - polyline[0]));
			}

			spline_editor->setSplinePoints(entity, points);
		}
		editor.endCommandGroup();
		editor.selectEntities(Span(&terrain->m_entity, 1), false);
	}

	StaticString<128> m_key;
	StaticString<128> m_value;
	float m_width = 1.f;
};

struct PlaceInstancesNode : OSMNodeEditor::Node {
	PlaceInstancesNode(OSMNodeEditor& editor)
		: Node(editor)
		, m_models(editor.m_allocator)
	{}

	~PlaceInstancesNode() {
		for (const ModelProbability& mp : m_models) {
			if (mp.resource) mp.resource->decRefCount();
		}
	}

	NodeType getType() const override { return NodeType::PLACE_INSTANCES; }
	bool hasInputPins() const override { return true; }
	bool hasOutputPins() const override { return false; }
	
	void serialize(OutputMemoryStream& blob) override {
		blob.write(m_spacing);
		blob.write(m_models.size());
		for (const ModelProbability& mp : m_models) {
			blob.writeString(mp.resource ? mp.resource->getPath().c_str() : "");
			blob.write(mp.distances);
			blob.write(mp.scale);
			blob.write(mp.y_offset);
			blob.write(mp.multiplier);
		}
	}

	void deserialize(InputMemoryStream& blob) override {
		ResourceManagerHub& rm = m_editor.m_app.getEngine().getResourceManager();
		blob.read(m_spacing);
		u32 count;
		blob.read(count);
		m_models.resize(count);
		for (ModelProbability& mp : m_models) {
			const char* path = blob.readString();
			if (path[0]) {
				mp.resource = rm.load<Model>(Path(path));
			}
			else {
				mp.resource = nullptr;
			}
			blob.read(mp.distances);
			blob.read(mp.scale);
			blob.read(mp.y_offset);
			blob.read(mp.multiplier);
		}
	}

	void run() {
		clearErrors();
		if (!ensureOSMData()) return;

		UniquePtr<OutputValue> input = getInput(0);
		if (!input) return error("Invalid input");

		DistanceFieldOutput* df = (DistanceFieldOutput*)input.get();

		WorldEditor& editor = m_editor.m_app.getWorldEditor();
		World* world = editor.getWorld();
		RenderModule* render_module = (RenderModule*)world->getModule(TERRAIN_TYPE);
		Terrain* terrain = getTerrain(m_editor.m_app);
		if (!terrain) return error("Terrain not found");
		EntityRef terrain_entity = terrain->m_entity;

		const DVec3 terrain_pos = world->getPosition(terrain_entity);
	
		struct Group {
			EntityRef e;
			InstancedModel* im;
		};
	
		StackArray<Group, 64> groups(m_editor.m_app.getAllocator());
		editor.beginCommandGroup("maps_place_instances");
		for (const ModelProbability& m : m_models) {
			const EntityRef e = editor.addEntity();
			groups.emplace().e = e;
			editor.makeParent(terrain_entity, e);
			editor.addComponent(Span(&e, 1), INSTANCED_MODEL_TYPE);
			editor.setProperty(INSTANCED_MODEL_TYPE, "", 0, "Model", Span(&e, 1), m.resource->getPath());
			editor.setEntitiesPositions(&e, &terrain_pos, 1);
		}
	
		for (Group& g : groups) {
			g.im = &render_module->beginInstancedModelEditing(g.e);
		}
	
		const double y_base = terrain_pos.y;
		const Vec2 size = render_module->getTerrainSize(terrain_entity);
		const Vec2 df_to_terrain = size / Vec2((float)df->m_size, (float)df->m_size);
		const Vec2 terrain_to_df = Vec2((float)df->m_size, (float)df->m_size) / size;
	
		float min_dist = FLT_MAX;
		float max_dist = -FLT_MAX;
	
		for (const ModelProbability& prob : m_models) {
			min_dist = minimum(min_dist, prob.distances.x);
			max_dist = maximum(max_dist, prob.distances.w);
		}
	
		for (float y = 0; y < df->m_size; y += m_spacing * terrain_to_df.y) {
			for (float x = 0; x < df->m_size; x += m_spacing * terrain_to_df.x) {
				float fx = x;
				float fy = y;
				fx = clamp(fx + (randFloat() * 0.9f - 0.45f) * m_spacing * terrain_to_df.x, 0.f, (float)df->m_size - 1);
				fy = clamp(fy + (randFloat() * 0.9f - 0.45f) * m_spacing * terrain_to_df.y, 0.f, (float)df->m_size - 1);
	
				DVec3 pos;
				pos.x = fx * df_to_terrain.x;
				pos.z = fy * df_to_terrain.y;
	
				const i32 idx = i32(fx) + i32(fy) * df->m_size;
				const float distance = df->m_field[idx];
				if (distance >= min_dist && distance <= max_dist) {
					pos.y = render_module->getTerrainHeightAt(terrain_entity, (float)pos.x, (float)pos.z);
	
					pos.x -= size.x * 0.5f;
					pos.y += y_base;
					pos.z -= size.y * 0.5f;
						
					const u32 r = getRandomItem(distance, m_models);
					if (r != 0xffFFffFF) {
						const Vec2& yoffset_range = m_models[r].y_offset;
						pos.y += lerp(yoffset_range.x, yoffset_range.y, randFloat());
	
						const Vec2& scale_range = m_models[r].scale;
						const float scale = lerp(scale_range.x, scale_range.y, randFloat());
						
						InstancedModel::InstanceData& id = groups[r].im->instances.emplace();
						const Quat rot(Vec3(0, 1, 0), randFloat() * 2 * PI);
						id.pos = Vec3(pos - terrain_pos);
						id.scale = scale;
						id.rot_quat = rot.w < 0 ? -Vec3(rot.x, rot.y, rot.z) : Vec3(rot.x, rot.y, rot.z);
						id.lod = 3;
					}
				}
			}
		}
	
		for (Group& g : groups) {
			render_module->endInstancedModelEditing(g.e);
		}
	
		editor.endCommandGroup();
	}

	UniquePtr<OutputValue> getOutputValue(u16 output_idx) override { return {}; }

	bool gui() override {
		ImGuiEx::BeginNodeTitleBar(ImGui::GetColorU32(ImGuiCol_PlotLinesHovered));
		ImGui::TextUnformatted("Place instances");
		ImGui::SameLine();
		if (ImGui::Button(ICON_FA_PLAY)) run();
		ImGuiEx::EndNodeTitleBar();
		
		inputSlot(OutputType::DISTANCE_FIELD);
		bool res = ImGui::DragFloat("Spacing", &m_spacing);
		if (ImGui::Button("Edit models")) ImGui::OpenPopup("Edit models");
		if (ImGui::BeginPopup("Edit models")) {
			for (ModelProbability& mp : m_models) {
				if (ImGui::TreeNode(&mp, "%d", u32(&mp - m_models.begin()))) {
					char path[LUMIX_MAX_PATH];
					copyString(path, mp.resource ? mp.resource->getPath().c_str() : "");
					if (m_editor.m_app.getAssetBrowser().resourceInput("model", Span(path), Model::TYPE, 150)) {
						res = true;
						if (mp.resource) mp.resource->decRefCount();
						ResourceManagerHub& rm = m_editor.m_app.getEngine().getResourceManager();
						mp.resource = rm.load<Model>(Path(path));
					}
					res = ImGui::DragFloat4("Distances", &mp.distances.x) || res;
					res = ImGui::DragFloat2("Scale", &mp.scale.x) || res;
					res = ImGui::DragFloat2("Y Offset", &mp.y_offset.x) || res;
					res = ImGui::DragFloat("Multiplier", &mp.multiplier) || res;
					ImGui::TreePop();
				}
			}
			if (ImGui::Button("Add")) {
				m_models.emplace();
			}
			ImGui::EndPopup();
		}
		return res;
	}

	struct ModelProbability {
		Model* resource = nullptr;
		Vec4 distances = Vec4(10, 20, 30, 40);
		Vec2 scale = Vec2(1, 1);
		Vec2 y_offset = Vec2(0, 0);
		float multiplier = 1.f;
	};
	
	Array<ModelProbability> m_models;
	float m_spacing = 5.f;
};

struct NoiseNode : OSMNodeEditor::Node {
	NoiseNode(OSMNodeEditor& editor)
		: Node(editor)
	{}

	NodeType getType() const override { return NodeType::NOISE; }
	bool hasInputPins() const override { return false; }
	bool hasOutputPins() const override { return true; }

	void serialize(OutputMemoryStream& blob) override {
		blob.write(m_value);
		blob.write(m_probability);
	}
	
	void deserialize(InputMemoryStream& blob) override {
		blob.read(m_value);
		blob.read(m_probability);
	}

	UniquePtr<OutputValue> getOutputValue(u16 output_idx) override {
		if (!getTerrain(m_editor.m_app)) return outputError("Terrain not found");

		IAllocator& allocator = m_editor.m_app.getAllocator();
		UniquePtr<MaskOutput> output = UniquePtr<MaskOutput>::create(allocator, allocator);
		output->m_size = getSplatmapSize(m_editor.m_app);
		output->m_bitmap.resize(output->m_size * output->m_size);
		memset(output->m_bitmap.begin(), 0, output->m_bitmap.byte_size());
		MaskOutput* mask = (MaskOutput*)output.get();

		for (u8& v : mask->m_bitmap) {
			if (randFloat(0, 1) < m_probability) v = m_value;
		}
		return output.move();
	}

	bool gui() override {
		nodeTitle("Noise");
		outputSlot();
		bool res = ImGui::DragFloat("Probability", &m_probability, 0.01f, 0.f, 1.f);
		i32 v = m_value;
		if (ImGui::DragInt("Value", &v, 1, 0, 255)) {
			m_value = v;
			res = true;
		}
		return res;
	}

	float m_probability = 0.5f;
	u8 m_value = 1;
};

struct MaskDistanceNode : OSMNodeEditor::Node {
	MaskDistanceNode(OSMNodeEditor& editor)
		: Node(editor)
	{}

	NodeType getType() const override { return NodeType::MASK_DISTANCE; }
	bool hasInputPins() const override { return true; }
	bool hasOutputPins() const override { return true; }
	void serialize(OutputMemoryStream& blob) override {}
	void deserialize(InputMemoryStream& blob) override {}

	bool gui() override {
		nodeTitle("Mask distance");
		inputSlot(OutputType::DISTANCE_FIELD);
		outputSlot();
		return ImGui::DragFloatRange2("Distance", &m_from, &m_to, 1.f, -FLT_MAX, FLT_MAX, "%.1f", nullptr, ImGuiSliderFlags_AlwaysClamp);
	}
	
	UniquePtr<OutputValue> getOutputValue(u16 output_idx) override {
		const UniquePtr<OutputValue> input = getInput(output_idx);
		if (!input) return outputError("Invalid input");
		if (input->getType() != OutputType::DISTANCE_FIELD) return outputError("Invalid input");
		
		DistanceFieldOutput* df = (DistanceFieldOutput*)input.get();

		IAllocator& allocator = m_editor.m_app.getAllocator();
		UniquePtr<MaskOutput> output = UniquePtr<MaskOutput>::create(allocator, allocator);
		output->m_size = df->m_size;
		output->m_bitmap.resize(output->m_size * output->m_size);

		for (u32 j = 0; j < df->m_size; ++j) {
			for (u32 i = 0; i < df->m_size; ++i) {
				const float dist = df->m_field[i + j * df->m_size];
				output->m_bitmap[i + (df->m_size - j - 1) * df->m_size] = dist >= m_from && dist <= m_to ? 1 : 0;
			}
		}

		return output.move();
	}

	float m_from = 0.f;
	float m_to = 1.f;
};

struct MaskTextureNode : OSMNodeEditor::Node {
	MaskTextureNode(OSMNodeEditor& editor)
		: Node(editor)
	{}

	NodeType getType() const override { return NodeType::MASK_TEXTURE; }
	bool hasInputPins() const override { return false; }
	bool hasOutputPins() const override { return true; }
	
	void serialize(OutputMemoryStream& blob) override {
		blob.write(m_ref);
		blob.write(m_mask_scale);
		blob.writeString(m_texture);
	}

	void deserialize(InputMemoryStream& blob) override {
		blob.read(m_ref);
		blob.read(m_mask_scale);
		m_texture = blob.readString();
	}

	static float sampleMask(const u8* mask, Vec2 uv, IVec2 size) {
		const u32 w = size.x;
		const u32 h = size.y;
		const float a = fmodf(uv.x, float(w - 1));
		const float b = fmodf(uv.y, float(h - 1));
		
		u32 a0 = u32(a);
		u32 b0 = u32(b);
		const float tx = a - a0;
		const float ty = b - b0;
		a0 = a0 % w;
		b0 = b0 % h;

		const float v00 = mask[a0 + b0 * w] / float(0xff);
		const float v10 = mask[a0 + 1 + b0 * w] / float(0xff);
		const float v11 = mask[a0 + 1 + b0 * w + w] / float(0xff);
		const float v01 = mask[a0 + b0 * w + w] / float(0xff);

		return lerp(
			lerp(v00, v10, tx),
			lerp(v01, v11, tx),
			ty
		);
	};
	
	bool gui() override {
		nodeTitle("Mask texture");
		outputSlot();
		bool res = textureMaskInput(m_texture);
		res = ImGui::DragFloat("Ref value", &m_ref, 0.01f, 0.f, 1.f) || res;
		res = ImGui::DragFloat("Mask scale", &m_mask_scale, 0.01f, FLT_MIN, FLT_MAX) || res;
		return res;
	}
	
	UniquePtr<OutputValue> getOutputValue(u16 output_idx) override {
		IAllocator& allocator = m_editor.m_app.getAllocator();
		UniquePtr<MaskOutput> output = UniquePtr<MaskOutput>::create(allocator, allocator);
		output->m_size = getSplatmapSize(m_editor.m_app);
		output->m_bitmap.resize(output->m_size * output->m_size);
		u32 mask_w, mask_h;
		stbi_uc* mask = loadTexture(m_texture, mask_w, mask_h, m_editor.m_app);
		if (!mask) return outputError("Failed to load the texture");

		u8* out = output->m_bitmap.begin();
		const Vec2 rand_offset(randFloat(0, float(mask_w)), randFloat(0, float(mask_h)));
		for (u32 j = 0; j < output->m_size; ++j) {
			for (u32 i = 0; i < output->m_size; ++i) {
				const float k = fmodf(rand_offset.x + i * m_mask_scale, (float)mask_w);
				const float l = fmodf(rand_offset.y + j * m_mask_scale, (float)mask_h);
				u8& m = out[i + j * output->m_size]; 
				m = sampleMask(mask, Vec2(k, l), IVec2(mask_w, mask_h)) > m_ref ? 0xff : m;
			}
		}
		stbi_image_free(mask);
		return output.move();
	}

	StaticString<LUMIX_MAX_PATH> m_texture;
	float m_ref = 0.f;
	float m_mask_scale = 1.f;
};

struct InvertNode : OSMNodeEditor::Node {
	InvertNode(OSMNodeEditor& editor)
		: Node(editor)
	{}

	NodeType getType() const override { return NodeType::INVERT; }
	bool hasInputPins() const override { return true; }
	bool hasOutputPins() const override { return true; }
	void serialize(OutputMemoryStream& blob) override {}
	void deserialize(InputMemoryStream& blob) override {}

	UniquePtr<OutputValue> getOutputValue(u16 output_idx) override {
		UniquePtr<OutputValue> input = getInput(0);
		if (!input) return outputError("Invalid input");
		if (input->getType() != OutputType::MASK) return outputError("Invalid input");
		MaskOutput* mask = (MaskOutput*)input.get();

		for (u8& v : mask->m_bitmap) v = v ? 0 : 1;
		return input.move();
	}

	bool gui() override {
		nodeTitle("Invert");
		inputSlot();
		outputSlot();
		ImGui::TextUnformatted(" ");
		return false;
	}
};

struct PaintGroundNode : OSMNodeEditor::Node {
	PaintGroundNode(OSMNodeEditor& editor)
		: Node(editor)
	{}

	NodeType getType() const override { return NodeType::PAINT_GROUND; }
	bool hasInputPins() const override { return true; }
	bool hasOutputPins() const override { return false; }

	void serialize(OutputMemoryStream& blob) override {
		blob.write(m_ground);
	}

	void deserialize(InputMemoryStream& blob) override {
		blob.read(m_ground);
	}

	UniquePtr<OutputValue> getOutputValue(u16 output_idx) override { ASSERT(false); return {nullptr, nullptr}; }

	void run() {
		clearErrors();
		if (!ensureOSMData()) return;

		const UniquePtr<OutputValue> val = getInput(0);
		if (!val) return error("Invalid input");
		if (val->getType() != OutputType::MASK) return error("Invalid input");
		const MaskOutput* mask = (MaskOutput*)val.get();

		Terrain* terrain = getTerrain(m_editor.m_app);
		if (!terrain) return error("Terrain not found");
		
		TerrainEditor* terrain_editor = m_editor.getTerrainEditor();
		if (!terrain_editor) return error("Terrain editor not found");

		Texture* splatmap = terrain->getSplatmap();
		if (!splatmap) return error("Missing splatmap");
		if (!splatmap->isReady()) return error("Splatmap not ready");
		
		auto is_masked = [&](u32 x, u32 y){
			u32 i = u32(x / float(splatmap->width) * mask->m_size);
			u32 j = u32(y / float(splatmap->height) * mask->m_size);
			i = clamp(i, 0, mask->m_size - 1);
			j = clamp(j, 0, mask->m_size - 1);
			
			return mask->m_bitmap[i + j * mask->m_size] != 0;
		};

		OutputMemoryStream new_data(m_editor.m_allocator);
		new_data.resize(splatmap->height * splatmap->width * 4);
		u8* data = new_data.getMutableData();
		memcpy(data, splatmap->getData(), new_data.size());

		for (u32 y = 0; y < splatmap->height; ++y) {
			for (u32 x = 0; x < splatmap->width; ++x) {
				if (is_masked(x, y)) {
					u8* pixel = data + (x + (splatmap->height - y - 1) * splatmap->width) * 4;
					pixel[0] = m_ground;
					pixel[1] = m_ground;
				}
			}
		}
		terrain_editor->updateSplatmap(terrain, static_cast<OutputMemoryStream&&>(new_data), 0, 0, splatmap->width, splatmap->height, false);
	}

	bool gui() override {
		ImGuiEx::BeginNodeTitleBar(ImGui::GetColorU32(ImGuiCol_PlotLinesHovered));
		ImGui::AlignTextToFramePadding();
		ImGui::TextUnformatted("Paint ground");
		ImGui::SameLine();
		if (ImGui::Button(ICON_FA_PLAY)) run();
		ImGuiEx::EndNodeTitleBar();
		inputSlot();
		return ImGui::DragInt("Ground", (i32*)&m_ground, 1, 0, 256);
	}

	u32 m_ground = 0;
};

struct MaskBaseNode : OSMNodeEditor::Node {
	MaskBaseNode(OSMNodeEditor& editor)
		: Node(editor)
	{}
	
	DVec2 toBitmap(const DVec2& p, u32 size) const {
		DVec2 tmp;
		tmp = p;
		const Terrain* terrain = getTerrain(m_editor.m_app);
		const Vec2 s = terrain->getSize();
	
		tmp.x += s.x * 0.5f; 
		tmp.y += s.y * 0.5f; 
	
		tmp.x = tmp.x / s.x * (float)(size - 1);
		tmp.y = (1 - tmp.y  / s.y) * (float)(size - 1);
		return tmp;
	}
	
	Vec2 toBitmap(const Vec2& p, u32 size) const {
		Vec2 tmp;
		tmp = p;
		const Terrain* terrain = getTerrain(m_editor.m_app);
		const Vec2 s = terrain->getSize();
		tmp.x += s.x * 0.5f; 
		tmp.y += s.y * 0.5f; 
	
		tmp.x = tmp.x  / s.x * (float)size;
		tmp.y = (1 - tmp.y  / s.y) * (float)size;
		return tmp;
	}

	UniquePtr<MaskOutput> createOutput() {
		if (!getTerrain(m_editor.m_app)) return outputError("Terrain not found");

		IAllocator& allocator = m_editor.m_app.getAllocator();
		UniquePtr<MaskOutput> output = UniquePtr<MaskOutput>::create(allocator, allocator);
		output->m_size = getSplatmapSize(m_editor.m_app);
		output->m_bitmap.resize(output->m_size * output->m_size);
		memset(output->m_bitmap.begin(), 0, output->m_bitmap.byte_size());
		return output.move();
	}

	bool commonGUI() {
		outputSlot();
		return tagInput(Span(m_key.data), Span(m_value.data), 150);
	}

	StaticString<128> m_key;
	StaticString<128> m_value;
};

struct MaskPolylinesNode : MaskBaseNode {
	MaskPolylinesNode(OSMNodeEditor& editor)
		: MaskBaseNode(editor)
	{}

	NodeType getType() const override { return NodeType::MASK_POLYLINES; }
	bool hasInputPins() const override { return true; }
	bool hasOutputPins() const override { return true; }

	void serialize(OutputMemoryStream& blob) override {
		blob.write(m_width);
		blob.write(m_key);
		blob.write(m_value);
	}

	void deserialize(InputMemoryStream& blob) override {
		blob.read(m_width);
		blob.read(m_key);
		blob.read(m_value);
	}

	UniquePtr<OutputValue> getOutputValue(u16 output_idx) override {
		StudioApp& app = m_editor.m_app;
		Array<DVec2> polyline(app.getAllocator());
		UniquePtr<MaskOutput> output = createOutput();
		if (!output.get()) return output;

		for (pugi::xml_node& w : m_editor.m_osm_parser.m_ways) {
			if (!OSMParser::hasTag(w, m_key, m_value)) continue;

			polyline.clear();
			m_editor.m_osm_parser.getWay(w, polyline);
			for (i32 i = 0; i < polyline.size() - 1; ++i) {
				const DVec2 dir = normalize(polyline[i + 1] - polyline[i]) * 0.5 * double(m_width);
				const DVec2 n = DVec2(dir.y, -dir.x);
				const DVec2 a = toBitmap(polyline[i] + n - dir, output->m_size);
				const DVec2 b = toBitmap(polyline[i + 1] + n + dir, output->m_size);
				const DVec2 c = toBitmap(polyline[i + 1] - n + dir, output->m_size);
				const DVec2 d = toBitmap(polyline[i] - n - dir, output->m_size);
				const Vec2 vecs[] = {Vec2(a), Vec2(b), Vec2(c), Vec2(d), Vec2(a)};
				raster(Span(vecs), output->m_size, 1, output->m_bitmap);
			}
		}
		return output.move();
	}

	bool gui() override {
		nodeTitle("Mask polylines");
		bool res = commonGUI();
		res = ImGui::DragFloat("Width", &m_width, 0.1f, FLT_MIN, FLT_MAX) || res;
		return res;
	}

	float m_width = 1;
};

struct MaskPolygonsNode : MaskBaseNode {
	MaskPolygonsNode(OSMNodeEditor& editor)
		: MaskBaseNode(editor)
	{}

	NodeType getType() const override { return NodeType::MASK_POLYGONS; }
	bool hasInputPins() const override { return false; }
	bool hasOutputPins() const override { return true; }

	void serialize(OutputMemoryStream& blob) override {
		blob.write(m_key);
		blob.write(m_value);
	}

	void deserialize(InputMemoryStream& blob) override {
		blob.read(m_key);
		blob.read(m_value);
	}

	UniquePtr<OutputValue> getOutputValue(u16 output_idx) override {
		StudioApp& app = m_editor.m_app;
		Array<DVec2> polygon(app.getAllocator());
		Array<Vec2> points(app.getAllocator());

		UniquePtr<MaskOutput> output = createOutput();
		if (!output.get()) return output;

		Multipolygon2D multipolygon(app.getAllocator());
		for (pugi::xml_node& r : m_editor.m_osm_parser.m_relations) {
			if (!OSMParser::hasTag(r,m_key, m_value)) continue;
			
			m_editor.m_osm_parser.getMultipolygon(r, multipolygon);

			for (const Polygon2D& poly : multipolygon.outer_polygons) {
				points.clear();
				for (const DVec2 p : poly) {
					const DVec2 tmp = toBitmap(p, output->m_size);
					points.push(Vec2(tmp));
				}
				raster(points, output->m_size, 1, output->m_bitmap);
			}
			
			for (const Polygon2D& poly : multipolygon.inner_polygons) {
				points.clear();
				for (const DVec2 p : poly) {
					DVec2 tmp = toBitmap(p, output->m_size);
					points.push(Vec2(tmp));
				}
				raster(points, output->m_size, -1, output->m_bitmap);
			}
		}

		for (pugi::xml_node& w : m_editor.m_osm_parser.m_ways) {
			if (!OSMParser::hasTag(w, m_key, m_value)) continue;

			polygon.clear();
			points.clear();
			m_editor.m_osm_parser.getWay(w, polygon);

			for (const DVec2 p : polygon) {
				DVec2 tmp = toBitmap(p, output->m_size);
				points.push(Vec2(tmp));
			}
			raster(points, output->m_size, 1, output->m_bitmap);
		}

		return output.move();
	}

	bool gui() override {
		nodeTitle("Mask polygons");
		return commonGUI();
	}

};

void OSMNodeEditor::run() {
	for (Node* node : m_nodes) node->m_error = "";
	
	if (!getTerrain(m_app)) return;

	for (Node* node : m_nodes) {
		switch (node->getType()) {
			case NodeType::GRASS:
				((GrassNode*)node)->run();
				break;
			case NodeType::PLACE_SPLINES:
				((PlaceSplinesNode*)node)->run();
				break;
			case NodeType::PLACE_INSTANCES:
				((PlaceInstancesNode*)node)->run();
				break;
			case NodeType::ADJUST_HEIGHT:
				((AdjustHeightNode*)node)->run();
				break;
			case NodeType::PAINT_GROUND:
				((PaintGroundNode*)node)->run();
				break;
			default:
				break;
		}
	}
}

OSMNodeEditor::Node* OSMNodeEditor::addNode(NodeType type, ImVec2 pos) {
	Node* node = nullptr;
	switch(type) {
		case NodeType::MASK_POLYLINES: node = LUMIX_NEW(m_allocator, MaskPolylinesNode)(*this); break;
		case NodeType::MASK_POLYGONS: node = LUMIX_NEW(m_allocator, MaskPolygonsNode)(*this); break;
		case NodeType::PAINT_GROUND: node = LUMIX_NEW(m_allocator, PaintGroundNode)(*this); break;
		case NodeType::INVERT: node = LUMIX_NEW(m_allocator, InvertNode)(*this); break;
		case NodeType::GRASS: node = LUMIX_NEW(m_allocator, GrassNode)(*this); break;
		case NodeType::NOISE: node = LUMIX_NEW(m_allocator, NoiseNode)(*this); break;
		case NodeType::MASK_TEXTURE: node = LUMIX_NEW(m_allocator, MaskTextureNode)(*this); break;
		case NodeType::MERGE_MASKS: node = LUMIX_NEW(m_allocator, MergeMasksNode)(*this); break;
		case NodeType::DISTANCE_FIELD: node = LUMIX_NEW(m_allocator, DistanceFieldNode)(*this); break;
		case NodeType::PLACE_INSTANCES: node = LUMIX_NEW(m_allocator, PlaceInstancesNode)(*this); break;
		case NodeType::PLACE_SPLINES: node = LUMIX_NEW(m_allocator, PlaceSplinesNode)(*this); break;
		case NodeType::ADJUST_HEIGHT: node = LUMIX_NEW(m_allocator, AdjustHeightNode)(*this); break;
		case NodeType::FLATTEN_POLYLINES: node = LUMIX_NEW(m_allocator, FlattenPolylinesNode)(*this); break;
		case NodeType::MASK_DISTANCE: node = LUMIX_NEW(m_allocator, MaskDistanceNode)(*this); break;
		case NodeType::MERGE_DISTANCE_FIELDS: node = LUMIX_NEW(m_allocator, MergeDistanceFieldsNode)(*this); break;
	}
	node->m_pos = pos;
	node->m_id = ++m_node_id_genereator;
	m_nodes.push(node);
	return node;
}

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

constexpr int TILE_SIZE = 256;
constexpr int MAX_ZOOM = 18;
constexpr float MAP_UI_SIZE = 512;

struct MapsPlugin final : public StudioApp::GUIPlugin
{
	struct MapsTask;

	struct TileData {
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

	struct Area {
		Area(IAllocator& allocator) : prefabs(allocator) {}

		u16 grass = 0xffff;
		u8 ground = 0xff;
		bool inverted = false;
		float spacing = 1;
		StaticString<64> key = "";
		StaticString<64> value = "";
		Array<PrefabResource*> prefabs;
	};

	struct MapsTask : public Thread
	{
		MapsTask(StudioApp& app, TileData* tile, IAllocator& _allocator)
			: Thread(_allocator)
			, app(&app)
			, allocator(_allocator)
			, tile(*tile)
		{
		}


		static int getHTTPHeaderLength(Span<const u8> data)
		{
			for (u32 i = 0; i < data.length() - 4; ++i)
			{
				if (data[i] == '\r' && data[i + 1] == '\n' && data[i + 2] == '\r' && data[i + 3] == '\n')
				{
					return i + 4;
				}
			}
			return 0;
		}

		bool parseImage(Span<const u8> data) const
		{
			int header_size = getHTTPHeaderLength(data);

			int channels, w, h;
			int image_size = data.length() - header_size;
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
			const StaticString<LUMIX_MAX_PATH> path(".lumix/maps_cache", "/", is_heightmap ? "hm" : "im", tile.loc.z, "_", tile.loc.x, "_", tile.loc.y);
			
			os::InputFile file;
			if (fs.open(path, file)) {
				u8* out = is_heightmap ? (u8*)tile.hm_data.begin() : (u8*)tile.imagery_data.begin();
				const bool res = file.read(out, TILE_SIZE * TILE_SIZE * sizeof(u32));
				file.close();
				return res;
			}
			return false;
		}


		void saveToCache() {
			FileSystem& fs = app->getWorldEditor().getEngine().getFileSystem();
			const StaticString<LUMIX_MAX_PATH> dir(fs.getBasePath(), ".lumix/maps_cache");
			if (!os::makePath(dir)) logError("Could not create", dir);

			const StaticString<LUMIX_MAX_PATH> path(dir, "/", is_heightmap ? "hm" : "im", tile.loc.z, "_", tile.loc.x, "_", tile.loc.y);
			os::OutputFile file;
			if (file.open(path)) {
				u8* out = is_heightmap ? (u8*)tile.hm_data.begin() : (u8*)tile.imagery_data.begin();
				if (!file.write(out, TILE_SIZE * TILE_SIZE * sizeof(u32))) {
					logError("Could not write ", path);
				}
				file.close();
			}
			else {
				logError("Fail to create ", path);
			}
		}


		int task() override {
			if (loadFromCache()) return 0;
			
			String url("https://", allocator);
			url.cat((const char*)host);
			url.cat((const char*)path);
			OutputMemoryStream data(allocator);
			u32 local_downloaded_bytes;
			if (!::download(url.c_str(), data, local_downloaded_bytes)) {
				logError("Failed to download ", url);
				return -1;
			}

			atomicAdd(downloaded_bytes, local_downloaded_bytes);
			const bool res = parseImage(data);
			if (res) saveToCache();
			return res ? 0 : -1;
		}

		StaticString<LUMIX_MAX_PATH> host;
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
		, m_bitmap(app.getAllocator())
		, m_osm_editor(*this, app)
	{
		m_toggle_ui.init("Maps", "maps", "maps", "", true);
		m_toggle_ui.func.bind<&MapsPlugin::toggleOpen>(this);
		m_toggle_ui.is_selected.bind<&MapsPlugin::isOpen>(this);
		app.addWindowAction(&m_toggle_ui);
		m_out_path[0] = '\0';
	}
	
	void onBeforeSettingsSaved() override {
		Settings& settings = m_app.getSettings();
		settings.setValue(Settings::GLOBAL, "is_maps_plugin_open", m_open);
		settings.setValue(Settings::LOCAL, "maps_x", m_x);
		settings.setValue(Settings::LOCAL, "maps_y", m_y);
		settings.setValue(Settings::LOCAL, "maps_scale", m_scale);
		settings.setValue(Settings::LOCAL, "maps_resample", m_resample_hm);
		settings.setValue(Settings::LOCAL, "maps_zoom", m_zoom);
		settings.setValue(Settings::LOCAL, "maps_offset_x", m_pixel_offset.x);
		settings.setValue(Settings::LOCAL, "maps_offset_y", m_pixel_offset.y);
		settings.setValue(Settings::LOCAL, "maps_size", m_size);
		settings.setValue(Settings::LOCAL, "maps_osm_area_edge", m_osm_editor.m_area_edge);
		m_osm_editor.onBeforeSettingsSaved(settings);
	}

	void onSettingsLoaded() override {
		Settings& settings = m_app.getSettings();
		m_open = settings.getValue(Settings::GLOBAL, "is_maps_plugin_open", false);
		m_x = settings.getValue(Settings::LOCAL, "maps_x", 0);
		m_y = settings.getValue(Settings::LOCAL, "maps_y", 0);
		m_scale = settings.getValue(Settings::LOCAL, "maps_scale", 1.f);
		m_osm_editor.m_area_edge = settings.getValue(Settings::LOCAL, "maps_osm_area_edge", 0);
		m_resample_hm = settings.getValue(Settings::LOCAL, "maps_resample", 1);
		m_zoom = settings.getValue(Settings::LOCAL, "maps_zoom", 1);
		m_pixel_offset.x = settings.getValue(Settings::LOCAL, "maps_offset_x", 0);
		m_pixel_offset.y = settings.getValue(Settings::LOCAL, "maps_offset_y", 0);
		m_size = settings.getValue(Settings::LOCAL, "maps_size", 1);
		m_osm_editor.onSettingsLoaded(settings);
	}

	~MapsPlugin()
	{
		m_app.removeAction(&m_toggle_ui);
		finishAllTasks();
		clear();
	}

	void finishAllTasks()
	{
		IAllocator& allocator = m_app.getWorldEditor().getEngine().getAllocator();
		for (MapsTask* task : m_in_progress) {
			task->canceled = true;
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

		const double half = m_size == 0 ? 0.5 / double(size) : (1 << (m_size - 1)) / double(size);

		res.x = ((m_x + size) % size) / double(size);
		res.y = ((m_y + size) % size) / double(size);
		res.x += half;
		res.y += half;
		res.x -= m_pixel_offset.x * pixelToWorld();
		res.y -= m_pixel_offset.y * pixelToWorld();
		return res;
	}

	void setCorner(const DVec2& p) {
		const double worldToPixel = 1.0 / pixelToWorld();
		
		const i32 size = 1 << m_zoom;
		m_x = i32(p.x * size);
		m_y = i32(p.y * size);

		const double dx = m_x / double(size) - p.x;
		const double dy = m_y / double(size) - p.y;

		m_pixel_offset.x = i32(worldToPixel * dx);
		m_pixel_offset.y = i32(worldToPixel * dy);
		
		download();
	}

	DVec2 getCorner() {
		int size = 1 << m_zoom;
		DVec2 res;

		res.x = ((m_x + size) % size) / double(size);
		res.y = ((m_y + size) % size) / double(size);
		res.x -= m_pixel_offset.x * pixelToWorld();
		res.y -= m_pixel_offset.y * pixelToWorld();
		return res;
	}

	void clear()
	{
		IAllocator& allocator = m_app.getEngine().getAllocator();
		RenderInterface* ri = m_app.getRenderInterface();
		if (ri) {
			for (TileData* tile : m_tiles) {
				ri->destroyTexture(tile->imagery);
				ri->destroyTexture(tile->hm);
				
			}
			for (TileData* tile : m_cache) {
				ri->destroyTexture(tile->imagery);
				ri->destroyTexture(tile->hm);
				LUMIX_DELETE(allocator, tile);
			}
		}
		for (TileData* tile : m_tiles) LUMIX_DELETE(allocator, tile);
		for (TileData* tile : m_cache) LUMIX_DELETE(allocator, tile);
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
		IAllocator& allocator = editor.getEngine().getAllocator();
		TileData& tile = *m_tiles.emplace(LUMIX_NEW(allocator, TileData)(loc.x, loc.y, loc.z, allocator));
		
		const int map_size = TILE_SIZE * (1 << m_size);

		char url[1024];
		{
			getSatellitePath(url, loc);
			MapsTask* task = LUMIX_NEW(allocator, MapsTask)(m_app, &tile, allocator);
			// https://tiles.maps.eox.at/wmts/1.0.0/s2cloudless-2017_3857/default/g/2/1/1.jpg
			task->host = "tiles.maps.eox.at";
			task->path = url;
			task->downloaded_bytes = &m_downloaded_bytes;
			task->is_heightmap = false;
			tile.imagery_task = task;
			m_queue.push(task);
		}

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

		const int right_edge = m_pixel_offset.x < 0;
		const int left_edge = m_pixel_offset.x > 0;
		const int bottom_edge = m_pixel_offset.y < 0;
		const int top_edge = m_pixel_offset.y > 0;
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

	void createMapEntity() {
		const double lat = double(tiley2lat(double(m_y + (1 << (m_size - 1))), m_zoom));
		const double width = m_scale * 256 * (1 << m_size) * 156543.03 * cos(degreesToRadians(lat)) / (1 << m_zoom);
		WorldEditor& editor = m_app.getWorldEditor();
		const EntityRef e = editor.addEntityAt({-width * 0.5, m_last_saved_hm_range.x, -width * 0.5});
		editor.addComponent(Span(&e, 1), TERRAIN_TYPE);
		const PathInfo file_info(m_out_path);
		Path mat_path(file_info.m_dir, "/", file_info.m_basename, ".mat");
		
		editor.setProperty(TERRAIN_TYPE, "", -1, "Material", Span(&e, 1), mat_path);

		const float scale = float(width / ((1 << m_size) * 256));
		editor.setProperty(TERRAIN_TYPE, "", -1, "XZ scale", Span(&e, 1), scale / m_resample_hm);
		editor.setProperty(TERRAIN_TYPE, "", -1, "Height scale", Span(&e, 1), m_scale * (m_last_saved_hm_range.y - m_last_saved_hm_range.x));
	}

	void resample(Array<u16>& raw, i32 map_size, i32 scale) {
		Array<u16> tmp(m_app.getAllocator());
		const i32 stride = map_size * scale;
		tmp.resize(map_size * map_size * scale * scale);
		for (i32 j = 0; j < map_size * scale; ++j) {
			for (i32 i = 0; i < map_size * scale; ++i) {
				const double u = i / double(map_size * scale - 1) * (map_size - 1);
				const double v = j / double(map_size * scale - 1) * (map_size - 1);

				const i32 m = i32(u);
				const i32 n = i32(v);
				const i32 ma = minimum(m + 1, map_size - 1);
				const i32 na = minimum(n + 1, map_size - 1);
				const float tx = float(u - m);
				const float ty = float(v - n);

				const u16 h00 = raw[m + n * map_size];
				const u16 h10 = raw[ma + n * map_size];
				const u16 h01 = raw[m + na * map_size];
				const u16 h11 = raw[ma + na * map_size];

				const float h = lerp(
					lerp((float)h00, (float)h10, tx),
					lerp((float)h01, (float)h11, tx),
					ty);
				tmp[i + j * stride] = u16(h + 0.5f);
			}
		}
		raw.resize(tmp.size());
		memcpy(raw.begin(), tmp.begin(), tmp.byte_size());
	}

	static float toFloatHeight(u32 height) {
		return (height >> 16) * 256.f + ((height >> 8) & 0xff) * 1.f + (height & 0xff) / 256.f - 32768.f;
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
			if (p != 0xffFFff) {
				if (max < p) max = p;
				if (min > p) min = p;
			}
		});

		m_last_saved_hm_range.x = toFloatHeight(min);
		m_last_saved_hm_range.y = toFloatHeight(max);

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
		os::OutputFile file;
		FileSystem& fs = m_app.getEngine().getFileSystem();
		if (!fs.open(m_out_path, file)) {
			logError("Failed to save ", m_out_path);
			return;
		}
		RawTextureHeader header;
		header.channels_count = 1;
		header.channel_type = RawTextureHeader::ChannelType::U16;
		header.depth = 1;
		header.is_array = false;
		header.width = map_size * m_resample_hm;
		header.height = map_size * m_resample_hm;
		bool success = file.write(&header, sizeof(header));
		if (m_resample_hm > 1) {
			resample(raw, map_size, m_resample_hm);
		}
		success = file.write(&raw[0], raw.byte_size()) && success;
		if (!success) {
			logError("Could not write ", m_out_path);
		}
		file.close();

		RenderInterface* ri = m_app.getRenderInterface();
		PathInfo file_info(m_out_path);
		StaticString<LUMIX_MAX_PATH> satellite_path(file_info.m_dir, "/", file_info.m_basename, ".tga");
		ri->saveTexture(editor.getEngine(), satellite_path, imagery.begin(), map_size, map_size, true);

		const StaticString<LUMIX_MAX_PATH> albedo_path(file_info.m_dir, "albedo_detail.ltc");
		const StaticString<LUMIX_MAX_PATH> normal_path(file_info.m_dir, "normal_detail.ltc");
		const StaticString<LUMIX_MAX_PATH> splatmap_path(file_info.m_dir, "splatmap.tga");
		const StaticString<LUMIX_MAX_PATH> satellite_meta_path(file_info.m_dir, file_info.m_basename, ".tga.meta");
		const StaticString<LUMIX_MAX_PATH> splatmap_meta_path(file_info.m_dir, "splatmap.tga.meta");
		
		if (!fs.open(satellite_meta_path, file)) {
			logError("Failed to create ", satellite_meta_path);
		}
		else {
			file << "filter = \"point\"";
			file.close();
		}
		
		if (!fs.open(splatmap_meta_path, file)) {
			logError("Failed to create ", splatmap_meta_path);
		}
		else {
			file << "compress = false\n";
			file << "mips = false\n";
			file << "filter = \"point\"";
			file.close();
		}

		if (!fs.fileExists(splatmap_path)) {
			if (!fs.open(splatmap_path, file)) {
				logError("Failed to create ", splatmap_path);
			}
			else {
				OutputMemoryStream splatmap(m_app.getAllocator());
				splatmap.resize(header.width * header.height * 4);
				memset(splatmap.getMutableData(), 0, splatmap.size());
				Texture::saveTGA(&file, header.width, header.height, gpu::TextureFormat::RGBA8, splatmap.data(), true, Path(splatmap_path), m_app.getAllocator());
				file.close();
			}
		}

		if (!fs.fileExists(albedo_path)) {
			if (!fs.open(albedo_path, file)) {
				logError("Failed to create ", albedo_path);
			}
			else {
				CompositeTexture ct(m_app, m_app.getAllocator());
				OutputMemoryStream blob(m_app.getAllocator());
				ct.initTerrainAlbedo();
				ct.serialize(blob);
				if (!file.write(blob.data(), blob.size())) {
					logError("Failed to write ", albedo_path);
				}
				file.close();
			}
		}

		if (!fs.fileExists(normal_path)) {
			if (!fs.open(normal_path, file)) {
				logError("Failed to create ", normal_path);
			}
			else {
				CompositeTexture ct(m_app, m_app.getAllocator());
				OutputMemoryStream blob(m_app.getAllocator());
				ct.initTerrainNormal();
				ct.serialize(blob);
				if (!file.write(blob.data(), blob.size())) {
					logError("Failed to write ", normal_path);
				}
				file.close();
			}
		}

		StaticString<LUMIX_MAX_PATH> mat_path(file_info.m_dir, "/", file_info.m_basename, ".mat");
		os::OutputFile mat_file;
		if (!fs.fileExists(mat_path)) {
			if (fs.open(mat_path, mat_file)) {
				mat_file << R"#(
					shader "/pipelines/terrain.shd"
					texture ")#";
				mat_file << file_info.m_basename;
				mat_file << R"#(.raw"
					texture "albedo_detail.ltc"
					texture "normal_detail.ltc"
					texture "splatmap.tga"
					texture ")#" << file_info.m_basename << R"#(.tga"
					uniform("Detail distance", 50.000000)
					uniform("Detail scale", 1.000000)
					uniform("Noise UV scale", 0.200000)
					uniform("Detail diffusion", 0.500000)
					uniform("Detail power", 16.000000)
				)#";

				mat_file.close();
			}
		}

		StaticString<LUMIX_MAX_PATH> raw_meta_path(file_info.m_dir, "/", file_info.m_basename, ".raw.meta");
		os::OutputFile raw_meta_file;
		if (fs.open(raw_meta_path, raw_meta_file)) {
			raw_meta_file << "wrap_mode_u = \"clamp\"\n";
			raw_meta_file << "wrap_mode_v = \"clamp\"\n";
			raw_meta_file.close();
		}

		StaticString<LUMIX_MAX_PATH> tga_meta_path(file_info.m_dir, "/", file_info.m_basename, ".tga.meta");
		os::OutputFile tga_meta_file;
		if (fs.open(tga_meta_path, tga_meta_file)) {
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

	void resize(const DVec2& corner, i32 old_size)
	{
		m_zoom += m_size - old_size;
		setCorner(corner);
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
		IVec2 offset = m_pixel_offset;
		m_pixel_offset = IVec2(0);
		const DVec2 new_center = getCenter();
		m_pixel_offset.x += int((new_center.x - center.x) / pixelToWorld());
		m_pixel_offset.y += int((new_center.y - center.y) / pixelToWorld());
		const DVec2 check = getCenter();

		download();
	}

	ImVec2 getPos(const TileData& tile) const {
		ImVec2 res;
		res.x = float(256 * (tile.loc.x - m_x)) + m_pixel_offset.x;
		res.y = float(256 * (tile.loc.y - m_y)) + m_pixel_offset.y;
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
		World* world = editor.getWorld();
		if (!world->hasComponent(entities[0], TERRAIN_TYPE)) {
			ImGui::TextUnformatted("Selected entity does not have terrain component");
			return;
		}
		RenderModule* module = (RenderModule*)world->getModule("renderer");
		Material* mat = module->getTerrainMaterial(entities[0]);
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

	bool hasFocus() override { return m_has_focus; }
	
	void onWindowGUI() override {
		m_has_focus = false;
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
		m_has_focus = ImGui::IsWindowFocused(ImGuiFocusedFlags_RootAndChildWindows);

		if (ImGui::BeginTabBar("tabs")) {
			if (ImGui::BeginTabItem("Map")) {
				mapGUI();
				ImGui::EndTabItem();
			}
			if (ImGui::BeginTabItem("OSM")) {
				m_osm_editor.gui(m_x, m_y, m_pixel_offset, m_zoom, m_scale, m_size);
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

	Terrain* getSelectedTerrain() const {
		WorldEditor& editor = m_app.getWorldEditor();
		World* world = m_app.getWorldEditor().getWorld();
		const Array<EntityRef>& selected_entities = editor.getSelectedEntities();
		
		if (selected_entities.size() != 1) return nullptr;
		if (!world->hasComponent(selected_entities[0], TERRAIN_TYPE)) return nullptr;

		RenderModule* module = (RenderModule*)world->getModule("renderer");
		return module->getTerrain(selected_entities[0]);
	}

	void mapGUI() {
		if (m_is_download_deferred) download();

		ImGuiEx::Label("Size");
		const DVec2 corner = getCorner();
		const i32 old_size = m_size;
		if (ImGui::Combo("##size", &m_size, "256\0" "512\0" "1024\0" "2048\0" "4096\0")) resize(corner, old_size);

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

		ImGuiEx::Label("Scale");
		ImGui::DragFloat("##objscale", &m_scale);

		ImGuiEx::Label("Resample");
		ImGui::InputInt("##hmresample", &m_resample_hm);
		ImGuiEx::Label("Output");
		if (ImGui::Button(StaticString<LUMIX_MAX_PATH + 128>(m_out_path[0] ? m_out_path : "Click to set"), ImVec2(-1, 0))) {
			m_show_save_raw = true;
		}

		FileSelector& fs = m_app.getFileSelector();
		if (fs.gui("Save As", &m_show_save_raw, "raw", true)) copyString(m_out_path, fs.getPath());

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
				if (tile->hm != (void*)(intptr_t)0xffFFffFF && m_show_hm) ImGui::ImageButton("hm", tile->hm, ImVec2(TILE_SIZE * scale, TILE_SIZE* scale));
				if (tile->imagery != (void*)(intptr_t)0xffFFffFF && !m_show_hm) ImGui::ImageButton("img", tile->imagery, ImVec2(TILE_SIZE* scale, TILE_SIZE* scale));
				hovered = hovered || ImGui::IsItemHovered();
			}
			ImGui::SetCursorPos(cp);
			ImGui::Dummy(ImVec2(512, 512));
		}
		ImGui::PopStyleVar();
		ImGui::EndChild();

		if(ImGui::IsMouseDragging(0) && m_is_dragging) {
			m_pixel_offset.x = m_drag_start_offset.x + int(ImGui::GetMouseDragDelta().x) * (1 << (m_size - 1));
			m_pixel_offset.y = m_drag_start_offset.y + int(ImGui::GetMouseDragDelta().y) * (1 << (m_size - 1));
			
			const int size = 1 << m_zoom;
			if (m_pixel_offset.x > 256) {
				m_drag_start_offset.x -= 256;
				m_pixel_offset.x -= 256;
				--m_x;
			} 
			if (m_pixel_offset.x < -256) {
				m_drag_start_offset.x += 256;
				m_pixel_offset.x += 256;
				++m_x;
			} 
			if (m_pixel_offset.y > 256) {
				m_drag_start_offset.y -= 256;
				m_pixel_offset.y -= 256;
				--m_y;
			} 
			if (m_pixel_offset.y < -256) {
				m_drag_start_offset.y += 256;
				m_pixel_offset.y += 256;
				++m_y;
			} 
			download();
		}

		if (ImGui::GetIO().MouseWheel && hovered) {
			zoom(ImGui::GetIO().MouseWheel > 0 ? 1 : -1);
		}

		if (ImGui::IsMouseClicked(0) && hovered) {
			m_is_dragging = true;
			m_drag_start_offset = m_pixel_offset;
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
			StaticString<sizeof(loc)> tmp(m_x, ";", m_y, ";", m_zoom, ";", m_pixel_offset.x, ";", m_pixel_offset.y);
			copyString(loc, tmp);
		}
		ImGui::SameLine();
		if (ImGuiEx::IconButton(ICON_FA_COPY, "Copy to clipboard")) {
			os::copyToClipboard(loc);
		}
		ImGui::SameLine();
		if (ImGuiEx::IconButton(ICON_FA_BULLSEYE, "View")) {
			sscanf(loc, "%d;%d;%d;%d;%d", &m_x, &m_y, &m_zoom, &m_pixel_offset.x, &m_pixel_offset.y);
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
	Array<u8> m_bitmap;
	u32 m_bitmap_size = 0;
	Array<TileData*> m_tiles;
	Array<TileData*> m_cache;
	Array<MapsTask*> m_queue;
	Array<MapsTask*> m_in_progress;
	volatile i32 m_downloaded_bytes = 0;
	bool m_open = false;
	bool m_is_download_deferred = true;
	i32 m_zoom = 1;
	float m_scale = 1.f;
	i32 m_resample_hm = 1;
	i32 m_x = 0;
	i32 m_y = 0;
	IVec2 m_pixel_offset{0, 0};
	i32 m_size = 1;
	char m_out_path[LUMIX_MAX_PATH];
	IVec2 m_drag_start_offset;
	bool m_is_dragging = false;
	bool m_has_focus = false;
	bool m_show_save_raw = false;
	Action m_toggle_ui;
	Vec2 m_last_saved_hm_range = Vec2(0, 1000);
	OSMNodeEditor m_osm_editor;
};


} // anonoymous namespace


LUMIX_STUDIO_ENTRY(maps)
{
	WorldEditor& editor = app.getWorldEditor();

	auto* plugin = LUMIX_NEW(editor.getAllocator(), MapsPlugin)(app);
	app.addPlugin(*plugin);
	return nullptr;
}
