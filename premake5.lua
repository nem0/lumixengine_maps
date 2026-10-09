-- Runs inside the plugin project. Paths are relative to this file.
files { "src/**.c", "src/**.cpp", "src/**.h" }
defines { "BUILDING_MAPS" }

-- plugins link each other only in dynamic builds
if _OPTIONS["dynamic-plugins"] then
	links { "core", "engine", "renderer" }
	if _OPTIONS["no-studio"] == nil then
		links { "editor" }
	end
end
