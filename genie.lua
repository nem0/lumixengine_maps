if plugin "maps" then
	files { 
		"src/**.c",
		"src/**.cpp",
		"src/**.h",
		"genie.lua"
	}
	defines { "BUILDING_MAPS" }
	dynamic_link_plugin { "engine", "core", "renderer" }
	if build_studio then
		dynamic_link_plugin { "editor" }
	end
end