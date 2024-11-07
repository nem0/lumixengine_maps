project "maps"
	libType()
	files { 
		"src/**.c",
		"src/**.cpp",
		"src/**.h",
		"genie.lua"
	}
	defines { "BUILDING_MAPS" }
	links { "engine", "core", "renderer" }
	if build_studio then
		links { "editor" }
	end
	defaultConfigurations()

linkPlugin("maps")