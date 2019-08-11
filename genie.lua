project "maps"
	libType()
	files { 
		"src/**.c",
		"src/**.cpp",
		"src/**.h",
		"genie.lua"
	}
	defines { "BUILDING_MAPS" }
	links { "engine" }
	useLua()
	defaultConfigurations()

linkPlugin("maps")