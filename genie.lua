project "lumixengine_maps"
	libType()
	files { 
		"src/**.c",
		"src/**.cpp",
		"src/**.h",
		"genie.lua"
	}
	includedirs { "../../lumixengine_maps/src", }
	defines { "BUILDING_MAPS" }
	links { "engine" }
	useLua()
	defaultConfigurations()
