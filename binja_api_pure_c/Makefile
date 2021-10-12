# BN_API_DIR must be set, eg: ~/repos/vector35/binaryninja/api
# BN_INSTALL_DIR must be set, eg: /Applications/Binary\ Ninja.app

# determine PATH_CORE
ifeq ($(OS),Windows_NT)
    PATH_CORE = $(BN_INSTALL_DIR)/dunno
else
	# os
    UNAME_S := $(shell uname -s)
    ifeq ($(UNAME_S),Linux)
    	PATH_CORE = $(BN_INSTALL_DIR)/dunno
    endif
    ifeq ($(UNAME_S),Darwin)
    	PATH_CORE = $(BN_INSTALL_DIR)/Contents/MacOS/
    endif
endif

all: go

go: go.c
	gcc go.c -std=c17 -o go -I$(BN_API_PATH) -L$(PATH_CORE) -lbinaryninjacore
	install_name_tool -change @rpath/libbinaryninjacore.1.dylib $(PATH_CORE)/libbinaryninjacore.dylib ./go

clean:
	rm -f go
