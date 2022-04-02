all: test.dylib

#------------------------------------------------------------------------------
# plugin
#------------------------------------------------------------------------------

test.dylib: test.cpp
	g++ -std=c++17 -I$(BN_API_PATH) $(BN_LIBBINARYNINJAAPI) $(BN_LIBBINARYNINJACORE) test.cpp -fPIC -shared -o test.dylib
	install_name_tool -change @rpath/libbinaryninjacore.1.dylib $(BN_LIBBINARYNINJACORE) ./test.dylib

#------------------------------------------------------------------------------
# tests
#------------------------------------------------------------------------------

#------------------------------------------------------------------------------
# clean/install/uninstall targets
#------------------------------------------------------------------------------

clean:
	rm -f test.dylib *.o tests

install:
	cp test.dylib "$(BN_PLUGINS)"
	cp testcomms.py "$(BN_PLUGINS)"

uninstall:
	rm -f "$(BN_PLUGINS)/test.dylib"
	rm -f "$(BN_PLUGINS)/testcomms.py"
