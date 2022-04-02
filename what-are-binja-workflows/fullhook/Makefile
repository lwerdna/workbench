all: libtest.dylib

libtest.dylib: test.cpp
	g++ -std=c++17 -I$(BN_API_PATH) test.cpp $(BN_LIBBINARYNINJAAPI) $(BN_LIBBINARYNINJACORE) -fPIC -shared -o libtest.dylib
	install_name_tool -change @rpath/libbinaryninjacore.1.dylib $(BN_LIBBINARYNINJACORE) ./libtest.dylib

clean:
	rm -f libtest.dylib

install:
	cp libtest.dylib "$(BN_PLUGINS)"

uninstall:
	rm "$(BN_PLUGINS)/libtest.dylib"
