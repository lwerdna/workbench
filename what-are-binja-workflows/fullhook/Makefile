all: libtest.dylib

libtest.dylib: test.cpp
	g++ -std=c++17 -I$(BN_API) test.cpp $(BN_LIBBINARYNINJAAPI) $(BN_LIBBINARYNINJACORE) -fPIC -shared -o libtest.dylib

clean:
	rm -f libtest.dylib

install:
	cp libtest.dylib "$(BN_PLUGINS)"

uninstall:
	rm "$(BN_PLUGINS)/libtest.dylib"
