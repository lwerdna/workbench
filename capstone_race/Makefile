CPPFLAGS = 
CPPFLAGS += -I/usr/local/include -std=c++11 -O0 -g

all: binthunk.so binary

binthunk.so: binthunk.cpp
	g++ $(CPPFLAGS) \
		-lcapstone \
		-shared -o binthunk.so binthunk.cpp \
		-Wl,-headerpad_max_install_names
	install_name_tool -change libcapstone.3.dylib /usr/local/lib/libcapstone.3.dylib binthunk.so
	#install_name_tool -add_rpath `pwd` binthunk.so

binary: binary.cpp
	g++ $(CPPFLAGS) binary.cpp -lcapstone -o binary

