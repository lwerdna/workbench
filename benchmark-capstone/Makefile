CPPFLAGS = 
CPPFLAGS += -I/usr/local/include -std=c++11 -Ofast

all: gofer.so method0 method1

gofer.so: gofer.cpp
	g++ $(CPPFLAGS) \
		-lcapstone \
		-shared -o gofer.so gofer.cpp \
		-Wl,-headerpad_max_install_names
	install_name_tool -change libcapstone.3.dylib /usr/local/lib/libcapstone.3.dylib gofer.so
	#install_name_tool -add_rpath `pwd` gofer.so

method0: method0.cpp
	g++ $(CPPFLAGS) method0.cpp -lcapstone -o method0

method1: method1.cpp
	g++ $(CPPFLAGS) method1.cpp -lcapstone -o method1

clean:
	rm method0 2>/dev/null
	rm method1 2>/dev/null
	rm -rf method0.DSYM 2>/dev/null
	rm -rf method1.DSYM 2>/dev/null
	rm gofer.so 2>/dev/null
	rm -rf gofer.so.DSYM 2>/dev/null
