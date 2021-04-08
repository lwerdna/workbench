all: sample_x86 sample_x64

sample_x86: sample.c
	clang -shared -undefined dynamic_lookup -arch i386 -Wl,-macos_version_min,10.4 sample.c -o sample_x86

sample_x64: sample.c
	clang -shared -undefined dynamic_lookup -arch x86_64 -Wl,-macos_version_min,10.4 sample.c -o sample_x64
