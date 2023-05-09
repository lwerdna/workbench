
UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Darwin)
    $(info ******** host platform: MACOS! ********)
	TOOLCHAIN_SYSTEM := darwin-x86_64
endif
ifeq ($(UNAME_S),Linux)
    $(info ******** host platform: LINUX! ********)
	TOOLCHAIN_SYSTEM := linux-x86_64
endif

ifeq (TOOLCHAIN_SYSTEM,"")
    $(error unable to detect OS!)
endif

TOOLCHAIN_NAME := arm-linux-androideabi-4.9
TOOLCHAIN_PREFIX := arm-linux-androideabi-
SYSROOT := $(NDK)/platforms/android-21/arch-arm

LIB_SWITCHES := -L$(HOME)/$(TOOLCHAIN_NAME)/platforms/android-21/arch-arm/usr/lib

CC = $(NDK)/toolchains/$(TOOLCHAIN_NAME)/prebuilt/$(TOOLCHAIN_SYSTEM)/bin/$(TOOLCHAIN_PREFIX)gcc --sysroot=$(SYSROOT)
CPP = $(NDK)/toolchains/$(TOOLCHAIN_NAME)/prebuilt/$(TOOLCHAIN_SYSTEM)/bin/$(TOOLCHAIN_PREFIX)c++ --sysroot=$(SYSROOT)
AS = $(NDK)/toolchains/$(TOOLCHAIN_NAME)/prebuilt/$(TOOLCHAIN_SYSTEM)/bin/$(TOOLCHAIN_PREFIX)as
LD = $(NDK)/toolchains/$(TOOLCHAIN_NAME)/prebuilt/$(TOOLCHAIN_SYSTEM)/bin/$(TOOLCHAIN_PREFIX)ld

all: refload libfake.so

detours_thumb.o: detours_thumb.c
	$(CC) -g -O0 -c -march=armv7-a -mthumb -fPIE detours_thumb.c

detours_arm.o: detours_arm.c
	$(CC) -g -O0 -c -march=armv7-a -fPIE detours_arm.c

refload.o: refload.c
	$(CC) -g -O0 -c -march=armv7-a -fPIE refload.c

refload: refload.o detours_thumb.o detours_arm.o
	$(CC) -g -O0 refload.o detours_thumb.o detours_arm.o -o refload libcutils.so -Wl,-pie

libfake.so: libfake.c
	$(CC) -g -O0 -fPIE -shared libfake.c -o libfake.so

clean:
	if [ -e refload ]; then rm refload; fi;
	if [ -e refload.o ]; then rm refload.o; fi;
	if [ -e detours_thumb.o ]; then rm detours_thumb.o; fi;
	if [ -e detours_arm.o ]; then rm detours_arm.o; fi;
	if [ -e libfake.so ]; then rm libfake.so; fi;
