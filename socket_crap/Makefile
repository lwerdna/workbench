UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Darwin)
    $(info ******** compiling for MACOS! ********)
    CC = clang
    CFLAGS += -D OS_IS_MACOS
endif
ifeq ($(UNAME_S),Linux)
    $(info ******** compiling for LINUX! ********)
    CC = gcc
    CFLAGS += -D OS_IS_LINUX
endif
ifeq ($(UNAME_S),FreeBSD)
    $(info ******** compiling for FreeBSD! ********)
    CC = cc
    CFLAGS += -D OS_IS_FREEBSD
endif
ifeq (CC,"")
    $(error unable to detect OS!)
endif

all: openscan openscan_pcap connectscan interfaces

connectscan: connectscan.c
	$(CC) connectscan.c -o connectscan

openscan: openscan.c
	$(CC) openscan.c -o openscan

openscan_pcap: openscan_pcap.c
	$(CC) openscan_pcap.c -lpcap -o openscan_pcap

interfaces: interfaces.c
	$(CC) interfaces.c -o interfaces

clean:
	rm connectscan openscan openscan_pcap interfaces

