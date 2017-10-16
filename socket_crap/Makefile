
UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Darwin)
    $(info ******** compiling for MACOS! ********)
    CC = clang
    CFLAGS += -D OS_IS_MACOS -D OS_IS_BSD
    IFACES_SRC = interfaces_bsd.c
endif
ifeq ($(UNAME_S),Linux)
    $(info ******** compiling for LINUX! ********)
    CC = gcc
    CFLAGS += -D OS_IS_LINUX
    IFACES_SRC = interfaces_linux.c
endif
ifeq ($(UNAME_S),FreeBSD)
    $(info ******** compiling for FreeBSD! ********)
    CC = cc
    CFLAGS += -D OS_IS_FREEBSD -D OS_IS_BSD
    IFACES_SRC = interfaces_bsd.c
endif
ifeq (CC,"")
    $(error unable to detect OS!)
endif

all: openscan openscan_pcap connectscan interfaces

connectscan: connectscan.c
	$(CC) $(CFLAGS) connectscan.c -o connectscan

openscan: openscan.c
	$(CC) $(CFLAGS) openscan.c -o openscan

openscan_pcap: openscan_pcap.c
	$(CC) $(CFLAGS) openscan_pcap.c -lpcap -o openscan_pcap

interfaces: $(IFACES_SRC)
	$(CC) $(CFLAGS) $(IFACES_SRC) -o interfaces

clean:
	rm connectscan openscan openscan_pcap interfaces

