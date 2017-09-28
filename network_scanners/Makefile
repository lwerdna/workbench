all: openscan openscan_pcap connectscan

connectscan: connectscan.c
	gcc connectscan.c -o connectscan

openscan: openscan.c
	gcc openscan.c -o openscan

openscan_pcap: openscan_pcap.c
	gcc openscan_pcap.c -lpcap -o openscan_pcap

clean:
	rm connectscan openscan openscan_pcap

