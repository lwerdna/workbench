
#include <stdio.h>
#include <stdlib.h>
#include <memory.h>
#include <errno.h>

#include <unistd.h>

#include <sys/socket.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/time.h> /* struct timeval, gettimeofday() */
#include <arpa/inet.h> /* inet_addr() */
#include <netinet/in.h> /* IPPROTO_TCP */
#include <netinet/ip.h> /* struct ip */
#include <netinet/tcp.h> /* struct tcphdr */

#include <net/if.h>
#include <net/ethernet.h>
#include <ifaddrs.h>

#include <pcap.h>

/* how many write() calls to do before read() all packets in the queue

	for each write() of SYN, we queue and read() 2 packets (outgoing, and RST)
	and additionally a SYNACK if the port is open

	if blast size is too large, we overflow the read() queue and potentially
	lose SYNACK

	on my Ubuntu machine, read queue was around ~140 bare IP+TCP packets
*/
#define BLAST_SZ 32
#define PCAP_TIMEOUT_MS 1
#define PCAP_SNAPLEN 256

/*****************************************************************************/
/* MISCELLANY */
/*****************************************************************************/
void dump_bytes(const uint8_t *buf, int len, uintptr_t addr)
{
    int i, j;
    char ascii[17];

    i = 0;
    while(i < len) {
        printf("%016llX: ", (long long unsigned int)addr);
        for(j=0; j<16; ++j) {
            if(i < len) {
                printf("%02X ", buf[i]);
                if((buf[i] >= ' ') && (buf[i] < '~')) {
                    ascii[j] = buf[i];
                }
                else {
                    ascii[j] = '.';
                }
            }
            else {
                printf("   ");
                ascii[j] = ' ';
            }

            i++;
        }
        ascii[sizeof(ascii)-1] = '\0';
        printf(" %s\n", ascii);
        addr += 16;
    }
}

/* https://en.wikipedia.org/wiki/Transmission_Control_Protocol#TCP_checksum_for_IPv4 */
typedef struct csum_input_ipv4_ {
	uint32_t s_addr, d_addr;
	uint16_t zeros, protocol;
	uint32_t tcp_len;
	struct tcphdr tcp_hdr;
} csum_input_ipv4;

uint16_t csum(uint16_t *buf, int nwords)
{
	int i;
	uint32_t sum = 0;
	for(i = 0; i<nwords; ++i) {
		//printf("processing word %04X", buf[i]);
		sum += buf[i];
		//printf(" -> sum = %04X\n", sum);
	}
	sum = (sum >> 16) + (sum & 0xffff);
	sum += (sum >> 16);
	return ~sum;
}

/*****************************************************************************/
/* PACKET READING */
/*****************************************************************************/

/* We are sent ETHERNET layer 

   [ transport/TCP (ports)         ]
   [ network/IP    (ip addrs)      ]
   [ link/ethernet (mac addrs)     ] <-- here
   [ phys          (pulses, waves) ]
*/
void process_pkt_cb(uint8_t *user, const struct pcap_pkthdr *h, const uint8_t *bytes)
{
	struct ip *iph = NULL;
	int n = h->caplen;
	pcap_t *handle = (pcap_t *)user;
	
	//printf("%s() gets packet sized 0x%X\n", __func__, h->caplen);
	//dump_bytes(bytes, n, (uintptr_t)bytes);
	
	int dlt = pcap_datalink(handle);
	switch(dlt) {
		case DLT_NULL:
		//case LINKTYPE_NULL:
			iph = (struct ip *)(bytes + 4);
			break;
		case DLT_EN10MB:
		//case LINKTYPE_ETHERNET:
			iph = (struct ip *)(bytes + ETHER_HDR_LEN);
			break;
		default:
			printf("unknown data link type: %d\n", dlt);
	}

	if(!iph) {
		printf("ERROR: could not set ip header pointer\n");
		goto cleanup;
	}


	//printf("ip header ok ihl:%d (len:0x%X bytes)\n", iph->ip_hl, iph->ip_hl*4);

	if(iph->ip_v != 4 || iph->ip_hl != 5) {
		dump_bytes(bytes, n, 0);
		printf("WARNING: malformed IP packet\n");
		goto cleanup;
	}
	
	if(iph->ip_p != IPPROTO_TCP)
		goto cleanup;

	struct tcphdr *tcph = (struct tcphdr *)((uint8_t *)iph + iph->ip_hl*4);
	//printf("tcp header:\n");
	uint16_t sport = ntohs(tcph->th_sport);
	uint16_t dport = ntohs(tcph->th_dport);

	if(tcph->th_flags == (TH_SYN|TH_ACK)) {
		//printf("SYNACK %d->%d\n", sport, dport);
		printf("port %d is open!\n", sport);
		dump_bytes((void *)tcph, 16, (uintptr_t)tcph);
		//dump_bytes(bytes, n, 0);
	}
	else if(tcph->th_flags == (TH_RST)) {
		printf("RST %d->%d\n", sport, dport);
		while(0);
	}
	else if(tcph->th_flags == (TH_SYN)) {
		printf("SYN %d->%d\n", sport, dport);
		while(0);
	}
	else {
		printf("ignoring %d->%d with flags:%04X\n", sport, dport, tcph->th_flags);
		//dump_bytes(bytes, n, 0);
		while(0);
	}

	cleanup:
	return;
}

int pcap_setup(pcap_t **handle_out)
{
	int rc = -1;

	pcap_t *handle;
	char *dev_name;
	char errbuf[PCAP_ERRBUF_SIZE];
	struct bpf_program fp;
	//char filter_exp[] = "tcp[tcpflags] & (tcp-syn|tcp-ack) != 0";	/* The filter expression */
	char filter_exp[] = "tcp[tcpflags] == (tcp-syn|tcp-ack)";	/* The filter expression */
	bpf_u_int32 mask;
	bpf_u_int32 na;	
	int dl_type;

	/* Define the device */
	dev_name = pcap_lookupdev(errbuf);
	if (dev_name == NULL) {
		printf("ERROR: pcap_lookupdev(), %s\n", errbuf);
		goto cleanup;
	}
	dev_name = "lo0";
	printf("using device: %s\n", dev_name);

	/* Find the properties for the device */
	if (pcap_lookupnet(dev_name, &na, &mask, errbuf) == -1) {
		printf("ERROR: pcap_lookupnet(), %s\n", errbuf);
		na = 0;
		mask = 0;
	}
	printf("IP: %d.%d.%d.%d\n", na&0xFF, (na&0xFF00)>>8, (na&0xFF0000)>>16, (na&0xFF000000)>>24);
	printf("MASK: %d.%d.%d.%d\n", mask&0xFF, (mask&0xFF00)>>8, (mask&0xFF0000)>>16, (mask&0xFF000000)>>24);

	/* Open the session in promiscuous mode */
	errbuf[0] = '\0';
	handle = pcap_open_live(dev_name, PCAP_SNAPLEN, 1, PCAP_TIMEOUT_MS, errbuf);
	if (handle == NULL) {
		printf("ERROR: pcap_open_live(), %s\n", errbuf);
		goto cleanup;
	}
	if(errbuf[0]) {
		printf("WARNING: %s\n", errbuf);
	}

	if(pcap_setnonblock(handle, 1, errbuf) == -1) {
		printf("ERROR: pcap_setnonblock(), %s\n", errbuf);
		goto cleanup;
	}

	// DLT_NULL==0, DLT_EN10MB==1, etc.
	// in my testing, it's ethernet (DLT_EN10MB) or 802.3 frame
	dl_type = pcap_datalink(handle);
	printf("data link type: %d\n", dl_type);

	//* Compile and apply the filter */
	if(1) {
		if (pcap_compile(handle, &fp, filter_exp, 0, na) == -1) {
			printf("ERROR: pcap_compile(), %s\n", pcap_geterr(handle));
			goto cleanup;
		}
		if (pcap_setfilter(handle, &fp) == -1) {
			printf("ERROR: pcap_setfilter(), %s\n", pcap_geterr(handle));
			goto cleanup;
		}
	}

	/* success */
	*handle_out = handle;
	rc = 0;

	cleanup:
	return rc;
}

int pcap_consume(pcap_t *handle)
{
	int rc = -1, pcr;
	char errbuf[PCAP_ERRBUF_SIZE];
	const uint8_t *packet;
	fd_set fds_r;
	int fd;
	struct timeval timeout = {0, 1};

	fd = pcap_get_selectable_fd(handle);

	if(fd == -1) {
		printf("ERROR: pcap_get_selectable_fd()\n");
		goto cleanup;
	}
	//printf("pcap_get_selectable_fd() returned: %d\n", fd);

	//printf("starting pcap capture loop\n");

	while(1) {
		int num_ready;
		FD_ZERO(&fds_r);
		FD_SET(fd, &fds_r);
		//printf("calling select()\n");
		num_ready = select(fd+1, &fds_r, NULL, NULL, &timeout);
		//printf("select() returned %d\n", num_ready);

		if(num_ready == -1) {
			perror("select()");
			goto cleanup;
		}

		if(num_ready == 0) {
			break;
		}

		int pdr = pcap_dispatch(handle, 1, process_pkt_cb, (uint8_t *)handle);
		switch(pdr) {
			case 0:
				/* no packets anyways */
				break;
			case -1:
				printf("ERROR: pcap_dispatch(), %s\n", pcap_geterr(handle));
				goto cleanup;
			case -2:
				printf("pcap_breakloop() must have been called\n");
				goto cleanup;
			default:
				//printf("pcap_dispatch() says it processed %d packets\n", pdr);
				break;
		}
	}

	//printf("ending pcap capture loop\n");

	rc = 0;
	cleanup:
	return rc;
}
	
/*****************************************************************************/
/* PACKET CRAFTING */
/*****************************************************************************/

/*  initialize an IPv4 packet

	note: assumes it envelops an empty (header only) tcp packet
*/
void init_ip_pkt(uint8_t *pkt, uint32_t saddr, uint32_t daddr)
{
	struct ip *iph = (struct ip *)pkt;

	memset(iph, 0, sizeof(*iph));
	iph->ip_hl = 5;
	iph->ip_v = 4;
	iph->ip_tos = 0;
	iph->ip_len = sizeof(struct ip) + sizeof(struct tcphdr);
	iph->ip_off = 0;
	iph->ip_ttl = 255;
	iph->ip_p = IPPROTO_TCP; /* protocol TCP */
	iph->ip_src.s_addr = htonl(saddr);
	iph->ip_dst.s_addr = htonl(daddr);
	iph->ip_sum = csum((uint16_t *)pkt, iph->ip_len/2);
}

/*  initialize a TCP SYN packet

	note: during checksum calculation, the checksum field itself is an input
	and must temporarily be zero
*/
void init_syn_pkt(uint8_t *pkt, uint32_t saddr, uint32_t daddr, uint16_t dport)
{
	csum_input_ipv4 csi;
	struct tcphdr *tcph;

	tcph = (struct tcphdr *)pkt;
	memset(tcph, 0, sizeof(*tcph));
	tcph->th_flags = TH_SYN; /* we send SYN, hope for SYN|ACK */
	tcph->th_sport = 1;
	tcph->th_dport = htons(dport);
	tcph->th_x2 = 5;
	tcph->th_off = 5;
	tcph->th_win = htons(65535); 

	memset(&csi, 0, sizeof(csi));
	csi.s_addr = htonl(saddr);
	csi.d_addr = htonl(daddr);
	csi.protocol = htons(IPPROTO_TCP);
	csi.tcp_len = htons(sizeof(struct tcphdr));
	memcpy(&csi.tcp_hdr, tcph, sizeof(struct tcphdr));

	/* see /usr/include/netinet/tcp.h */
	#if defined(__APPLE__) || defined(__MACH__)
	tcph->th_sum = csum((uint16_t *)&csi, sizeof(csum_input_ipv4) / 2);
	#else
	tcph->check = csum((uint16_t *)&csi, sizeof(csum_input_ipv4) / 2);
	#endif
}

/*****************************************************************************/
/* MAIN ACTION */
/*****************************************************************************/

int main(int argc, char *argv[])
{
	int rc=-1, i, n, sock_raw;
	uint32_t port_start, port_end, port_cur;
	char *daddr_str;
	uint32_t saddr, daddr;
	uint8_t datagram[4096];
	struct ip *iph;
	struct tcphdr *tcph;
	struct sockaddr_in sin;
	struct timeval tvstart, tvstop;
	double tvdelta;
	pcap_t *pcap_handle = NULL;

	/* addresses and ports, in host ordering */
	daddr_str = (char *)"127.0.0.1";
	saddr = ntohl(inet_addr("127.0.0.1"));
	port_start = 1;
	port_end = 65536;

	if(argc > 1)
		daddr_str = argv[1];
	if(argc > 2)
		port_start = atoi(argv[2]);
	if(argc > 3)
		port_end = atoi(argv[3]);
	
	daddr = ntohl(inet_addr(daddr_str));
	printf("scanning %s port [%d,%d)\n", daddr_str, port_start, port_end);

	/* pcap setup */
	if(pcap_setup(&pcap_handle)) {
		printf("ERROR: pcap_setup()\n");
		goto cleanup;
	}

	/* socket */
	sock_raw = socket(AF_INET, SOCK_RAW, IPPROTO_TCP);
	if(sock_raw == -1) {
		printf("ERROR: socket()\n");
		goto cleanup;
	}

	sin.sin_family = AF_INET;
	sin.sin_addr.s_addr = htonl(saddr);

	/* initialize IP part of header */
	init_ip_pkt(datagram, saddr, daddr);

	/* inform kernel we have headers, instruct not to insert new ones */
	n = 1;
	if(setsockopt(sock_raw, IPPROTO_IP, IP_HDRINCL, &n, sizeof(n)) < 0)
		printf("Warning: Cannot set HDRINCL!\terrno = %d\n",errno);
	
	gettimeofday(&tvstart, NULL);

	/* send, receive */
	for(port_cur=port_start; port_cur<port_end; port_cur+=BLAST_SZ) {
		pcap_consume(pcap_handle);

		/* send BLAST_SZ packets */
		for(i=0; i<BLAST_SZ; ++i) {
			/* packet contains addr:port */
			init_syn_pkt(datagram + sizeof(*iph), saddr, daddr, port_cur+i);
	
			/* sockaddr_in contains addr:port (shouldn't matter) */
			sin.sin_port = htons(port_cur+i);

			/* send! */
			n = sendto(sock_raw, datagram,
			  sizeof(struct ip) + sizeof(struct tcphdr), 
			  0, (struct sockaddr *)&sin, sizeof(sin));

			if(n <= 0) {
				printf("ERROR: sendto() returned %d\n", n);
				goto cleanup;
			}
		}
	}
	
	gettimeofday(&tvstop, NULL);
	tvdelta = (double)(tvstop.tv_usec - tvstart.tv_usec) / 1000000;
	tvdelta += (double)tvstop.tv_sec - tvstart.tv_sec;
	printf("scan send/recv main part took %f seconds\n", tvdelta);

	/* final receive with longer timeout, just in case */
	pcap_consume(pcap_handle);

	/* success */
	rc = 0;
	cleanup:
	if(pcap_handle) pcap_close(pcap_handle);
	return rc;
}
