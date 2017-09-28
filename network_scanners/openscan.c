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
#include <netinet/ip.h>
#include <netinet/tcp.h> /* struct tcphdr */

#include <net/if.h>
#include <ifaddrs.h>

/* how many write() calls to do before read() all packets in the queue

	for each write() of SYN, we queue and read() 2 packets (outgoing, and RST)
	and additionally a SYNACK if the port is open

	if blast size is too large, we overflow the read() queue and potentially
	lose SYNACK

	on my Ubuntu machine, read queue was around ~140 bare IP+TCP packets
*/
#define BLAST_SZ 16

/*****************************************************************************/
/* MISCELLANY */
/*****************************************************************************/
void dump_bytes(uint8_t *buf, int len, uintptr_t addr)
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

/* Ethernet layer is stripped at this point, we are sent IP layer

   [ transport/TCP (ports)         ]
   [ network/IP    (ip addrs)      ] <-- here
   [ link/ethernet (mac addrs)     ]
   [ phys          (pulses, waves) ]
*/
int process_pkt(uint8_t *pkt, int n)
{
	int rc = -1;

	struct ip *iph;
	struct tcphdr *tcph;
	uint16_t sport, dport;

	iph = (struct ip *)pkt;
	if(iph->ip_v != 4 || iph->ip_hl != 5 || iph->ip_p != IPPROTO_TCP) {
		printf("WARNING: malformed IP packet\n");
		goto cleanup;
	}

	tcph = (struct tcphdr *)((uint8_t *)iph + iph->ip_hl*4);
	sport = ntohs(tcph->th_sport);
	dport = ntohs(tcph->th_dport);

	if(tcph->th_flags == (TH_SYN|TH_ACK)) {
		printf("SYNACK from %d\n", sport);
		//dump_bytes(pkt, n, 0);
	}
	else {
		//printf("ignoring %d->%d with flags:%04X\n", sport, dport, tcph->th_flags);
		//dump_bytes(pkt, n, 0);
		while(0);
	}

	rc = 0;
	cleanup:
	return rc;
}

int consume_queued_pkts(int sock_raw, long usec)
{
	int rc = -1, iret, n;
	fd_set fds_read;
	struct timeval timeout = {0, usec};
	struct sockaddr saddr_tmp;
	socklen_t saddr_tmp_sz;
	uint8_t buf[4096];
	
	/* wait for packets */
	//printf("waiting for replies\n");
	while(1) {
		/* monitor the socket without blocking */
		FD_ZERO(&fds_read);
		FD_SET(sock_raw, &fds_read);
		iret = select(sock_raw+1, &fds_read, NULL, NULL, &timeout);

		if(!iret) {
			/* timeout, no packets, job's done! */
			break;
		}

		if(iret == -1) {
			printf("ERROR: select()\n");
			goto cleanup;
		}

		saddr_tmp_sz = sizeof(saddr_tmp);
		n = recvfrom(sock_raw, buf, sizeof(buf), 0, &saddr_tmp, &saddr_tmp_sz);
		process_pkt(buf, n);
	}

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
	tcph->th_sport = random();
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

	/* addresses and ports, in host ordering */
	daddr_str = (char *)"127.0.0.1";
	saddr = ntohl(inet_addr("127.0.0.1"));
	port_start = 0;
	port_end = 65536;

	if(argc > 1)
		daddr_str = argv[1];
	if(argc > 2)
		port_start = atoi(argv[2]);
	if(argc > 3)
		port_end = atoi(argv[3]);
	
	daddr = ntohl(inet_addr(daddr_str));
	printf("scanning %s port [%d,%d)\n", daddr_str, port_start, port_end);

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

		consume_queued_pkts(sock_raw, 1);
	}
	
	gettimeofday(&tvstop, NULL);
	tvdelta = (double)(tvstop.tv_usec - tvstart.tv_usec) / 1000000;
	tvdelta += (double)tvstop.tv_sec - tvstart.tv_sec;
	printf("scan send/recv main part took %f seconds\n", tvdelta);

	/* final receive with longer timeout, just in case */
	consume_queued_pkts(sock_raw, 1000000/4);

	/* success */
	rc = 0;
	cleanup:
	return rc;
}
