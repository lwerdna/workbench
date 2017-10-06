// the only differences I can tell between MacOS and FreeBSD int his context
// are the interface flags (IFF_XXX) and the address family flags (AF_XXX) but
// they mostly overlap

#include <stdio.h>
#include <string.h>
#include <unistd.h> // close()

#include <sys/ioctl.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <ifaddrs.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <net/if.h> // struct ifconf, struct ifreq
#include <net/if_dl.h> // link_ntoa()

/*****************************************************************************/
/* string lookup stuff */
/*****************************************************************************/

/* MACOS: defined in /usr/include/net/if.h */
void if_flags_to_str(int flags, char *result)
{
	strcpy(result, "");

	#if defined(__APPLE__) || defined(__MACH__)
	if(flags & IFF_UP) strcat(result, "UP,");
	if(flags & IFF_BROADCAST) strcat(result, "BROADCAST,");
	if(flags & IFF_DEBUG) strcat(result, "DEBUG,");
	if(flags & IFF_LOOPBACK) strcat(result, "LOOPBACK,");
	if(flags & IFF_POINTOPOINT) strcat(result, "POINTOPOINT,");
	if(flags & IFF_NOTRAILERS) strcat(result, "NOTRAILERS,");
	if(flags & IFF_RUNNING) strcat(result, "RUNNING,");
	if(flags & IFF_NOARP) strcat(result, "NOARP,");
	if(flags & IFF_PROMISC) strcat(result, "PROMISC,");
	if(flags & IFF_ALLMULTI) strcat(result, "ALLMULTI,");
	if(flags & IFF_OACTIVE) strcat(result, "OACTIVE,");
	if(flags & IFF_SIMPLEX) strcat(result, "SIMPLEX,");
	if(flags & IFF_LINK0) strcat(result, "LINK0,");
	if(flags & IFF_LINK1) strcat(result, "LINK1,");
	if(flags & IFF_LINK2) strcat(result, "LINK2,");
	if(flags & IFF_ALTPHYS) strcat(result, "ALTPHYS,");
	if(flags & IFF_MULTICAST) strcat(result, "MULTICAST,");
	#else
	if(flags & IFF_UP) { strcat(result, "IFF_UP,"); return; }
	if(flags & IFF_BROADCAST) { strcat(result, "IFF_BROADCAST,"); return; }
	if(flags & IFF_DEBUG) { strcat(result, "IFF_DEBUG,"); return; }
	if(flags & IFF_LOOPBACK) { strcat(result, "IFF_LOOPBACK,"); return; }
	if(flags & IFF_POINTOPOINT) { strcat(result, "IFF_POINTOPOINT,"); return; }
	if(flags & IFF_SMART) { strcat(result, "IFF_SMART,"); return; }
	if(flags & IFF_DRV_RUNNING) { strcat(result, "IFF_DRV_RUNNING,"); return; }
	if(flags & IFF_NOARP) { strcat(result, "IFF_NOARP,"); return; }
	if(flags & IFF_PROMISC) { strcat(result, "IFF_PROMISC,"); return; }
	if(flags & IFF_ALLMULTI) { strcat(result, "IFF_ALLMULTI,"); return; }
	if(flags & IFF_DRV_OACTIVE) { strcat(result, "IFF_DRV_OACTIVE,"); return; }
	if(flags & IFF_SIMPLEX) { strcat(result, "IFF_SIMPLEX,"); return; }
	if(flags & IFF_LINK0) { strcat(result, "IFF_LINK0,"); return; }
	if(flags & IFF_LINK1) { strcat(result, "IFF_LINK1,"); return; }
	if(flags & IFF_LINK2) { strcat(result, "IFF_LINK2,"); return; }
	if(flags & IFF_ALTPHYS) { strcat(result, "IFF_ALTPHYS,"); return; }
	if(flags & IFF_MULTICAST) { strcat(result, "IFF_MULTICAST,"); return; }
	if(flags & IFF_CANTCONFIG) { strcat(result, "IFF_CANTCONFIG,"); return; }
	if(flags & IFF_PPROMISC) { strcat(result, "IFF_PPROMISC,"); return; }
	if(flags & IFF_MONITOR) { strcat(result, "IFF_MONITOR,"); return; }
	if(flags & IFF_STATICARP) { strcat(result, "IFF_STATICARP,"); return; }
	if(flags & IFF_DYING) { strcat(result, "IFF_DYING,"); return; }
	if(flags & IFF_RENAMING) { strcat(result, "IFF_RENAMING,"); return; }
	#endif

	if(!result[0]) {
		if(flags)
			strcat(result, "ERROR");
		else
			strcat(result, "none");
	}
	else {
		int n = strlen(result);
		if(result[n-1] == ',')
			result[n-1] = '\0';
	}
}

/* MACOS: defined in /usr/include/sys/socket.h */
void family_to_str(int family, char *result)
{
	strcpy(result, "");

	#if defined(__APPLE__) || defined(__MACH__)
	if(family == AF_UNSPEC) { strcat(result, "AF_UNSPEC"); return; }
	if(family == AF_UNIX) { strcat(result, "AF_UNIX"); return; }
	if(family == AF_LOCAL) { strcat(result, "AF_LOCAL"); return; }
	if(family == AF_INET) { strcat(result, "AF_INET"); return; }
	if(family == AF_IMPLINK) { strcat(result, "AF_IMPLINK"); return; }
	if(family == AF_PUP) { strcat(result, "AF_PUP"); return; }
	if(family == AF_CHAOS) { strcat(result, "AF_CHAOS"); return; }
	if(family == AF_NS) { strcat(result, "AF_NS"); return; }
	if(family == AF_ISO) { strcat(result, "AF_ISO"); return; }
	if(family == AF_OSI) { strcat(result, "AF_OSI"); return; }
	if(family == AF_ECMA) { strcat(result, "AF_ECMA"); return; }
	if(family == AF_DATAKIT) { strcat(result, "AF_DATAKIT"); return; }
	if(family == AF_CCITT) { strcat(result, "AF_CCITT"); return; }
	if(family == AF_SNA) { strcat(result, "AF_SNA"); return; }
	if(family == AF_DECnet) { strcat(result, "AF_DECnet"); return; }
	if(family == AF_DLI) { strcat(result, "AF_DLI"); return; }
	if(family == AF_LAT) { strcat(result, "AF_LAT"); return; }
	if(family == AF_HYLINK) { strcat(result, "AF_HYLINK"); return; }
	if(family == AF_APPLETALK) { strcat(result, "AF_APPLETALK"); return; }
	if(family == AF_ROUTE) { strcat(result, "AF_ROUTE"); return; }
	if(family == AF_LINK) { strcat(result, "AF_LINK"); return; }
	if(family == pseudo_AF_XTP) { strcat(result, "pseudo_AF_XTP"); return; }
	if(family == AF_COIP) { strcat(result, "AF_COIP"); return; }
	if(family == AF_CNT) { strcat(result, "AF_CNT"); return; }
	if(family == pseudo_AF_RTIP) { strcat(result, "pseudo_AF_RTIP"); return; }
	if(family == AF_IPX) { strcat(result, "AF_IPX"); return; }
	if(family == AF_SIP) { strcat(result, "AF_SIP"); return; }
	if(family == pseudo_AF_PIP) { strcat(result, "pseudo_AF_PIP"); return; }
	if(family == AF_NDRV) { strcat(result, "AF_NDRV"); return; }
	if(family == AF_ISDN) { strcat(result, "AF_ISDN"); return; }
	if(family == AF_E164) { strcat(result, "AF_E164"); return; }
	if(family == pseudo_AF_KEY) { strcat(result, "pseudo_AF_KEY"); return; }
	if(family == AF_INET6) { strcat(result, "AF_INET6"); return; }
	if(family == AF_NATM) { strcat(result, "AF_NATM"); return; }
	if(family == AF_SYSTEM) { strcat(result, "AF_SYSTEM"); return; }
	if(family == AF_NETBIOS) { strcat(result, "AF_NETBIOS"); return; }
	if(family == AF_PPP) { strcat(result, "AF_PPP"); return; }
	if(family == pseudo_AF_HDRCMPLT) { strcat(result, "pseudo_AF_HDRCMPLT"); return; }
	if(family == AF_RESERVED_36) { strcat(result, "AF_RESERVED_36"); return; }
	if(family == AF_IEEE80211) { strcat(result, "AF_IEEE80211"); return; }
	if(family == AF_UTUN) { strcat(result, "AF_UTUN"); return; }
	#else
	if(family == AF_UNIX) { strcat(result, "AF_UNIX"); return; }
	if(family == AF_INET) { strcat(result, "AF_INET"); return; }
	if(family == AF_IMPLINK) { strcat(result, "AF_IMPLINK"); return; }
	if(family == AF_PUP) { strcat(result, "AF_PUP"); return; }
	if(family == AF_CHAOS) { strcat(result, "AF_CHAOS"); return; }
	if(family == AF_NETBIOS) { strcat(result, "AF_NETBIOS"); return; }
	if(family == AF_ISO) { strcat(result, "AF_ISO"); return; }
	if(family == AF_OSI) { strcat(result, "AF_OSI"); return; }
	if(family == AF_ECMA) { strcat(result, "AF_ECMA"); return; }
	if(family == AF_DATAKIT) { strcat(result, "AF_DATAKIT"); return; }
	if(family == AF_CCITT) { strcat(result, "AF_CCITT"); return; }
	if(family == AF_SNA) { strcat(result, "AF_SNA"); return; }
	if(family == AF_DECnet) { strcat(result, "AF_DECnet"); return; }
	if(family == AF_DLI) { strcat(result, "AF_DLI"); return; }
	if(family == AF_LAT) { strcat(result, "AF_LAT"); return; }
	if(family == AF_HYLINK) { strcat(result, "AF_HYLINK"); return; }
	if(family == AF_APPLETALK) { strcat(result, "AF_APPLETALK"); return; }
	if(family == AF_ROUTE) { strcat(result, "AF_ROUTE"); return; }
	if(family == AF_LINK) { strcat(result, "AF_LINK"); return; }
	if(family == pseudo_AF_XTP) { strcat(result, "pseudo_AF_XTP"); return; }
	if(family == AF_COIP) { strcat(result, "AF_COIP"); return; }
	if(family == AF_CNT) { strcat(result, "AF_CNT"); return; }
	if(family == pseudo_AF_RTIP) { strcat(result, "pseudo_AF_RTIP"); return; }
	if(family == AF_IPX) { strcat(result, "AF_IPX"); return; }
	if(family == AF_SIP) { strcat(result, "AF_SIP"); return; }
	if(family == pseudo_AF_PIP) { strcat(result, "pseudo_AF_PIP"); return; }
	if(family == AF_ISDN) { strcat(result, "AF_ISDN"); return; }
	if(family == AF_E164) { strcat(result, "AF_E164"); return; }
	if(family == pseudo_AF_KEY) { strcat(result, "pseudo_AF_KEY"); return; }
	if(family == AF_INET6) { strcat(result, "AF_INET6"); return; }
	if(family == AF_NATM) { strcat(result, "AF_NATM"); return; }
	if(family == AF_ATM) { strcat(result, "AF_ATM"); return; }
	if(family == pseudo_AF_HDRCMPLT) { strcat(result, "pseudo_AF_HDRCMPLT"); return; }
	if(family == AF_NETGRAPH) { strcat(result, "AF_NETGRAPH"); return; }
	if(family == AF_SLOW) { strcat(result, "AF_SLOW"); return; }
	if(family == AF_SCLUSTER) { strcat(result, "AF_SCLUSTER"); return; }
	if(family == AF_ARP) { strcat(result, "AF_ARP"); return; }
	if(family == AF_BLUETOOTH) { strcat(result, "AF_BLUETOOTH"); return; }
	if(family == AF_IEEE80211) { strcat(result, "AF_IEEE80211"); return; }
	if(family == AF_INET_SDP) { strcat(result, "AF_INET_SDP"); return; }
	if(family == AF_INET6_SDP) { strcat(result, "AF_INET6_SDP"); return; }
	#endif

	strcat(result, "ERROR");
}

void addr_to_str(int family, void *addr, char *result)
{
	/* parse the various structs depending on address family

		struct sockaddr		// sys/socket.h
		struct sockaddr_in	// netinet/in.h
		struct sockaddr_in6	// netinet6/in6.h
		struct sockaddr_dl	// net/if_dl.h
	*/

	char buf[256];
	result[0] = '\0';

	if(family == AF_INET) {
		struct sockaddr_in *a = (void *)addr;
		inet_ntop(AF_INET, &(a->sin_addr), result, 256);
		//strcpy(result, inet_ntoa(a->sin_addr));
	}
	else if(family == AF_INET6) {	
		struct sockaddr_in6 *a = (void *)addr;
		inet_ntop(AF_INET6, &(a->sin6_addr), result, 256);
	}
	else if(family == AF_LINK) {
		struct sockaddr_dl *a = (void *)addr;
		strcpy(result, link_ntoa(a));
	}
	else {
		strcpy(result, "(unknown)");
	}
}

/*****************************************************************************/
/* the two interface enumerating methods */
/*****************************************************************************/

/*	ioctl's defined in sys/sockio.h
	structs ifconf, ifreq defined in net/if.h

	ioctl() with ifconf to get array of ifreq
*/
void method_ioctls(void)
{
    int i;
    uint8_t buf[4096] = {0};

	int sock = socket(AF_INET, SOCK_DGRAM, 0);
	if(sock < 0)
		{ perror("socket()"); goto cleanup; }

	/* use ifconf as in/out to get array of ifreq that has:
		.ifr_name populated
		.ifr_addr populated (among the other union members)
	*/
	memset(buf, 0, sizeof(buf));
	struct ifconf ifc = { sizeof(buf), (char *)buf };
    if(ioctl(sock, SIOCGIFCONF, &ifc) != 0)
		{ perror("ioctl()"); goto cleanup; }

	printf("SIOCGIFCONF returned 0x%X bytes\n", ifc.ifc_len);

	uint8_t *cursor = buf;
	while(cursor < (buf + ifc.ifc_len)) {
		char tmp[64];
		struct ifreq *ifr = (struct ifreq *)cursor;
		struct sockaddr *saddr = &(ifr->ifr_addr);
		uint16_t family = saddr->sa_family;
	
		printf("           name: %s\n", ifr->ifr_name);
		printf("sockaddr length: %d\n", saddr->sa_len);
		
		family_to_str(family, tmp);
		printf("         family: %d (%s)\n", family, tmp);
		addr_to_str(family, saddr, tmp);
		printf("        address: %s\n", tmp);

		/* here you can use other SIOCXXX calls like SIOCIFFLAGS to query the
			interface flags */

		cursor += IFNAMSIZ; /* skip over .ifr_name */
		cursor += saddr->sa_len; /* skip over .ifru_addr */
		printf("\n");
	}

	cleanup:
	if(sock != -1)
		close(sock);
}

/* this uses the platform specific API's

	on Windows: GetAdaptersInfo() and GetAdaptersAddresses()

	on Linux: getifaddrs() to get linked list of struct ifaddrs
*/
int method_getifaddrs(void)
{
	int rc = -1;
	struct ifaddrs *ifap, *ifap_cur;
	char buf[1024];

	if(0 != getifaddrs(&ifap))
		{ printf("ERROR: getifaddrs()\n"); goto cleanup; }

	ifap_cur = ifap;
	while(ifap_cur) {
		char tmp[256];

		if_flags_to_str(ifap_cur->ifa_flags, tmp);
		printf("%s: flags=%d<%s>\n",
		  ifap_cur->ifa_name, ifap_cur->ifa_flags, tmp);

		if(ifap_cur->ifa_addr) {
			sa_family_t family = ifap_cur->ifa_addr->sa_family;

			family_to_str(family, tmp);
			printf("   family %d(%s)\n", family, tmp);

			addr_to_str(family, ifap_cur->ifa_addr, tmp);
			printf("  address %s\n", tmp);

			if(ifap_cur->ifa_netmask) {
				addr_to_str(family, ifap_cur->ifa_netmask, tmp);
				printf("  netmask %s\n", tmp);
			}
			if(ifap_cur->ifa_dstaddr) {
				addr_to_str(family, ifap_cur->ifa_dstaddr, tmp);
				printf("  dstaddr %s\n", tmp);
			}
	
			ifap_cur = ifap_cur->ifa_next;
		}
	}

	rc = 0;
	cleanup:
	if(ifap)
		freeifaddrs(ifap);
	return rc;
}

/*****************************************************************************/
/* main */
/*****************************************************************************/

int main(int ac, char **av)
{
	method_ioctls();

	printf("--------\n");

	method_getifaddrs();

	return 0;
}
