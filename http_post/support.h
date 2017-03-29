#include <stdio.h>
#include <stdarg.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>

#include <unistd.h>
#include <signal.h> // kill()
#include <errno.h>
#include <netdb.h>
#include <stdio.h> // for STDIN_FILENO, etc.
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h> // for wait(), waitpid()
#include <arpa/inet.h>
#include <netinet/in.h>
#include <netinet/ip.h>

#define B64_MAX(N) ((N+2)/3)*4+1

void
base64_encode(unsigned char *data, int len, char *out);
unsigned char *
base64_decode(const unsigned char *src, size_t len);

void
base64_encode(unsigned char *data, int len, char *out)
{
    char *lookup = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    int mod_table[] = {0, 2, 1};
    int out_len = 4 * ((len + 2) / 3);
    int i, j;

    for(i=0, j=0; i<len;) {
        uint32_t octet_a = i < len ? (unsigned char)data[i++] : 0;
        uint32_t octet_b = i < len ? (unsigned char)data[i++] : 0;
        uint32_t octet_c = i < len ? (unsigned char)data[i++] : 0;

        uint32_t triple = (octet_a << 0x10) + (octet_b << 0x08) + octet_c;

        out[j++] = lookup[(triple >> 3 * 6) & 0x3F];
        out[j++] = lookup[(triple >> 2 * 6) & 0x3F];
        out[j++] = lookup[(triple >> 1 * 6) & 0x3F];
        out[j++] = lookup[(triple >> 0 * 6) & 0x3F];
    }

    for(i=0; i<mod_table[len % 3]; i++)
        out[out_len - 1 - i] = '=';

    out[out_len] = '\0';
}

/* from Jouni Malinen */
unsigned char *
base64_decode(const unsigned char *src, size_t len)
{
	unsigned char dtable[256], *out, *pos, in[4], block[4], tmp;
	size_t i, count, olen;

	const unsigned char base64_table[64] =
		"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

	memset(dtable, 0x80, 256);
	for (i = 0; i < sizeof(base64_table); i++)
		dtable[base64_table[i]] = i;
	dtable['='] = 0;

	count = 0;
	for (i = 0; i < len; i++) {
		if (dtable[src[i]] != 0x80)
			count++;
	}

	if (count % 4)
		return NULL;

	olen = count / 4 * 3;
	pos = out = malloc(count);
	if (out == NULL)
		return NULL;

	count = 0;
	for (i = 0; i < len; i++) {
		tmp = dtable[src[i]];
		if (tmp == 0x80)
			continue;

		in[count] = src[i];
		block[count] = tmp;
		count++;
		if (count == 4) {
			*pos++ = (block[0] << 2) | (block[1] >> 4);
			*pos++ = (block[1] << 4) | (block[2] >> 2);
			*pos++ = (block[2] << 6) | block[3];
			count = 0;
		}
	}

	if (pos > out) {
		if (in[2] == '=')
			pos -= 2;
		else if (in[3] == '=')
			pos--;
	}

	return out;
}

static int network_initialized = 0;

int
network_init(void)
{
    int rc = -1;

    printf("%s()\n", __func__);

    if(network_initialized) {
        printf("network already initialized! redundant calls?\n");
        rc = 0;
        goto cleanup;
    }

    network_initialized = 1;
    rc = 0;
    cleanup:
    return rc;
}

int
network_release(void)
{
    network_initialized = 0;
    return 0;
}

int
network_resolve_target(char *addr, unsigned int port, struct sockaddr_in *out)
{
    int rc = -1;
    int is_ip = 0;
    int addr_len = strlen(addr);

    // initialize
    memset((char *)out, 0, sizeof(*out));
    out->sin_family = AF_INET;
    out->sin_port = htons(port);

    // educated guess whether incoming string is ip address or hostname
    if(addr_len >= (4+3) && addr_len <= (12+3)) {
        int num_dots=0, num_digs=0, num_other=0, i;

        for(i=0; i<addr_len; ++i) {
            switch(addr[i]) {
                case '.':
                    num_dots++;
                    break;
                case '0':
                case '1':
                case '2':
                case '3':
                case '4':
                case '5':
                case '6':
                case '7':
                case '8':
                case '9':
                    num_digs++;
                    break;
                default:
                    num_other++;
            }
        }

        if(num_other==0 && num_dots==3 && (num_digs>=4 && num_digs<=12)) {
            is_ip = 1;
        }
    }

    if(is_ip) {
        unsigned long uladdr;

        // simple ascii -> dword conversion
        printf("%s() performs ascii->dword on %s\n", __func__, addr);

        if(0 == inet_aton(addr, &(out->sin_addr))) {
            printf("ERROR: inet_aton()\n");
            goto cleanup;
        }
    }
    else {
        struct hostent *hentry;
        // gethostbyname() to populate hostent
        printf("%s() resolves %s...\n", __func__, addr);
        hentry = gethostbyname(addr);
        if(!hentry) {
            printf("ERROR: gethostbyname(%s)\n", addr);
            goto cleanup;
        }
        else {
            // hostent -> sockaddr_in
            memcpy((void *)&(out->sin_addr), hentry->h_addr_list[0], hentry->h_length);
        }
    }

    rc = 0;
    cleanup:
    return rc;
}

void
network_saddr_tostr(struct sockaddr_in *addr, char *out)
{
    int rc = -1;
	uint8_t *oct = (void *)&(addr->sin_addr.s_addr);

	sprintf(out, "%d.%d.%d.%d:%d", oct[3], oct[2], oct[1], oct[0],
	  ntohs(addr->sin_port));
}


int network_connect(struct sockaddr_in *addr_in, int *out)
{
	int rc = -1;
	int sock_fd;
	/* internet address is "subclass" of address */
	const struct sockaddr *addr = (void *)addr_in;

	sock_fd = (int)socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
	if(sock_fd < 0) {
		printf("ERROR: socket()/WSASocket()\n");
        goto cleanup;
	}

	rc = connect(sock_fd, addr, sizeof(*addr));

	if(rc) {
		printf("ERROR: connect()\n");
        goto cleanup;
	}

	*out = sock_fd;
	rc = 0;
	cleanup:
	return rc;
}
