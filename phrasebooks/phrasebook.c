#include <stdio.h>
#include <stdint.h>
#include <string.h>

#include <stdlib.h>
#include <time.h>

// preprocessor pragma stuff
#ifdef DEBUG
static int g_debug = 1;
#pragma message "DEBUG MESSAGES ON!"
#else
static int g_debug = 0;
#pragma message "DEBUG MESSAGES OFF!"
#endif

#define eprintf(...) fprintf (stderr, __VA_ARGS__)

/* format strings, see inttypes.h
%zu      size_t
%lu      unsigned long
PRIdPTR  intptr_t       "PRInt d(ecimal) PoinTeR", usually "llu"
PRIx8    uint8_t        "PRInt (he)x 8-bit", usually "x" on linux
PRIx64   uint64_t       "PRInt (he)x 64-bit", usually "llx"
SCNx8    uint8_t        "hhx" because sscanf
         __uint128_t    "0x%llX%llX", (uint64_t)(result>>64), (uint64_t)result
*/

/* read input hex number */
#include <stdlib.h>
uint32_t input = strtoul(av[1], NULL, 16);

void random_numbers(void)
{
	int i;

	srand(time(NULL)); // randomize seed

	for(i=0; i<20; ++i)
		printf("random number [0,9]: %d\n", rand() % 10);
}

void os_detection(void)
{
	#ifdef _WIN32
	printf("_WIN32 defined (Windows 32-bit and 64-bit)\n");
	#endif
	#ifdef _WIN64
	printf("_WIN64 defined (Windows 64-bit)\n");
	#endif
	#if defined(unix) || defined(__unix__) || defined(__unix)
	printf("unix || __unix__ || __unix (Unix (Linux, *BSD, MacOS)\n");
	#endif
	#if defined(__APPLE__) || defined(__MACH__)
	printf("__APPLE__ || __MACH__ (MacOS)\n");
	#endif
	#if defined(__linux__) || defined(linux) || defined(__linux)
	printf("__linux__ || linux || __linux");
	#endif
	#ifdef __FreeBSD__
	printf("__FreeBSD__ defined (FreeBSD)\n");
	#endif
}

void dump_bytes(uint8_t *buf, int len, uint32_t addr)
{
	int i, j;
	char ascii[17];
	for(i=0; i<len; addr+=16) {
		strcpy(ascii, "................");
		printf("%08X: ", addr);
		for(j=0; j<16; j++, i++) {
			if(i < len) {
				printf("%02X ", buf[i]);
				if(buf[i]>=' ' && buf[i]<'~')
					ascii[j] = buf[i];
			}
			else {
				printf("   ");
				ascii[j] = ' ';
			}
		}
		printf(" %s\n", ascii);
	}
}


void printBits(uint32_t foo, int width)
{
	int i;
	char buf[33];
	buf[32] = '\0';
	for(i=0; i<width; ++i)
		buf[31-i] = (foo & (1<<i)) ? '1':'0';
	printf("%s", buf+(32-i));
}

void hexdump(uint8_t *data, size_t size, uintptr_t addr) 
{
	char ascii[17];
	for (int i = 0; i < size; ++i) {
		if (i % 16 == 0)
			printf("%" PRIxPTR ": ", addr+i); // print address
		printf("%02X ", ((unsigned char*)data)[i]); // print byte
		ascii[i % 16] = (data[i]>=' ' && data[i]<='~') ? (char)data[i] : '.'; // fill ascii
		if (i==size-1 || (i+1) % 16 == 0) {
			for (int j=15-(i%16); j>0; --j) // advance to ascii
				printf("   ");
			ascii[i%16 + 1] = '\0';
			printf(" %s\n", ascii); // print ascii
		}
	}
}

#include <time.h> /* clock(), CLOCKS_PER_SEC */
void time_using_process_clock()
{
	clock_t cstart, cstop;
	double cdelta;

	cstart = clock();
	//spin();
	cstop = clock();
		
	cdelta = (double)(cstop-cstart) / CLOCKS_PER_SEC;
	printf("according to clock() method: %f\n", cdelta);
}

#include <sys/time.h> /* struct timeval, gettimeofday() */
void time_using_timeval()
{
	struct timeval tvstart, tvstop;
	double tvdelta;

	gettimeofday(&tvstart, NULL);
	//spin();
	gettimeofday(&tvstop, NULL);
		
	tvdelta = (double)(tvstop.tv_usec - tvstart.tv_usec) / 1000000;
	tvdelta += (double)tvstop.tv_sec - tvstart.tv_sec;
	printf("according to timeval method: %f\n", tvdelta);	
}

uint16_t bswap16(uint16_t x)
{
	return ((x&0xFF)<<8) | (x>>8);
}

uint32_t bswap32(uint32_t x)
{
	return ((x&0xFF)<<24) |
		((x&0xFF00)<<8) |
		((x&0xFF0000)>>8) |
		((x&0xFF000000)>>24);
}

uint64_t bswap64(uint64_t x)
{
	return ((x&0xFF)<<56) |
		((x&0xFF00)<<40) |
		((x&0xFF0000)<<24) |
		((x&0xFF000000)<<8) |
		((x&0xFF00000000)>>8) |
		((x&0xFF0000000000)>>24) |
		((x&0xFF000000000000)>>40) |
		((x&0xFF00000000000000)>>56);
}

void get_iso8601_time()
{
	time_t seconds = time(NULL);

	struct tm now;
	memcpy(&now, localtime(&seconds), sizeof(struct tm));

	char buf[64];
	strftime(buf, 64, "%F", &now);

	printf("%s\n", buf);
}

/* alarming! */
#include <unistd.h>
volatile sig_atomic_t show_status = false;
void cb_alarm(int sig) {
	show_status = true;
}

signal(SIGALRM, cb_alarm);
alarm(8);

if(show_status) {
	printf("current instruction word: %08X\n", insword);
	show_status = false;
	alarm(8);
}

/* ctrl+c signal */
volatile sig_atomic_t breakout = false;
void cb_int(int sig) {
	breakout = true;
}

signal(SIGINT, cb_int);

/* main */
int main(int ac, char **av)
{
	printf("is8601 time: ");
	get_iso8601_time();	

	printf("OS detection: ");
	os_detection();

	random_numbers();
}
