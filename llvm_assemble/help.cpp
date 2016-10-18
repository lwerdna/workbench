#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

void dump_bytes(unsigned char *buf, int len, uintptr_t addr)
{
    int i, j;
    char ascii[17];

    //printf("dumping at 0x%08X (len:0%X)\n", buf, len);

    i = 0;
    while(i < len) {
        printf("%08" PRIxPTR ": ", addr);
       
        /* we write a 16-<space> line everytime */ 
        for(j=0; j<16; ++j) {

            /* if byte to consume, consume it */
            if(i < len) {
                printf("%02X ", buf[i]);
    
                /* ascii part too */        
                if((buf[i] >= ' ') && (buf[i] < '~')) {
                    ascii[j] = buf[i];
                }
                else {
                    ascii[j] = '.';
                }
            }
            /* otherwise, fill in blanks */
            else {
                printf("   ");
                ascii[j] = ' ';
            }

            i++;
        }
        ascii[sizeof(ascii)-1] = '\0';

        /* extra space important here! the resulting double space delimits 
            the byte list from the ascii interpretation */
        printf(" %s\n", ascii);
        addr += 16;
    }
}

