#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

#include <string>
#include <vector>
#include <numeric>
using namespace std;

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

int readTextFileToVector(string path, vector<string> &result, string &error)
{
	int rc = -1;
	size_t len;
	FILE *fp = NULL;
	char *line = NULL;

	fp = fopen(path.c_str(), "r");
	if(!fp) {
		error = "fopen()";
		goto cleanup;
	}
	
	result.clear();
	while(getline(&line, &len, fp) != -1) {
		result.push_back(line);
		if(line) {
			free(line);
			line = NULL;
		}
    }

	rc = 0;
	cleanup:
	if(line) free(line);
	if(fp) fclose(fp);
	return rc;

}

int readTextFileToString(string path, string &result, string &error)
{
	int rc = -1;

	vector<string> vec;

	if(readTextFileToVector(path.c_str(), vec, error))
		goto cleanup;

   	result = accumulate(vec.begin(), vec.end(), string(""));

	rc = 0;
	cleanup:
	return rc;
}

