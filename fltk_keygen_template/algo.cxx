#include <string.h>

void keyAlgo(const char *name, char *serial)
{
    int n = strlen(name);
    int j = 0;

    for(int i=0; i<n; ++i) {
        serial[j] = serial[j+1] = name[i];
        serial[j+2] = '\0';
        j+=2;
    }


}
