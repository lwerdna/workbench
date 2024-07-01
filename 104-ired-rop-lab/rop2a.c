// rop1a but:
// input is from stdin instead of command line argument
// memcpy() instead of strcpy()

#include <stdio.h>
#include <string.h>

#include <unistd.h>

void rop1() 
{
    printf("ROP 1!\n");
}

void rop2() {
    printf("ROP 2!\n");
}

void rop3() {
    printf("ROP 3!\n");
}

void vulnerable(char* string, int length) 
{
    char buffer[100];
    memcpy(buffer, string, length);
}

int main(int argc, char** argv) 
{
	char buffer[1024];
	int len = read(STDIN_FILENO, buffer, 1024);
	printf("read() returned 0x%X\n", len);
    vulnerable(buffer, len);
    return 0;
}
