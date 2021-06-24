#include <stdio.h>

typedef struct foo_ {
    int a;
    int b;
} foo;

int main(int argc, char **argv)
{
    struct foo_ hehe;
    hehe.a = 5;
    hehe.b = 6;
	printf("Hello, world! %d", hehe.a);

}
