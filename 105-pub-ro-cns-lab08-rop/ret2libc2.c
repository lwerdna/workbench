#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

void vuln() {
	char buf[128];
	read(99, buf, 256);
}

int main() {
	vuln();
	write(1, "Hello, World\n", 13);
}
