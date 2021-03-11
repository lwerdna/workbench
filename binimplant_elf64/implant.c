// compile with:
// scc --arch x64 --platform linux --allow-return implant.c -o ./implant.bin
int main(int argc, char **argv)
{
	int i=0;
	for(i=0; i<argc; ++i)
		if(!strcmp(argv[i], "PING"))
			printf("\x1B[31m PONG! PONG! PONG! \x1B[0m \n");
	return 0;
}