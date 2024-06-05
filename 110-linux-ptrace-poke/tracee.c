#include <stdio.h>
#include <termios.h>
#include <unistd.h>

// https://stackoverflow.com/questions/10575478/wait-for-user-input-in-c
int mygetch(void) 
{
	int ch;
	struct termios oldt, newt;

	tcgetattr(STDIN_FILENO, &oldt);
	newt = oldt;
	newt.c_lflag &= ~(ICANON | ECHO);
	tcsetattr(STDIN_FILENO, TCSANOW, &newt);
	ch = getchar();
	tcsetattr(STDIN_FILENO, TCSANOW, &oldt);

	return ch;
}

int main(int ac, char **av)
{
	pid_t pid;
	long foo = 0xDEADBEEFCAFEBABE;

	pid = getpid();

	while (1) {
		printf("pid=%d &foo=%p foo=%lx\n", pid, &foo, foo);
		printf("Press any key...\n");
		mygetch();
	}

	return 0;
}

