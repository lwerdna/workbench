#include <stdio.h>
#include <termios.h>
#include <unistd.h>
#include <pthread.h>

void *threadfunc(void *arg)
{
	int thr_id = *(int *)arg;
	pid_t proc_id = getpid();

	while (1)
	{
		printf("I'm a thread id=%d in process pid=%d\n", thr_id, proc_id);
		sleep(1);
	}
}

int main(int ac, char **av)
{
	#define NTHREADS 8

	pthread_t threads[NTHREADS];

	printf("Creating threads...\n");
	for (int i=0; i<NTHREADS; ++i)
	{
		pthread_create(&threads[i], NULL, threadfunc, &i);
	}

	printf("Waiting on threads...\n");
	for (int i=0; i<NTHREADS; ++i)
	{
		pthread_join(threads[i], NULL);
	}

	return 0;
}

