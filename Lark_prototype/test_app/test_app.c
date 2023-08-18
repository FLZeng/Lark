#include <stdio.h>
#include <fcntl.h>
#include <stdlib.h>
#include <fcntl.h>
#include <signal.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <signal.h>
#include <time.h>

int alloc_size;
char * rbuf;
char * wbuf;
//char rbuf[100];
//char wbuf[100];

void segv_handler(int signal_number)
{
        printf("handle SIGSEGV!\n");
}


char *readline(char *s, int size) {
	fgets(s, size, stdin);
	char* p = strchr(s,'\n');
	if (NULL != p) {
		*p = '\0';
	}
	return s;
}

int micro_benchmark(int fd, int num, int type) {
	if (type=0) {
		for (int i = 0; i < num; ++i) {
			write(fd, wbuf, alloc_size);
		}
	} else {
		for (int i = 0; i < num; ++i) {
			read(fd, rbuf, alloc_size);
		}
	}
}

int main() {
	char ch;
	char cmd[20];
	int fd;
	int ret;
	int num;
	int test_type;
	int begin, end;
	//int alloc_size;
	struct sigaction sa;

	//alloc_size = 100;
	alloc_size = getpagesize();
	printf("page size: %d\n", alloc_size);

        fd = open("/dev/zero", O_RDONLY);
        rbuf = mmap(NULL, alloc_size, PROT_READ | PROT_WRITE, MAP_PRIVATE, fd, 0);
        wbuf = mmap(NULL, alloc_size, PROT_READ | PROT_WRITE, MAP_PRIVATE, fd, 0);
        close(fd);

	//rbuf = (char *) malloc(alloc_size);
	//wbuf = (char *) malloc(alloc_size);

	strcpy(wbuf, "Hello from user!");
	printf("rbuf addr: %p\n", rbuf);
	printf("wbuf addr: %p\n", wbuf);
	

	fd = open("/dev/cdd5", O_RDWR);
	if (fd < 0) {
		printf("open failed!\n");
		return -1;
	}
	printf("open successed fd = %d\n", fd);
	
	printf("starting to test /dev/cdd...\n");

	while (1) {
		printf("waiting for cmd [r/w/ro/wo/rw/rwn/t/q]: ");
		
		readline(cmd, 20);

		if (strcmp(cmd, "q") == 0) {
			break;
		} else if (strcmp(cmd, "w") == 0) {
			read(fd, rbuf, alloc_size);
			printf("kernel copy to user\n");
		} else if (strcmp(cmd, "r") == 0) {
			write(fd, wbuf, alloc_size);
			printf("kernel copy from user\n");
		} else if (strcmp(cmd, "rwn") == 0) {
			ret = mprotect(rbuf, alloc_size, PROT_NONE);
			printf("mprotect set rbuf PROT_NONE, ret = %d\n", ret);
			ret = mprotect(wbuf, alloc_size, PROT_NONE);
			printf("mprotect set wbuf PROT_NONE, ret = %d\n", ret);
		} else if (strcmp(cmd, "ro") == 0) {
			ret = mprotect(rbuf, alloc_size, PROT_READ);
			printf("mprotect set rbuf PROT_READ, ret = %d\n", ret);
			ret = mprotect(wbuf, alloc_size, PROT_READ);
			printf("mprotect set wbuf PROT_READ, ret = %d\n", ret);
		} else if (strcmp(cmd, "wo") == 0) {
			ret = mprotect(rbuf, alloc_size, PROT_WRITE);
			printf("mprotect set rbuf PROT_WRITE, ret = %d\n", ret);
			ret = mprotect(wbuf, alloc_size, PROT_WRITE);
			printf("mprotect set wbuf PROT_WRITE, ret = %d\n", ret);
		} else if (strcmp(cmd, "rw") == 0) {
			ret = mprotect(rbuf, alloc_size, PROT_READ | PROT_WRITE);
			printf("mprotect set rbuf PROT_READ | PROT_WRITE, ret = %d\n", ret);
			ret = mprotect(wbuf, alloc_size, PROT_READ | PROT_WRITE);
			printf("mprotect set wbuf PROT_READ | PROT_WRITE, ret = %d\n", ret);
		} else if (strcmp(cmd, "t") == 0) {
			printf("\ntest rounds: ");
			scanf("%d", &num);
			printf("test type [0-read, 1-write]: ");
			scanf("%d", &test_type);
			begin = clock();
			micro_benchmark(fd, num, test_type);
			end = clock();
			printf("test rounds: %d, time = %.6fs\n\n", num, (double)(end - begin) / CLOCKS_PER_SEC);
			getchar();
		}
	}
	
	close(fd);

	return 0;
}
