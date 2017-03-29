#include "support.h"

#define FILE_NAME "sent.pdf"
#define FILE_DATA "Hello, I am the contents of a pdf file."

int main(int ac, char **av)
{
	char headers[1024];
	char request[2048];
	char *b64file;
	int sock_fd;
	struct sockaddr_in addr;

	/* base64 encode the file */
	b64file = malloc(B64_MAX(strlen(FILE_DATA)));
	base64_encode((uint8_t *)FILE_DATA, strlen(FILE_DATA), b64file);

	/* create the front of the request (the back is the b64 data) */
	strcat(request, "fname=" FILE_NAME);
	strcat(request, "&fpath=%%2Ftmp");
	strcat(request, "&fdata=");

	/* make headers */
	strcat(headers, "POST /script.py HTTP/1.1\x0d\x0a");
	strcat(headers, "Host: localhost:8080\x0d\x0a");
	strcat(headers, "Connection: keep-alive\x0d\x0a");
	sprintf(headers + strlen(headers), "Content-Length: %lu\x0d\x0a", 
		strlen(request) + strlen(b64file));
	strcat(headers, "Origin: http://localhost:8080\x0d\x0a");
	strcat(headers, "User-Agent: Mozilla/5.0 (Macintosh; Intel Mac OS X 10_12_2) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/56.0.2924.87 Safari/537.36\x0d\x0a");
	strcat(headers, "Content-type: application/x-www-form-urlencoded\x0d\x0a");
	strcat(headers, "Accept: */*\x0d\x0a");
	strcat(headers, "Referer: http://localhost:8080/\x0d\x0a");
	strcat(headers, "Accept-Encoding: gzip, deflate, br\x0d\x0a");
	strcat(headers, "Accept-Language: en-US,en;q=0.8\x0d\x0a");

	/* enable print of what's sent, also try:
		* sudo tcpdump -i lo0 -s0 -A port 8080
		* sudo tcpdump -i lo0 -s0 -X port 8080
	*/
	if(0) {
		printf("%s", headers);
		/* double newlines mark end of headers and start of contents */
		printf("\x0d\x0a");
		printf("%s", request);
		printf("%s", b64file);
	}	

	/* connect to server and send */
	network_init();
	network_resolve_target("localhost", 8080, &addr);
	network_connect(&addr, &sock_fd);

	close(sock_fd);
	free(b64file);

	return 0;		
}


