/* demonstrate command line mail send using smtp.google.com

    the account you use must have "less secure apps" access setting

    smtp.gmail.com:465 is SSL
    smtp.gmail.com:587 starts plaintext and requies STARTTLS command

    we pipe to openssl for the SSL responsibility */

/* includes */
#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>

#include <sys/types.h>
#include <sys/poll.h>

#define MAX_NAME_PASS 2048
#define MAX_ENC_NAME_PASS 2048
#define PATH_OPENSSL "/usr/bin/openssl"
#define GMAIL_USER "XXXXXX@gmail.com"
#define GMAIL_PASS "ABABBABABABAB"
#define SENDER "alice@domain.com" // this gets overridden by GMAIL_USER
#define RECEIVER "bob@domain.com"

//****************************************************************************
// UTILS
//****************************************************************************

void
base64_encode(unsigned char *data, size_t len, char *out)
{
    int i, j;
    char *lookup = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    int mod_table[] = {0, 2, 1};
    int out_len = 4 * ((len + 2) / 3);

    for (int i = 0, j = 0; i < len;) {

        uint32_t octet_a = i < len ? (unsigned char)data[i++] : 0;
        uint32_t octet_b = i < len ? (unsigned char)data[i++] : 0;
        uint32_t octet_c = i < len ? (unsigned char)data[i++] : 0;

        uint32_t triple = (octet_a << 0x10) + (octet_b << 0x08) + octet_c;

        out[j++] = lookup[(triple >> 3 * 6) & 0x3F];
        out[j++] = lookup[(triple >> 2 * 6) & 0x3F];
        out[j++] = lookup[(triple >> 1 * 6) & 0x3F];
        out[j++] = lookup[(triple >> 0 * 6) & 0x3F];
    }

    for (int i = 0; i < mod_table[len % 3]; i++)
        out[out_len - 1 - i] = '=';

    out[out_len] = '\0';
}

//****************************************************************************
// OPENSSL COMM HELPERS
//****************************************************************************

int 
openssl_read_until(int fd, char *buf, int capacity, char *terminator)
{
    int i, n;
    int rc = -1;

    memset(buf, '\0', capacity);

    /* read one character at a time until terminator found */
    for(i=0; i<(capacity-1); ++i) {
        n = read(fd, buf+i, 1);

        if(n != 1) {
            goto cleanup;
        }
    
        /* is terminating string found? */
        if(strstr(buf, terminator)) {
            rc = i+1;
            goto cleanup;
        }
    }

    cleanup:
    return rc;
}

int
openssl_read_line(int fd, char *buf, int capacity)
{
    return openssl_read_until(fd, buf, capacity, "\n");
}

int
openssl_read_lines_until(int fd, char *match)
{
    int rc = -1;
    char buf[1024];

    while(1) {
        rc = openssl_read_line(fd, buf, sizeof(buf));
        if(rc < 0) {
            printf("ERROR: openssl_read_line()\n");
            goto cleanup;
        }

        printf("got line: %s (match %s?)\n", buf, match);

        if(strstr(buf, match)) break;
    }

    rc = 0;

    cleanup:
    return rc;
}

int openssl_write_line(int fd, char *buf)
{
    printf("sending openssl: \"%s\"\n", buf);
    write(fd, buf, strlen(buf));
    write(fd, "\n", strlen("\n"));
    return 0;
}

int openssl_write(int fd, char *buf)
{
    printf("sending openssl: \"%s\"\n", buf);
    write(fd, buf, strlen(buf));
    return 0;
}

//****************************************************************************
// MAIN
//****************************************************************************

int main(int ac, char **av)
{
    int rc = -1;
    int i;
    ssize_t n;
    pid_t childpid;
    char enc_name_pass[MAX_ENC_NAME_PASS];

    // both argv and envp must be terminated by a NULL pointer.
    char *args_openssl[] = { "/usr/bin/openssl", "s_client", "-connect", 
        "smtp.gmail.com:465", "-crlf", "-ign_eof", NULL };
    char *search_move;

    /* these fd's used to send commands down to openssl */
    int fds_down[2];
    /* these fd's used to read output from openssl (he writes up to us) */
    int fds_up[2];

    /* encode the name and pass */
    {
        int len = 0;
        // we form "\x00<email>\x00<pass>"
        char name_pass_buf[MAX_NAME_PASS];
        name_pass_buf[len++] = '\x00';
        strcpy(name_pass_buf + len, GMAIL_USER);
        len += strlen(GMAIL_USER);
        name_pass_buf[len++] = '\x00';
        strcpy(name_pass_buf + len, GMAIL_PASS);
        len += strlen(GMAIL_PASS);
        base64_encode((unsigned char *)name_pass_buf, len, enc_name_pass);
        printf("encoded name/pass to: %s\n", enc_name_pass);
    }

    /* create pipes */
    pipe(fds_down);
    pipe(fds_up);

    /* fork */
    childpid = fork();
    if(childpid == -1) {
        printf("ERROR: fork()\n");
        goto cleanup;
    }

    /* child activity */
    if(childpid == 0) {
        /* close writer from down pipes (we read from parent) */
        close(fds_down[1]); 
        /* close reader from up pipes (we write to parent) */
        close(fds_up[0]);

        /* duplicate the down rx pipe onto stdin */
        i = dup2(fds_down[0], STDIN_FILENO);
        if(i >= 0) {
            printf("dup2() on STDIN returned: %d\n", i);
        } 
        else {
            perror("dup2()");
            goto cleanup;
        }

        /* NO PRINTF() WORK AFTER dup2() IS DONE */

        /* duplicate the up tx pipe onto stdout */
        i = dup2(fds_up[1], STDOUT_FILENO);
        if(i >= 0) {
            printf("dup2() on STDOUT returned: %d\n", i);
        } 
        else {
            perror("dup2()");
            goto cleanup;
        }

        /* now execute openssl, which inherits file descriptors */
        execv(PATH_OPENSSL, args_openssl);

        printf("ERROR: execv()\n");
    }
    /* parent activity */
    else {
        printf("spawned child process: %d\n", childpid);

        /* close reader from down pipes (we write to child) */
        close(fds_down[0]); 
        /* close writer from up pipes (we read from child) */
        close(fds_up[1]);

        /* consume initial blurb */
        openssl_read_lines_until(fds_up[0], "220 smtp.gmail.com ESMTP");
        openssl_write(fds_down[1], "EHLO ");
        openssl_write_line(fds_down[1], SENDER);
        openssl_read_lines_until(fds_up[0], "250 SMTPUTF8");
        openssl_write(fds_down[1], "AUTH PLAIN ");
        openssl_write(fds_down[1], enc_name_pass); 
        openssl_write(fds_down[1], "\n"); 
        openssl_read_lines_until(fds_up[0], "Accepted");
        openssl_write(fds_down[1], "MAIL FROM: <");
        openssl_write(fds_down[1], SENDER);
        openssl_write(fds_down[1], ">\n");
        openssl_read_lines_until(fds_up[0], " OK ");
        openssl_write(fds_down[1], "rcpt to: <");
        openssl_write(fds_down[1], RECEIVER);
        openssl_write(fds_down[1], ">\n");
        openssl_read_lines_until(fds_up[0], " OK ");
        openssl_write_line(fds_down[1], "DATA");
        openssl_read_lines_until(fds_up[0], " Go ahead ");
        openssl_write_line(fds_down[1], "Subject: MySubject");
        openssl_write_line(fds_down[1], "\n");
        openssl_write_line(fds_down[1], "MyBody");
        openssl_write_line(fds_down[1], ".");
        openssl_read_lines_until(fds_up[0], " OK ");
        openssl_write_line(fds_down[1], "quit");

        printf("all done here\n");
        close(fds_down[1]);
        close(fds_down[0]);
    }

    cleanup:
    return rc;
}
