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

#include <autils/subprocess.h>

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
    pid_t child_pid;
    char enc_name_pass[MAX_ENC_NAME_PASS];

    // both argv and envp must be terminated by a NULL pointer.
    char *const argv[] = { PATH_OPENSSL, "s_client", "-connect", 
        "smtp.gmail.com:465", "-crlf", "-ign_eof", NULL };

    int fd_child_stdin, fd_child_stdout, pid_child;

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

    if(fork_and_launch(PATH_OPENSSL, argv, &child_pid, &fd_child_stdout, &fd_child_stdin)) {
        printf("ERROR: fork_and_launch()\n");
        goto cleanup;
    }
    printf("openssl launched with PID=%d\n", child_pid);

    /* consume initial blurb */
    openssl_read_lines_until(fd_child_stdout, "220 smtp.gmail.com ESMTP");
    openssl_write(fd_child_stdin, "EHLO ");
    openssl_write_line(fd_child_stdin, "doesn.t.mat.ter");
    openssl_read_lines_until(fd_child_stdout, "250 SMTPUTF8");
    openssl_write(fd_child_stdin, "AUTH PLAIN ");
    openssl_write(fd_child_stdin, enc_name_pass); 
    openssl_write(fd_child_stdin, "\n"); 
    openssl_read_lines_until(fd_child_stdout, "Accepted");
    openssl_write(fd_child_stdin, "MAIL FROM: <");
    openssl_write(fd_child_stdin, SENDER);
    openssl_write(fd_child_stdin, ">\n");
    openssl_read_lines_until(fd_child_stdout, " OK ");
    openssl_write(fd_child_stdin, "rcpt to: <");
    openssl_write(fd_child_stdin, RECEIVER);
    openssl_write(fd_child_stdin, ">\n");
    openssl_read_lines_until(fd_child_stdout, " OK ");
    openssl_write_line(fd_child_stdin, "DATA");
    openssl_read_lines_until(fd_child_stdout, " Go ahead ");
    openssl_write_line(fd_child_stdin, "Subject: MySubject");
    openssl_write_line(fd_child_stdin, "\n");
    openssl_write_line(fd_child_stdin, "MyBody");
    openssl_write_line(fd_child_stdin, ".");
    openssl_read_lines_until(fd_child_stdout, " OK ");
    openssl_write_line(fd_child_stdin, "quit");

    printf("all done here\n");
    close(fd_child_stdout);
    close(fd_child_stdin);

    cleanup:
    return rc;
}
