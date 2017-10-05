# How hard is it to implement the familiar port scanners?

I tried to make these as simple as possible, avoiding threads and libpcap when possible.

## using connect()
I didn't know connect() could be made nonblocking with `fcntl()` and a thousand connections queued up at once. The `connect()` call will technically fail (returning -1) but errno will be set to EINPROGRESS.

On linux, `select()` returned when anything in the write set changed. But on MacOS, it needed to be in the error or exception set. Making every socket a member of both sets appeared to do no harm.

See connectscan.c.

## using raw sockets for syn or half-open scanning
Everyone knows a full TCP connection has the 3-handshake SYN, ACK, SYNACK encapsulated by the OS appeal connect(). Using raw sockets, you can just send SYN, and sniff the SYNACK. OS will not recognize connection and send RST itself.

See openscan.c

## pitfalls
* bit flag precedence `if(tcphdr->th_flags == TH_SYN|TH_ACK)` (needs parenthesis)
* size-appropriate network/host ordering `saddr_in.sin_port = htonl(port)` (needs htons())
* size-appropriate comparisons `for(port=0; port<65536; port++)` doesn't work if sizeof(port)==2
* overflow packet queue: every outgoing syn queued that syn and rst (and synack of port open) read for read on the raw socket
* BSD's (MacOS and FreeBSD) do *not* place TCP and UDP packets on raw sockets, you must use pcap instead
 
## pitfall: self connect
The connect scanner was detecting open ports at random high values, in addition to the real ones open down low (22, 80, 631). Never the same value either:

```
slot[1003] = {.sock=1006, .port=35275} added to FD_SET()
slot[1004] = {.sock=1007, .port=35276} added to FD_SET()
slot[1005] = {.sock=1008, .port=35277} added to FD_SET()
slot[1006] = {.sock=1009, .port=35278} added to FD_SET()
slot[1007] = {.sock=1010, .port=35279} added to FD_SET()
port 34522 is open!
```
I spent a lot of time trying to "fix" what was surely a logic bug, until daring the scanner to keep the connection so I could look at it from some network tools:

```
a@ubuntu:~$ netstat -A inet -p
(Not all processes could be identified, non-owned process info
 will not be shown, you would have to be root to see it all.)
Active Internet connections (w/o servers)
Proto Recv-Q Send-Q Local Address           Foreign Address         State       PID/Program name
tcp        0      0 localhost:34522         localhost:34522         ESTABLISHED 75442/connectscan
tcp        0      0 localhost:51579         localhost:ipp           TIME_WAIT   -
```
What the hell is it connected to? Itself?! Its own port? Yes, turns out it's a thing, when the randomly assigned client port (linux speak: ephemeral port) happens to be the destination port you provided.
Here's one of the better explanations I found online: http://sgros.blogspot.com/2013/08/tcp-client-self-connect.html

## resources
* https://nmap.org/book/man-port-scanning-techniques.html
* http://sock-raw.org/papers/sock_raw under section "b. FreeBSD"
* scan local, then `tcpdump -i lo0 -X -s0` has little noise
* scan, then `nc -l 31337` to ensure the port is detected

<!-- CREATED: 2017-09-27 -->
<!-- TAGS: derp,lerp -->