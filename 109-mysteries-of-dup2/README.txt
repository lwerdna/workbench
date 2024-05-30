This corrects a couple confusions I had about dup2():
* I thought when dup2(a,b) closed the file described by b and reassigned b to a's described file, it would also reassign any other descriptors that described b's file.
* I thought dup2(a,b) closed the file described by b, instead it closes the descriptor b, and only if the file described by b is not described by any other descriptor is the file itself (the "file description") closed. See file2.c

For a file (see file.c) only 0 is replaced, and writes to 1 and 2 still go to the terminal while a write to 0 after the dup2() call goes to the file:

write 0
write 1
write 2
fd: 3
0: /dev/pts/23
1: /dev/pts/23
2: /dev/pts/23
3: /home/andrewl/repos/lwerdna/workbench/109-mysteries-of-dup2/test.txt
--------
0: /home/andrewl/repos/lwerdna/workbench/109-mysteries-of-dup2/test.txt
1: /dev/pts/23
2: /dev/pts/23
3: /home/andrewl/repos/lwerdna/workbench/109-mysteries-of-dup2/test.txt
write 1
write 2
$ cat test.txt
write 0

For a socket (see sock.c) only 0 is replaced:

0: /dev/pts/23
1: /dev/pts/23
2: /dev/pts/23
3: socket:[24626649]
--------
0: socket:[24626649]
1: /dev/pts/23
2: /dev/pts/23
3: socket:[24626649]

For client socket (a socket upon which listen() was called) (see sock-server.c) only 0 is replaced:

0: /dev/pts/23
1: /dev/pts/23
2: /dev/pts/23
3: socket:[24626642]
--------
0: socket:[24626642]
1: /dev/pts/23
2: /dev/pts/23
3: socket:[24626642]

For client socket (a socket returned from accept()) (see sock-client.c) only 0 is replaced:

0: /dev/pts/23
1: /dev/pts/23
2: /dev/pts/23
3: socket:[24640665]
4: socket:[24640666]
--------
0: socket:[24640666]
1: /dev/pts/23
2: /dev/pts/23
3: socket:[24640665]
4: socket:[24640666]
