# 2025-03-10

{
Ping's UDP connect() Trick to Find Source IP

There was a case where I had multiple interfaces on different networks, like (simplified):

```
eth0: 192.168.1.123
eth1: 192.168.100.123
eth2: 192.168.200.123
```

And I needed my source IP address as one of the fields in a packet I was crafting.
But how?
Should I iterate over interfaces, perhaps parsing the output of `ip link`, and determining which interface (and thus which source IP) to use?
Interfaces can have multiple IP's too.
No, the solution was to let Linux do the work, then observe what IP it used.
If I connect to 192.168.100.x, Linux will route that through eth1, with source 192.168.100.123.
Since I knew of one port open on the server, I could establish a connection, and query what IP Linux assigned:

```python
s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
try:
    s.connect((host, port))
    ip, port = s.getsocknane()
    result = ip
except ConnectionRefusedError:
    pass
```

This morning I mistyped an IP assignment, and ping wasn't working when I thought it should.
I could see packets in wireshark, I knew the link was up and active, what was going on?
The error message was strange too:

> ping: connect: Network is unreachable

Connect? This is ping, what is happening?
I ran under `strace` and saw that, just prior to the error message, it tries:

```C
s = socket(AF_INET, SOCK_DGRAM, IPPROTO_IP)
connect(s, /* destination ip, port 1025 */)
```

I searched this and essentially it is a more advanced "trick" than the TCP connect one, because it doesn't require an open port on the destination.
The `connect()` call for UDP sockets just establishes a source ip/port and destination ip/port, it doesn't actually send a SYN or establish any state as in TCP sockets.
Thus, it forces Linux to consider interfaces and determine the source IP.
The port 1025 is arbitrary, but it's so close to 1024 (the first port not requiring root to bind to) that I wonder if it's one-off by accident.
} #Networking

# 2025-03-07

{
The sudo `-E` switch.

There have been so many times my python scripts requiring privileges (like opening a port below 1024) wouldn't work.
And when I `sudo myscript.py` the needed libraries weren't found.
I resorted to `sudo -i` to get a root environment then `pip install` libraries (if permitted) before invoking the script.
Or, I would I would install the libraries in a [venv](https://docs.python.org/3/library/venv.html), then `sudo -i` and activate that venv from the root environment, before invoking the script.
But now I have learned `-E`, which preserves the environment and the PYTHONPATH or whatever is needed for my root-requiring script to run.
} #TIL #Linux.Bash

{
Shell variables are different than environment variables.

Set a shell variable (AKA: local variable), and not the environment of children:

```bash
FOO=7
python -c 'import os; print("FOO" in os.environ)'
False
```

Variables like "i" in: `for i in * ;` are shell variables.

Do not set a shell variable, but set the environment of children:

```bash
FOO=7 python -c 'import os; print("FOO" in os.environ)'
True
```

Set environment variable here and in children.

```
export FOO=7
python -c 'import os; print("FOO" in os.environ)'
True
```

Note `export` is a bash builtin, `FOO=7` is bash syntax, and `env` is an external program.
The env program takes <environment> <command> <args>.
In its environment, env will set the variables given in the <environment> argument, then replace itself with command using execvp().

## References:
1. https://help.ubuntu.com/community/EnvironmentVariables
2. https://askubuntu.com/questions/26318/environment-variable-vs-shell-variable-whats-the-difference

} #TIL #Linux.Bash

# 2024-12-10

{
Parse X509 certificates.

https://github.com/lwerdna/filesamples/blob/master/x509_lets_encrypt.cer
https://github.com/lwerdna/finter/blob/master/finter/x509_der.py

Best tutorial:
  https://letsencrypt.org/docs/a-warm-welcome-to-asn1-and-der

Very good tool:
  https://lapo.it/asn1js
  https://asn1js.eu
}

{
Use a meta-language to abstract away data structure byte representation.

There's a very nice idea that I am late to learn.
Instead of defining a data structure in a language dependent way (eg: in a C struct), a meta-language can be designed and used, here ASN.1, but protocol buffers is another example.
The meta language might then be "compiled" to produce the C struct.
The noun "serialization" is then used to denote the actual byte layout of the data structure, just as it more commonly denoted the byte representation of a serialized object.
Mediated by this meta language, different languages can exchange these data structures, with issues of representation (how primitives are encoded, alignment, etc.) conveniently abstracted away.

References:
  1. https://en.wikipedia.org/wiki/ASN.1
  2. https://en.wikipedia.org/wiki/Protocol_Buffers
}

# 2024-12-09

{
Force a TLS v1.0 connection.

It's deprecated everywhere!
`openssl s_client -debug -connect 192.168.1.123 -tls1` doesn't work:
   SSL routines:tls_setup_handshake:no protocols available:../ssl/statem/statem_lib.c:104
The python ssl library doesn't work:
   DeprecationWarning: ssl.PROTOCOL_TLSv1 is deprecated

Luckily we have tlslite (`pip install tlslite-ng`)!

TODO: put TLS code
}

{
Make a windows startup disk.

Balena Etcher
Rufus
Startup Disk Creator (Ubuntu)

WoeUSB, WoeUSB-ng, Ventoy

ISO's are optical images (ISO9660) and typically cannot be dd'd directly to USB drives.
Linux distros use "IsoHybrid" hack, Windows ISO's don't.
A tool that works with Windows ISOs writes a partition scheme (MBR or GPT) and puts the contents of the ISO to a filesystem (FAT32 or NTFS).
Competing partition standards and schemes: MBR, GUID partition table (GPT), Apple Partition Table (APT)
}

{
Analyze certificate in TLS negotiation.

Make the server speak:
  nmap --script ssl-enum-ciphers -p 55754 192.168.122.102

In wireshark:
  capture TLS exchange
  identify "Server Hello" packet
  right-click "Certificate" -> "Export Packet Bytes" -> cert.bin

Dump:
  openssl x509 -text -in cert.bin
  openssl asn1parse -in cert.bin -inform DER
  openssl s_client -trace -connect 192.168.122.102 -tls1
  openssl s_client -debug -connect 192.168.122.102 -tls1

Certificate is basically a signed tuple of (subject, public key).
If "Issuer" and "Subject" are the same, certificate is "self-signed".
RFC5280 gives cert structure in ASN.1 (abstract syntax notation).
Actual representation "encoding" can then be made into:
  - DER (distinguished encoding rules) (bytes)
  - XER (xml encoding rules)
  - JER (json encoding rules)
Further processing can base64 encode, PEM, etc.

References:
  darutk.medium.com
}

{
Convert between bytes and hex strings in Python

mybytes.hex()          # b'\xAA' -> 'AA'
bytes.fromhex(hexstr)  # 'AA' -> b'\xAA'
}

# 2024-12-08

{
Make ISO image from files

mkisofs -o image.iso /path/to/files

The tool comes from package "genisoimage".
}

# 2024-11-27

{
Ethernet II is different than Ethernet 802.3!

Actually they are 2 of 4 possible ethernet frames.
Both start with DstMac(6), SrcMac(6), EtherType(2).
The former follows with the payload bytes, the latter follows with an 802.2 header.
The ethertype/length field and the first two bytes of the payload decide.
see: "Ethernet Frame Differentiation" at https://en.wikipedia.org/wiki/Ethernet_frame
} #Networking #TIL

# 2024-10-12

{
/etc/shells and getusershell()

TIL: the allowed login shells are in a only-writeable-by-root list in /etc/shell.
Some helper functions are available for reading this file, see `man getusershell`.
Here's a demo:

```C
#include <stdio.h>
#include <unistd.h>
int main(int ac, char **av)
{
	char *shell;
	while (1) {
		if((shell = getusershell()) == NULL) break;
		printf("%s\n", shell);
	}
	endusershell();
	return 0;
}
```

```
$ gcc test.c -o test
$ ./test
/bin/sh
/bin/bash
/usr/bin/bash
/bin/rbash
/usr/bin/rbash
/usr/bin/sh
/bin/dash
/usr/bin/dash
/usr/bin/screen
```

We use the mount --bind technique to override /etc/shells and see if getusershell() responds:

```
$ echo '/path/to/yomomma' > haha
$ sudo mount --bind haha /etc/shells
$ ./test
/path/to/yomomma
$ sudo umount /etc/shell
```

This might also be used to temporarily deny logins (even thru ssh) without disabling those services.
The check for the login shell just fails.
In dropbear, for example, see initshells() from compat.c.
}

{
< vs. << vs. <<< in bash

<   passes the contents of a file to stdin
<<  "here document" passes multiple lines until a terminator to stdin
<<< "here string" passes a string to stdin

To experiment, use:

```
#!/usr/bin/env python
import sys

result = ''
while True:
    char = sys.stdin.read(1)
    if not char:
        break
    result += char

print('repr:', repr(result))
print(' hex:', result.encode('utf-8').hex())
```

And input file:

```
$ echo -n 'AAAA' > a.txt # -n for no newline
$ cat a.txt | xxd -g 1   # -g 1 for 1-byte groups
00000000: 41 41 41 41                                      AAAA
```

It's clean when stdin comes from a file:

```
$ ./test.py < a.txt
repr: 'AAAA'
 hex: 41414141
```

Newlines creep in, as the terminator must be on a line by itself:

```
$ ./test.py << MYEND
> A
> AA
> AAA
> MYEND
repr: 'A\nAA\nAAA\n'
 hex: 410a41410a4141410a
```

A newline even exists after a lone string:

```
$ ./test.py <<< "AAAA"
repr: 'AAAA\n'
 hex: 414141410a
```

You can create files in a bash script with:

```
$ cat > b.txt <<MY_END
> one
> two
> three
> MY_END
$ cat b.txt
one
two
three
```

You can create binaries too, since base64 ignores the newlines introduced in the "here document":

```
$ python -c 'import sys; sys.stdout.buffer.write(b"".join([x.to_bytes(1,"big") for x in range(256)]))' > test.bin
$ xxd -g 1 ./test.bin
00000000: 00 01 02 03 04 05 06 07 08 09 0a 0b 0c 0d 0e 0f  ................
00000010: 10 11 12 13 14 15 16 17 18 19 1a 1b 1c 1d 1e 1f  ................
00000020: 20 21 22 23 24 25 26 27 28 29 2a 2b 2c 2d 2e 2f   !"#$%&'()*+,-./
00000030: 30 31 32 33 34 35 36 37 38 39 3a 3b 3c 3d 3e 3f  0123456789:;<=>?
00000040: 40 41 42 43 44 45 46 47 48 49 4a 4b 4c 4d 4e 4f  @ABCDEFGHIJKLMNO
00000050: 50 51 52 53 54 55 56 57 58 59 5a 5b 5c 5d 5e 5f  PQRSTUVWXYZ[\]^_
00000060: 60 61 62 63 64 65 66 67 68 69 6a 6b 6c 6d 6e 6f  `abcdefghijklmno
00000070: 70 71 72 73 74 75 76 77 78 79 7a 7b 7c 7d 7e 7f  pqrstuvwxyz{|}~.
00000080: 80 81 82 83 84 85 86 87 88 89 8a 8b 8c 8d 8e 8f  ................
00000090: 90 91 92 93 94 95 96 97 98 99 9a 9b 9c 9d 9e 9f  ................
000000a0: a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 aa ab ac ad ae af  ................
000000b0: b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 ba bb bc bd be bf  ................
000000c0: c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 ca cb cc cd ce cf  ................
000000d0: d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 da db dc dd de df  ................
000000e0: e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 ea eb ec ed ee ef  ................
000000f0: f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 fa fb fc fd fe ff  ................

$ base64 ./test.bin
AAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8gISIjJCUmJygpKissLS4vMDEyMzQ1Njc4
OTo7PD0+P0BBQkNERUZHSElKS0xNTk9QUVJTVFVWV1hZWltcXV5fYGFiY2RlZmdoaWprbG1ub3Bx
cnN0dXZ3eHl6e3x9fn+AgYKDhIWGh4iJiouMjY6PkJGSk5SVlpeYmZqbnJ2en6ChoqOkpaanqKmq
q6ytrq+wsbKztLW2t7i5uru8vb6/wMHCw8TFxsfIycrLzM3Oz9DR0tPU1dbX2Nna29zd3t/g4eLj
5OXm5+jp6uvs7e7v8PHy8/T19vf4+fr7/P3+/w==

$ base64 -d <<MY_END > test2.bin
> AAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8gISIjJCUmJygpKissLS4vMDEyMzQ1Njc4
OTo7PD0+P0BBQkNERUZHSElKS0xNTk9QUVJTVFVWV1hZWltcXV5fYGFiY2RlZmdoaWprbG1ub3Bx
cnN0dXZ3eHl6e3x9fn+AgYKDhIWGh4iJiouMjY6PkJGSk5SVlpeYmZqbnJ2en6ChoqOkpaanqKmq
q6ytrq+wsbKztLW2t7i5uru8vb6/wMHCw8TFxsfIycrLzM3Oz9DR0tPU1dbX2Nna29zd3t/g4eLj
5OXm5+jp6uvs7e7v8PHy8/T19vf4+fr7/P3+/w==
> MY_END

$ diff test.bin test2.bin
$
```

This can be extended to multiple files in a single blob, by encoding the output
of tar, and piping it to base64 and `tar -x` at runtime.
}

# 2024-06-21

What's wrong with this logic?

if mylib.so is present in /proc/<pid>/maps
  handle = dlopen("mylib.so", ...)
  dlclose(handle)

This, from man 3 dlopen:

> The dl library maintains reference counts for library handles, so a dynamic library is not deallocated until dlclose() has been called on it as many times as dlopen() has succeeded on it.

So each time I retrieved a handle, I was taking one step back.

# 2024-06-19

I didn't know there were no load multiple (ldm), store multiple (stm), push, or pop instructions in A64.

This is a handy template for experimenting with instruction encodings:

```python
import os
from struct import pack, unpack

def disasm(instr):
    instr, = unpack('<I', pack('>I', instr))
    cmd = 'cstool arm64 ' + hex(instr)[2:]
    os.system(cmd)

# LDP <Xt1>, <Xt2> [Xn], #<imm>
instr = 0
instr |= 0b10 << 30 # opc
instr |= 0b10100011 << 22
instr |= 2 << 15 # imm7 = imm/8 = 16/8 = 2
instr |= 31 << 10 # Rt2
instr |= 31 << 5 # Rn
instr |= 0 << 0 # Rt
disasm(instr)
```

# 2024-06-17

Beware readlink(), which does not null-terminate strings. In my case, there happened to be a 0x02
after the string and then a 0x00, so it would print fine, but functions like strcmp() and strstr()
wouldn't fail mysteriously.

# 2024-06-12

Compile AARCH64 binaries using apt installable packages and examine the resulting executables:
https://github.com/lwerdna/reference_code/tree/master/hello_aarch64_linux_gnu_gcc

# 2024-06-06

There are a number of ways to programmatically break an attached GDB on ARM, including at least:

__asm__ volatile("bkpt");
PROS: breaks right in the instruction stream
CONS: some targets (my qemu) won't let me advance $pc over the instruction (`set $pc = $pc+4` does nothing)

raise(SIGTRAP);
PROS: can continue easily from trapped location
CONS: execution is somewhere (signal handler stuff?) so you can't reap useful values around the stopping point, like the returns from functions

# 2024-06-04

Project 110: use PTRACE to attach to a process, change value, then detach.

# 2024-05-31

What order do the registers appear on the stack after push {r4-r11,lr}?
Project 000 unicorn repls makes it easy:
$ ./repl_a32_blank.py 
> r4=4
> r4=5
> r11=0xB
> lr=0xDEADBEEF
> push {r4-r11,lr}
> dds ffffffdc
FFFFFFDC: 0x00000004
FFFFFFE0: 0x00000005
FFFFFFE4: 0x00000000
FFFFFFE8: 0x00000000
FFFFFFEC: 0x00000000
FFFFFFF0: 0x00000000
FFFFFFF4: 0x00000000
FFFFFFF8: 0x0000000B
FFFFFFFC: 0xDEADBEEF

So when you push {A,B,C}, C is pushed first, B second, and A third.
Or, A,B,C appears in this order when viewing the stack from the side, reading top to bottom.

# 2024-05-30

Project 108: simple and predictable remote listening shell, with loose future plans to make an optimized, dependency-free version with manual syscalls

# 2024-05-29

Project 109: clear up some personal confusion about dup2()

# 2024-05-20

Project 106: It appears unicorn stops at the first or second instruction of the last JIT'd block upon unmapped memory write.

# 2024-05-16

Project 107: Can a usermode emulator (unicorn) be used to automatically decompress zImages?

# 2024-05-15

Blackbox some code in gdb:
- breakpoint at end of function
- quick script to /tmp/tmp.gdb:
define try
	set $pc = 0x400104
	set $r0 = $arg0
	set $r1 = 32
	c
(gdb) source /tmp/tmp.gdb
(gdb) try 1
(gdb) try 2

Reminder for how to configure the guest interpreter in qemu arm emulation:
$ qemu-arm ./target
qemu-arm: Could not open '/lib/ld-linux.so.3': No such file or directory
$ dpkg-query --search ld-linux.so.3
libc6-armhf-cross: /usr/arm-linux-gnueabihf/lib/ld-linux.so.3
libc6-armel-cross: /usr/arm-linux-gnueabi/lib/ld-linux.so.3
$ qemu-arm -L /usr/arm-linux-gnueabi ./target

# 2024-05-14

{
Approaches to "ripping" or "lifting" code

The only verb I knew for stealing code from a target (instead of reimplementing it) was "rip", but in some whitebox crypto papers they use "lift".
With the ease of setting up one-off emulators, I'm up to three methods for doing this:
1) copy the blob(s), jump/call into it carefully
2) copy the assembly(s), fixing things manually, and assemble an executable object
3) copy the blob(s), and set up a quick VM to execute it

There are pros/cons to each, but #1 and #2 require the target and host tool architecture match.
Option #3 is not just architecture independent, the host tool can be a scripting language.
Namely, python and pip-installable unicorn emulator make for a very powerful combination for these tasks.

There are initial barriers with new tooling, but after some examples and experience are collected, the investment pays off.
Here's one useful pattern:
Instead of ahead-of-time knowing and planning all the paths the ripped code will take, a sort of "rip template" is useful.
Start with an initial dumped blob.
Capture every time execution reaches outside of the blob(s) (via UC_HOOK_MEM_FETCH_UNMAPPED), and output enough information to track down what needs to be further ripped.
Now it's an iterative process.

Add dump_best_effort function to my gdb script, which, unlike gdb's built-in dump, won't abandon the dump completely when encountering unreadable memory:

https://github.com/lwerdna/dotfiles/blob/master/gdbinit_mem

Remember, gdb doesn't mean only linux targets, it's anything that accepts gdb rsp connections, like qemu, renode, etc.

Add whitebox-lift.py example to Project 106
}

# 2024-05-13

Project 106: Add example where unicorn UC_HOOK_MEM_FETCH_UNMAPPED can detect unmapped fetches, and survive execution. I thought changing PC/RIP from the offending fetch address would be sufficient, but you must also map in memory at the fetch address to prevent an additional UC_ERR_MAP.

# 2024-05-11

{
Correcting misconception of STDIN, STDOUT, STDERR and dup2()

Project 105: upgrade with dup2() call so payload can come from redirected stdin but spawned shell can still interact with terminal.

I was conceptualizing STDIN, STDOUT, STDERR wrong.
They're not distinct descriptors (0, 1, 2) that refer to distinct things (terminals? parts of terminals? streams?).
They're distinct descriptors that refer to the SAME thing (a pseudo terminal).
It's when you do redirection (like "./foo > output.txt") that you draw a descriptor away, to refer to a new thing (here, STDOUT/1 describes the file output.txt).
To convince yourself, try to read() from STDOUT, it works!
See test-fds.c in Project 105.
Now dup(1, 0) says make 0 describe to whatever 1 describes, closing 0 if it currently describes something.
So if 0 has been redirected, you can restore it the original pts because 1 and 2 still hold a reference.
So dup(2, 0) should also work.
}

# 2024-05-10

Project 105: slightly harder ROP, call system("/bin/sh") and exit()

{
"2>&1" type stuff in bash are called redirections or redirection operators.

https://www.gnu.org/software/bash/manual/bash.html#Redirections

ls > dirlist 2>&1
can be thought of as an imperative program:
stdout = fp_dirlist
stderr = stdout # and thus dirlist
both stdout and stderr are descriptors of file "dirlist", so it accomplishes the goal of collecting all of ls's output (stdout and stderr) into the file

ls 2>&1 > dirlist
stderr = stdout # gets a copy of stdout
stdout = fp_dirlist
now stderr has the stdout descriptor, while stdout has the descriptor of file "dirlist", so you'll see error messages on the screen and normal messages in the file
} #TIL

{
Is a "site" like python's location for packages and modules outside the core location?
python -m site
Compare and contrast these two commands:
python -c "import sys; print(sys.path)"
python -S -c "import sys; print(sys.path)"

find where a package gets imported from:
python -v -c 'import pwn' 2>&1 | less

list info on a package, including dependencies:
pip show pwntools
pip show -f pwntools
} #Python #TIL

# 2024-05-09

Project 104: easy return oriented programming (ROP) exercise from ired.team

{
Passing command output or files contents as command argument

Pass command output as argument:
$ echo $(echo -n 'hey')
Pass file contents as argument:
$ echo -n 'hey' > /tmp/tmp.txt
$ echo $(</tmp/tmp.txt)
} #Techtip #Linux.Bash

# 2024-05-08

{
A look below the surface of APT

I always used apt at the "surface", never understanding deeper inner workings.
Sometimes some answers used dpkg, which I kind of knew was related.
dpkg is debian base / low-level package management, while apt is higher.
apt reaches out to sources, handles dependencies, etc.
'dpkg' is a package itself, containing (abridged):
$ dpkg -L dpkg
    dpkg, dpkg-deb, dpkg-divert, dpkg-maintscript-helper, dpkg-query,
    dpkg-realpath, dpkg-split, dpkg-statoverride, dpkg-trigger,
    update-alternatives,
'dpkg-dev' is a package, containing (abridged):
$ pkg -L dpkg-dev
    dpkg-architecture, dpkg-buildflags, dpkg-buildpackage, dpkg-checkbuilddeps,
    dpkg-distaddfile, dpkg-genbuildinfo, dpkg-genchanges, dpkg-gencontrol,
    dpkg-gensymbols, dpkg-mergechangelogs, dpkg-name, dpkg-parsechangelog,
    dpkg-scanpackages, dpkg-scansources, dpkg-shlibdeps, dpkg-source,
    dpkg-vendor,
dpkg invocations are worth memorizing, like:
  dpkg -S <file> to find where a file comes from
  dpkg -L <package> to find what files are contained in a package
  dpkg -l to list all packages installed on the system
The package filenames are a bitch to parse.
qemu-user-binfmt_6.2+dfsg-2ubuntu6.18_amd64.deb is something like:
qemu-user-binfmt    name of package
6.2                 version of qemu
+dfsg               repacked to meet Debian free software compliance
                    https://wiki.debian.org/DebianFreeSoftwareGuidelines
                    (+ds would mean repacked for other reasons)
-2                  number of Debian packaging revisions

Having an idea of how software goes from author to conveniently installable on your machine is very useful.
My current simple understanding is:
Qemu is a project written by qemu people.
That is "consumed" by Debian, who modify it, repackage it, and slap a tag on it.
That is "consumed" by Ubuntu, who modify it, repackage it, and slap a tag on it.
That is "consumed" by Ubuntu users, who `apt install` the packages.
From sources to destination, it kind of flows like a river or stream.
Bugs whose fix can only be fixed earlier in the process are upstream bugs.
Bugs whose cause is due to repackaging, later in the process, are downstream bugs.
See: https://askubuntu.com/questions/4868/what-is-the-difference-between-upstream-and-downstream-when-referring-to-who-to locally mirrored at ./assets/great-explanation-upstream-downstream.txt
Upstream is synonymous with "source".

A #IDoAndIUnderstand project I need to undertake:
https://askubuntu.com/questions/458748/is-it-possible-to-add-a-location-folder-on-my-hard-disk-to-sources-list for creating a local package.
}

# 2024-05-07

Compile ARM binaries using apt installable packages and examine the resulting executables:
https://github.com/lwerdna/reference_code/tree/master/hello_arm_linux_gnueabi_gcc

# 2024-05-06

{
Run an ARM application inside an ARM chroot with qemu.

What happens if a usermode binary you're emulating with qemu references another file?
For example, it's dynamic interpreter?
Or other shared objects?
You can `chroot` on qemu to make these all resolve seamlessly.

Note qemu-arm is the user binary emulator and qemu-system-arm is the system emulator.
If error "chroot: failed to run command ‘/usr/bin/qemu-arm’: No such file or directory", it is due (I think) to inability to find some dependency (a .so?) of qemu-arm, not missing qemu-arm itself.
Using qemu-arm-static from package qemu-user-static is easiest since no dependencies, and no interpreter / dynamic linker.
Place it in sysroot at path/to/sysroot/usr/bin.
Final command was:
```
$ sudo LD_LIBRARY_PATH="/path/libs/a;/path/libs/b" chroot . /usr/bin/qemu-arm-static -g 12345 /path/to/executable
```
It is a little mindbending since:
* All paths are given as if the chroot has taken effect.
* qemu-arm-static is host architecture, executable is guest architecture (ARM)

Is Linux and its ways of thinking like a mindbending playground? Consider:
* Chroot and emulation.
* SLIP and tuntap and tunneling packets.
* A file can contain a filesystem (which of course contains files).
}

# 2024-05-03
Project 102 updated with devices (switch, nic, host) implemented as threads, can ping from host OS.

# 2024-05-01
{
Patch files with `dd`:

$ xxd -g 1 /tmp/probe.bin
00000000: de ad be ef                                      ....
$ xxd -g 1 /tmp/tmp.bin
00000000: 41 41 41 41 41 41 41 41                          AAAAAAAA
$ dd if=/tmp/probe.bin iseek=0 of=/tmp/tmp.bin oseek=2 bs=1 conv=notrunc
$ xxd -g 1 /tmp/tmp.bin
00000000: 41 41 de ad be ef 41 41                          AA....AA
} #TIL

# 2024-04-24
Project 102: Using a tap (layer 2) virtual network device, simulate a switch and some hosts with python.

# 2024-04-23

{
VIM Customization costs me 2 hours troubleshooting SSH

I spent close to 2 hours trying to resolve why passwordless login wasn't working.

I didn't have access to /var/log/auth.log or alternatives because it is not my server.

The standard advice was to check permissions:
chmod 700 ~/.ssh                 (only user can rwx)
chmod 600 ~/.ssh/authorized_keys (only user can rw)

Then I tried the tool:
ssh-copy-id -i .ssh/id_rsa.pub remoteuser@HOST.IP.ADDR.ESS

And it worked!
I examined ~/.ssh/authorized_keys and saw that the line added by the tool was slightly different than the one I pasted in.

I pasted again and compared.
Near a "...K15ujkaRc..." it would actually put:
       "...K15uRc..."

That's because I adopted "jk" as an escape for vim editor ages ago after reading: https://learnvimscriptthehardway.stevelosh.com:

:inoremap jk <esc>
} #SSH #TIL #Vim

# 2024-04-22
Project 101: make a tap (layer 2) virtual network device and print packets sent to it with python

# 2024-04-19
Project 100: sample CP15 feature registers in REnode guest with armv7 assembler

# 2024-04-05
Project 098: try to generate constraints in SMT form from KConfig, solve with z3 (WIP)

# 2024-03-20
Project 099: search /dev/mem (physical) or /dev/kmem (virtual) for target
I needed to recover kernel parameters sent as a tagged list from bootloader.
add ATAGs dissection to: https://github.com/lwerdna/finter

# 2024-03-13
Add "hello world" LKM for Ubuntu
https://github.com/lwerdna/reference_code/tree/master/hello_world_ubuntu_lkm

# 2024-03-12
Project 103: Dump binaries and emulate them using unicorn, aiming to get some of the graphical output of stack reads/writes that whitebox crypto defeat papers have. Demonstrate use of unicorn hooks. #Crypto #Emulation #Unicorn

# 2024-03-08
{
Add u-boot dissection to: https://github.com/lwerdna/finter
uImage is (image or zImage or ?) wrapped in struct legacy_img_hdr
https://github.com/u-boot/u-boot/blob/master/include/image.h
}
