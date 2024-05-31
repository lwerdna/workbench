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

# 2024-05-13

Project 106: Add example where unicorn UC_HOOK_MEM_FETCH_UNMAPPED can detect unmapped fetches, and survive execution. I thought changing PC/RIP from the offending fetch address would be sufficient, but you must also map in memory at the fetch address to prevent an additional UC_ERR_MAP.

# 2024-05-11

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

# 2024-05-10

Project 105: slightly harder ROP, call system("/bin/sh") and exit()

{
All that "2>&1" type stuff in bash are called redirections or redirection operators.
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

Pass command output as argument:
$ echo $(echo -n 'hey')
Pass file contents as argument:
$ echo -n 'hey' > /tmp/tmp.txt
$ echo $(</tmp/tmp.txt)

# 2024-05-08

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

# 2024-05-07

Compile ARM binaries using apt installable packages and examine the resulting executables:
https://github.com/lwerdna/reference_code/tree/master/hello_arm_linux_gnueabi_gcc

# 2024-05-06

Run an ARM application inside an ARM chroot with qemu.
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

# 2024-05-03
Project 102 updated with devices (switch, nic, host) implemented as threads, can ping from host OS.

# 2024-04-24
Project 102: Using a tap (layer 2) virtual network device, simulate a switch and some hosts with python.

# 2024-04-23

{
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
add u-boot dissection to: https://github.com/lwerdna/finter
uImage is (image or zImage or ?) wrapped in struct legacy_img_hdr
https://github.com/u-boot/u-boot/blob/master/include/image.h
