simple driver demonstrating a proc file entry on linux

tested on Ubuntu 14.04 x86_64

the linux kernel interface changes often, I'm using proc_create() here, but be sure to see proc_fs.h for the latest way to go about it

# Building
Use `uname -r` and look for a matching resuilt in /usr/src. For example 3.16.0-30-generic means that you should find /usr/src/linux-headers-3.16.0-30-generic. Now:
```
$ KERNEL_DIR=/usr/src/linux-headers-3.16.0-30-generic/ make
```

# Installing
```
$ sudo insmod proctest
```


