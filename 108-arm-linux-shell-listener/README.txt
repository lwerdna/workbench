For your native machine:
  $ gcc backdoor.c -o backdoor
  $ ./backdoor
  then from another shell:
  $ nc localhost 31337

To cross compile for ARM and test:
  $ arm-linux-gnueabi-gcc backdoor.c -o backdoor
  $ qemu-arm -L /usr/arm-linux-gnueabi ./backdoor
  and connect from another shell

Dependencies:
  $ apt install gcc-arm-linux-gnueabi # for arm-linux-gnueabi-gcc
  $ apt install qemu-user # qemu-arm
  $ apt install libc6-armel-cross # for /usr/arm-linux-gnueabi/lib/ld-linux.so.3
