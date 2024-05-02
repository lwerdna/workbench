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

# 2024-03-08
add u-boot dissection to: https://github.com/lwerdna/finter
uImage is (image or zImage or ?) wrapped in struct legacy_img_hdr
https://github.com/u-boot/u-boot/blob/master/include/image.h
