how difficult is it to use an arduino?

brew cask install arduino

lost 15 minutes before realizing cord was power only, not data!

now dmesg shows:
AppleUSBFTDI: fInBufPool,kMaxInBufPool 8,64
         0 [Level 5] [com.apple.message.domain com.apple.commssw.ftdi.device] [com.apple.message.signature AppleUSBFTDI] [com.apple.message.signature2 0x403] [com.apple.message.signature3 0x6001] [com.apple.message.summarize YES]
AppleUSBFTDI: Version number - 5.0.0, Input buffers 8, Output buffers 16

and /dev/tty.usbserial-B2KXJSS5 shows up

choose it in tools->port
