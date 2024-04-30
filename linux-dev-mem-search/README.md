Quick tools for searching `/dev/mem` (physical) and `/dev/kmem` (virtual).

`sense.c` tells you the boundaries where memory is accessible or not.

`search.c` actually goes after some bytes.

Adjust to taste.If you get a failure right at 0x100000 you likely have a kernel with `CONFIG_STRICT_DEVMEM` enabled, which prevents access above 1MB.

This is also an implied parameter if `HARDENED_USERCOPY` or `HAVE_HARDENED_USERCOPY_ALLOCATOR` are enabled.

