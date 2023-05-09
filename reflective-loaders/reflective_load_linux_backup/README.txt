(gdb) bt
#0  open_verify (name=0x602010 "/lib/libm.so.6", fbp=0x7fffffffd518, loader=0x7ffff7ffe1c8, whatcode=0, 
    found_other_class=0x7fffffffd500, free_name=true) at dl-load.c:1873
#1  0x00007ffff7de2d9f in _dl_map_object (loader=loader@entry=0x7ffff7ffe1c8, 
    name=name@entry=0x400954 "/lib/libm.so.6", type=type@entry=2, trace_mode=trace_mode@entry=0, 
    mode=mode@entry=-1879048191, nsid=0) at dl-load.c:2543

#2  0x00007ffff7deea54 in dl_open_worker (a=a@entry=0x7fffffffda98) at dl-open.c:235

#3  0x00007ffff7de9ff4 in _dl_catch_error (objname=objname@entry=0x7fffffffda88, 
    errstring=errstring@entry=0x7fffffffda90, mallocedp=mallocedp@entry=0x7fffffffda80, 
    operate=operate@entry=0x7ffff7dee9a0 <dl_open_worker>, args=args@entry=0x7fffffffda98) at dl-error.c:187
#4  0x00007ffff7dee3bb in _dl_open (file=0x400954 "/lib/libm.so.6", mode=-2147483647, caller_dlopen=<optimized out>, 
    nsid=-2, argc=1, argv=0x7fffffffde18, env=0x7fffffffde28) at dl-open.c:661
#5  0x00007ffff7bd702b in dlopen_doit (a=a@entry=0x7fffffffdcb0) at dlopen.c:66
#6  0x00007ffff7de9ff4 in _dl_catch_error (objname=0x7ffff7dd9110 <last_result+16>, 
    errstring=0x7ffff7dd9118 <last_result+24>, mallocedp=0x7ffff7dd9108 <last_result+8>, 
    operate=0x7ffff7bd6fd0 <dlopen_doit>, args=0x7fffffffdcb0) at dl-error.c:187
#7  0x00007ffff7bd762d in _dlerror_run (operate=operate@entry=0x7ffff7bd6fd0 <dlopen_doit>, 
    args=args@entry=0x7fffffffdcb0) at dlerror.c:163
#8  0x00007ffff7bd70c1 in __dlopen (file=<optimized out>, mode=<optimized out>) at dlopen.c:87
#9  0x000000000040080c in main (argc=1, argv=0x7fffffffde18) at test.c:10
