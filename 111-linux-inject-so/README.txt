injectee.c - process that gets injected
injector.c - does the injecting
injected.c - what gets injected

`make`, then in first terminal do:

$ ./injectee
Creating threads...
I'm a thread id=4 in process pid=1276799
I'm a thread id=6 in process pid=1276799

In second terminal do:

$ ./injector 1276799
(injector) libc base: 0x7ffff7c00000
(injector) address of raise(): 0x7ffff7c42460
(injector) address of dlopen(): 0x7ffff7c90680
injectee found at 0x555555554000
injectee!main at 0x55555555529d
injectee libc based at 0x7ffff7c00000
stub: 48C7C602000000488D05100000004889C748B88006C9F7FF7F0000FFD0CC2E2F696E6A65637465642E736F0090909090
attaching to process pid=1276799
...

Back in first terminal, you should see:

...
I'm a thread id=8 in process pid=1276799
I'm a thread id=7 in process pid=1276799
Hello from injected!

NOTES:
first stoppage is due to signal: SIGSTOP
stoppage after PTRACE_SYSCALL is due to signal: SIGTRAP (see rax for syscall)

Can wait on raise(SIGTRAP) at end of .so loading stub.
