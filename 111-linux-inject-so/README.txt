
NOTES:
first stoppage is due to signal: SIGSTOP
stoppage after PTRACE_SYSCALL is due to signal: SIGTRAP (see rax for syscall)

Can wait on raise(SIGTRAP) at end of .so loading stub.
