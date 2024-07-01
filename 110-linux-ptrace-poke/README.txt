Quickly attach to a process, change a memory value, then detach.

TERMINAL A:
$ ./tracee
pid=955114 &foo=0x7fffffffe2c0 foo=deadbeefcafebabe
Press any key...

TERMINAL B:
$ ./tracer 955114 0x7fffffffe2c0 0xAAAAAAAABBBBBBBB
attaching to process pid=955114
waiting on pid=955114
reading from 0x7fffffffe2c0
read: 0xdeadbeefcafebabe
sizeof(long)==8
writing 0xaaaaaaaabbbbbbbb to 0x7fffffffe2c0
detaching from pid=955114

TERMINAL A:
$ ./tracee
id=955114 &foo=0x7fffffffe2c0 foo=deadbeefcafebabe
Press any key...
pid=955114 &foo=0x7fffffffe2c0 foo=aaaaaaaabbbbbbbb
Press any key...
