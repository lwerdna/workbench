Build everything with build.bat, in an environment where cl and link are available.
Visual Studio probably gives you a "x64 Native Tools Command Prompt for VS 2022" shortcut.

Run helloworld.exe, it should give output like:
>helloworld.exe
PID=18684 hKernel32=0x00007FFBE28D0000 hThis=0x00007FF74ED90000

In another console, run attack.exe, and the helloworld.exe console should print:
...
PID=18684 hKernel32=0x00007FFBE28D0000 hThis=0x00007FF74ED90000
mydll: DLL_PROCESS_ATTACH
mydll: DLL_PROCESS_DETACH
