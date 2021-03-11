Binary Ninja Devs @BinjaDevs · Aug 24, 2019
binja's shellcode compiler (scc) https://buff.ly/2ZjQtq2 isn't just for one or two liners, it can do some heavy lifting too - here's an example using windows COM for a BITS downloader: https://buff.ly/33MlYN2

COM and Background Intelligent Transfer Service (BITS) can be done in plain C without any help from headers and macros. Just keep an idea in your mind of what you get back from `CoCreateInstance()`:

```
    IBackgroundCopyManager     IBackgroundCopyManager_vtable
    +--------------------+     +------------------------------+
--> | .vtable            | --> | .QueryInterface // IUnknown  |
    +--------------------+     | .AddRef         // IUnknown  |
                               | .Release        // IUnknown  |
                               | .CreateJob                   |
                               | ...                          |
                               +------------------------------+
```

To compile with Visual Studio, just link against Ole32.lib: `cl /Zi bits.c Ole32.lib /Fe:bits.exe`.

To compile with [shellcode compiler](<https://scc.binary.ninja/>), use the --unloaded-modules, otherwise the compiler assumes it's running in the memory space of a process with ole32.dll and combase.dll already loaded: `scc -D SCC --unloaded-modules --arch x64 --platform windows bits.c -o bits.exe -f pe`.

I keep the source file able to compile with Visual Studio because debugging with WinDbg is so nice. Here's BITS after CoCreateInstance:

```
0:000> dqs poi(pBits)
000002ab`ff3148a8  00007fff`6aede310 BitsProxy!IBackgroundCopyManagerProxyVtbl+0x10
000002ab`ff3148b0  00000000`00000001
...
```

And here are its functions:

```
0:000> dqs poi(poi(pBits))
00007fff`6aede310  00007fff`6aed27f0 BitsProxy!IUnknown_QueryInterface_Proxy
00007fff`6aede318  00007fff`6aed27b0 BitsProxy!IUnknown_AddRef_Proxy
00007fff`6aede320  00007fff`6aed27d0 BitsProxy!IUnknown_Release_Proxy
00007fff`6aede328  00007fff`7f3e2740 combase!ObjectStublessClient3 
00007fff`6aede330  00007fff`7f3e2760 combase!ObjectStublessClient4 
00007fff`6aede338  00007fff`7f3e2780 combase!ObjectStublessClient5 
00007fff`6aede340  00007fff`7f3e27a0 combase!ObjectStublessClient6
...
```

I don't know what's up with all the "Proxy" and "StublessClient" stuff. Alright, here's the code. The only remaining challenge is generating your wchar_t URL's:
