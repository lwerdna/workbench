functions = [
{
    'name': 'sub_5c8',
    'description': 'int32_t sub_5c8()',
    'address': 0x5C8,
    'instructions': [
        b'\x04\xE0\x2D\xE5',                            # str     lr, [sp,  #-0x4]!
        b'\x04\xE0\x9F\xE5',                            # ldr     lr, 0x5d8
        b'\x0E\xE0\x8F\xE0',                            # add     lr, pc, lr
        b'\x08\xF0\xBE\xE5',                            # ldr     pc, [lr,  #0x8]!
    ],
    'length': 0x10
},
{
    'name': '__libc_init',
    'description': 'void __libc_init(void* raw_args, void (* onexit)(), int32_t (* main)(int32_t argc, char** argv, char** envp), void const* structors) __noreturn',
    'address': 0x5DC,
    'instructions': [
        b'\x00\xC6\x8F\xE2',                            # adr     r12, 0x5e4
        b'\x05\xCA\x8C\xE2',                            # add     r12, r12, #0x5000
        b'\xE0\xF9\xBC\xE5',                            # ldr     pc, [r12,  #0x9e0]!
    ],
    'length': 0xC
},
{
    'name': '__cxa_atexit',
    'description': 'int32_t __cxa_atexit(void (* func)(void*), void* arg, void* dso_handle)',
    'address': 0x5E8,
    'instructions': [
        b'\x00\xC6\x8F\xE2',                            # adr     r12, 0x5f0
        b'\x05\xCA\x8C\xE2',                            # add     r12, r12, #0x5000
        b'\xD8\xF9\xBC\xE5',                            # ldr     pc, [r12,  #0x9d8]!
    ],
    'length': 0xC
},
{
    'name': 'strcmp',
    'description': 'int32_t strcmp(char const* p1, char const* p2)',
    'address': 0x5F4,
    'instructions': [
        b'\x00\xC6\x8F\xE2',                            # adr     r12, 0x5fc
        b'\x05\xCA\x8C\xE2',                            # add     r12, r12, #0x5000
        b'\xD0\xF9\xBC\xE5',                            # ldr     pc, [r12,  #0x9d0]!
    ],
    'length': 0xC
},
{
    'name': 'strlen',
    'description': 'int32_t strlen()',
    'address': 0x600,
    'instructions': [
        b'\x00\xC6\x8F\xE2',                            # adr     r12, 0x608
        b'\x05\xCA\x8C\xE2',                            # add     r12, r12, #0x5000
        b'\xC8\xF9\xBC\xE5',                            # ldr     pc, [r12,  #0x9c8]!
    ],
    'length': 0xC
},
{
    'name': 'printf',
    'description': 'int32_t printf(char* arg1, char const* format, ...)',
    'address': 0x60C,
    'instructions': [
        b'\x00\xC6\x8F\xE2',                            # adr     r12, 0x614
        b'\x05\xCA\x8C\xE2',                            # add     r12, r12, #0x5000
        b'\xC0\xF9\xBC\xE5',                            # ldr     pc, [r12,  #0x9c0]!
    ],
    'length': 0xC
},
{
    'name': 'time',
    'description': 'time_t time(time_t* timer)',
    'address': 0x618,
    'instructions': [
        b'\x00\xC6\x8F\xE2',                            # adr     r12, 0x620
        b'\x05\xCA\x8C\xE2',                            # add     r12, r12, #0x5000
        b'\xB8\xF9\xBC\xE5',                            # ldr     pc, [r12,  #0x9b8]!
    ],
    'length': 0xC
},
{
    'name': 'fopen',
    'description': 'FILE* fopen(char const* filename, char const* mode)',
    'address': 0x624,
    'instructions': [
        b'\x00\xC6\x8F\xE2',                            # adr     r12, 0x62c
        b'\x05\xCA\x8C\xE2',                            # add     r12, r12, #0x5000
        b'\xB0\xF9\xBC\xE5',                            # ldr     pc, [r12,  #0x9b0]!
    ],
    'length': 0xC
},
{
    'name': 'fread',
    'description': 'size_t fread(void* buf, size_t size, size_t count, FILE* fp)',
    'address': 0x630,
    'instructions': [
        b'\x00\xC6\x8F\xE2',                            # adr     r12, 0x638
        b'\x05\xCA\x8C\xE2',                            # add     r12, r12, #0x5000
        b'\xA8\xF9\xBC\xE5',                            # ldr     pc, [r12,  #0x9a8]!
    ],
    'length': 0xC
},
{
    'name': 'fclose',
    'description': 'int32_t fclose(FILE* fp)',
    'address': 0x63C,
    'instructions': [
        b'\x00\xC6\x8F\xE2',                            # adr     r12, 0x644
        b'\x05\xCA\x8C\xE2',                            # add     r12, r12, #0x5000
        b'\xA0\xF9\xBC\xE5',                            # ldr     pc, [r12,  #0x9a0]!
    ],
    'length': 0xC
},
{
    'name': 'raise',
    'description': 'int32_t raise(int32_t sig)',
    'address': 0x648,
    'instructions': [
        b'\x00\xC6\x8F\xE2',                            # adr     r12, 0x650
        b'\x05\xCA\x8C\xE2',                            # add     r12, r12, #0x5000
        b'\x98\xF9\xBC\xE5',                            # ldr     pc, [r12,  #0x998]!
    ],
    'length': 0xC
},
{
    'name': '__gnu_Unwind_Find_exidx',
    'description': '_Unwind_Ptr __gnu_Unwind_Find_exidx(_Unwind_Ptr pc, int32_t* pcount)',
    'address': 0x654,
    'instructions': [
        b'\x00\xC6\x8F\xE2',                            # adr     r12, 0x65c
        b'\x05\xCA\x8C\xE2',                            # add     r12, r12, #0x5000
        b'\x90\xF9\xBC\xE5',                            # ldr     pc, [r12,  #0x990]!
    ],
    'length': 0xC
},
{
    'name': 'abort',
    'description': 'void abort() __noreturn',
    'address': 0x660,
    'instructions': [
        b'\x00\xC6\x8F\xE2',                            # adr     r12, 0x668
        b'\x05\xCA\x8C\xE2',                            # add     r12, r12, #0x5000
        b'\x88\xF9\xBC\xE5',                            # ldr     pc, [r12,  #0x988]!
    ],
    'length': 0xC
},
{
    'name': 'memcpy',
    'description': 'int32_t memcpy()',
    'address': 0x66C,
    'instructions': [
        b'\x00\xC6\x8F\xE2',                            # adr     r12, 0x674
        b'\x05\xCA\x8C\xE2',                            # add     r12, r12, #0x5000
        b'\x80\xF9\xBC\xE5',                            # ldr     pc, [r12,  #0x980]!
    ],
    'length': 0xC
},
{
    'name': '__cxa_begin_cleanup',
    'description': 'int32_t __cxa_begin_cleanup()',
    'address': 0x678,
    'instructions': [
        b'\x00\xC6\x8F\xE2',                            # adr     r12, 0x680
        b'\x05\xCA\x8C\xE2',                            # add     r12, r12, #0x5000
        b'\x78\xF9\xBC\xE5',                            # ldr     pc, [r12,  #0x978]!
    ],
    'length': 0xC
},
{
    'name': '__cxa_type_match',
    'description': 'int32_t __cxa_type_match()',
    'address': 0x684,
    'instructions': [
        b'\x00\xC6\x8F\xE2',                            # adr     r12, 0x68c
        b'\x05\xCA\x8C\xE2',                            # add     r12, r12, #0x5000
        b'\x70\xF9\xBC\xE5',                            # ldr     pc, [r12,  #0x970]!
    ],
    'length': 0xC
},
{
    'name': '_start',
    'description': 'int32_t _start() __noreturn',
    'address': 0x690,
    'instructions': [
        b'\x0D\x00\xA0\xE1',                            # mov     r0, sp
        b'\xFF\xFF\xFF\xEA',                            # b       0x698
    ],
    'length': 0x8
},
{
    'name': '_start_main',
    'description': 'int32_t _start_main(void* arg1) __noreturn',
    'address': 0x698,
    'instructions': [
        b'\x00\x48\x2D\xE9',                            # push    {r11, lr}
        b'\x0D\xB0\xA0\xE1',                            # mov     r11, sp
        b'\x10\xD0\x4D\xE2',                            # sub     sp, sp, #0x10
        b'\x30\x10\x9F\xE5',                            # ldr     r1, 0x6dc
        b'\x04\x30\x8D\xE2',                            # add     r3, sp, #0x4
        b'\x01\x10\x9F\xE7',                            # ldr     r1, [pc, r1]
        b'\x0C\x10\x8D\xE5',                            # str     r1, [sp,  #0xc]
        b'\x24\x10\x9F\xE5',                            # ldr     r1, 0x6e0
        b'\x01\x10\x9F\xE7',                            # ldr     r1, [pc, r1]
        b'\x08\x10\x8D\xE5',                            # str     r1, [sp,  #0x8]
        b'\x1C\x10\x9F\xE5',                            # ldr     r1, 0x6e4
        b'\x01\x10\x9F\xE7',                            # ldr     r1, [pc, r1]
        b'\x04\x10\x8D\xE5',                            # str     r1, [sp,  #0x4]
        b'\x00\x10\xA0\xE3',                            # mov     r1, #0
        b'\x10\x20\x9F\xE5',                            # ldr     r2, 0x6e8
        b'\x02\x20\x9F\xE7',                            # ldr     r2, [pc, r2]
        b'\xBF\xFF\xFF\xEB',                            # bl      0x5dc
    ],
    'length': 0x44
},
{
    'name': '__atexit_handler_wrapper',
    'description': 'void __atexit_handler_wrapper(void* arg1)',
    'address': 0x6EC,
    'instructions': [
        b'\x00\x00\x50\xE3',                            # cmp     r0, #0
        b'\x1E\xFF\x2F\x01',                            # bxeq    lr
        b'\x10\xFF\x2F\xE1',                            # bx      r0
    ],
    'length': 0xC
},
{
    'name': 'atexit',
    'description': 'int32_t atexit(void* arg1)',
    'address': 0x6F8,
    'instructions': [
        b'\x00\x10\xA0\xE1',                            # mov     r1, r0
        b'\x0C\x00\x9F\xE5',                            # ldr     r0, 0x710
        b'\x0C\x20\x9F\xE5',                            # ldr     r2, 0x714
        b'\x00\x00\x8F\xE0',                            # add     r0, pc, r0
        b'\x02\x20\x8F\xE0',                            # add     r2, pc, r2
        b'\xB5\xFF\xFF\xEA',                            # b       0x5e8
    ],
    'length': 0x18
},
{
    'name': 'main',
    'description': 'int32_t main(int32_t argc, char** argv, char** envp)',
    'address': 0x718,
    'instructions': [
        b'\x00\x48\x2D\xE9',                            # push    {r11, lr}
        b'\x0D\xB0\xA0\xE1',                            # mov     r11, sp
        b'\x10\xD0\x4D\xE2',                            # sub     sp, sp, #0x10
        b'\x00\x20\x00\xE3',                            # movw    r2, #0
        b'\x04\x20\x0B\xE5',                            # str     r2, [r11,  #-0x4]
        b'\x08\x00\x8D\xE5',                            # str     r0, [sp,  #0x8]
        b'\x04\x10\x8D\xE5',                            # str     r1, [sp,  #0x4]
        b'\x08\x00\x9D\xE5',                            # ldr     r0, [sp,  #0x8]
        b'\x01\x00\x50\xE3',                            # cmp     r0, #0x1
        b'\x3D\x00\x00\xDA',                            # ble     0x838
        b'\x01\x00\x00\xE3',                            # movw    r0, #0x1
        b'\x00\x00\x8D\xE5',                            # str     r0, [sp]
        b'\x00\x00\x9D\xE5',                            # ldr     r0, [sp]
        b'\x08\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x8]
        b'\x01\x00\x50\xE1',                            # cmp     r0, r1
        b'\x36\x00\x00\xAA',                            # bge     0x834
        b'\x04\x00\x9D\xE5',                            # ldr     r0, [sp,  #0x4]
        b'\x00\x10\x9D\xE5',                            # ldr     r1, [sp]
        b'\x01\x01\x80\xE0',                            # add     r0, r0, r1, lsl  #0x2
        b'\x00\x00\x90\xE5',                            # ldr     r0, [r0]
        b'\x00\x00\xD0\xE5',                            # ldrb    r0, [r0]
        b'\x2D\x00\x50\xE3',                            # cmp     r0, #0x2d
        b'\x0D\x00\x00\x1A',                            # bne     0x7ac
        b'\x04\x00\x9D\xE5',                            # ldr     r0, [sp,  #0x4]
        b'\x00\x10\x9D\xE5',                            # ldr     r1, [sp]
        b'\x01\x01\x80\xE0',                            # add     r0, r0, r1, lsl  #0x2
        b'\x00\x00\x90\xE5',                            # ldr     r0, [r0]
        b'\x01\x00\xD0\xE5',                            # ldrb    r0, [r0,  #0x1]
        b'\x73\x00\x50\xE3',                            # cmp     r0, #0x73
        b'\x06\x00\x00\x1A',                            # bne     0x7ac
        b'\x04\x00\x9D\xE5',                            # ldr     r0, [sp,  #0x4]
        b'\x00\x10\x9D\xE5',                            # ldr     r1, [sp]
        b'\x01\x01\x80\xE0',                            # add     r0, r0, r1, lsl  #0x2
        b'\x00\x00\x90\xE5',                            # ldr     r0, [r0]
        b'\x02\x00\x80\xE2',                            # add     r0, r0, #0x2
        b'\x29\x00\x00\xEB',                            # bl      0x850
        b'\x1C\x00\x00\xEA',                            # b       0x820
        b'\x04\x00\x9D\xE5',                            # ldr     r0, [sp,  #0x4]
        b'\x00\x10\x9D\xE5',                            # ldr     r1, [sp]
        b'\x01\x01\x80\xE0',                            # add     r0, r0, r1, lsl  #0x2
        b'\x00\x00\x90\xE5',                            # ldr     r0, [r0]
        b'\x84\x10\x9F\xE5',                            # ldr     r1, 0x848
        b'\x01\x10\x8F\xE0',                            # add     r1, pc, r1
        b'\x8A\xFF\xFF\xEB',                            # bl      0x5f4
        b'\x00\x00\x50\xE3',                            # cmp     r0, #0
        b'\x01\x00\x00\x1A',                            # bne     0x7d8
        b'\x66\x00\x00\xEB',                            # bl      0x970
        b'\x10\x00\x00\xEA',                            # b       0x81c
        b'\x04\x00\x9D\xE5',                            # ldr     r0, [sp,  #0x4]
        b'\x00\x10\x9D\xE5',                            # ldr     r1, [sp]
        b'\x01\x01\x80\xE0',                            # add     r0, r0, r1, lsl  #0x2
        b'\x00\x00\x90\xE5',                            # ldr     r0, [r0]
        b'\x5C\x10\x9F\xE5',                            # ldr     r1, 0x84c
        b'\x01\x10\x8F\xE0',                            # add     r1, pc, r1
        b'\x7F\xFF\xFF\xEB',                            # bl      0x5f4
        b'\x00\x00\x50\xE3',                            # cmp     r0, #0
        b'\x01\x00\x00\x1A',                            # bne     0x804
        b'\xC8\x00\x00\xEB',                            # bl      0xb24
        b'\x04\x00\x00\xEA',                            # b       0x818
        b'\x04\x00\x9D\xE5',                            # ldr     r0, [sp,  #0x4]
        b'\x00\x10\x9D\xE5',                            # ldr     r1, [sp]
        b'\x01\x01\x80\xE0',                            # add     r0, r0, r1, lsl  #0x2
        b'\x00\x00\x90\xE5',                            # ldr     r0, [r0]
        b'\xEA\x00\x00\xEB',                            # bl      0xbc4
        b'\xFF\xFF\xFF\xEA',                            # b       0x81c
        b'\xFF\xFF\xFF\xEA',                            # b       0x820
        b'\xFF\xFF\xFF\xEA',                            # b       0x824
        b'\x00\x00\x9D\xE5',                            # ldr     r0, [sp]
        b'\x01\x00\x80\xE2',                            # add     r0, r0, #0x1
        b'\x00\x00\x8D\xE5',                            # str     r0, [sp]
        b'\xC4\xFF\xFF\xEA',                            # b       0x748
        b'\x00\x00\x00\xEA',                            # b       0x83c
        b'\x2D\x01\x00\xEB',                            # bl      0xcf4
        b'\x00\x00\x00\xE3',                            # movw    r0, #0
        b'\x0B\xD0\xA0\xE1',                            # mov     sp, r11
        b'\x00\x88\xBD\xE8',                            # pop     {r11, pc}
    ],
    'length': 0x130
},
{
    'name': 'MDString',
    'description': 'int32_t MDString(void* arg1)',
    'address': 0x850,
    'instructions': [
        b'\x00\x48\x2D\xE9',                            # push    {r11, lr}
        b'\x0D\xB0\xA0\xE1',                            # mov     r11, sp
        b'\x80\xD0\x4D\xE2',                            # sub     sp, sp, #0x80
        b'\xAC\x10\x9F\xE5',                            # ldr     r1, 0x910
        b'\x01\x10\x9F\xE7',                            # ldr     r1, [pc, r1]
        b'\x04\x00\x0B\xE5',                            # str     r0, [r11,  #-0x4]
        b'\x04\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x4]
        b'\x0C\x10\x8D\xE5',                            # str     r1, [sp,  #0xc]
        b'\x62\xFF\xFF\xEB',                            # bl      0x600
        b'\x10\x00\x8D\xE5',                            # str     r0, [sp,  #0x10]
        b'\x24\x00\x8D\xE2',                            # add     r0, sp, #0x24
        b'\x0C\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xc]
        b'\x31\xFF\x2F\xE1',                            # blx     r1
        b'\x80\x00\x9F\xE5',                            # ldr     r0, 0x90c
        b'\x00\x00\x9F\xE7',                            # ldr     r0, [pc, r0]
        b'\x04\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x4]
        b'\x10\x20\x9D\xE5',                            # ldr     r2, [sp,  #0x10]
        b'\x24\x30\x8D\xE2',                            # add     r3, sp, #0x24
        b'\x08\x00\x8D\xE5',                            # str     r0, [sp,  #0x8]
        b'\x03\x00\xA0\xE1',                            # mov     r0, r3
        b'\x08\x30\x9D\xE5',                            # ldr     r3, [sp,  #0x8]
        b'\x33\xFF\x2F\xE1',                            # blx     r3
        b'\x58\x00\x9F\xE5',                            # ldr     r0, 0x908
        b'\x00\x00\x9F\xE7',                            # ldr     r0, [pc, r0]
        b'\x14\x10\x8D\xE2',                            # add     r1, sp, #0x14
        b'\x04\x00\x8D\xE5',                            # str     r0, [sp,  #0x4]
        b'\x01\x00\xA0\xE1',                            # mov     r0, r1
        b'\x24\x10\x8D\xE2',                            # add     r1, sp, #0x24
        b'\x04\x20\x9D\xE5',                            # ldr     r2, [sp,  #0x4]
        b'\x32\xFF\x2F\xE1',                            # blx     r2
        b'\x34\x00\x9F\xE5',                            # ldr     r0, 0x904
        b'\x00\x00\x8F\xE0',                            # add     r0, pc, r0
        b'\x04\x20\x1B\xE5',                            # ldr     r2, [r11,  #-0x4]
        b'\x05\x10\x00\xE3',                            # movw    r1, #0x5
        b'\x4B\xFF\xFF\xEB',                            # bl      0x60c
        b'\x14\x10\x8D\xE2',                            # add     r1, sp, #0x14
        b'\x00\x00\x8D\xE5',                            # str     r0, [sp]
        b'\x01\x00\xA0\xE1',                            # mov     r0, r1
        b'\x09\x00\x00\xEB',                            # bl      0x914
        b'\x0C\x00\x9F\xE5',                            # ldr     r0, 0x900
        b'\x00\x00\x8F\xE0',                            # add     r0, pc, r0
        b'\x44\xFF\xFF\xEB',                            # bl      0x60c
        b'\x0B\xD0\xA0\xE1',                            # mov     sp, r11
        b'\x00\x88\xBD\xE8',                            # pop     {r11, pc}
    ],
    'length': 0xB0
},
{
    'name': 'MDPrint',
    'description': 'int32_t MDPrint(void* arg1)',
    'address': 0x914,
    'instructions': [
        b'\x00\x48\x2D\xE9',                            # push    {r11, lr}
        b'\x0D\xB0\xA0\xE1',                            # mov     r11, sp
        b'\x08\xD0\x4D\xE2',                            # sub     sp, sp, #0x8
        b'\x04\x00\x8D\xE5',                            # str     r0, [sp,  #0x4]
        b'\x00\x00\x00\xE3',                            # movw    r0, #0
        b'\x00\x00\x8D\xE5',                            # str     r0, [sp]
        b'\x00\x00\x9D\xE5',                            # ldr     r0, [sp]
        b'\x10\x00\x50\xE3',                            # cmp     r0, #0x10
        b'\x0A\x00\x00\x2A',                            # bhs     0x964
        b'\x2C\x00\x9F\xE5',                            # ldr     r0, 0x96c
        b'\x00\x00\x8F\xE0',                            # add     r0, pc, r0
        b'\x04\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x4]
        b'\x00\x20\x9D\xE5',                            # ldr     r2, [sp]
        b'\x02\x10\x81\xE0',                            # add     r1, r1, r2
        b'\x00\x10\xD1\xE5',                            # ldrb    r1, [r1]
        b'\x2D\xFF\xFF\xEB',                            # bl      0x60c
        b'\x00\x00\x9D\xE5',                            # ldr     r0, [sp]
        b'\x01\x00\x80\xE2',                            # add     r0, r0, #0x1
        b'\x00\x00\x8D\xE5',                            # str     r0, [sp]
        b'\xF1\xFF\xFF\xEA',                            # b       0x92c
        b'\x0B\xD0\xA0\xE1',                            # mov     sp, r11
        b'\x00\x88\xBD\xE8',                            # pop     {r11, pc}
    ],
    'length': 0x58
},
{
    'name': 'MDTimeTrial',
    'description': 'int32_t MDTimeTrial()',
    'address': 0x970,
    'instructions': [
        b'\x30\x48\x2D\xE9',                            # push    {r4, r5, r11, lr}
        b'\x08\xB0\x8D\xE2',                            # add     r11, sp, #0x8
        b'\x88\xD0\x4D\xE2',                            # sub     sp, sp, #0x88
        b'\x01\xDB\x4D\xE2',                            # sub     sp, sp, #0x400
        b'\x78\x01\x9F\xE5',                            # ldr     r0, 0xb00
        b'\x00\x00\x8F\xE0',                            # add     r0, pc, r0
        b'\x05\x10\x00\xE3',                            # movw    r1, #0x5
        b'\xE8\x23\x00\xE3',                            # movw    r2, #0x3e8
        b'\x28\x20\x8D\xE5',                            # str     r2, [sp,  #0x28]
        b'\x28\x30\x9D\xE5',                            # ldr     r3, [sp,  #0x28]
        b'\x1B\xFF\xFF\xEB',                            # bl      0x60c
        b'\x00\x10\x00\xE3',                            # movw    r1, #0
        b'\x2C\x10\x8D\xE5',                            # str     r1, [sp,  #0x2c]
        b'\x2C\x00\x9D\xE5',                            # ldr     r0, [sp,  #0x2c]
        b'\xFA\x0F\x50\xE3',                            # cmp     r0, #0x3e8
        b'\x09\x00\x00\x2A',                            # bhs     0x9d8
        b'\x2C\x00\x9D\xE5',                            # ldr     r0, [sp,  #0x2c]
        b'\xFF\x00\x00\xE2',                            # and     r0, r0, #0xff
        b'\x2C\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x2c]
        b'\x40\x20\x8D\xE2',                            # add     r2, sp, #0x40
        b'\x01\x10\x82\xE0',                            # add     r1, r2, r1
        b'\x00\x00\xC1\xE5',                            # strb    r0, [r1]
        b'\x2C\x00\x9D\xE5',                            # ldr     r0, [sp,  #0x2c]
        b'\x01\x00\x80\xE2',                            # add     r0, r0, #0x1
        b'\x2C\x00\x8D\xE5',                            # str     r0, [sp,  #0x2c]
        b'\xF2\xFF\xFF\xEA',                            # b       0x9a4
        b'\x68\x00\x4B\xE2',                            # sub     r0, r11, #0x68
        b'\x0D\xFF\xFF\xEB',                            # bl      0x618
        b'\x1C\x11\x9F\xE5',                            # ldr     r1, 0xb04
        b'\x01\x10\x9F\xE7',                            # ldr     r1, [pc, r1]
        b'\x60\x20\x4B\xE2',                            # sub     r2, r11, #0x60
        b'\x24\x00\x8D\xE5',                            # str     r0, [sp,  #0x24]
        b'\x02\x00\xA0\xE1',                            # mov     r0, r2
        b'\x31\xFF\x2F\xE1',                            # blx     r1
        b'\x00\x00\x00\xE3',                            # movw    r0, #0
        b'\x2C\x00\x8D\xE5',                            # str     r0, [sp,  #0x2c]
        b'\x2C\x00\x9D\xE5',                            # ldr     r0, [sp,  #0x2c]
        b'\xFA\x0F\x50\xE3',                            # cmp     r0, #0x3e8
        b'\x0C\x00\x00\x2A',                            # bhs     0xa40
        b'\x0C\x01\x9F\xE5',                            # ldr     r0, 0xb20
        b'\x00\x00\x9F\xE7',                            # ldr     r0, [pc, r0]
        b'\x40\x10\x8D\xE2',                            # add     r1, sp, #0x40
        b'\x60\x20\x4B\xE2',                            # sub     r2, r11, #0x60
        b'\x20\x00\x8D\xE5',                            # str     r0, [sp,  #0x20]
        b'\x02\x00\xA0\xE1',                            # mov     r0, r2
        b'\xE8\x23\x00\xE3',                            # movw    r2, #0x3e8
        b'\x20\x30\x9D\xE5',                            # ldr     r3, [sp,  #0x20]
        b'\x33\xFF\x2F\xE1',                            # blx     r3
        b'\x2C\x00\x9D\xE5',                            # ldr     r0, [sp,  #0x2c]
        b'\x01\x00\x80\xE2',                            # add     r0, r0, #0x1
        b'\x2C\x00\x8D\xE5',                            # str     r0, [sp,  #0x2c]
        b'\xEF\xFF\xFF\xEA',                            # b       0xa00
        b'\xD4\x00\x9F\xE5',                            # ldr     r0, 0xb1c
        b'\x00\x00\x9F\xE7',                            # ldr     r0, [pc, r0]
        b'\x30\x10\x8D\xE2',                            # add     r1, sp, #0x30
        b'\x1C\x00\x8D\xE5',                            # str     r0, [sp,  #0x1c]
        b'\x01\x00\xA0\xE1',                            # mov     r0, r1
        b'\x60\x10\x4B\xE2',                            # sub     r1, r11, #0x60
        b'\x1C\x20\x9D\xE5',                            # ldr     r2, [sp,  #0x1c]
        b'\x32\xFF\x2F\xE1',                            # blx     r2
        b'\x64\x00\x4B\xE2',                            # sub     r0, r11, #0x64
        b'\xEB\xFE\xFF\xEB',                            # bl      0x618
        b'\xA8\x10\x9F\xE5',                            # ldr     r1, 0xb18
        b'\x01\x10\x8F\xE0',                            # add     r1, pc, r1
        b'\x18\x00\x8D\xE5',                            # str     r0, [sp,  #0x18]
        b'\x01\x00\xA0\xE1',                            # mov     r0, r1
        b'\xE3\xFE\xFF\xEB',                            # bl      0x60c
        b'\x90\x10\x9F\xE5',                            # ldr     r1, 0xb14
        b'\x01\x10\x8F\xE0',                            # add     r1, pc, r1
        b'\x14\x00\x8D\xE5',                            # str     r0, [sp,  #0x14]
        b'\x01\x00\xA0\xE1',                            # mov     r0, r1
        b'\xDE\xFE\xFF\xEB',                            # bl      0x60c
        b'\x30\x10\x8D\xE2',                            # add     r1, sp, #0x30
        b'\x10\x00\x8D\xE5',                            # str     r0, [sp,  #0x10]
        b'\x01\x00\xA0\xE1',                            # mov     r0, r1
        b'\x9C\xFF\xFF\xEB',                            # bl      0x914
        b'\x68\x00\x9F\xE5',                            # ldr     r0, 0xb10
        b'\x00\x00\x8F\xE0',                            # add     r0, pc, r0
        b'\x64\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x64]
        b'\x68\x20\x1B\xE5',                            # ldr     r2, [r11,  #-0x68]
        b'\x02\x10\x41\xE0',                            # sub     r1, r1, r2
        b'\xD4\xFE\xFF\xEB',                            # bl      0x60c
        b'\x48\x10\x9F\xE5',                            # ldr     r1, 0xb08
        b'\x01\x10\x8F\xE0',                            # add     r1, pc, r1
        b'\x44\x20\x9F\xE5',                            # ldr     r2, 0xb0c
        b'\x64\x30\x1B\xE5',                            # ldr     r3, [r11,  #-0x64]
        b'\x68\xC0\x1B\xE5',                            # ldr     r12, [r11,  #-0x68]
        b'\x0C\x30\x43\xE0',                            # sub     r3, r3, r12
        b'\x0C\x00\x8D\xE5',                            # str     r0, [sp,  #0xc]
        b'\x02\x00\xA0\xE1',                            # mov     r0, r2
        b'\x08\x10\x8D\xE5',                            # str     r1, [sp,  #0x8]
        b'\x03\x10\xA0\xE1',                            # mov     r1, r3
        b'\x41\x09\x00\xEB',                            # bl      0x2fec
        b'\x08\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x8]
        b'\x04\x00\x8D\xE5',                            # str     r0, [sp,  #0x4]
        b'\x01\x00\xA0\xE1',                            # mov     r0, r1
        b'\x04\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x4]
        b'\xC4\xFE\xFF\xEB',                            # bl      0x60c
        b'\x08\xD0\x4B\xE2',                            # sub     sp, r11, #0x8
        b'\x30\x88\xBD\xE8',                            # pop     {r4, r5, r11, pc}
    ],
    'length': 0x190
},
{
    'name': 'MDTestSuite',
    'description': 'int32_t MDTestSuite()',
    'address': 0xB24,
    'instructions': [
        b'\x00\x48\x2D\xE9',                            # push    {r11, lr}
        b'\x0D\xB0\xA0\xE1',                            # mov     r11, sp
        b'\x08\xD0\x4D\xE2',                            # sub     sp, sp, #0x8
        b'\x88\x00\x9F\xE5',                            # ldr     r0, 0xbc0
        b'\x00\x00\x8F\xE0',                            # add     r0, pc, r0
        b'\x05\x10\x00\xE3',                            # movw    r1, #0x5
        b'\xB2\xFE\xFF\xEB',                            # bl      0x60c
        b'\x74\x10\x9F\xE5',                            # ldr     r1, 0xbbc
        b'\x01\x10\x8F\xE0',                            # add     r1, pc, r1
        b'\x04\x00\x8D\xE5',                            # str     r0, [sp,  #0x4]
        b'\x01\x00\xA0\xE1',                            # mov     r0, r1
        b'\x3E\xFF\xFF\xEB',                            # bl      0x850
        b'\x5C\x00\x9F\xE5',                            # ldr     r0, 0xbb8
        b'\x00\x00\x8F\xE0',                            # add     r0, pc, r0
        b'\x3B\xFF\xFF\xEB',                            # bl      0x850
        b'\x4C\x00\x9F\xE5',                            # ldr     r0, 0xbb4
        b'\x00\x00\x8F\xE0',                            # add     r0, pc, r0
        b'\x38\xFF\xFF\xEB',                            # bl      0x850
        b'\x3C\x00\x9F\xE5',                            # ldr     r0, 0xbb0
        b'\x00\x00\x8F\xE0',                            # add     r0, pc, r0
        b'\x35\xFF\xFF\xEB',                            # bl      0x850
        b'\x2C\x00\x9F\xE5',                            # ldr     r0, 0xbac
        b'\x00\x00\x8F\xE0',                            # add     r0, pc, r0
        b'\x32\xFF\xFF\xEB',                            # bl      0x850
        b'\x1C\x00\x9F\xE5',                            # ldr     r0, 0xba8
        b'\x00\x00\x8F\xE0',                            # add     r0, pc, r0
        b'\x2F\xFF\xFF\xEB',                            # bl      0x850
        b'\x0C\x00\x9F\xE5',                            # ldr     r0, 0xba4
        b'\x00\x00\x8F\xE0',                            # add     r0, pc, r0
        b'\x2C\xFF\xFF\xEB',                            # bl      0x850
        b'\x0B\xD0\xA0\xE1',                            # mov     sp, r11
        b'\x00\x88\xBD\xE8',                            # pop     {r11, pc}
    ],
    'length': 0x80
},
{
    'name': 'MDFile',
    'description': 'int32_t MDFile(char* arg1)',
    'address': 0xBC4,
    'instructions': [
        b'\x30\x48\x2D\xE9',                            # push    {r4, r5, r11, lr}
        b'\x08\xB0\x8D\xE2',                            # add     r11, sp, #0x8
        b'\x88\xD0\x4D\xE2',                            # sub     sp, sp, #0x88
        b'\x01\xDB\x4D\xE2',                            # sub     sp, sp, #0x400
        b'\xFC\x10\x9F\xE5',                            # ldr     r1, 0xcd8
        b'\x01\x10\x8F\xE0',                            # add     r1, pc, r1
        b'\x0C\x00\x0B\xE5',                            # str     r0, [r11,  #-0xc]
        b'\x0C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0xc]
        b'\x8E\xFE\xFF\xEB',                            # bl      0x624
        b'\x10\x00\x0B\xE5',                            # str     r0, [r11,  #-0x10]
        b'\x00\x10\x00\xE3',                            # movw    r1, #0
        b'\x01\x00\x50\xE1',                            # cmp     r0, r1
        b'\x04\x00\x00\x1A',                            # bne     0xc0c
        b'\xF0\x00\x9F\xE5',                            # ldr     r0, 0xcf0
        b'\x00\x00\x8F\xE0',                            # add     r0, pc, r0
        b'\x0C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xc]
        b'\x80\xFE\xFF\xEB',                            # bl      0x60c
        b'\x30\x00\x00\xEA',                            # b       0xcd0
        b'\xC8\x00\x9F\xE5',                            # ldr     r0, 0xcdc
        b'\x00\x00\x9F\xE7',                            # ldr     r0, [pc, r0]
        b'\x68\x10\x4B\xE2',                            # sub     r1, r11, #0x68
        b'\x10\x00\x8D\xE5',                            # str     r0, [sp,  #0x10]
        b'\x01\x00\xA0\xE1',                            # mov     r0, r1
        b'\x10\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x10]
        b'\x31\xFF\x2F\xE1',                            # blx     r1
        b'\x24\x00\x8D\xE2',                            # add     r0, sp, #0x24
        b'\x10\x30\x1B\xE5',                            # ldr     r3, [r11,  #-0x10]
        b'\x01\x10\x00\xE3',                            # movw    r1, #0x1
        b'\x00\x24\x00\xE3',                            # movw    r2, #0x400
        b'\x7C\xFE\xFF\xEB',                            # bl      0x630
        b'\x6C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x6c]
        b'\x00\x00\x50\xE3',                            # cmp     r0, #0
        b'\x09\x00\x00\x0A',                            # beq     0xc70
        b'\x9C\x00\x9F\xE5',                            # ldr     r0, 0xcec
        b'\x00\x00\x9F\xE7',                            # ldr     r0, [pc, r0]
        b'\x24\x10\x8D\xE2',                            # add     r1, sp, #0x24
        b'\x6C\x20\x1B\xE5',                            # ldr     r2, [r11,  #-0x6c]
        b'\x68\x30\x4B\xE2',                            # sub     r3, r11, #0x68
        b'\x0C\x00\x8D\xE5',                            # str     r0, [sp,  #0xc]
        b'\x03\x00\xA0\xE1',                            # mov     r0, r3
        b'\x0C\x30\x9D\xE5',                            # ldr     r3, [sp,  #0xc]
        b'\x33\xFF\x2F\xE1',                            # blx     r3
        b'\xED\xFF\xFF\xEA',                            # b       0xc28
        b'\x70\x00\x9F\xE5',                            # ldr     r0, 0xce8
        b'\x00\x00\x9F\xE7',                            # ldr     r0, [pc, r0]
        b'\x14\x10\x8D\xE2',                            # add     r1, sp, #0x14
        b'\x08\x00\x8D\xE5',                            # str     r0, [sp,  #0x8]
        b'\x01\x00\xA0\xE1',                            # mov     r0, r1
        b'\x68\x10\x4B\xE2',                            # sub     r1, r11, #0x68
        b'\x08\x20\x9D\xE5',                            # ldr     r2, [sp,  #0x8]
        b'\x32\xFF\x2F\xE1',                            # blx     r2
        b'\x10\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x10]
        b'\x68\xFE\xFF\xEB',                            # bl      0x63c
        b'\x44\x10\x9F\xE5',                            # ldr     r1, 0xce4
        b'\x01\x10\x8F\xE0',                            # add     r1, pc, r1
        b'\x0C\x20\x1B\xE5',                            # ldr     r2, [r11,  #-0xc]
        b'\x04\x00\x8D\xE5',                            # str     r0, [sp,  #0x4]
        b'\x01\x00\xA0\xE1',                            # mov     r0, r1
        b'\x05\x10\x00\xE3',                            # movw    r1, #0x5
        b'\x55\xFE\xFF\xEB',                            # bl      0x60c
        b'\x14\x10\x8D\xE2',                            # add     r1, sp, #0x14
        b'\x00\x00\x8D\xE5',                            # str     r0, [sp]
        b'\x01\x00\xA0\xE1',                            # mov     r0, r1
        b'\x13\xFF\xFF\xEB',                            # bl      0x914
        b'\x14\x00\x9F\xE5',                            # ldr     r0, 0xce0
        b'\x00\x00\x8F\xE0',                            # add     r0, pc, r0
        b'\x4E\xFE\xFF\xEB',                            # bl      0x60c
        b'\x08\xD0\x4B\xE2',                            # sub     sp, r11, #0x8
        b'\x30\x88\xBD\xE8',                            # pop     {r4, r5, r11, pc}
    ],
    'length': 0x114
},
{
    'name': 'MDFilter',
    'description': 'int32_t MDFilter()',
    'address': 0xCF4,
    'instructions': [
        b'\x00\x48\x2D\xE9',                            # push    {r11, lr}
        b'\x0D\xB0\xA0\xE1',                            # mov     r11, sp
        b'\x88\xD0\x4D\xE2',                            # sub     sp, sp, #0x88
        b'\x9C\x00\x9F\xE5',                            # ldr     r0, 0xda4
        b'\x00\x00\x9F\xE7',                            # ldr     r0, [pc, r0]
        b'\x30\x10\x8D\xE2',                            # add     r1, sp, #0x30
        b'\x08\x00\x8D\xE5',                            # str     r0, [sp,  #0x8]
        b'\x01\x00\xA0\xE1',                            # mov     r0, r1
        b'\x08\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x8]
        b'\x31\xFF\x2F\xE1',                            # blx     r1
        b'\x84\x00\x9F\xE5',                            # ldr     r0, 0xda8
        b'\x00\x30\x9F\xE7',                            # ldr     r3, [pc, r0]
        b'\x1C\x00\x8D\xE2',                            # add     r0, sp, #0x1c
        b'\x01\x10\x00\xE3',                            # movw    r1, #0x1
        b'\x10\x20\x00\xE3',                            # movw    r2, #0x10
        b'\x3E\xFE\xFF\xEB',                            # bl      0x630
        b'\x2C\x00\x8D\xE5',                            # str     r0, [sp,  #0x2c]
        b'\x00\x00\x50\xE3',                            # cmp     r0, #0
        b'\x09\x00\x00\x0A',                            # beq     0xd68
        b'\x6C\x00\x9F\xE5',                            # ldr     r0, 0xdb4
        b'\x00\x00\x9F\xE7',                            # ldr     r0, [pc, r0]
        b'\x1C\x10\x8D\xE2',                            # add     r1, sp, #0x1c
        b'\x2C\x20\x9D\xE5',                            # ldr     r2, [sp,  #0x2c]
        b'\x30\x30\x8D\xE2',                            # add     r3, sp, #0x30
        b'\x04\x00\x8D\xE5',                            # str     r0, [sp,  #0x4]
        b'\x03\x00\xA0\xE1',                            # mov     r0, r3
        b'\x04\x30\x9D\xE5',                            # ldr     r3, [sp,  #0x4]
        b'\x33\xFF\x2F\xE1',                            # blx     r3
        b'\xEC\xFF\xFF\xEA',                            # b       0xd1c
        b'\x40\x00\x9F\xE5',                            # ldr     r0, 0xdb0
        b'\x00\x00\x9F\xE7',                            # ldr     r0, [pc, r0]
        b'\x0C\x10\x8D\xE2',                            # add     r1, sp, #0xc
        b'\x00\x00\x8D\xE5',                            # str     r0, [sp]
        b'\x01\x00\xA0\xE1',                            # mov     r0, r1
        b'\x30\x10\x8D\xE2',                            # add     r1, sp, #0x30
        b'\x00\x20\x9D\xE5',                            # ldr     r2, [sp]
        b'\x32\xFF\x2F\xE1',                            # blx     r2
        b'\x0C\x00\x8D\xE2',                            # add     r0, sp, #0xc
        b'\xE0\xFE\xFF\xEB',                            # bl      0x914
        b'\x14\x00\x9F\xE5',                            # ldr     r0, 0xdac
        b'\x00\x00\x8F\xE0',                            # add     r0, pc, r0
        b'\x1B\xFE\xFF\xEB',                            # bl      0x60c
        b'\x0B\xD0\xA0\xE1',                            # mov     sp, r11
        b'\x00\x88\xBD\xE8',                            # pop     {r11, pc}
    ],
    'length': 0xB0
},
{
    'name': 'MD5Init',
    'description': 'int32_t* MD5Init(int32_t* arg1)',
    'address': 0xDB8,
    'instructions': [
        b'\x00\x48\x2D\xE9',                            # push    {r11, lr}
        b'\x0D\xB0\xA0\xE1',                            # mov     r11, sp
        b'\x04\xD0\x4D\xE2',                            # sub     sp, sp, #0x4
        b'\x48\x10\x9F\xE5',                            # ldr     r1, 0xe14
        b'\x48\x20\x9F\xE5',                            # ldr     r2, 0xe18
        b'\x48\x30\x9F\xE5',                            # ldr     r3, 0xe1c
        b'\x48\xC0\x9F\xE5',                            # ldr     r12, 0xe20
        b'\x00\x00\x8D\xE5',                            # str     r0, [sp]
        b'\x00\x00\x9D\xE5',                            # ldr     r0, [sp]
        b'\x00\xE0\x00\xE3',                            # movw    lr, #0
        b'\x14\xE0\x80\xE5',                            # str     lr, [r0,  #0x14]
        b'\x00\x00\x9D\xE5',                            # ldr     r0, [sp]
        b'\x10\xE0\x80\xE5',                            # str     lr, [r0,  #0x10]
        b'\x00\x00\x9D\xE5',                            # ldr     r0, [sp]
        b'\x00\xC0\x80\xE5',                            # str     r12, [r0]
        b'\x00\x00\x9D\xE5',                            # ldr     r0, [sp]
        b'\x04\x30\x80\xE5',                            # str     r3, [r0,  #0x4]
        b'\x00\x00\x9D\xE5',                            # ldr     r0, [sp]
        b'\x08\x20\x80\xE5',                            # str     r2, [r0,  #0x8]
        b'\x00\x00\x9D\xE5',                            # ldr     r0, [sp]
        b'\x0C\x10\x80\xE5',                            # str     r1, [r0,  #0xc]
        b'\x0B\xD0\xA0\xE1',                            # mov     sp, r11
        b'\x00\x88\xBD\xE8',                            # pop     {r11, pc}
        b'\x76\x54\x32\x10',                            # manual add: literal pool
        b'\xfe\xdc\xba\x98',
        b'\x89\xab\xcd\xef',
        b'\x01\x23\x45\x67'
    ],
    'length': 0x5C + 16                                 # +16 for literal pool
},
{
    'name': 'MD5Update',
    'description': 'int32_t MD5Update(int32_t* arg1, void* arg2, int32_t arg3)',
    'address': 0xE24,
    'instructions': [
        b'\x00\x48\x2D\xE9',                            # push    {r11, lr}
        b'\x0D\xB0\xA0\xE1',                            # mov     r11, sp
        b'\x18\xD0\x4D\xE2',                            # sub     sp, sp, #0x18
        b'\x04\x00\x0B\xE5',                            # str     r0, [r11,  #-0x4]
        b'\x08\x10\x0B\xE5',                            # str     r1, [r11,  #-0x8]
        b'\x0C\x20\x8D\xE5',                            # str     r2, [sp,  #0xc]
        b'\x04\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x4]
        b'\x10\x00\x90\xE5',                            # ldr     r0, [r0,  #0x10]
        b'\xA0\x01\xA0\xE1',                            # lsr     r0, r0, #0x3
        b'\x3F\x00\x00\xE2',                            # and     r0, r0, #0x3f
        b'\x04\x00\x8D\xE5',                            # str     r0, [sp,  #0x4]
        b'\x0C\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xc]
        b'\x80\x01\xA0\xE1',                            # lsl     r0, r0, #0x3
        b'\x04\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x4]
        b'\x10\x20\x91\xE5',                            # ldr     r2, [r1,  #0x10]
        b'\x00\x00\x82\xE0',                            # add     r0, r2, r0
        b'\x10\x00\x81\xE5',                            # str     r0, [r1,  #0x10]
        b'\x0C\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xc]
        b'\x81\x11\xA0\xE1',                            # lsl     r1, r1, #0x3
        b'\x01\x00\x50\xE1',                            # cmp     r0, r1
        b'\x03\x00\x00\x2A',                            # bhs     0xe88
        b'\x04\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x4]
        b'\x14\x10\x90\xE5',                            # ldr     r1, [r0,  #0x14]
        b'\x01\x10\x81\xE2',                            # add     r1, r1, #0x1
        b'\x14\x10\x80\xE5',                            # str     r1, [r0,  #0x14]
        b'\x0C\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xc]
        b'\xA0\x0E\xA0\xE1',                            # lsr     r0, r0, #0x1d
        b'\x04\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x4]
        b'\x14\x20\x91\xE5',                            # ldr     r2, [r1,  #0x14]
        b'\x00\x00\x82\xE0',                            # add     r0, r2, r0
        b'\x14\x00\x81\xE5',                            # str     r0, [r1,  #0x14]
        b'\x04\x00\x9D\xE5',                            # ldr     r0, [sp,  #0x4]
        b'\x40\x10\x00\xE3',                            # movw    r1, #0x40
        b'\x00\x00\x41\xE0',                            # sub     r0, r1, r0
        b'\x00\x00\x8D\xE5',                            # str     r0, [sp]
        b'\x0C\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xc]
        b'\x00\x10\x9D\xE5',                            # ldr     r1, [sp]
        b'\x01\x00\x50\xE1',                            # cmp     r0, r1
        b'\x1D\x00\x00\x3A',                            # blo     0xf38
        b'\x04\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x4]
        b'\x18\x00\x80\xE2',                            # add     r0, r0, #0x18
        b'\x04\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x4]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x08\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x8]
        b'\x00\x20\x9D\xE5',                            # ldr     r2, [sp]
        b'\x16\x08\x00\xEB',                            # bl      0x2f38
        b'\x04\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x4]
        b'\x04\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x4]
        b'\x18\x10\x81\xE2',                            # add     r1, r1, #0x18
        b'\x53\x00\x00\xEB',                            # bl      0x103c
        b'\x00\x00\x9D\xE5',                            # ldr     r0, [sp]
        b'\x08\x00\x8D\xE5',                            # str     r0, [sp,  #0x8]
        b'\x08\x00\x9D\xE5',                            # ldr     r0, [sp,  #0x8]
        b'\x3F\x00\x80\xE2',                            # add     r0, r0, #0x3f
        b'\x0C\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xc]
        b'\x01\x00\x50\xE1',                            # cmp     r0, r1
        b'\x08\x00\x00\x2A',                            # bhs     0xf2c
        b'\x04\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x4]
        b'\x08\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x8]
        b'\x08\x20\x9D\xE5',                            # ldr     r2, [sp,  #0x8]
        b'\x02\x10\x81\xE0',                            # add     r1, r1, r2
        b'\x47\x00\x00\xEB',                            # bl      0x103c
        b'\x08\x00\x9D\xE5',                            # ldr     r0, [sp,  #0x8]
        b'\x40\x00\x80\xE2',                            # add     r0, r0, #0x40
        b'\x08\x00\x8D\xE5',                            # str     r0, [sp,  #0x8]
        b'\xF1\xFF\xFF\xEA',                            # b       0xef4
        b'\x00\x00\x00\xE3',                            # movw    r0, #0
        b'\x04\x00\x8D\xE5',                            # str     r0, [sp,  #0x4]
        b'\x01\x00\x00\xEA',                            # b       0xf40
        b'\x00\x00\x00\xE3',                            # movw    r0, #0
        b'\x08\x00\x8D\xE5',                            # str     r0, [sp,  #0x8]
        b'\x04\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x4]
        b'\x18\x00\x80\xE2',                            # add     r0, r0, #0x18
        b'\x04\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x4]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x08\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x8]
        b'\x08\x20\x9D\xE5',                            # ldr     r2, [sp,  #0x8]
        b'\x02\x10\x81\xE0',                            # add     r1, r1, r2
        b'\x0C\x20\x9D\xE5',                            # ldr     r2, [sp,  #0xc]
        b'\x08\x30\x9D\xE5',                            # ldr     r3, [sp,  #0x8]
        b'\x03\x20\x42\xE0',                            # sub     r2, r2, r3
        b'\xF2\x07\x00\xEB',                            # bl      0x2f38
        b'\x0B\xD0\xA0\xE1',                            # mov     sp, r11
        b'\x00\x88\xBD\xE8',                            # pop     {r11, pc}
    ],
    'length': 0x150
},
{
    'name': 'MD5Final',
    'description': 'int32_t MD5Final(char* arg1, int32_t* arg2)',
    'address': 0xF74,
    'instructions': [
        b'\x00\x48\x2D\xE9',                            # push    {r11, lr}
        b'\x0D\xB0\xA0\xE1',                            # mov     r11, sp
        b'\x20\xD0\x4D\xE2',                            # sub     sp, sp, #0x20
        b'\x10\x20\x8D\xE2',                            # add     r2, sp, #0x10
        b'\x04\x00\x0B\xE5',                            # str     r0, [r11,  #-0x4]
        b'\x08\x10\x0B\xE5',                            # str     r1, [r11,  #-0x8]
        b'\x08\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x8]
        b'\x10\x10\x80\xE2',                            # add     r1, r0, #0x10
        b'\x02\x00\xA0\xE1',                            # mov     r0, r2
        b'\x08\x20\x00\xE3',                            # movw    r2, #0x8
        b'\xB0\x07\x00\xEB',                            # bl      0x2e64
        b'\x08\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x8]
        b'\x10\x00\x90\xE5',                            # ldr     r0, [r0,  #0x10]
        b'\xA0\x01\xA0\xE1',                            # lsr     r0, r0, #0x3
        b'\x3F\x00\x00\xE2',                            # and     r0, r0, #0x3f
        b'\x0C\x00\x8D\xE5',                            # str     r0, [sp,  #0xc]
        b'\x0C\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xc]
        b'\x38\x00\x50\xE3',                            # cmp     r0, #0x38
        b'\x04\x00\x00\x2A',                            # bhs     0xfd4
        b'\x0C\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xc]
        b'\x38\x10\x00\xE3',                            # movw    r1, #0x38
        b'\x00\x00\x41\xE0',                            # sub     r0, r1, r0
        b'\x04\x00\x8D\xE5',                            # str     r0, [sp,  #0x4]
        b'\x03\x00\x00\xEA',                            # b       0xfe4
        b'\x0C\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xc]
        b'\x78\x10\x00\xE3',                            # movw    r1, #0x78
        b'\x00\x00\x41\xE0',                            # sub     r0, r1, r0
        b'\x04\x00\x8D\xE5',                            # str     r0, [sp,  #0x4]
        b'\x04\x00\x9D\xE5',                            # ldr     r0, [sp,  #0x4]
        b'\x48\x10\x9F\xE5',                            # ldr     r1, 0x1038
        b'\x01\x10\x8F\xE0',                            # add     r1, pc, r1
        b'\x08\x00\x8D\xE5',                            # str     r0, [sp,  #0x8]
        b'\x08\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x8]
        b'\x08\x20\x9D\xE5',                            # ldr     r2, [sp,  #0x8]
        b'\x88\xFF\xFF\xEB',                            # bl      0xe24
        b'\x10\x10\x8D\xE2',                            # add     r1, sp, #0x10
        b'\x08\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x8]
        b'\x08\x20\x00\xE3',                            # movw    r2, #0x8
        b'\x84\xFF\xFF\xEB',                            # bl      0xe24
        b'\x04\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x4]
        b'\x08\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x8]
        b'\x10\x20\x00\xE3',                            # movw    r2, #0x10
        b'\x90\x07\x00\xEB',                            # bl      0x2e64
        b'\x08\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x8]
        b'\x00\x10\x00\xE3',                            # movw    r1, #0
        b'\x58\x20\x00\xE3',                            # movw    r2, #0x58
        b'\xD9\x07\x00\xEB',                            # bl      0x2f98
        b'\x0B\xD0\xA0\xE1',                            # mov     sp, r11
        b'\x00\x88\xBD\xE8',                            # pop     {r11, pc}
        b'\x0c\x50\x00\x00',                            # manual add: literal pool
    ],
    'length': 0xC4 + 4                                  # +4 for literal pool
},
{
    'name': 'MD5Transform',
    'description': 'int32_t MD5Transform(int32_t* arg1, int32_t* arg2)',
    'address': 0x103C,
    'instructions': [
        b'\xF0\x4F\x2D\xE9',                            # push    {r4, r5, r6, r7, r8, r9, r10, r11, lr}
        b'\x1C\xB0\x8D\xE2',                            # add     r11, sp, #0x1c
        b'\x8B\xDF\x4D\xE2',                            # sub     sp, sp, #0x22c
        b'\x78\x20\x4B\xE2',                            # sub     r2, r11, #0x78
        b'\x24\x00\x0B\xE5',                            # str     r0, [r11,  #-0x24]
        b'\x28\x10\x0B\xE5',                            # str     r1, [r11,  #-0x28]
        b'\x24\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x24]
        b'\x00\x00\x90\xE5',                            # ldr     r0, [r0]
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x24\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x24]
        b'\x04\x00\x90\xE5',                            # ldr     r0, [r0,  #0x4]
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x24\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x24]
        b'\x08\x00\x90\xE5',                            # ldr     r0, [r0,  #0x8]
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x24\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x24]
        b'\x0C\x00\x90\xE5',                            # ldr     r0, [r0,  #0xc]
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x28\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x28]
        b'\x02\x00\xA0\xE1',                            # mov     r0, r2
        b'\x40\x20\x00\xE3',                            # movw    r2, #0x40
        b'\x58\x07\x00\xEB',                            # bl      0x2df8
        b'\x78\x00\x4B\xE2',                            # sub     r0, r11, #0x78
        b'\xF0\x1F\x9F\xE5',                            # ldr     r1, 0x2090
        b'\xF0\x2F\x9F\xE5',                            # ldr     r2, 0x2094
        b'\xF0\x3F\x9F\xE5',                            # ldr     r3, 0x2098
        b'\xF0\xCF\x9F\xE5',                            # ldr     r12, 0x209c
        b'\xF0\xEF\x9F\xE5',                            # ldr     lr, 0x20a0
        b'\xF0\x4F\x9F\xE5',                            # ldr     r4, 0x20a4
        b'\xF0\x5F\x9F\xE5',                            # ldr     r5, 0x20a8
        b'\xF0\x6F\x9F\xE5',                            # ldr     r6, 0x20ac
        b'\xF0\x7F\x9F\xE5',                            # ldr     r7, 0x20b0
        b'\xF0\x8F\x9F\xE5',                            # ldr     r8, 0x20b4
        b'\xF0\x9F\x9F\xE5',                            # ldr     r9, 0x20b8
        b'\xF0\xAF\x9F\xE5',                            # ldr     r10, 0x20bc
        b'\x7C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x7c]
        b'\xEC\x0F\x9F\xE5',                            # ldr     r0, 0x20c0
        b'\x80\x00\x0B\xE5',                            # str     r0, [r11,  #-0x80]
        b'\xE8\x0F\x9F\xE5',                            # ldr     r0, 0x20c4
        b'\x84\x00\x0B\xE5',                            # str     r0, [r11,  #-0x84]
        b'\xE4\x0F\x9F\xE5',                            # ldr     r0, 0x20c8
        b'\x88\x00\x0B\xE5',                            # str     r0, [r11,  #-0x88]
        b'\xE0\x0F\x9F\xE5',                            # ldr     r0, 0x20cc
        b'\x8C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x8c]
        b'\xDC\x0F\x9F\xE5',                            # ldr     r0, 0x20d0
        b'\x90\x00\x0B\xE5',                            # str     r0, [r11,  #-0x90]
        b'\xD8\x0F\x9F\xE5',                            # ldr     r0, 0x20d4
        b'\x94\x00\x0B\xE5',                            # str     r0, [r11,  #-0x94]
        b'\xD4\x0F\x9F\xE5',                            # ldr     r0, 0x20d8
        b'\x98\x00\x0B\xE5',                            # str     r0, [r11,  #-0x98]
        b'\xD0\x0F\x9F\xE5',                            # ldr     r0, 0x20dc
        b'\x9C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x9c]
        b'\xCC\x0F\x9F\xE5',                            # ldr     r0, 0x20e0
        b'\xA0\x00\x0B\xE5',                            # str     r0, [r11,  #-0xa0]
        b'\xC8\x0F\x9F\xE5',                            # ldr     r0, 0x20e4
        b'\xA4\x00\x0B\xE5',                            # str     r0, [r11,  #-0xa4]
        b'\xC4\x0F\x9F\xE5',                            # ldr     r0, 0x20e8
        b'\xA8\x00\x0B\xE5',                            # str     r0, [r11,  #-0xa8]
        b'\xC0\x0F\x9F\xE5',                            # ldr     r0, 0x20ec
        b'\xAC\x00\x0B\xE5',                            # str     r0, [r11,  #-0xac]
        b'\xBC\x0F\x9F\xE5',                            # ldr     r0, 0x20f0
        b'\xB0\x00\x0B\xE5',                            # str     r0, [r11,  #-0xb0]
        b'\xB8\x0F\x9F\xE5',                            # ldr     r0, 0x20f4
        b'\xB4\x00\x0B\xE5',                            # str     r0, [r11,  #-0xb4]
        b'\xB4\x0F\x9F\xE5',                            # ldr     r0, 0x20f8
        b'\xB8\x00\x0B\xE5',                            # str     r0, [r11,  #-0xb8]
        b'\xB0\x0F\x9F\xE5',                            # ldr     r0, 0x20fc
        b'\xBC\x00\x0B\xE5',                            # str     r0, [r11,  #-0xbc]
        b'\xAC\x0F\x9F\xE5',                            # ldr     r0, 0x2100
        b'\xC0\x00\x0B\xE5',                            # str     r0, [r11,  #-0xc0]
        b'\xA8\x0F\x9F\xE5',                            # ldr     r0, 0x2104
        b'\xC4\x00\x0B\xE5',                            # str     r0, [r11,  #-0xc4]
        b'\xA4\x0F\x9F\xE5',                            # ldr     r0, 0x2108
        b'\xC8\x00\x0B\xE5',                            # str     r0, [r11,  #-0xc8]
        b'\xA0\x0F\x9F\xE5',                            # ldr     r0, 0x210c
        b'\xCC\x00\x0B\xE5',                            # str     r0, [r11,  #-0xcc]
        b'\x9C\x0F\x9F\xE5',                            # ldr     r0, 0x2110
        b'\xD0\x00\x0B\xE5',                            # str     r0, [r11,  #-0xd0]
        b'\x98\x0F\x9F\xE5',                            # ldr     r0, 0x2114
        b'\xD4\x00\x0B\xE5',                            # str     r0, [r11,  #-0xd4]
        b'\x94\x0F\x9F\xE5',                            # ldr     r0, 0x2118
        b'\xD8\x00\x0B\xE5',                            # str     r0, [r11,  #-0xd8]
        b'\x90\x0F\x9F\xE5',                            # ldr     r0, 0x211c
        b'\xDC\x00\x0B\xE5',                            # str     r0, [r11,  #-0xdc]
        b'\x8C\x0F\x9F\xE5',                            # ldr     r0, 0x2120
        b'\xE0\x00\x0B\xE5',                            # str     r0, [r11,  #-0xe0]
        b'\x88\x0F\x9F\xE5',                            # ldr     r0, 0x2124
        b'\xE4\x00\x0B\xE5',                            # str     r0, [r11,  #-0xe4]
        b'\x84\x0F\x9F\xE5',                            # ldr     r0, 0x2128
        b'\xE8\x00\x0B\xE5',                            # str     r0, [r11,  #-0xe8]
        b'\x80\x0F\x9F\xE5',                            # ldr     r0, 0x212c
        b'\xEC\x00\x0B\xE5',                            # str     r0, [r11,  #-0xec]
        b'\x7C\x0F\x9F\xE5',                            # ldr     r0, 0x2130
        b'\xF0\x00\x0B\xE5',                            # str     r0, [r11,  #-0xf0]
        b'\x78\x0F\x9F\xE5',                            # ldr     r0, 0x2134
        b'\xF4\x00\x0B\xE5',                            # str     r0, [r11,  #-0xf4]
        b'\x74\x0F\x9F\xE5',                            # ldr     r0, 0x2138
        b'\xF8\x00\x0B\xE5',                            # str     r0, [r11,  #-0xf8]
        b'\x70\x0F\x9F\xE5',                            # ldr     r0, 0x213c
        b'\xFC\x00\x0B\xE5',                            # str     r0, [r11,  #-0xfc]
        b'\x6C\x0F\x9F\xE5',                            # ldr     r0, 0x2140
        b'\x00\x01\x0B\xE5',                            # str     r0, [r11,  #-0x100]
        b'\x68\x0F\x9F\xE5',                            # ldr     r0, 0x2144
        b'\x04\x01\x0B\xE5',                            # str     r0, [r11,  #-0x104]
        b'\x64\x0F\x9F\xE5',                            # ldr     r0, 0x2148
        b'\x08\x01\x0B\xE5',                            # str     r0, [r11,  #-0x108]
        b'\x60\x0F\x9F\xE5',                            # ldr     r0, 0x214c
        b'\x0C\x01\x0B\xE5',                            # str     r0, [r11,  #-0x10c]
        b'\x5C\x0F\x9F\xE5',                            # ldr     r0, 0x2150
        b'\x10\x01\x0B\xE5',                            # str     r0, [r11,  #-0x110]
        b'\x58\x0F\x9F\xE5',                            # ldr     r0, 0x2154
        b'\x14\x01\x0B\xE5',                            # str     r0, [r11,  #-0x114]
        b'\x54\x0F\x9F\xE5',                            # ldr     r0, 0x2158
        b'\x18\x01\x0B\xE5',                            # str     r0, [r11,  #-0x118]
        b'\x50\x0F\x9F\xE5',                            # ldr     r0, 0x215c
        b'\x1C\x01\x0B\xE5',                            # str     r0, [r11,  #-0x11c]
        b'\x4C\x0F\x9F\xE5',                            # ldr     r0, 0x2160
        b'\x20\x01\x0B\xE5',                            # str     r0, [r11,  #-0x120]
        b'\x48\x0F\x9F\xE5',                            # ldr     r0, 0x2164
        b'\x24\x01\x8D\xE5',                            # str     r0, [sp,  #0x124]
        b'\x44\x0F\x9F\xE5',                            # ldr     r0, 0x2168
        b'\x20\x01\x8D\xE5',                            # str     r0, [sp,  #0x120]
        b'\x40\x0F\x9F\xE5',                            # ldr     r0, 0x216c
        b'\x1C\x01\x8D\xE5',                            # str     r0, [sp,  #0x11c]
        b'\x3C\x0F\x9F\xE5',                            # ldr     r0, 0x2170
        b'\x18\x01\x8D\xE5',                            # str     r0, [sp,  #0x118]
        b'\x38\x0F\x9F\xE5',                            # ldr     r0, 0x2174
        b'\x14\x01\x8D\xE5',                            # str     r0, [sp,  #0x114]
        b'\x34\x0F\x9F\xE5',                            # ldr     r0, 0x2178
        b'\x10\x01\x8D\xE5',                            # str     r0, [sp,  #0x110]
        b'\x30\x0F\x9F\xE5',                            # ldr     r0, 0x217c
        b'\x0C\x01\x8D\xE5',                            # str     r0, [sp,  #0x10c]
        b'\x2C\x0F\x9F\xE5',                            # ldr     r0, 0x2180
        b'\x08\x01\x8D\xE5',                            # str     r0, [sp,  #0x108]
        b'\x28\x0F\x9F\xE5',                            # ldr     r0, 0x2184
        b'\x04\x01\x8D\xE5',                            # str     r0, [sp,  #0x104]
        b'\x24\x0F\x9F\xE5',                            # ldr     r0, 0x2188
        b'\x00\x01\x8D\xE5',                            # str     r0, [sp,  #0x100]
        b'\x20\x0F\x9F\xE5',                            # ldr     r0, 0x218c
        b'\xFC\x00\x8D\xE5',                            # str     r0, [sp,  #0xfc]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\xF8\x00\x8D\xE5',                            # str     r0, [sp,  #0xf8]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\xF4\x00\x8D\xE5',                            # str     r0, [sp,  #0xf4]
        b'\xF8\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xf8]
        b'\xF0\x10\x8D\xE5',                            # str     r1, [sp,  #0xf0]
        b'\xF4\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xf4]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\xEC\x00\x8D\xE5',                            # str     r0, [sp,  #0xec]
        b'\x00\x00\xE0\xE3',                            # mvn     r0, #0
        b'\x00\x10\x21\xE0',                            # eor     r1, r1, r0
        b'\xE8\x00\x8D\xE5',                            # str     r0, [sp,  #0xe8]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\xEC\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xec]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x78\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x78]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xFC\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xfc]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x80\x03\xA0\xE1',                            # lsl     r0, r0, #0x7
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\xA1\x1C\xA0\xE1',                            # lsr     r1, r1, #0x19
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\xE4\x00\x8D\xE5',                            # str     r0, [sp,  #0xe4]
        b'\xE8\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xe8]
        b'\x00\x10\x21\xE0',                            # eor     r1, r1, r0
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\xE4\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe4]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x74\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x74]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x00\x11\x9D\xE5',                            # ldr     r1, [sp,  #0x100]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x00\x06\xA0\xE1',                            # lsl     r0, r0, #0xc
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x21\x1A\xA0\xE1',                            # lsr     r1, r1, #0x14
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\xE0\x00\x8D\xE5',                            # str     r0, [sp,  #0xe0]
        b'\xE8\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xe8]
        b'\x00\x10\x21\xE0',                            # eor     r1, r1, r0
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\xE0\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe0]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x70\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x70]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x04\x11\x9D\xE5',                            # ldr     r1, [sp,  #0x104]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x80\x08\xA0\xE1',                            # lsl     r0, r0, #0x11
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\xA1\x17\xA0\xE1',                            # lsr     r1, r1, #0xf
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\xDC\x00\x8D\xE5',                            # str     r0, [sp,  #0xdc]
        b'\xE8\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xe8]
        b'\x00\x10\x21\xE0',                            # eor     r1, r1, r0
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\xDC\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xdc]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x6C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x6c]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x08\x11\x9D\xE5',                            # ldr     r1, [sp,  #0x108]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x00\x0B\xA0\xE1',                            # lsl     r0, r0, #0x16
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x21\x15\xA0\xE1',                            # lsr     r1, r1, #0xa
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\xD8\x00\x8D\xE5',                            # str     r0, [sp,  #0xd8]
        b'\xE8\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xe8]
        b'\x00\x10\x21\xE0',                            # eor     r1, r1, r0
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\xD8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xd8]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x68\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x68]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x0C\x11\x9D\xE5',                            # ldr     r1, [sp,  #0x10c]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x80\x03\xA0\xE1',                            # lsl     r0, r0, #0x7
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\xA1\x1C\xA0\xE1',                            # lsr     r1, r1, #0x19
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\xD4\x00\x8D\xE5',                            # str     r0, [sp,  #0xd4]
        b'\xE8\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xe8]
        b'\x00\x10\x21\xE0',                            # eor     r1, r1, r0
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\xD4\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xd4]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x64\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x64]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x10\x11\x9D\xE5',                            # ldr     r1, [sp,  #0x110]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x00\x06\xA0\xE1',                            # lsl     r0, r0, #0xc
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x21\x1A\xA0\xE1',                            # lsr     r1, r1, #0x14
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\xD0\x00\x8D\xE5',                            # str     r0, [sp,  #0xd0]
        b'\xE8\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xe8]
        b'\x00\x10\x21\xE0',                            # eor     r1, r1, r0
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\xD0\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xd0]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x60\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x60]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x14\x11\x9D\xE5',                            # ldr     r1, [sp,  #0x114]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x80\x08\xA0\xE1',                            # lsl     r0, r0, #0x11
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\xA1\x17\xA0\xE1',                            # lsr     r1, r1, #0xf
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\xCC\x00\x8D\xE5',                            # str     r0, [sp,  #0xcc]
        b'\xE8\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xe8]
        b'\x00\x10\x21\xE0',                            # eor     r1, r1, r0
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\xCC\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xcc]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x5C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x5c]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x18\x11\x9D\xE5',                            # ldr     r1, [sp,  #0x118]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x00\x0B\xA0\xE1',                            # lsl     r0, r0, #0x16
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x21\x15\xA0\xE1',                            # lsr     r1, r1, #0xa
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\xC8\x00\x8D\xE5',                            # str     r0, [sp,  #0xc8]
        b'\xE8\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xe8]
        b'\x00\x10\x21\xE0',                            # eor     r1, r1, r0
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\xC8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xc8]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x58\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x58]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x1C\x11\x9D\xE5',                            # ldr     r1, [sp,  #0x11c]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x80\x03\xA0\xE1',                            # lsl     r0, r0, #0x7
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\xA1\x1C\xA0\xE1',                            # lsr     r1, r1, #0x19
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\xC4\x00\x8D\xE5',                            # str     r0, [sp,  #0xc4]
        b'\xE8\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xe8]
        b'\x00\x10\x21\xE0',                            # eor     r1, r1, r0
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\xC4\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xc4]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x54\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x54]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x20\x11\x9D\xE5',                            # ldr     r1, [sp,  #0x120]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x00\x06\xA0\xE1',                            # lsl     r0, r0, #0xc
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x21\x1A\xA0\xE1',                            # lsr     r1, r1, #0x14
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\xC0\x00\x8D\xE5',                            # str     r0, [sp,  #0xc0]
        b'\xE8\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xe8]
        b'\x00\x10\x21\xE0',                            # eor     r1, r1, r0
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\xC0\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xc0]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x50\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x50]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x24\x11\x9D\xE5',                            # ldr     r1, [sp,  #0x124]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x80\x08\xA0\xE1',                            # lsl     r0, r0, #0x11
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\xA1\x17\xA0\xE1',                            # lsr     r1, r1, #0xf
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\xBC\x00\x8D\xE5',                            # str     r0, [sp,  #0xbc]
        b'\xE8\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xe8]
        b'\x00\x10\x21\xE0',                            # eor     r1, r1, r0
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\xBC\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xbc]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x4C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x4c]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x20\x11\x1B\xE5',                            # ldr     r1, [r11,  #-0x120]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x00\x0B\xA0\xE1',                            # lsl     r0, r0, #0x16
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x21\x15\xA0\xE1',                            # lsr     r1, r1, #0xa
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\xB8\x00\x8D\xE5',                            # str     r0, [sp,  #0xb8]
        b'\xE8\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xe8]
        b'\x00\x10\x21\xE0',                            # eor     r1, r1, r0
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\xB8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xb8]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x48\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x48]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x1C\x11\x1B\xE5',                            # ldr     r1, [r11,  #-0x11c]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x80\x03\xA0\xE1',                            # lsl     r0, r0, #0x7
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\xA1\x1C\xA0\xE1',                            # lsr     r1, r1, #0x19
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\xB4\x00\x8D\xE5',                            # str     r0, [sp,  #0xb4]
        b'\xE8\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xe8]
        b'\x00\x10\x21\xE0',                            # eor     r1, r1, r0
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\xB4\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xb4]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x44\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x44]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x18\x11\x1B\xE5',                            # ldr     r1, [r11,  #-0x118]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x00\x06\xA0\xE1',                            # lsl     r0, r0, #0xc
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x21\x1A\xA0\xE1',                            # lsr     r1, r1, #0x14
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\xB0\x00\x8D\xE5',                            # str     r0, [sp,  #0xb0]
        b'\xE8\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xe8]
        b'\x00\x10\x21\xE0',                            # eor     r1, r1, r0
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\xB0\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xb0]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x40\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x40]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x14\x11\x1B\xE5',                            # ldr     r1, [r11,  #-0x114]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x80\x08\xA0\xE1',                            # lsl     r0, r0, #0x11
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\xA1\x17\xA0\xE1',                            # lsr     r1, r1, #0xf
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\xAC\x00\x8D\xE5',                            # str     r0, [sp,  #0xac]
        b'\xE8\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xe8]
        b'\x00\x10\x21\xE0',                            # eor     r1, r1, r0
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\xAC\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xac]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x3C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x3c]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x10\x11\x1B\xE5',                            # ldr     r1, [r11,  #-0x110]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x00\x0B\xA0\xE1',                            # lsl     r0, r0, #0x16
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x21\x15\xA0\xE1',                            # lsr     r1, r1, #0xa
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\xA8\x00\x8D\xE5',                            # str     r0, [sp,  #0xa8]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\xA4\x10\x8D\xE5',                            # str     r1, [sp,  #0xa4]
        b'\xE8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe8]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\xA4\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xa4]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\xA8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xa8]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x74\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x74]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x0C\x11\x1B\xE5',                            # ldr     r1, [r11,  #-0x10c]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x80\x02\xA0\xE1',                            # lsl     r0, r0, #0x5
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\xA1\x1D\xA0\xE1',                            # lsr     r1, r1, #0x1b
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\xA0\x00\x8D\xE5',                            # str     r0, [sp,  #0xa0]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x9C\x10\x8D\xE5',                            # str     r1, [sp,  #0x9c]
        b'\xE8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe8]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x9C\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x9c]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\xA0\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xa0]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x60\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x60]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x08\x11\x1B\xE5',                            # ldr     r1, [r11,  #-0x108]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x80\x04\xA0\xE1',                            # lsl     r0, r0, #0x9
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\xA1\x1B\xA0\xE1',                            # lsr     r1, r1, #0x17
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x98\x00\x8D\xE5',                            # str     r0, [sp,  #0x98]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x94\x10\x8D\xE5',                            # str     r1, [sp,  #0x94]
        b'\xE8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe8]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x94\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x94]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\x98\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x98]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x4C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x4c]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x04\x11\x1B\xE5',                            # ldr     r1, [r11,  #-0x104]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x00\x07\xA0\xE1',                            # lsl     r0, r0, #0xe
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x21\x19\xA0\xE1',                            # lsr     r1, r1, #0x12
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x90\x00\x8D\xE5',                            # str     r0, [sp,  #0x90]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x8C\x10\x8D\xE5',                            # str     r1, [sp,  #0x8c]
        b'\xE8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe8]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x8C\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x8c]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\x90\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x90]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x78\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x78]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x00\x11\x1B\xE5',                            # ldr     r1, [r11,  #-0x100]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x00\x0A\xA0\xE1',                            # lsl     r0, r0, #0x14
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x21\x16\xA0\xE1',                            # lsr     r1, r1, #0xc
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x88\x00\x8D\xE5',                            # str     r0, [sp,  #0x88]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x84\x10\x8D\xE5',                            # str     r1, [sp,  #0x84]
        b'\xE8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe8]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x84\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x84]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\x88\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x88]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x64\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x64]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xFC\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xfc]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x80\x02\xA0\xE1',                            # lsl     r0, r0, #0x5
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\xA1\x1D\xA0\xE1',                            # lsr     r1, r1, #0x1b
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x80\x00\x8D\xE5',                            # str     r0, [sp,  #0x80]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x7C\x10\x8D\xE5',                            # str     r1, [sp,  #0x7c]
        b'\xE8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe8]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x7C\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x7c]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\x80\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x80]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x50\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x50]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xF8\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xf8]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x80\x04\xA0\xE1',                            # lsl     r0, r0, #0x9
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\xA1\x1B\xA0\xE1',                            # lsr     r1, r1, #0x17
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x78\x00\x8D\xE5',                            # str     r0, [sp,  #0x78]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x74\x10\x8D\xE5',                            # str     r1, [sp,  #0x74]
        b'\xE8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe8]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x74\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x74]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\x78\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x78]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x3C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x3c]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xF4\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xf4]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x00\x07\xA0\xE1',                            # lsl     r0, r0, #0xe
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x21\x19\xA0\xE1',                            # lsr     r1, r1, #0x12
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x70\x00\x8D\xE5',                            # str     r0, [sp,  #0x70]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x6C\x10\x8D\xE5',                            # str     r1, [sp,  #0x6c]
        b'\xE8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe8]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x6C\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x6c]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\x70\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x70]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x68\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x68]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xF0\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xf0]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x00\x0A\xA0\xE1',                            # lsl     r0, r0, #0x14
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x21\x16\xA0\xE1',                            # lsr     r1, r1, #0xc
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x68\x00\x8D\xE5',                            # str     r0, [sp,  #0x68]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x64\x10\x8D\xE5',                            # str     r1, [sp,  #0x64]
        b'\xE8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe8]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x64\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x64]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\x68\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x68]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x54\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x54]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xEC\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xec]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x80\x02\xA0\xE1',                            # lsl     r0, r0, #0x5
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\xA1\x1D\xA0\xE1',                            # lsr     r1, r1, #0x1b
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x60\x00\x8D\xE5',                            # str     r0, [sp,  #0x60]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x5C\x10\x8D\xE5',                            # str     r1, [sp,  #0x5c]
        b'\xE8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe8]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x5C\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x5c]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\x60\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x60]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x40\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x40]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xE8\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xe8]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x80\x04\xA0\xE1',                            # lsl     r0, r0, #0x9
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\xA1\x1B\xA0\xE1',                            # lsr     r1, r1, #0x17
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x58\x00\x8D\xE5',                            # str     r0, [sp,  #0x58]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x54\x10\x8D\xE5',                            # str     r1, [sp,  #0x54]
        b'\xE8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe8]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x54\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x54]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\x58\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x58]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x6C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x6c]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xE4\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xe4]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x00\x07\xA0\xE1',                            # lsl     r0, r0, #0xe
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x21\x19\xA0\xE1',                            # lsr     r1, r1, #0x12
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x50\x00\x8D\xE5',                            # str     r0, [sp,  #0x50]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x4C\x10\x8D\xE5',                            # str     r1, [sp,  #0x4c]
        b'\xE8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe8]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x4C\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x4c]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\x50\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x50]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x58\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x58]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xE0\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xe0]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x00\x0A\xA0\xE1',                            # lsl     r0, r0, #0x14
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x21\x16\xA0\xE1',                            # lsr     r1, r1, #0xc
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x48\x00\x8D\xE5',                            # str     r0, [sp,  #0x48]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x44\x10\x8D\xE5',                            # str     r1, [sp,  #0x44]
        b'\xE8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe8]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x44\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x44]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\x48\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x48]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x44\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x44]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xDC\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xdc]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x80\x02\xA0\xE1',                            # lsl     r0, r0, #0x5
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\xA1\x1D\xA0\xE1',                            # lsr     r1, r1, #0x1b
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x40\x00\x8D\xE5',                            # str     r0, [sp,  #0x40]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x3C\x10\x8D\xE5',                            # str     r1, [sp,  #0x3c]
        b'\xE8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe8]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x3C\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x3c]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\x40\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x40]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x70\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x70]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xD8\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xd8]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x80\x04\xA0\xE1',                            # lsl     r0, r0, #0x9
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\xA1\x1B\xA0\xE1',                            # lsr     r1, r1, #0x17
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x38\x00\x8D\xE5',                            # str     r0, [sp,  #0x38]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x34\x10\x8D\xE5',                            # str     r1, [sp,  #0x34]
        b'\xE8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe8]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x34\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x34]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\x38\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x38]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x5C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x5c]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xD4\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xd4]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x00\x07\xA0\xE1',                            # lsl     r0, r0, #0xe
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x21\x19\xA0\xE1',                            # lsr     r1, r1, #0x12
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x3F\x00\x00\xEA',                            # b       0x2190
        b'\x91\xD3\x86\xEB',                            # manual add: literal pool
        b'\xBB\xD2\xD7\x2A',
        b'\x35\xF2\x3A\xBD',
        b'\x82\x7E\x53\xF7',
        b'\xA1\x11\x08\x4E',
        b'\x14\x43\x01\xA3',
        b'\xE0\xE6\x2C\xFE',
        b'\x4F\x7E\xA8\x6F',
        b'\xD1\x5D\x84\x85',
        b'\x7D\xF4\xEF\xFF',
        b'\x92\xCC\x0C\x8F',
        b'\xC3\x59\x5B\x65',
        b'\x39\xA0\x93\xFC',
        b'\xA7\x23\x94\xAB',
        b'\x97\xFF\x2A\x43',
        b'\x44\x22\x29\xF4',
        b'\x65\x56\xAC\xC4',
        b'\xF8\x7C\xA2\x1F',
        b'\xE5\x99\xDB\xE6',
        b'\x39\xD0\xD4\xD9',
        b'\x05\x1D\x88\x04',
        b'\x85\x30\xEF\xD4',
        b'\xFA\x27\xA1\xEA',
        b'\xC6\x7E\x9B\x28',
        b'\x70\xBC\xBF\xBE',
        b'\x60\x4B\xBB\xF6',
        b'\xA9\xCF\xDE\x4B',
        b'\x44\xEA\xBE\xA4',
        b'\x0C\x38\xE5\xFD',
        b'\x22\x61\x9D\x6D',
        b'\x81\xF6\x71\x87',
        b'\x42\x39\xFA\xFF',
        b'\x8A\x4C\x2A\x8D',
        b'\xD9\x02\x6F\x67',
        b'\xF8\xA3\xEF\xFC',
        b'\x05\xE9\xE3\xA9',
        b'\xED\x14\x5A\x45',
        b'\x87\x0D\xD5\xF4',
        b'\xD6\x07\x37\xC3',
        b'\xE6\xCD\xE1\x21',
        b'\xC8\xFB\xD3\xE7',
        b'\x81\xE6\xA1\xD8',
        b'\x53\x14\x44\x02',
        b'\x5D\x10\x2F\xD6',
        b'\xAA\xC7\xB6\xE9',
        b'\x51\x5A\x5E\x26',
        b'\x40\xB3\x40\xC0',
        b'\x62\x25\x1E\xF6',
        b'\x21\x08\xB4\x49',
        b'\x8E\x43\x79\xA6',
        b'\x93\x71\x98\xFD',
        b'\x22\x11\x90\x6B',
        b'\xBE\xD7\x5C\x89',
        b'\xB1\x5B\xFF\xFF',
        b'\xAF\xF7\x44\x8B',
        b'\xD8\x98\x80\x69',
        b'\x01\x95\x46\xFD',
        b'\x13\x46\x30\xA8',
        b'\x2A\xC6\x87\x47',
        b'\xAF\x0F\x7C\xF5',
        b'\xEE\xCE\xBD\xC1',
        b'\xDB\x70\x20\x24',
        b'\x56\xB7\xC7\xE8',
        b'\x78\xA4\x6A\xD7',
    ],
    'length': 0x1054 + 256                              # +256 for literal pool
},
{
    'name': '_6',
    'description': 'int32_t _6(int32_t arg1, int32_t arg2, int32_t arg3, int32_t arg4, int32_t arg5 @ r4, int32_t arg6 @ r5, int32_t arg7 @ r6, int32_t arg8 @ r7, int32_t arg9 @ r8, int32_t arg10 @ r9, int32_t arg11 @ r10, int32_t arg12 @ r11, int32_t arg13 @ r12, int32_t arg14, int32_t arg15)',
    'address': 0x2190,
    'instructions': [
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x01\x00\x00\xE0',                            # and     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x30\x00\x8D\xE5',                            # str     r0, [sp,  #0x30]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x2C\x10\x8D\xE5',                            # str     r1, [sp,  #0x2c]
        b'\xE8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe8]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x2C\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x2c]
        b'\x00\x00\x01\xE0',                            # and     r0, r1, r0
        b'\x30\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x30]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x48\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x48]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xD0\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xd0]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x00\x0A\xA0\xE1',                            # lsl     r0, r0, #0x14
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x21\x16\xA0\xE1',                            # lsr     r1, r1, #0xc
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x64\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x64]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xCC\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xcc]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x00\x02\xA0\xE1',                            # lsl     r0, r0, #0x4
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x21\x1E\xA0\xE1',                            # lsr     r1, r1, #0x1c
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x58\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x58]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xC8\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xc8]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x80\x05\xA0\xE1',                            # lsl     r0, r0, #0xb
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\xA1\x1A\xA0\xE1',                            # lsr     r1, r1, #0x15
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x4C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x4c]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xC4\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xc4]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x00\x08\xA0\xE1',                            # lsl     r0, r0, #0x10
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x21\x18\xA0\xE1',                            # lsr     r1, r1, #0x10
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x40\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x40]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xC0\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xc0]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x80\x0B\xA0\xE1',                            # lsl     r0, r0, #0x17
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\xA1\x14\xA0\xE1',                            # lsr     r1, r1, #0x9
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x74\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x74]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xBC\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xbc]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x00\x02\xA0\xE1',                            # lsl     r0, r0, #0x4
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x21\x1E\xA0\xE1',                            # lsr     r1, r1, #0x1c
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x68\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x68]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xB8\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xb8]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x80\x05\xA0\xE1',                            # lsl     r0, r0, #0xb
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\xA1\x1A\xA0\xE1',                            # lsr     r1, r1, #0x15
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x5C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x5c]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xB4\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xb4]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x00\x08\xA0\xE1',                            # lsl     r0, r0, #0x10
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x21\x18\xA0\xE1',                            # lsr     r1, r1, #0x10
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x50\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x50]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xB0\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xb0]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x80\x0B\xA0\xE1',                            # lsl     r0, r0, #0x17
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\xA1\x14\xA0\xE1',                            # lsr     r1, r1, #0x9
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x44\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x44]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xAC\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xac]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x00\x02\xA0\xE1',                            # lsl     r0, r0, #0x4
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x21\x1E\xA0\xE1',                            # lsr     r1, r1, #0x1c
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x78\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x78]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xA8\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xa8]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x80\x05\xA0\xE1',                            # lsl     r0, r0, #0xb
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\xA1\x1A\xA0\xE1',                            # lsr     r1, r1, #0x15
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x6C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x6c]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xA4\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xa4]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x00\x08\xA0\xE1',                            # lsl     r0, r0, #0x10
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x21\x18\xA0\xE1',                            # lsr     r1, r1, #0x10
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x60\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x60]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\xA0\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0xa0]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x80\x0B\xA0\xE1',                            # lsl     r0, r0, #0x17
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\xA1\x14\xA0\xE1',                            # lsr     r1, r1, #0x9
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x54\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x54]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x9C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x9c]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x00\x02\xA0\xE1',                            # lsl     r0, r0, #0x4
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x21\x1E\xA0\xE1',                            # lsr     r1, r1, #0x1c
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x48\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x48]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x98\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x98]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x80\x05\xA0\xE1',                            # lsl     r0, r0, #0xb
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\xA1\x1A\xA0\xE1',                            # lsr     r1, r1, #0x15
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x3C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x3c]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x94\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x94]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x00\x08\xA0\xE1',                            # lsl     r0, r0, #0x10
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x21\x18\xA0\xE1',                            # lsr     r1, r1, #0x10
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x70\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x70]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x90\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x90]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x80\x0B\xA0\xE1',                            # lsl     r0, r0, #0x17
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\xA1\x14\xA0\xE1',                            # lsr     r1, r1, #0x9
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x28\x00\x8D\xE5',                            # str     r0, [sp,  #0x28]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x24\x10\x8D\xE5',                            # str     r1, [sp,  #0x24]
        b'\xE8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe8]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x24\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x24]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x28\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x28]
        b'\x00\x00\x21\xE0',                            # eor     r0, r1, r0
        b'\x78\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x78]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x8C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x8c]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x00\x03\xA0\xE1',                            # lsl     r0, r0, #0x6
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x21\x1D\xA0\xE1',                            # lsr     r1, r1, #0x1a
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x20\x00\x8D\xE5',                            # str     r0, [sp,  #0x20]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x1C\x10\x8D\xE5',                            # str     r1, [sp,  #0x1c]
        b'\xE8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe8]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x1C\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x1c]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x20\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x20]
        b'\x00\x00\x21\xE0',                            # eor     r0, r1, r0
        b'\x5C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x5c]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x88\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x88]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x00\x05\xA0\xE1',                            # lsl     r0, r0, #0xa
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x21\x1B\xA0\xE1',                            # lsr     r1, r1, #0x16
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x38\x00\x0B\xE5',                            # str     r0, [r11,  #-0x38]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x18\x00\x8D\xE5',                            # str     r0, [sp,  #0x18]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x14\x10\x8D\xE5',                            # str     r1, [sp,  #0x14]
        b'\xE8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe8]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x14\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x14]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x18\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x18]
        b'\x00\x00\x21\xE0',                            # eor     r0, r1, r0
        b'\x40\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x40]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x84\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x84]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x80\x07\xA0\xE1',                            # lsl     r0, r0, #0xf
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\xA1\x18\xA0\xE1',                            # lsr     r1, r1, #0x11
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x34\x00\x0B\xE5',                            # str     r0, [r11,  #-0x34]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x10\x00\x8D\xE5',                            # str     r0, [sp,  #0x10]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x0C\x10\x8D\xE5',                            # str     r1, [sp,  #0xc]
        b'\xE8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe8]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x0C\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xc]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x10\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x10]
        b'\x00\x00\x21\xE0',                            # eor     r0, r1, r0
        b'\x64\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x64]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x80\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x80]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x80\x0A\xA0\xE1',                            # lsl     r0, r0, #0x15
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\xA1\x15\xA0\xE1',                            # lsr     r1, r1, #0xb
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x30\x00\x0B\xE5',                            # str     r0, [r11,  #-0x30]
        b'\x34\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x34]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x08\x00\x8D\xE5',                            # str     r0, [sp,  #0x8]
        b'\x38\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x38]
        b'\x04\x10\x8D\xE5',                            # str     r1, [sp,  #0x4]
        b'\xE8\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xe8]
        b'\x01\x00\x20\xE0',                            # eor     r0, r0, r1
        b'\x04\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x4]
        b'\x00\x00\x81\xE1',                            # orr     r0, r1, r0
        b'\x08\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x8]
        b'\x00\x00\x21\xE0',                            # eor     r0, r1, r0
        b'\x48\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x48]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x0A\x00\x80\xE0',                            # add     r0, r0, r10
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x2C\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x2c]
        b'\x00\x03\xA0\xE1',                            # lsl     r0, r0, #0x6
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x21\x1D\xA0\xE1',                            # lsr     r1, r1, #0x1a
        b'\x01\x00\x80\xE1',                            # orr     r0, r0, r1
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x00\x00\x81\xE0',                            # add     r0, r1, r0
        b'\x2C\x00\x0B\xE5',                            # str     r0, [r11,  #-0x2c]
        b'\x30\x00\x1B\xE5',                            # ldr     r0, [r11,  #-0x30]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x34\xA0\x1B\xE5',                            # ldr     r10, [r11,  #-0x34]
        b'\x00\x00\x8D\xE5',                            # str     r0, [sp]
        b'\xE8\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xe8]
        b'\x00\xA0\x2A\xE0',                            # eor     r10, r10, r0
        b'\x0A\x10\x81\xE1',                            # orr     r1, r1, r10
        b'\x00\xA0\x9D\xE5',                            # ldr     r10, [sp]
        b'\x01\x10\x2A\xE0',                            # eor     r1, r10, r1
        b'\x6C\xA0\x1B\xE5',                            # ldr     r10, [r11,  #-0x6c]
        b'\x0A\x10\x81\xE0',                            # add     r1, r1, r10
        b'\x09\x10\x81\xE0',                            # add     r1, r1, r9
        b'\x38\x90\x1B\xE5',                            # ldr     r9, [r11,  #-0x38]
        b'\x01\x10\x89\xE0',                            # add     r1, r9, r1
        b'\x38\x10\x0B\xE5',                            # str     r1, [r11,  #-0x38]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x01\x15\xA0\xE1',                            # lsl     r1, r1, #0xa
        b'\x38\x90\x1B\xE5',                            # ldr     r9, [r11,  #-0x38]
        b'\x29\x9B\xA0\xE1',                            # lsr     r9, r9, #0x16
        b'\x09\x10\x81\xE1',                            # orr     r1, r1, r9
        b'\x38\x10\x0B\xE5',                            # str     r1, [r11,  #-0x38]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x38\x90\x1B\xE5',                            # ldr     r9, [r11,  #-0x38]
        b'\x01\x10\x89\xE0',                            # add     r1, r9, r1
        b'\x38\x10\x0B\xE5',                            # str     r1, [r11,  #-0x38]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x38\x90\x1B\xE5',                            # ldr     r9, [r11,  #-0x38]
        b'\x30\xA0\x1B\xE5',                            # ldr     r10, [r11,  #-0x30]
        b'\x00\xA0\x2A\xE0',                            # eor     r10, r10, r0
        b'\x0A\x90\x89\xE1',                            # orr     r9, r9, r10
        b'\x09\x10\x21\xE0',                            # eor     r1, r1, r9
        b'\x50\x90\x1B\xE5',                            # ldr     r9, [r11,  #-0x50]
        b'\x09\x10\x81\xE0',                            # add     r1, r1, r9
        b'\x08\x10\x81\xE0',                            # add     r1, r1, r8
        b'\x34\x80\x1B\xE5',                            # ldr     r8, [r11,  #-0x34]
        b'\x01\x10\x88\xE0',                            # add     r1, r8, r1
        b'\x34\x10\x0B\xE5',                            # str     r1, [r11,  #-0x34]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x81\x17\xA0\xE1',                            # lsl     r1, r1, #0xf
        b'\x34\x80\x1B\xE5',                            # ldr     r8, [r11,  #-0x34]
        b'\xA8\x88\xA0\xE1',                            # lsr     r8, r8, #0x11
        b'\x08\x10\x81\xE1',                            # orr     r1, r1, r8
        b'\x34\x10\x0B\xE5',                            # str     r1, [r11,  #-0x34]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x34\x80\x1B\xE5',                            # ldr     r8, [r11,  #-0x34]
        b'\x01\x10\x88\xE0',                            # add     r1, r8, r1
        b'\x34\x10\x0B\xE5',                            # str     r1, [r11,  #-0x34]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x34\x80\x1B\xE5',                            # ldr     r8, [r11,  #-0x34]
        b'\x2C\x90\x1B\xE5',                            # ldr     r9, [r11,  #-0x2c]
        b'\x00\x90\x29\xE0',                            # eor     r9, r9, r0
        b'\x09\x80\x88\xE1',                            # orr     r8, r8, r9
        b'\x08\x10\x21\xE0',                            # eor     r1, r1, r8
        b'\x74\x80\x1B\xE5',                            # ldr     r8, [r11,  #-0x74]
        b'\x08\x10\x81\xE0',                            # add     r1, r1, r8
        b'\x07\x10\x81\xE0',                            # add     r1, r1, r7
        b'\x30\x70\x1B\xE5',                            # ldr     r7, [r11,  #-0x30]
        b'\x01\x10\x87\xE0',                            # add     r1, r7, r1
        b'\x30\x10\x0B\xE5',                            # str     r1, [r11,  #-0x30]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x81\x1A\xA0\xE1',                            # lsl     r1, r1, #0x15
        b'\x30\x70\x1B\xE5',                            # ldr     r7, [r11,  #-0x30]
        b'\xA7\x75\xA0\xE1',                            # lsr     r7, r7, #0xb
        b'\x07\x10\x81\xE1',                            # orr     r1, r1, r7
        b'\x30\x10\x0B\xE5',                            # str     r1, [r11,  #-0x30]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x30\x70\x1B\xE5',                            # ldr     r7, [r11,  #-0x30]
        b'\x01\x10\x87\xE0',                            # add     r1, r7, r1
        b'\x30\x10\x0B\xE5',                            # str     r1, [r11,  #-0x30]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x30\x70\x1B\xE5',                            # ldr     r7, [r11,  #-0x30]
        b'\x38\x80\x1B\xE5',                            # ldr     r8, [r11,  #-0x38]
        b'\x00\x80\x28\xE0',                            # eor     r8, r8, r0
        b'\x08\x70\x87\xE1',                            # orr     r7, r7, r8
        b'\x07\x10\x21\xE0',                            # eor     r1, r1, r7
        b'\x58\x70\x1B\xE5',                            # ldr     r7, [r11,  #-0x58]
        b'\x07\x10\x81\xE0',                            # add     r1, r1, r7
        b'\x06\x10\x81\xE0',                            # add     r1, r1, r6
        b'\x2C\x60\x1B\xE5',                            # ldr     r6, [r11,  #-0x2c]
        b'\x01\x10\x86\xE0',                            # add     r1, r6, r1
        b'\x2C\x10\x0B\xE5',                            # str     r1, [r11,  #-0x2c]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x01\x13\xA0\xE1',                            # lsl     r1, r1, #0x6
        b'\x2C\x60\x1B\xE5',                            # ldr     r6, [r11,  #-0x2c]
        b'\x26\x6D\xA0\xE1',                            # lsr     r6, r6, #0x1a
        b'\x06\x10\x81\xE1',                            # orr     r1, r1, r6
        b'\x2C\x10\x0B\xE5',                            # str     r1, [r11,  #-0x2c]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x2C\x60\x1B\xE5',                            # ldr     r6, [r11,  #-0x2c]
        b'\x01\x10\x86\xE0',                            # add     r1, r6, r1
        b'\x2C\x10\x0B\xE5',                            # str     r1, [r11,  #-0x2c]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x2C\x60\x1B\xE5',                            # ldr     r6, [r11,  #-0x2c]
        b'\x34\x70\x1B\xE5',                            # ldr     r7, [r11,  #-0x34]
        b'\x00\x70\x27\xE0',                            # eor     r7, r7, r0
        b'\x07\x60\x86\xE1',                            # orr     r6, r6, r7
        b'\x06\x10\x21\xE0',                            # eor     r1, r1, r6
        b'\x3C\x60\x1B\xE5',                            # ldr     r6, [r11,  #-0x3c]
        b'\x06\x10\x81\xE0',                            # add     r1, r1, r6
        b'\x05\x10\x81\xE0',                            # add     r1, r1, r5
        b'\x38\x50\x1B\xE5',                            # ldr     r5, [r11,  #-0x38]
        b'\x01\x10\x85\xE0',                            # add     r1, r5, r1
        b'\x38\x10\x0B\xE5',                            # str     r1, [r11,  #-0x38]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x01\x15\xA0\xE1',                            # lsl     r1, r1, #0xa
        b'\x38\x50\x1B\xE5',                            # ldr     r5, [r11,  #-0x38]
        b'\x25\x5B\xA0\xE1',                            # lsr     r5, r5, #0x16
        b'\x05\x10\x81\xE1',                            # orr     r1, r1, r5
        b'\x38\x10\x0B\xE5',                            # str     r1, [r11,  #-0x38]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x38\x50\x1B\xE5',                            # ldr     r5, [r11,  #-0x38]
        b'\x01\x10\x85\xE0',                            # add     r1, r5, r1
        b'\x38\x10\x0B\xE5',                            # str     r1, [r11,  #-0x38]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x38\x50\x1B\xE5',                            # ldr     r5, [r11,  #-0x38]
        b'\x30\x60\x1B\xE5',                            # ldr     r6, [r11,  #-0x30]
        b'\x00\x60\x26\xE0',                            # eor     r6, r6, r0
        b'\x06\x50\x85\xE1',                            # orr     r5, r5, r6
        b'\x05\x10\x21\xE0',                            # eor     r1, r1, r5
        b'\x60\x50\x1B\xE5',                            # ldr     r5, [r11,  #-0x60]
        b'\x05\x10\x81\xE0',                            # add     r1, r1, r5
        b'\x04\x10\x81\xE0',                            # add     r1, r1, r4
        b'\x34\x40\x1B\xE5',                            # ldr     r4, [r11,  #-0x34]
        b'\x01\x10\x84\xE0',                            # add     r1, r4, r1
        b'\x34\x10\x0B\xE5',                            # str     r1, [r11,  #-0x34]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x81\x17\xA0\xE1',                            # lsl     r1, r1, #0xf
        b'\x34\x40\x1B\xE5',                            # ldr     r4, [r11,  #-0x34]
        b'\xA4\x48\xA0\xE1',                            # lsr     r4, r4, #0x11
        b'\x04\x10\x81\xE1',                            # orr     r1, r1, r4
        b'\x34\x10\x0B\xE5',                            # str     r1, [r11,  #-0x34]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x34\x40\x1B\xE5',                            # ldr     r4, [r11,  #-0x34]
        b'\x01\x10\x84\xE0',                            # add     r1, r4, r1
        b'\x34\x10\x0B\xE5',                            # str     r1, [r11,  #-0x34]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x34\x40\x1B\xE5',                            # ldr     r4, [r11,  #-0x34]
        b'\x2C\x50\x1B\xE5',                            # ldr     r5, [r11,  #-0x2c]
        b'\x00\x50\x25\xE0',                            # eor     r5, r5, r0
        b'\x05\x40\x84\xE1',                            # orr     r4, r4, r5
        b'\x04\x10\x21\xE0',                            # eor     r1, r1, r4
        b'\x44\x40\x1B\xE5',                            # ldr     r4, [r11,  #-0x44]
        b'\x04\x10\x81\xE0',                            # add     r1, r1, r4
        b'\x0E\x10\x81\xE0',                            # add     r1, r1, lr
        b'\x30\xE0\x1B\xE5',                            # ldr     lr, [r11,  #-0x30]
        b'\x01\x10\x8E\xE0',                            # add     r1, lr, r1
        b'\x30\x10\x0B\xE5',                            # str     r1, [r11,  #-0x30]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x81\x1A\xA0\xE1',                            # lsl     r1, r1, #0x15
        b'\x30\xE0\x1B\xE5',                            # ldr     lr, [r11,  #-0x30]
        b'\xAE\xE5\xA0\xE1',                            # lsr     lr, lr, #0xb
        b'\x0E\x10\x81\xE1',                            # orr     r1, r1, lr
        b'\x30\x10\x0B\xE5',                            # str     r1, [r11,  #-0x30]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x30\xE0\x1B\xE5',                            # ldr     lr, [r11,  #-0x30]
        b'\x01\x10\x8E\xE0',                            # add     r1, lr, r1
        b'\x30\x10\x0B\xE5',                            # str     r1, [r11,  #-0x30]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x30\xE0\x1B\xE5',                            # ldr     lr, [r11,  #-0x30]
        b'\x38\x40\x1B\xE5',                            # ldr     r4, [r11,  #-0x38]
        b'\x00\x40\x24\xE0',                            # eor     r4, r4, r0
        b'\x04\xE0\x8E\xE1',                            # orr     lr, lr, r4
        b'\x0E\x10\x21\xE0',                            # eor     r1, r1, lr
        b'\x68\xE0\x1B\xE5',                            # ldr     lr, [r11,  #-0x68]
        b'\x0E\x10\x81\xE0',                            # add     r1, r1, lr
        b'\x0C\x10\x81\xE0',                            # add     r1, r1, r12
        b'\x2C\xC0\x1B\xE5',                            # ldr     r12, [r11,  #-0x2c]
        b'\x01\x10\x8C\xE0',                            # add     r1, r12, r1
        b'\x2C\x10\x0B\xE5',                            # str     r1, [r11,  #-0x2c]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x01\x13\xA0\xE1',                            # lsl     r1, r1, #0x6
        b'\x2C\xC0\x1B\xE5',                            # ldr     r12, [r11,  #-0x2c]
        b'\x2C\xCD\xA0\xE1',                            # lsr     r12, r12, #0x1a
        b'\x0C\x10\x81\xE1',                            # orr     r1, r1, r12
        b'\x2C\x10\x0B\xE5',                            # str     r1, [r11,  #-0x2c]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x2C\xC0\x1B\xE5',                            # ldr     r12, [r11,  #-0x2c]
        b'\x01\x10\x8C\xE0',                            # add     r1, r12, r1
        b'\x2C\x10\x0B\xE5',                            # str     r1, [r11,  #-0x2c]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x2C\xC0\x1B\xE5',                            # ldr     r12, [r11,  #-0x2c]
        b'\x34\xE0\x1B\xE5',                            # ldr     lr, [r11,  #-0x34]
        b'\x00\xE0\x2E\xE0',                            # eor     lr, lr, r0
        b'\x0E\xC0\x8C\xE1',                            # orr     r12, r12, lr
        b'\x0C\x10\x21\xE0',                            # eor     r1, r1, r12
        b'\x4C\xC0\x1B\xE5',                            # ldr     r12, [r11,  #-0x4c]
        b'\x0C\x10\x81\xE0',                            # add     r1, r1, r12
        b'\x03\x10\x81\xE0',                            # add     r1, r1, r3
        b'\x38\x30\x1B\xE5',                            # ldr     r3, [r11,  #-0x38]
        b'\x01\x10\x83\xE0',                            # add     r1, r3, r1
        b'\x38\x10\x0B\xE5',                            # str     r1, [r11,  #-0x38]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x01\x15\xA0\xE1',                            # lsl     r1, r1, #0xa
        b'\x38\x30\x1B\xE5',                            # ldr     r3, [r11,  #-0x38]
        b'\x23\x3B\xA0\xE1',                            # lsr     r3, r3, #0x16
        b'\x03\x10\x81\xE1',                            # orr     r1, r1, r3
        b'\x38\x10\x0B\xE5',                            # str     r1, [r11,  #-0x38]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x38\x30\x1B\xE5',                            # ldr     r3, [r11,  #-0x38]
        b'\x01\x10\x83\xE0',                            # add     r1, r3, r1
        b'\x38\x10\x0B\xE5',                            # str     r1, [r11,  #-0x38]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x38\x30\x1B\xE5',                            # ldr     r3, [r11,  #-0x38]
        b'\x30\xC0\x1B\xE5',                            # ldr     r12, [r11,  #-0x30]
        b'\x00\xC0\x2C\xE0',                            # eor     r12, r12, r0
        b'\x0C\x30\x83\xE1',                            # orr     r3, r3, r12
        b'\x03\x10\x21\xE0',                            # eor     r1, r1, r3
        b'\x70\x30\x1B\xE5',                            # ldr     r3, [r11,  #-0x70]
        b'\x03\x10\x81\xE0',                            # add     r1, r1, r3
        b'\x02\x10\x81\xE0',                            # add     r1, r1, r2
        b'\x34\x20\x1B\xE5',                            # ldr     r2, [r11,  #-0x34]
        b'\x01\x10\x82\xE0',                            # add     r1, r2, r1
        b'\x34\x10\x0B\xE5',                            # str     r1, [r11,  #-0x34]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x81\x17\xA0\xE1',                            # lsl     r1, r1, #0xf
        b'\x34\x20\x1B\xE5',                            # ldr     r2, [r11,  #-0x34]
        b'\xA2\x28\xA0\xE1',                            # lsr     r2, r2, #0x11
        b'\x02\x10\x81\xE1',                            # orr     r1, r1, r2
        b'\x34\x10\x0B\xE5',                            # str     r1, [r11,  #-0x34]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x34\x20\x1B\xE5',                            # ldr     r2, [r11,  #-0x34]
        b'\x01\x10\x82\xE0',                            # add     r1, r2, r1
        b'\x34\x10\x0B\xE5',                            # str     r1, [r11,  #-0x34]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x34\x20\x1B\xE5',                            # ldr     r2, [r11,  #-0x34]
        b'\x2C\x30\x1B\xE5',                            # ldr     r3, [r11,  #-0x2c]
        b'\x00\x30\x23\xE0',                            # eor     r3, r3, r0
        b'\x03\x20\x82\xE1',                            # orr     r2, r2, r3
        b'\x02\x10\x21\xE0',                            # eor     r1, r1, r2
        b'\x54\x20\x1B\xE5',                            # ldr     r2, [r11,  #-0x54]
        b'\x02\x10\x81\xE0',                            # add     r1, r1, r2
        b'\xF0\x20\x9D\xE5',                            # ldr     r2, [sp,  #0xf0]
        b'\x02\x10\x81\xE0',                            # add     r1, r1, r2
        b'\x30\x30\x1B\xE5',                            # ldr     r3, [r11,  #-0x30]
        b'\x01\x10\x83\xE0',                            # add     r1, r3, r1
        b'\x30\x10\x0B\xE5',                            # str     r1, [r11,  #-0x30]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x81\x1A\xA0\xE1',                            # lsl     r1, r1, #0x15
        b'\x30\x30\x1B\xE5',                            # ldr     r3, [r11,  #-0x30]
        b'\xA3\x35\xA0\xE1',                            # lsr     r3, r3, #0xb
        b'\x03\x10\x81\xE1',                            # orr     r1, r1, r3
        b'\x30\x10\x0B\xE5',                            # str     r1, [r11,  #-0x30]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x30\x30\x1B\xE5',                            # ldr     r3, [r11,  #-0x30]
        b'\x01\x10\x83\xE0',                            # add     r1, r3, r1
        b'\x30\x10\x0B\xE5',                            # str     r1, [r11,  #-0x30]
        b'\x2C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x2c]
        b'\x24\x30\x1B\xE5',                            # ldr     r3, [r11,  #-0x24]
        b'\x00\xC0\x93\xE5',                            # ldr     r12, [r3]
        b'\x01\x10\x8C\xE0',                            # add     r1, r12, r1
        b'\x00\x10\x83\xE5',                            # str     r1, [r3]
        b'\x30\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x30]
        b'\x24\x30\x1B\xE5',                            # ldr     r3, [r11,  #-0x24]
        b'\x04\xC0\x93\xE5',                            # ldr     r12, [r3,  #0x4]
        b'\x01\x10\x8C\xE0',                            # add     r1, r12, r1
        b'\x04\x10\x83\xE5',                            # str     r1, [r3,  #0x4]
        b'\x34\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x34]
        b'\x24\x30\x1B\xE5',                            # ldr     r3, [r11,  #-0x24]
        b'\x08\xC0\x93\xE5',                            # ldr     r12, [r3,  #0x8]
        b'\x01\x10\x8C\xE0',                            # add     r1, r12, r1
        b'\x08\x10\x83\xE5',                            # str     r1, [r3,  #0x8]
        b'\x38\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x38]
        b'\x24\x30\x1B\xE5',                            # ldr     r3, [r11,  #-0x24]
        b'\x0C\xC0\x93\xE5',                            # ldr     r12, [r3,  #0xc]
        b'\x01\x10\x8C\xE0',                            # add     r1, r12, r1
        b'\x0C\x10\x83\xE5',                            # str     r1, [r3,  #0xc]
        b'\x7C\x10\x1B\xE5',                            # ldr     r1, [r11,  #-0x7c]
        b'\x01\x00\xA0\xE1',                            # mov     r0, r1
        b'\x00\x10\x00\xE3',                            # movw    r1, #0
        b'\x40\x20\x00\xE3',                            # movw    r2, #0x40
        b'\x69\x00\x00\xEB',                            # bl      0x2f98
        b'\x1C\xD0\x4B\xE2',                            # sub     sp, r11, #0x1c
        b'\xF0\x8F\xBD\xE8',                            # pop     {r4, r5, r6, r7, r8, r9, r10, r11, pc}
    ],
    'length': 0xC68
},
{
    'name': 'Decode',
    'description': 'int32_t Decode(int32_t arg1, int32_t* arg2, int32_t arg3)',
    'address': 0x2DF8,
    'instructions': [
        b'\x14\xD0\x4D\xE2',                            # sub     sp, sp, #0x14
        b'\x10\x00\x8D\xE5',                            # str     r0, [sp,  #0x10]
        b'\x0C\x10\x8D\xE5',                            # str     r1, [sp,  #0xc]
        b'\x08\x20\x8D\xE5',                            # str     r2, [sp,  #0x8]
        b'\x00\x00\x00\xE3',                            # movw    r0, #0
        b'\x04\x00\x8D\xE5',                            # str     r0, [sp,  #0x4]
        b'\x00\x00\x8D\xE5',                            # str     r0, [sp]
        b'\x00\x00\x9D\xE5',                            # ldr     r0, [sp]
        b'\x08\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x8]
        b'\x01\x00\x50\xE1',                            # cmp     r0, r1
        b'\x0D\x00\x00\x2A',                            # bhs     0x2e5c
        b'\x0C\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xc]
        b'\x00\x10\x9D\xE5',                            # ldr     r1, [sp]
        b'\x01\x00\x90\xE7',                            # ldr     r0, [r0, r1]
        b'\x10\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x10]
        b'\x04\x20\x9D\xE5',                            # ldr     r2, [sp,  #0x4]
        b'\x02\x11\x81\xE0',                            # add     r1, r1, r2, lsl  #0x2
        b'\x00\x00\x81\xE5',                            # str     r0, [r1]
        b'\x04\x00\x9D\xE5',                            # ldr     r0, [sp,  #0x4]
        b'\x01\x00\x80\xE2',                            # add     r0, r0, #0x1
        b'\x04\x00\x8D\xE5',                            # str     r0, [sp,  #0x4]
        b'\x00\x00\x9D\xE5',                            # ldr     r0, [sp]
        b'\x04\x00\x80\xE2',                            # add     r0, r0, #0x4
        b'\x00\x00\x8D\xE5',                            # str     r0, [sp]
        b'\xED\xFF\xFF\xEA',                            # b       0x2e14
        b'\x14\xD0\x8D\xE2',                            # add     sp, sp, #0x14
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x6C
},
{
    'name': 'Encode',
    'description': 'void* Encode(char* arg1, int32_t arg2, int32_t arg3)',
    'address': 0x2E64,
    'instructions': [
        b'\x14\xD0\x4D\xE2',                            # sub     sp, sp, #0x14
        b'\x10\x00\x8D\xE5',                            # str     r0, [sp,  #0x10]
        b'\x0C\x10\x8D\xE5',                            # str     r1, [sp,  #0xc]
        b'\x08\x20\x8D\xE5',                            # str     r2, [sp,  #0x8]
        b'\x00\x00\x00\xE3',                            # movw    r0, #0
        b'\x04\x00\x8D\xE5',                            # str     r0, [sp,  #0x4]
        b'\x00\x00\x8D\xE5',                            # str     r0, [sp]
        b'\x00\x00\x9D\xE5',                            # ldr     r0, [sp]
        b'\x08\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x8]
        b'\x01\x00\x50\xE1',                            # cmp     r0, r1
        b'\x27\x00\x00\x2A',                            # bhs     0x2f30
        b'\x0C\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xc]
        b'\x04\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x4]
        b'\x01\x01\x90\xE7',                            # ldr     r0, [r0, r1, lsl  #0x2]
        b'\x10\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x10]
        b'\x00\x20\x9D\xE5',                            # ldr     r2, [sp]
        b'\x02\x00\xC1\xE7',                            # strb    r0, [r1, r2]
        b'\x0C\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xc]
        b'\x04\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x4]
        b'\x01\x01\x90\xE7',                            # ldr     r0, [r0, r1, lsl  #0x2]
        b'\x20\x04\xA0\xE1',                            # lsr     r0, r0, #0x8
        b'\x10\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x10]
        b'\x00\x20\x9D\xE5',                            # ldr     r2, [sp]
        b'\x01\x10\x82\xE0',                            # add     r1, r2, r1
        b'\x01\x00\xC1\xE5',                            # strb    r0, [r1,  #0x1]
        b'\x0C\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xc]
        b'\x04\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x4]
        b'\x01\x01\x80\xE0',                            # add     r0, r0, r1, lsl  #0x2
        b'\xB2\x00\xD0\xE1',                            # ldrh    r0, [r0,  #0x2]
        b'\x10\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x10]
        b'\x00\x20\x9D\xE5',                            # ldr     r2, [sp]
        b'\x01\x10\x82\xE0',                            # add     r1, r2, r1
        b'\x02\x00\xC1\xE5',                            # strb    r0, [r1,  #0x2]
        b'\x0C\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xc]
        b'\x04\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x4]
        b'\x01\x01\x80\xE0',                            # add     r0, r0, r1, lsl  #0x2
        b'\x00\x00\x90\xE5',                            # ldr     r0, [r0]
        b'\x20\x0C\xA0\xE1',                            # lsr     r0, r0, #0x18
        b'\xFF\x00\x00\xE2',                            # and     r0, r0, #0xff
        b'\x10\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x10]
        b'\x00\x20\x9D\xE5',                            # ldr     r2, [sp]
        b'\x03\x20\x82\xE2',                            # add     r2, r2, #0x3
        b'\x02\x10\x81\xE0',                            # add     r1, r1, r2
        b'\x00\x00\xC1\xE5',                            # strb    r0, [r1]
        b'\x04\x00\x9D\xE5',                            # ldr     r0, [sp,  #0x4]
        b'\x01\x00\x80\xE2',                            # add     r0, r0, #0x1
        b'\x04\x00\x8D\xE5',                            # str     r0, [sp,  #0x4]
        b'\x00\x00\x9D\xE5',                            # ldr     r0, [sp]
        b'\x04\x00\x80\xE2',                            # add     r0, r0, #0x4
        b'\x00\x00\x8D\xE5',                            # str     r0, [sp]
        b'\xD3\xFF\xFF\xEA',                            # b       0x2e80
        b'\x14\xD0\x8D\xE2',                            # add     sp, sp, #0x14
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0xD4
},
{
    'name': 'MD5_memcpy',
    'description': 'int32_t MD5_memcpy(void* arg1, void* arg2, int32_t arg3)',
    'address': 0x2F38,
    'instructions': [
        b'\x10\xD0\x4D\xE2',                            # sub     sp, sp, #0x10
        b'\x0C\x00\x8D\xE5',                            # str     r0, [sp,  #0xc]
        b'\x08\x10\x8D\xE5',                            # str     r1, [sp,  #0x8]
        b'\x04\x20\x8D\xE5',                            # str     r2, [sp,  #0x4]
        b'\x00\x00\x00\xE3',                            # movw    r0, #0
        b'\x00\x00\x8D\xE5',                            # str     r0, [sp]
        b'\x00\x00\x9D\xE5',                            # ldr     r0, [sp]
        b'\x04\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x4]
        b'\x01\x00\x50\xE1',                            # cmp     r0, r1
        b'\x0B\x00\x00\x2A',                            # bhs     0x2f90
        b'\x08\x00\x9D\xE5',                            # ldr     r0, [sp,  #0x8]
        b'\x00\x10\x9D\xE5',                            # ldr     r1, [sp]
        b'\x01\x00\x80\xE0',                            # add     r0, r0, r1
        b'\x00\x00\xD0\xE5',                            # ldrb    r0, [r0]
        b'\x0C\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xc]
        b'\x00\x20\x9D\xE5',                            # ldr     r2, [sp]
        b'\x02\x10\x81\xE0',                            # add     r1, r1, r2
        b'\x00\x00\xC1\xE5',                            # strb    r0, [r1]
        b'\x00\x00\x9D\xE5',                            # ldr     r0, [sp]
        b'\x01\x00\x80\xE2',                            # add     r0, r0, #0x1
        b'\x00\x00\x8D\xE5',                            # str     r0, [sp]
        b'\xEF\xFF\xFF\xEA',                            # b       0x2f50
        b'\x10\xD0\x8D\xE2',                            # add     sp, sp, #0x10
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x60
},
{
    'name': 'MD5_memset',
    'description': 'int32_t MD5_memset(void* arg1, char arg2, int32_t arg3)',
    'address': 0x2F98,
    'instructions': [
        b'\x10\xD0\x4D\xE2',                            # sub     sp, sp, #0x10
        b'\x0C\x00\x8D\xE5',                            # str     r0, [sp,  #0xc]
        b'\x08\x10\x8D\xE5',                            # str     r1, [sp,  #0x8]
        b'\x04\x20\x8D\xE5',                            # str     r2, [sp,  #0x4]
        b'\x00\x00\x00\xE3',                            # movw    r0, #0
        b'\x00\x00\x8D\xE5',                            # str     r0, [sp]
        b'\x00\x00\x9D\xE5',                            # ldr     r0, [sp]
        b'\x04\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x4]
        b'\x01\x00\x50\xE1',                            # cmp     r0, r1
        b'\x08\x00\x00\x2A',                            # bhs     0x2fe4
        b'\x08\x00\x9D\xE5',                            # ldr     r0, [sp,  #0x8]
        b'\x0C\x10\x9D\xE5',                            # ldr     r1, [sp,  #0xc]
        b'\x00\x20\x9D\xE5',                            # ldr     r2, [sp]
        b'\x02\x10\x81\xE0',                            # add     r1, r1, r2
        b'\x00\x00\xC1\xE5',                            # strb    r0, [r1]
        b'\x00\x00\x9D\xE5',                            # ldr     r0, [sp]
        b'\x01\x00\x80\xE2',                            # add     r0, r0, #0x1
        b'\x00\x00\x8D\xE5',                            # str     r0, [sp]
        b'\xF2\xFF\xFF\xEA',                            # b       0x2fb0
        b'\x10\xD0\x8D\xE2',                            # add     sp, sp, #0x10
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x54
},
{
    'name': '__divsi3',
    'description': 'int32_t __divsi3(uint32_t arg1, uint32_t arg2)',
    'address': 0x2FEC,
    'instructions': [
        b'\x00\x00\x51\xE3',                            # cmp     r1, #0
        b'\x30\x00\x00\x0A',                            # beq     0x30b8
        b'\x00\x00\x50\xE3',                            # cmp     r0, #0
        b'\x02\x01\xE0\xC3',                            # mvngt   r0, #0x80000000
        b'\x02\x01\xA0\xB3',                            # movlt   r0, #0x80000000
        b'\x07\x00\x00\xEA',                            # b       0x30e8
    ],
    'length': 0xDC
},
{
    'name': '.divsi3_skip_div0_test',
    'description': 'void .divsi3_skip_div0_test(uint32_t arg1, uint32_t arg2)',
    'address': 0x2FF4,
    'instructions': [
        b'\x01\xC0\x20\xE0',                            # eor     r12, r0, r1
        b'\x00\x10\x61\x42',                            # rsbmi   r1, r1, #0
        b'\x01\x20\x51\xE2',                            # sub.s   r2, r1, #0x1
        b'\x1F\x00\x00\x0A',                            # beq     0x3084
        b'\x00\x30\xB0\xE1',                            # mov.s   r3, r0
        b'\x00\x30\x60\x42',                            # rsbmi   r3, r0, #0
        b'\x01\x00\x53\xE1',                            # cmp     r3, r1
        b'\x1E\x00\x00\x9A',                            # bls     0x3090
        b'\x02\x00\x11\xE1',                            # tst     r1, r2
        b'\x20\x00\x00\x0A',                            # beq     0x30a0
        b'\x11\x2F\x6F\xE1',                            # clz     r2, r1
        b'\x13\x0F\x6F\xE1',                            # clz     r0, r3
        b'\x00\x00\x42\xE0',                            # sub     r0, r2, r0
        b'\x01\x20\xA0\xE3',                            # mov     r2, #0x1
        b'\x11\x10\xA0\xE1',                            # lsl     r1, r1, r0
        b'\x12\x20\xA0\xE1',                            # lsl     r2, r2, r0
        b'\x00\x00\xA0\xE3',                            # mov     r0, #0
        b'\x01\x00\x53\xE1',                            # cmp     r3, r1
        b'\x01\x30\x43\x20',                            # subhs   r3, r3, r1
        b'\x02\x00\x80\x21',                            # orrhs   r0, r0, r2
        b'\xA1\x00\x53\xE1',                            # cmp     r3, r1, lsr  #0x1
        b'\xA1\x30\x43\x20',                            # subhs   r3, r3, r1, lsr  #0x1
        b'\xA2\x00\x80\x21',                            # orrhs   r0, r0, r2, lsr  #0x1
        b'\x21\x01\x53\xE1',                            # cmp     r3, r1, lsr  #0x2
        b'\x21\x31\x43\x20',                            # subhs   r3, r3, r1, lsr  #0x2
        b'\x22\x01\x80\x21',                            # orrhs   r0, r0, r2, lsr  #0x2
        b'\xA1\x01\x53\xE1',                            # cmp     r3, r1, lsr  #0x3
        b'\xA1\x31\x43\x20',                            # subhs   r3, r3, r1, lsr  #0x3
        b'\xA2\x01\x80\x21',                            # orrhs   r0, r0, r2, lsr  #0x3
        b'\x00\x00\x53\xE3',                            # cmp     r3, #0
        b'\x22\x22\xB0\x11',                            # lsr.sne r2, r2, #0x4
        b'\x21\x12\xA0\x11',                            # lsrne   r1, r1, #0x4
        b'\xEF\xFF\xFF\x1A',                            # bne     0x3038
        b'\x00\x00\x5C\xE3',                            # cmp     r12, #0
        b'\x00\x00\x60\x42',                            # rsbmi   r0, r0, #0
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
        b'\x00\x00\x3C\xE1',                            # teq     r12, r0
        b'\x00\x00\x60\x42',                            # rsbmi   r0, r0, #0
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
        b'\x00\x00\xA0\x33',                            # movlo   r0, #0
        b'\xCC\x0F\xA0\x01',                            # asreq   r0, r12, #0x1f
        b'\x01\x00\x80\x03',                            # orreq   r0, r0, #0x1
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
        b'\x11\x2F\x6F\xE1',                            # clz     r2, r1
        b'\x1F\x20\x62\xE2',                            # rsb     r2, r2, #0x1f
        b'\x00\x00\x5C\xE3',                            # cmp     r12, #0
        b'\x33\x02\xA0\xE1',                            # lsr     r0, r3, r2
        b'\x00\x00\x60\x42',                            # rsbmi   r0, r0, #0
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0xC4
},
{
    'name': '__aeabi_idivmod',
    'description': 'int32_t __aeabi_idivmod(uint32_t arg1, uint32_t arg2)',
    'address': 0x30C8,
    'instructions': [
        b'\x00\x00\x50\xE3',                            # cmp     r0, #0
        b'\x02\x01\xE0\xC3',                            # mvngt   r0, #0x80000000
        b'\x02\x01\xA0\xB3',                            # movlt   r0, #0x80000000
        b'\x07\x00\x00\xEA',                            # b       0x30e8
        b'\x00\x00\x51\xE3',                            # cmp     r1, #0
        b'\xF9\xFF\xFF\x0A',                            # beq     0x30b8
        b'\x03\x40\x2D\xE9',                            # push    {r0, r1, lr}
        b'\xC6\xFF\xFF\xEB',                            # bl      0x2ff4
        b'\x06\x40\xBD\xE8',                            # pop     {r1, r2, lr}
        b'\x92\x00\x03\xE0',                            # mul     r3, r2, r0
        b'\x03\x10\x41\xE0',                            # sub     r1, r1, r3
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x20
},
{
    'name': '__aeabi_ldiv0',
    'description': 'int32_t __aeabi_ldiv0()',
    'address': 0x30E8,
    'instructions': [
        b'\x02\x40\x2D\xE9',                            # push    {r1, lr}
        b'\x08\x00\xA0\xE3',                            # mov     r0, #0x8
        b'\x54\xF5\xFF\xEB',                            # bl      0x648
        b'\x02\x80\xBD\xE8',                            # pop     {r1, pc}
    ],
    'length': 0x10
},
{
    'name': 'selfrel_offset31',
    'description': 'void* selfrel_offset31(int32_t* arg1)',
    'address': 0x30F8,
    'instructions': [
        b'\x00\x30\x90\xE5',                            # ldr     r3, [r0]
        b'\x01\x01\x13\xE3',                            # tst     r3, #0x40000000
        b'\x02\x31\x83\x13',                            # orrne   r3, r3, #0x80000000
        b'\x02\x31\xC3\x03',                            # biceq   r3, r3, #0x80000000
        b'\x03\x00\x80\xE0',                            # add     r0, r0, r3
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x18
},
{
    'name': 'search_EIT_table',
    'description': 'void* search_EIT_table(void* arg1, void* arg2, int32_t arg3)',
    'address': 0x3110,
    'instructions': [
        b'\xF7\x4F\x2D\xE9',                            # push    {r0, r1, r2, r4, r5, r6, r7, r8, r9, r10, r11, lr}
        b'\x00\x00\x51\xE3',                            # cmp     r1, #0
        b'\x01\x50\xA0\xE1',                            # mov     r5, r1
        b'\x21\x00\x00\x0A',                            # beq     0x31a8
        b'\x01\x80\x41\xE2',                            # sub     r8, r1, #0x1
        b'\x02\x60\xA0\xE1',                            # mov     r6, r2
        b'\x00\x70\xA0\xE1',                            # mov     r7, r0
        b'\x00\xB0\xA0\xE3',                            # mov     r11, #0
        b'\x08\x90\xA0\xE1',                            # mov     r9, r8
        b'\x09\x40\x8B\xE0',                            # add     r4, r11, r9
        b'\xA4\x4F\x84\xE0',                            # add     r4, r4, r4, lsr  #0x1f
        b'\xC4\x40\xA0\xE1',                            # asr     r4, r4, #0x1
        b'\x84\xA1\xA0\xE1',                            # lsl     r10, r4, #0x3
        b'\x0A\x50\x87\xE0',                            # add     r5, r7, r10
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\xE9\xFF\xFF\xEB',                            # bl      0x30f8
        b'\x08\x00\x54\xE1',                            # cmp     r4, r8
        b'\x11\x00\x00\x0A',                            # beq     0x31a0
        b'\x04\x00\x8D\xE5',                            # str     r0, [sp,  #0x4]
        b'\x08\x00\x8A\xE2',                            # add     r0, r10, #0x8
        b'\x00\x00\x87\xE0',                            # add     r0, r7, r0
        b'\xE3\xFF\xFF\xEB',                            # bl      0x30f8
        b'\x04\x30\x9D\xE5',                            # ldr     r3, [sp,  #0x4]
        b'\x03\x00\x56\xE1',                            # cmp     r6, r3
        b'\x03\x00\x00\x2A',                            # bhs     0x3184
        b'\x0B\x00\x54\xE1',                            # cmp     r4, r11
        b'\x06\x00\x00\x0A',                            # beq     0x3198
        b'\x01\x90\x44\xE2',                            # sub     r9, r4, #0x1
        b'\xEB\xFF\xFF\xEA',                            # b       0x3134
        b'\x01\x00\x40\xE2',                            # sub     r0, r0, #0x1
        b'\x00\x00\x56\xE1',                            # cmp     r6, r0
        b'\x05\x00\x00\x9A',                            # bls     0x31a8
        b'\x01\xB0\x84\xE2',                            # add     r11, r4, #0x1
        b'\xE6\xFF\xFF\xEA',                            # b       0x3134
        b'\x00\x50\xA0\xE3',                            # mov     r5, #0
        b'\x01\x00\x00\xEA',                            # b       0x31a8
        b'\x00\x00\x56\xE1',                            # cmp     r6, r0
        b'\xF2\xFF\xFF\x3A',                            # blo     0x3174
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x0C\xD0\x8D\xE2',                            # add     sp, sp, #0xc
        b'\xF0\x8F\xBD\xE8',                            # pop     {r4, r5, r6, r7, r8, r9, r10, r11, pc}
    ],
    'length': 0xA4
},
{
    'name': '__gnu_unwind_get_pr_addr',
    'description': 'int32_t __gnu_unwind_get_pr_addr(int32_t arg1)',
    'address': 0x31B4,
    'instructions': [
        b'\x01\x00\x50\xE3',                            # cmp     r0, #0x1
        b'\x06\x00\x00\x0A',                            # beq     0x31d8
        b'\x02\x00\x50\xE3',                            # cmp     r0, #0x2
        b'\x07\x00\x00\x0A',                            # beq     0x31e4
        b'\x00\x00\x50\xE3',                            # cmp     r0, #0
        b'\x08\x00\x00\x1A',                            # bne     0x31f0
        b'\x24\x00\x9F\xE5',                            # ldr     r0, 0x31f8
        b'\x00\x00\x9F\xE7',                            # ldr     r0, [pc, r0]
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
        b'\x1C\x00\x9F\xE5',                            # ldr     r0, 0x31fc
        b'\x00\x00\x9F\xE7',                            # ldr     r0, [pc, r0]
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
        b'\x14\x00\x9F\xE5',                            # ldr     r0, 0x3200
        b'\x00\x00\x9F\xE7',                            # ldr     r0, [pc, r0]
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
        b'\x00\x00\xA0\xE3',                            # mov     r0, #0
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x44
},
{
    'name': 'get_eit_entry',
    'description': 'int32_t get_eit_entry(void* arg1, void* arg2)',
    'address': 0x3204,
    'instructions': [
        b'\xEC\x30\x9F\xE5',                            # ldr     r3, 0x32f8
        b'\x37\x40\x2D\xE9',                            # push    {r0, r1, r2, r4, r5, lr}
        b'\x00\x40\xA0\xE1',                            # mov     r4, r0
        b'\x03\x30\x9F\xE7',                            # ldr     r3, [pc, r3]
        b'\x02\x50\x41\xE2',                            # sub     r5, r1, #0x2
        b'\x00\x00\x53\xE3',                            # cmp     r3, #0
        b'\x08\x00\x00\x0A',                            # beq     0x3244
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x04\x10\x8D\xE2',                            # add     r1, sp, #0x4
        b'\x09\xF5\xFF\xEB',                            # bl      0x654
        b'\x00\x00\x50\xE3',                            # cmp     r0, #0
        b'\x0A\x00\x00\x1A',                            # bne     0x3260
        b'\x00\x30\xA0\xE3',                            # mov     r3, #0
        b'\x09\x00\xA0\xE3',                            # mov     r0, #0x9
        b'\x10\x30\x84\xE5',                            # str     r3, [r4,  #0x10]
        b'\x2A\x00\x00\xEA',                            # b       0x32f0
        b'\xB0\x30\x9F\xE5',                            # ldr     r3, 0x32fc
        b'\xB0\x00\x9F\xE5',                            # ldr     r0, 0x3300
        b'\x03\x30\x9F\xE7',                            # ldr     r3, [pc, r3]
        b'\x00\x00\x9F\xE7',                            # ldr     r0, [pc, r0]
        b'\x03\x30\x60\xE0',                            # rsb     r3, r0, r3
        b'\xC3\x31\xA0\xE1',                            # asr     r3, r3, #0x3
        b'\x04\x30\x8D\xE5',                            # str     r3, [sp,  #0x4]
        b'\x05\x20\xA0\xE1',                            # mov     r2, r5
        b'\x04\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x4]
        b'\xA8\xFF\xFF\xEB',                            # bl      0x3110
        b'\x00\x50\x50\xE2',                            # sub.s   r5, r0, #0
        b'\xEF\xFF\xFF\x0A',                            # beq     0x3234
        b'\x9F\xFF\xFF\xEB',                            # bl      0x30f8
        b'\x04\x30\x95\xE5',                            # ldr     r3, [r5,  #0x4]
        b'\x01\x00\x53\xE3',                            # cmp     r3, #0x1
        b'\x00\x30\xA0\x03',                            # moveq   r3, #0
        b'\x10\x30\x84\x05',                            # streq   r3, [r4,  #0x10]
        b'\x48\x00\x84\xE5',                            # str     r0, [r4,  #0x48]
        b'\x05\x00\xA0\x03',                            # moveq   r0, #0x5
        b'\x16\x00\x00\x0A',                            # beq     0x32f0
        b'\x00\x00\x53\xE3',                            # cmp     r3, #0
        b'\x04\x00\x85\xE2',                            # add     r0, r5, #0x4
        b'\x4C\x00\x84\xB5',                            # strlt   r0, [r4,  #0x4c]
        b'\x01\x30\xA0\xB3',                            # movlt   r3, #0x1
        b'\x02\x00\x00\xBA',                            # blt     0x32b4
        b'\x92\xFF\xFF\xEB',                            # bl      0x30f8
        b'\x00\x30\xA0\xE3',                            # mov     r3, #0
        b'\x4C\x00\x84\xE5',                            # str     r0, [r4,  #0x4c]
        b'\x4C\x00\x94\xE5',                            # ldr     r0, [r4,  #0x4c]
        b'\x50\x30\x84\xE5',                            # str     r3, [r4,  #0x50]
        b'\x00\x30\x90\xE5',                            # ldr     r3, [r0]
        b'\x00\x00\x53\xE3',                            # cmp     r3, #0
        b'\x06\x00\x00\xAA',                            # bge     0x32e4
        b'\x53\x0C\xE3\xE7',                            # ubfx    r0, r3, #0x18, #0x4
        b'\xB8\xFF\xFF\xEB',                            # bl      0x31b4
        b'\x00\x00\x50\xE3',                            # cmp     r0, #0
        b'\x10\x00\x84\xE5',                            # str     r0, [r4,  #0x10]
        b'\x09\x00\xA0\x03',                            # moveq   r0, #0x9
        b'\x00\x00\xA0\x13',                            # movne   r0, #0
        b'\x02\x00\x00\xEA',                            # b       0x32f0
        b'\x83\xFF\xFF\xEB',                            # bl      0x30f8
        b'\x10\x00\x84\xE5',                            # str     r0, [r4,  #0x10]
        b'\x00\x00\xA0\xE3',                            # mov     r0, #0
        b'\x0C\xD0\x8D\xE2',                            # add     sp, sp, #0xc
        b'\x30\x80\xBD\xE8',                            # pop     {r4, r5, pc}
    ],
    'length': 0xF4
},
{
    'name': 'restore_non_core_regs',
    'description': 'void restore_non_core_regs(int32_t* arg1)',
    'address': 0x3304,
    'instructions': [
        b'\x00\x30\x90\xE5',                            # ldr     r3, [r0]
        b'\x10\x40\x2D\xE9',                            # push    {r4, lr}
        b'\x01\x00\x13\xE3',                            # tst     r3, #0x1
        b'\x00\x40\xA0\xE1',                            # mov     r4, r0
        b'\x05\x00\x00\x1A',                            # bne     0x3330
        b'\x02\x00\x13\xE3',                            # tst     r3, #0x2
        b'\x48\x00\x80\xE2',                            # add     r0, r0, #0x48
        b'\x01\x00\x00\x0A',                            # beq     0x332c
        b'\x31\x03\x00\xEB',                            # bl      0x3ff0
        b'\x00\x00\x00\xEA',                            # b       0x3330
        b'\x2B\x03\x00\xEB',                            # bl      0x3fe0
        b'\x00\x30\x94\xE5',                            # ldr     r3, [r4]
        b'\x04\x00\x13\xE3',                            # tst     r3, #0x4
        b'\x01\x00\x00\x1A',                            # bne     0x3344
        b'\xD0\x00\x84\xE2',                            # add     r0, r4, #0xd0
        b'\x2E\x03\x00\xEB',                            # bl      0x4000
        b'\x00\x30\x94\xE5',                            # ldr     r3, [r4]
        b'\x08\x00\x13\xE3',                            # tst     r3, #0x8
        b'\x01\x00\x00\x1A',                            # bne     0x3358
        b'\x15\x0E\x84\xE2',                            # add     r0, r4, #0x150
        b'\x2D\x03\x00\xEB',                            # bl      0x4010
        b'\x00\x30\x94\xE5',                            # ldr     r3, [r4]
        b'\x10\x00\x13\xE3',                            # tst     r3, #0x10
        b'\x10\x80\xBD\x18',                            # popne   {r4, pc}
        b'\x1D\x0E\x84\xE2',                            # add     r0, r4, #0x1d0
        b'\x10\x40\xBD\xE8',                            # pop     {r4, lr}
        b'\x49\x03\x00\xEA',                            # b       0x4098
    ],
    'length': 0x6C
},
{
    'name': '_Unwind_decode_typeinfo_ptr.isra.0',
    'description': 'int32_t* _Unwind_decode_typeinfo_ptr.isra.0(int32_t* arg1)',
    'address': 0x3370,
    'instructions': [
        b'\x00\x30\x90\xE5',                            # ldr     r3, [r0]
        b'\x00\x00\x53\xE3',                            # cmp     r3, #0
        b'\x00\x00\x93\x17',                            # ldrne   r0, [r3, r0]
        b'\x03\x00\xA0\x01',                            # moveq   r0, r3
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x14
},
{
    'name': '__gnu_unwind_24bit.isra.1',
    'description': 'int32_t __gnu_unwind_24bit.isra.1()',
    'address': 0x3384,
    'instructions': [
        b'\x09\x00\xA0\xE3',                            # mov     r0, #0x9
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x8
},
{
    'name': '_Unwind_DebugHook',
    'description': 'int32_t _Unwind_DebugHook()',
    'address': 0x338C,
    'instructions': [
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x4
},
{
    'name': 'unwind_phase2',
    'description': 'int32_t unwind_phase2(void* arg1, void* arg2)',
    'address': 0x3390,
    'instructions': [
        b'\x70\x40\x2D\xE9',                            # push    {r4, r5, r6, lr}
        b'\x00\x50\xA0\xE1',                            # mov     r5, r0
        b'\x01\x40\xA0\xE1',                            # mov     r4, r1
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x40\x10\x94\xE5',                            # ldr     r1, [r4,  #0x40]
        b'\x96\xFF\xFF\xEB',                            # bl      0x3204
        b'\x00\x60\x50\xE2',                            # sub.s   r6, r0, #0
        b'\x00\x00\x00\x0A',                            # beq     0x33b4
        b'\xAA\xF4\xFF\xEB',                            # bl      0x660
        b'\x40\x30\x94\xE5',                            # ldr     r3, [r4,  #0x40]
        b'\x01\x00\xA0\xE3',                            # mov     r0, #0x1
        b'\x05\x10\xA0\xE1',                            # mov     r1, r5
        b'\x04\x20\xA0\xE1',                            # mov     r2, r4
        b'\x14\x30\x85\xE5',                            # str     r3, [r5,  #0x14]
        b'\x10\x30\x95\xE5',                            # ldr     r3, [r5,  #0x10]
        b'\x33\xFF\x2F\xE1',                            # blx     r3
        b'\x08\x00\x50\xE3',                            # cmp     r0, #0x8
        b'\xF0\xFF\xFF\x0A',                            # beq     0x339c
        b'\x07\x00\x50\xE3',                            # cmp     r0, #0x7
        b'\xF3\xFF\xFF\x1A',                            # bne     0x33b0
        b'\x06\x00\xA0\xE1',                            # mov     r0, r6
        b'\x40\x10\x94\xE5',                            # ldr     r1, [r4,  #0x40]
        b'\xE7\xFF\xFF\xEB',                            # bl      0x338c
        b'\x04\x00\x84\xE2',                            # add     r0, r4, #0x4
        b'\xF5\x02\x00\xEB',                            # bl      0x3fcc
    ],
    'length': 0x64
},
{
    'name': 'unwind_phase2_forced',
    'description': 'int32_t unwind_phase2_forced(void* arg1, void* arg2, int32_t arg3)',
    'address': 0x33F4,
    'instructions': [
        b'\xF0\x4F\x2D\xE9',                            # push    {r4, r5, r6, r7, r8, r9, r10, r11, lr}
        b'\x04\xE0\x81\xE2',                            # add     lr, r1, #0x4
        b'\x0C\x80\x90\xE5',                            # ldr     r8, [r0,  #0xc]
        b'\x00\x40\xA0\xE1',                            # mov     r4, r0
        b'\x18\x90\x90\xE5',                            # ldr     r9, [r0,  #0x18]
        b'\x02\xA0\xA0\xE1',                            # mov     r10, r2
        b'\x0F\x00\xBE\xE8',                            # ldm     lr!, {r0, r1, r2, r3}
        b'\xF3\xDF\x4D\xE2',                            # sub     sp, sp, #0x3cc
        b'\x0C\xC0\x8D\xE2',                            # add     r12, sp, #0xc
        b'\x08\xB0\x8D\xE2',                            # add     r11, sp, #0x8
        b'\x7A\x7F\x8D\xE2',                            # add     r7, sp, #0x1e8
        b'\x00\x60\xA0\xE3',                            # mov     r6, #0
        b'\x0F\x00\xAC\xE8',                            # stm     r12!, {r0, r1, r2, r3}
        b'\x0F\x00\xBE\xE8',                            # ldm     lr!, {r0, r1, r2, r3}
        b'\x0F\x00\xAC\xE8',                            # stm     r12!, {r0, r1, r2, r3}
        b'\x0F\x00\xBE\xE8',                            # ldm     lr!, {r0, r1, r2, r3}
        b'\x0F\x00\xAC\xE8',                            # stm     r12!, {r0, r1, r2, r3}
        b'\x0F\x00\x9E\xE8',                            # ldm     lr, {r0, r1, r2, r3}
        b'\x0F\x00\x8C\xE8',                            # stm     r12, {r0, r1, r2, r3}
        b'\x08\x60\x8D\xE5',                            # str     r6, [sp,  #0x8]
        b'\x04\x00\xA0\xE1',                            # mov     r0, r4
        b'\x48\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x48]
        b'\x6C\xFF\xFF\xEB',                            # bl      0x3204
        b'\x00\x00\x5A\xE3',                            # cmp     r10, #0
        b'\x0A\xA0\xA0\x13',                            # movne   r10, #0xa
        b'\x09\xA0\xA0\x03',                            # moveq   r10, #0x9
        b'\x00\x50\x50\xE2',                            # sub.s   r5, r0, #0
        b'\x10\xA0\x8A\x13',                            # orrne   r10, r10, #0x10
        b'\x40\x30\x9D\x15',                            # ldrne   r3, [sp,  #0x40]
        b'\x0C\x00\x00\x1A',                            # bne     0x34a0
        b'\x48\x30\x9D\xE5',                            # ldr     r3, [sp,  #0x48]
        b'\x0B\x10\xA0\xE1',                            # mov     r1, r11
        b'\x1E\x2E\xA0\xE3',                            # mov     r2, #0x1e0
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\x14\x30\x84\xE5',                            # str     r3, [r4,  #0x14]
        b'\x79\xF4\xFF\xEB',                            # bl      0x66c
        b'\x10\x30\x94\xE5',                            # ldr     r3, [r4,  #0x10]
        b'\x0A\x00\xA0\xE1',                            # mov     r0, r10
        b'\x04\x10\xA0\xE1',                            # mov     r1, r4
        b'\x07\x20\xA0\xE1',                            # mov     r2, r7
        b'\x33\xFF\x2F\xE1',                            # blx     r3
        b'\x20\x32\x9D\xE5',                            # ldr     r3, [sp,  #0x220]
        b'\x00\x60\xA0\xE1',                            # mov     r6, r0
        b'\x4C\x30\x8D\xE5',                            # str     r3, [sp,  #0x4c]
        b'\x01\x00\xA0\xE3',                            # mov     r0, #0x1
        b'\x00\xB0\x8D\xE5',                            # str     r11, [sp]
        b'\x0A\x10\xA0\xE1',                            # mov     r1, r10
        b'\x04\x90\x8D\xE5',                            # str     r9, [sp,  #0x4]
        b'\x04\x20\xA0\xE1',                            # mov     r2, r4
        b'\x04\x30\xA0\xE1',                            # mov     r3, r4
        b'\x38\xFF\x2F\xE1',                            # blx     r8
        b'\x00\x00\x50\xE3',                            # cmp     r0, #0
        b'\x0F\x00\x00\x1A',                            # bne     0x3508
        b'\x00\x00\x55\xE3',                            # cmp     r5, #0
        b'\x0F\x00\x00\x1A',                            # bne     0x3510
        b'\x0B\x00\xA0\xE1',                            # mov     r0, r11
        b'\x07\x10\xA0\xE1',                            # mov     r1, r7
        b'\x1E\x2E\xA0\xE3',                            # mov     r2, #0x1e0
        b'\x05\xA0\xA0\xE1',                            # mov     r10, r5
        b'\x61\xF4\xFF\xEB',                            # bl      0x66c
        b'\x08\x00\x56\xE3',                            # cmp     r6, #0x8
        b'\xD5\xFF\xFF\x0A',                            # beq     0x3444
        b'\x07\x00\x56\xE3',                            # cmp     r6, #0x7
        b'\x04\x00\x00\x1A',                            # bne     0x3508
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x48\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x48]
        b'\xA2\xFF\xFF\xEB',                            # bl      0x338c
        b'\x0C\x00\x8D\xE2',                            # add     r0, sp, #0xc
        b'\xB0\x02\x00\xEB',                            # bl      0x3fcc
        b'\x09\x00\xA0\xE3',                            # mov     r0, #0x9
        b'\x00\x00\x00\xEA',                            # b       0x3514
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\xF3\xDF\x8D\xE2',                            # add     sp, sp, #0x3cc
        b'\xF0\x8F\xBD\xE8',                            # pop     {r4, r5, r6, r7, r8, r9, r10, r11, pc}
    ],
    'length': 0x128
},
{
    'name': '_Unwind_GetCFA',
    'description': 'int32_t _Unwind_GetCFA(void* arg1)',
    'address': 0x351C,
    'instructions': [
        b'\x44\x00\x90\xE5',                            # ldr     r0, [r0,  #0x44]
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x8
},
{
    'name': '__gnu_Unwind_RaiseException',
    'description': 'int32_t __gnu_Unwind_RaiseException(void* arg1, void* arg2)',
    'address': 0x3524,
    'instructions': [
        b'\x3C\x30\x91\xE5',                            # ldr     r3, [r1,  #0x3c]
        b'\xF0\x40\x2D\xE9',                            # push    {r4, r5, r6, r7, lr}
        b'\x04\xE0\x81\xE2',                            # add     lr, r1, #0x4
        b'\x40\x30\x81\xE5',                            # str     r3, [r1,  #0x40]
        b'\x00\x50\xA0\xE1',                            # mov     r5, r0
        b'\x01\x40\xA0\xE1',                            # mov     r4, r1
        b'\x79\xDF\x4D\xE2',                            # sub     sp, sp, #0x1e4
        b'\x0F\x00\xBE\xE8',                            # ldm     lr!, {r0, r1, r2, r3}
        b'\x04\xC0\x8D\xE2',                            # add     r12, sp, #0x4
        b'\x1E\x6E\x8D\xE2',                            # add     r6, sp, #0x1e0
        b'\x0F\x00\xAC\xE8',                            # stm     r12!, {r0, r1, r2, r3}
        b'\x0F\x00\xBE\xE8',                            # ldm     lr!, {r0, r1, r2, r3}
        b'\x0F\x00\xAC\xE8',                            # stm     r12!, {r0, r1, r2, r3}
        b'\x0F\x00\xBE\xE8',                            # ldm     lr!, {r0, r1, r2, r3}
        b'\x0F\x00\xAC\xE8',                            # stm     r12!, {r0, r1, r2, r3}
        b'\x0F\x00\x9E\xE8',                            # ldm     lr, {r0, r1, r2, r3}
        b'\x0F\x00\x8C\xE8',                            # stm     r12, {r0, r1, r2, r3}
        b'\x00\x30\xE0\xE3',                            # mvn     r3, #0
        b'\xE0\x31\x26\xE5',                            # str     r3, [r6,  #-0x1e0]!
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x40\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x40]
        b'\x21\xFF\xFF\xEB',                            # bl      0x3204
        b'\x00\x00\x50\xE3',                            # cmp     r0, #0
        b'\x0D\x00\x00\x1A',                            # bne     0x35bc
        b'\x10\x30\x95\xE5',                            # ldr     r3, [r5,  #0x10]
        b'\x05\x10\xA0\xE1',                            # mov     r1, r5
        b'\x06\x20\xA0\xE1',                            # mov     r2, r6
        b'\x33\xFF\x2F\xE1',                            # blx     r3
        b'\x08\x00\x50\xE3',                            # cmp     r0, #0x8
        b'\x00\x70\xA0\xE1',                            # mov     r7, r0
        b'\xF3\xFF\xFF\x0A',                            # beq     0x3570
        b'\x06\x00\xA0\xE1',                            # mov     r0, r6
        b'\x56\xFF\xFF\xEB',                            # bl      0x3304
        b'\x06\x00\x57\xE3',                            # cmp     r7, #0x6
        b'\x02\x00\x00\x1A',                            # bne     0x35bc
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x04\x10\xA0\xE1',                            # mov     r1, r4
        b'\x74\xFF\xFF\xEB',                            # bl      0x3390
        b'\x09\x00\xA0\xE3',                            # mov     r0, #0x9
        b'\x79\xDF\x8D\xE2',                            # add     sp, sp, #0x1e4
        b'\xF0\x80\xBD\xE8',                            # pop     {r4, r5, r6, r7, pc}
    ],
    'length': 0xA4
},
{
    'name': '__gnu_Unwind_ForcedUnwind',
    'description': 'int32_t __gnu_Unwind_ForcedUnwind(void* arg1, int32_t arg2, int32_t arg3, void* arg4)',
    'address': 0x35C8,
    'instructions': [
        b'\x18\x20\x80\xE5',                            # str     r2, [r0,  #0x18]
        b'\x3C\x20\x93\xE5',                            # ldr     r2, [r3,  #0x3c]
        b'\x0C\x10\x80\xE5',                            # str     r1, [r0,  #0xc]
        b'\x03\x10\xA0\xE1',                            # mov     r1, r3
        b'\x40\x20\x83\xE5',                            # str     r2, [r3,  #0x40]
        b'\x00\x20\xA0\xE3',                            # mov     r2, #0
        b'\x83\xFF\xFF\xEA',                            # b       0x33f4
    ],
    'length': 0x1C
},
{
    'name': '__gnu_Unwind_Resume',
    'description': 'int32_t __gnu_Unwind_Resume(void* arg1, void* arg2) __noreturn',
    'address': 0x35E4,
    'instructions': [
        b'\x70\x40\x2D\xE9',                            # push    {r4, r5, r6, lr}
        b'\x00\x50\xA0\xE1',                            # mov     r5, r0
        b'\x0C\x60\x90\xE5',                            # ldr     r6, [r0,  #0xc]
        b'\x01\x40\xA0\xE1',                            # mov     r4, r1
        b'\x14\x30\x90\xE5',                            # ldr     r3, [r0,  #0x14]
        b'\x00\x00\x56\xE3',                            # cmp     r6, #0
        b'\x40\x30\x81\xE5',                            # str     r3, [r1,  #0x40]
        b'\x02\x00\x00\x0A',                            # beq     0x3610
        b'\x01\x20\xA0\xE3',                            # mov     r2, #0x1
        b'\x79\xFF\xFF\xEB',                            # bl      0x33f4
        b'\x10\x00\x00\xEA',                            # b       0x3654
        b'\x10\x30\x90\xE5',                            # ldr     r3, [r0,  #0x10]
        b'\x05\x10\xA0\xE1',                            # mov     r1, r5
        b'\x02\x00\xA0\xE3',                            # mov     r0, #0x2
        b'\x04\x20\xA0\xE1',                            # mov     r2, r4
        b'\x33\xFF\x2F\xE1',                            # blx     r3
        b'\x07\x00\x50\xE3',                            # cmp     r0, #0x7
        b'\x04\x00\x00\x0A',                            # beq     0x3640
        b'\x08\x00\x50\xE3',                            # cmp     r0, #0x8
        b'\x07\x00\x00\x1A',                            # bne     0x3654
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x04\x10\xA0\xE1',                            # mov     r1, r4
        b'\x53\xFF\xFF\xEB',                            # bl      0x3390
        b'\x06\x00\xA0\xE1',                            # mov     r0, r6
        b'\x40\x10\x94\xE5',                            # ldr     r1, [r4,  #0x40]
        b'\x4F\xFF\xFF\xEB',                            # bl      0x338c
        b'\x04\x00\x84\xE2',                            # add     r0, r4, #0x4
        b'\x5D\x02\x00\xEB',                            # bl      0x3fcc
        b'\x01\xF4\xFF\xEB',                            # bl      0x660
    ],
    'length': 0x74
},
{
    'name': '__gnu_Unwind_Resume_or_Rethrow',
    'description': 'int32_t __gnu_Unwind_Resume_or_Rethrow(void* arg1, void* arg2)',
    'address': 0x3658,
    'instructions': [
        b'\x0C\x20\x90\xE5',                            # ldr     r2, [r0,  #0xc]
        b'\x00\x00\x52\xE3',                            # cmp     r2, #0
        b'\x00\x00\x00\x1A',                            # bne     0x3668
        b'\xAE\xFF\xFF\xEA',                            # b       0x3524
        b'\x3C\x20\x91\xE5',                            # ldr     r2, [r1,  #0x3c]
        b'\x40\x20\x81\xE5',                            # str     r2, [r1,  #0x40]
        b'\x00\x20\xA0\xE3',                            # mov     r2, #0
        b'\x5E\xFF\xFF\xEA',                            # b       0x33f4
    ],
    'length': 0x20
},
{
    'name': '_Unwind_Complete',
    'description': 'int32_t _Unwind_Complete()',
    'address': 0x3678,
    'instructions': [
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x4
},
{
    'name': '_Unwind_DeleteException',
    'description': 'void _Unwind_DeleteException(void* arg1)',
    'address': 0x367C,
    'instructions': [
        b'\x08\x30\x90\xE5',                            # ldr     r3, [r0,  #0x8]
        b'\x00\x10\xA0\xE1',                            # mov     r1, r0
        b'\x00\x00\x53\xE3',                            # cmp     r3, #0
        b'\x1E\xFF\x2F\x01',                            # bxeq    lr
        b'\x01\x00\xA0\xE3',                            # mov     r0, #0x1
        b'\x13\xFF\x2F\xE1',                            # bx      r3
    ],
    'length': 0x18
},
{
    'name': '_Unwind_VRS_Get',
    'description': 'int32_t _Unwind_VRS_Get(int32_t arg1, int32_t arg2, int32_t arg3, int32_t arg4, int32_t* arg5)',
    'address': 0x3694,
    'instructions': [
        b'\x04\x00\x51\xE3',                            # cmp     r1, #0x4
        b'\x01\xF1\x8F\x90',                            # addls   pc, pc, r1, lsl  #0x2
        b'\x11\x00\x00\xEA',                            # b       0x36e8
        b'\x03\x00\x00\xEA',                            # b       0x36b4
        b'\x0D\x00\x00\xEA',                            # b       0x36e0
        b'\x0E\x00\x00\xEA',                            # b       0x36e8
        b'\x0B\x00\x00\xEA',                            # b       0x36e0
        b'\x0A\x00\x00\xEA',                            # b       0x36e0
        b'\x0F\x00\x52\xE3',                            # cmp     r2, #0xf
        b'\x00\x00\x53\x93',                            # cmpls   r3, #0
        b'\x01\x30\xA0\x13',                            # movne   r3, #0x1
        b'\x00\x30\xA0\x03',                            # moveq   r3, #0
        b'\x07\x00\x00\x1A',                            # bne     0x36e8
        b'\x02\x01\x80\xE0',                            # add     r0, r0, r2, lsl  #0x2
        b'\x00\x20\x9D\xE5',                            # ldr     r2, [sp]
        b'\x04\x10\x90\xE5',                            # ldr     r1, [r0,  #0x4]
        b'\x03\x00\xA0\xE1',                            # mov     r0, r3
        b'\x00\x10\x82\xE5',                            # str     r1, [r2]
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
        b'\x01\x00\xA0\xE3',                            # mov     r0, #0x1
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
        b'\x02\x00\xA0\xE3',                            # mov     r0, #0x2
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x5C
},
{
    'name': '_Unwind_GetGR',
    'description': 'int32_t _Unwind_GetGR(int32_t arg1, int32_t arg2, int32_t arg3, int32_t arg4)',
    'address': 0x36F0,
    'instructions': [
        b'\x1F\x40\x2D\xE9',                            # push    {r0, r1, r2, r3, r4, lr}
        b'\x01\x20\xA0\xE1',                            # mov     r2, r1
        b'\x00\x10\xA0\xE3',                            # mov     r1, #0
        b'\x0C\x30\x8D\xE2',                            # add     r3, sp, #0xc
        b'\x00\x30\x8D\xE5',                            # str     r3, [sp]
        b'\x01\x30\xA0\xE1',                            # mov     r3, r1
        b'\xE1\xFF\xFF\xEB',                            # bl      0x3694
        b'\x0C\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xc]
        b'\x14\xD0\x8D\xE2',                            # add     sp, sp, #0x14
        b'\x04\xF0\x9D\xE4',                            # ldr     pc, [sp],  #0x4
    ],
    'length': 0x28
},
{
    'name': '_Unwind_VRS_Set',
    'description': 'int32_t _Unwind_VRS_Set(int32_t arg1, int32_t arg2, int32_t arg3, int32_t arg4, int32_t* arg5)',
    'address': 0x3718,
    'instructions': [
        b'\x04\x00\x51\xE3',                            # cmp     r1, #0x4
        b'\x01\xF1\x8F\x90',                            # addls   pc, pc, r1, lsl  #0x2
        b'\x11\x00\x00\xEA',                            # b       0x376c
        b'\x03\x00\x00\xEA',                            # b       0x3738
        b'\x0D\x00\x00\xEA',                            # b       0x3764
        b'\x0E\x00\x00\xEA',                            # b       0x376c
        b'\x0B\x00\x00\xEA',                            # b       0x3764
        b'\x0A\x00\x00\xEA',                            # b       0x3764
        b'\x0F\x00\x52\xE3',                            # cmp     r2, #0xf
        b'\x00\x00\x53\x93',                            # cmpls   r3, #0
        b'\x01\x30\xA0\x13',                            # movne   r3, #0x1
        b'\x00\x30\xA0\x03',                            # moveq   r3, #0
        b'\x07\x00\x00\x1A',                            # bne     0x376c
        b'\x00\x10\x9D\xE5',                            # ldr     r1, [sp]
        b'\x02\x01\x80\xE0',                            # add     r0, r0, r2, lsl  #0x2
        b'\x00\x10\x91\xE5',                            # ldr     r1, [r1]
        b'\x04\x10\x80\xE5',                            # str     r1, [r0,  #0x4]
        b'\x03\x00\xA0\xE1',                            # mov     r0, r3
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
        b'\x01\x00\xA0\xE3',                            # mov     r0, #0x1
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
        b'\x02\x00\xA0\xE3',                            # mov     r0, #0x2
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x5C
},
{
    'name': '_Unwind_SetGR',
    'description': 'int32_t _Unwind_SetGR(int32_t arg1, int32_t arg2, int32_t arg3, int32_t arg4)',
    'address': 0x3774,
    'instructions': [
        b'\x1F\x40\x2D\xE9',                            # push    {r0, r1, r2, r3, r4, lr}
        b'\x10\x30\x8D\xE2',                            # add     r3, sp, #0x10
        b'\x01\xC0\xA0\xE1',                            # mov     r12, r1
        b'\x00\x10\xA0\xE3',                            # mov     r1, #0
        b'\x04\x20\x23\xE5',                            # str     r2, [r3,  #-0x4]!
        b'\x0C\x20\xA0\xE1',                            # mov     r2, r12
        b'\x00\x30\x8D\xE5',                            # str     r3, [sp]
        b'\x01\x30\xA0\xE1',                            # mov     r3, r1
        b'\xDF\xFF\xFF\xEB',                            # bl      0x3718
        b'\x14\xD0\x8D\xE2',                            # add     sp, sp, #0x14
        b'\x04\xF0\x9D\xE4',                            # ldr     pc, [sp],  #0x4
    ],
    'length': 0x2C
},
{
    'name': '__gnu_Unwind_Backtrace',
    'description': 'int32_t __gnu_Unwind_Backtrace(int32_t arg1, int32_t arg2, void* arg3)',
    'address': 0x37A0,
    'instructions': [
        b'\x3C\x30\x92\xE5',                            # ldr     r3, [r2,  #0x3c]
        b'\x04\xC0\x82\xE2',                            # add     r12, r2, #0x4
        b'\xF0\x41\x2D\xE9',                            # push    {r4, r5, r6, r7, r8, lr}
        b'\x00\x70\xA0\xE1',                            # mov     r7, r0
        b'\x40\x30\x82\xE5',                            # str     r3, [r2,  #0x40]
        b'\x01\x80\xA0\xE1',                            # mov     r8, r1
        b'\x0F\x00\xBC\xE8',                            # ldm     r12!, {r0, r1, r2, r3}
        b'\x8E\xDF\x4D\xE2',                            # sub     sp, sp, #0x238
        b'\x5C\xE0\x8D\xE2',                            # add     lr, sp, #0x5c
        b'\x58\x40\x8D\xE2',                            # add     r4, sp, #0x58
        b'\x0D\x60\xA0\xE1',                            # mov     r6, sp
        b'\x0F\x00\xAE\xE8',                            # stm     lr!, {r0, r1, r2, r3}
        b'\x0F\x00\xBC\xE8',                            # ldm     r12!, {r0, r1, r2, r3}
        b'\x0F\x00\xAE\xE8',                            # stm     lr!, {r0, r1, r2, r3}
        b'\x0F\x00\xBC\xE8',                            # ldm     r12!, {r0, r1, r2, r3}
        b'\x0F\x00\xAE\xE8',                            # stm     lr!, {r0, r1, r2, r3}
        b'\x0F\x00\x9C\xE8',                            # ldm     r12, {r0, r1, r2, r3}
        b'\x0F\x00\x8E\xE8',                            # stm     lr, {r0, r1, r2, r3}
        b'\x00\x30\xE0\xE3',                            # mvn     r3, #0
        b'\x58\x30\x8D\xE5',                            # str     r3, [sp,  #0x58]
        b'\x06\x00\xA0\xE1',                            # mov     r0, r6
        b'\x98\x10\x9D\xE5',                            # ldr     r1, [sp,  #0x98]
        b'\x81\xFE\xFF\xEB',                            # bl      0x3204
        b'\x00\x00\x50\xE3',                            # cmp     r0, #0
        b'\x01\x00\x00\x0A',                            # beq     0x380c
        b'\x09\x50\xA0\xE3',                            # mov     r5, #0x9
        b'\x11\x00\x00\xEA',                            # b       0x3854
        b'\x04\x00\xA0\xE1',                            # mov     r0, r4
        b'\x0C\x10\xA0\xE3',                            # mov     r1, #0xc
        b'\x06\x20\xA0\xE1',                            # mov     r2, r6
        b'\xD5\xFF\xFF\xEB',                            # bl      0x3774
        b'\x04\x00\xA0\xE1',                            # mov     r0, r4
        b'\x08\x10\xA0\xE1',                            # mov     r1, r8
        b'\x37\xFF\x2F\xE1',                            # blx     r7
        b'\x00\x00\x50\xE3',                            # cmp     r0, #0
        b'\xF4\xFF\xFF\x1A',                            # bne     0x3804
        b'\x10\x30\x9D\xE5',                            # ldr     r3, [sp,  #0x10]
        b'\x08\x00\xA0\xE3',                            # mov     r0, #0x8
        b'\x06\x10\xA0\xE1',                            # mov     r1, r6
        b'\x04\x20\xA0\xE1',                            # mov     r2, r4
        b'\x33\xFF\x2F\xE1',                            # blx     r3
        b'\x05\x30\x40\xE2',                            # sub     r3, r0, #0x5
        b'\x00\x50\xA0\xE1',                            # mov     r5, r0
        b'\x04\x30\xD3\xE3',                            # bic.s   r3, r3, #0x4
        b'\xE6\xFF\xFF\x1A',                            # bne     0x37f0
        b'\x04\x00\xA0\xE1',                            # mov     r0, r4
        b'\xA9\xFE\xFF\xEB',                            # bl      0x3304
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x8E\xDF\x8D\xE2',                            # add     sp, sp, #0x238
        b'\xF0\x81\xBD\xE8',                            # pop     {r4, r5, r6, r7, r8, pc}
    ],
    'length': 0xC8
},
{
    'name': '__gnu_unwind_pr_common',
    'description': 'int32_t __gnu_unwind_pr_common(int32_t arg1, void* arg2, int32_t* arg3, int32_t arg4)',
    'address': 0x3868,
    'instructions': [
        b'\xF0\x4F\x2D\xE9',                            # push    {r4, r5, r6, r7, r8, r9, r10, r11, lr}
        b'\x02\x70\xA0\xE1',                            # mov     r7, r2
        b'\x4C\x20\x91\xE5',                            # ldr     r2, [r1,  #0x4c]
        b'\x24\xD0\x4D\xE2',                            # sub     sp, sp, #0x24
        b'\x00\x90\x53\xE2',                            # sub.s   r9, r3, #0
        b'\x01\x50\xA0\xE1',                            # mov     r5, r1
        b'\x04\xC0\x82\xE2',                            # add     r12, r2, #0x4
        b'\x03\x80\x00\xE2',                            # and     r8, r0, #0x3
        b'\x00\x40\x92\xE5',                            # ldr     r4, [r2]
        b'\x18\xC0\x8D\xE5',                            # str     r12, [sp,  #0x18]
        b'\x14\x40\x8D\xE5',                            # str     r4, [sp,  #0x14]
        b'\x05\x00\x00\x1A',                            # bne     0x38b0
        b'\x04\x44\xA0\xE1',                            # lsl     r4, r4, #0x8
        b'\x03\x30\xA0\xE3',                            # mov     r3, #0x3
        b'\x14\x40\x8D\xE5',                            # str     r4, [sp,  #0x14]
        b'\x1D\x90\xCD\xE5',                            # strb    r9, [sp,  #0x1d]
        b'\x1C\x30\xCD\xE5',                            # strb    r3, [sp,  #0x1c]
        b'\x09\x00\x00\xEA',                            # b       0x38d8
        b'\x02\x00\x59\xE3',                            # cmp     r9, #0x2
        b'\x07\x00\x00\xCA',                            # bgt     0x38d8
        b'\x24\x38\xA0\xE1',                            # lsr     r3, r4, #0x10
        b'\x1D\x30\xCD\xE5',                            # strb    r3, [sp,  #0x1d]
        b'\x04\x48\xA0\xE1',                            # lsl     r4, r4, #0x10
        b'\x02\x20\xA0\xE3',                            # mov     r2, #0x2
        b'\x73\x30\xEF\xE6',                            # uxtb    r3, r3, ror  #0
        b'\x14\x40\x8D\xE5',                            # str     r4, [sp,  #0x14]
        b'\x1C\x20\xCD\xE5',                            # strb    r2, [sp,  #0x1c]
        b'\x03\xC1\x8C\xE0',                            # add     r12, r12, r3, lsl  #0x2
        b'\x02\x00\x58\xE3',                            # cmp     r8, #0x2
        b'\x50\x30\x95\xE5',                            # ldr     r3, [r5,  #0x50]
        b'\x38\xC0\x95\x05',                            # ldreq   r12, [r5,  #0x38]
        b'\x01\x30\x13\xE2',                            # and.s   r3, r3, #0x1
        b'\xAF\x00\x00\x1A',                            # bne     0x3bac
        b'\x08\x00\x20\xE2',                            # eor     r0, r0, #0x8
        b'\x04\x30\x8D\xE5',                            # str     r3, [sp,  #0x4]
        b'\xD0\x31\xE0\xE7',                            # ubfx    r3, r0, #0x3, #0x1
        b'\x08\x30\x8D\xE5',                            # str     r3, [sp,  #0x8]
        b'\x00\x40\x9C\xE5',                            # ldr     r4, [r12]
        b'\x00\x00\x54\xE3',                            # cmp     r4, #0
        b'\xAA\x00\x00\x0A',                            # beq     0x3bb4
        b'\x02\x00\x59\xE3',                            # cmp     r9, #0x2
        b'\x48\x30\x95\xE5',                            # ldr     r3, [r5,  #0x48]
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\x0F\x10\xA0\xE3',                            # mov     r1, #0xf
        b'\x04\xA0\x9C\x05',                            # ldreq   r10, [r12,  #0x4]
        b'\x08\x60\x8C\x02',                            # addeq   r6, r12, #0x8
        b'\xB2\xA0\xDC\x11',                            # ldrhne  r10, [r12,  #0x2]
        b'\x04\x60\x8C\x12',                            # addne   r6, r12, #0x4
        b'\xB0\x40\xDC\x11',                            # ldrhne  r4, [r12]
        b'\x01\xB0\xCA\xE3',                            # bic     r11, r10, #0x1
        b'\x03\xB0\x8B\xE0',                            # add     r11, r11, r3
        b'\x6D\xFF\xFF\xEB',                            # bl      0x36f0
        b'\x00\x00\x5B\xE1',                            # cmp     r11, r0
        b'\x00\xC0\xA0\x83',                            # movhi   r12, #0
        b'\x04\x00\x00\x8A',                            # bhi     0x3958
        b'\x01\x30\xC4\xE3',                            # bic     r3, r4, #0x1
        b'\x03\xB0\x8B\xE0',                            # add     r11, r11, r3
        b'\x0B\x00\x50\xE1',                            # cmp     r0, r11
        b'\x00\xC0\xA0\x23',                            # movhs   r12, #0
        b'\x01\xC0\xA0\x33',                            # movlo   r12, #0x1
        b'\x01\xA0\x0A\xE2',                            # and     r10, r10, #0x1
        b'\x01\x40\x04\xE2',                            # and     r4, r4, #0x1
        b'\x8A\x40\x84\xE1',                            # orr     r4, r4, r10, lsl  #0x1
        b'\x01\x00\x54\xE3',                            # cmp     r4, #0x1
        b'\x17\x00\x00\x0A',                            # beq     0x39cc
        b'\x02\x00\x00\x3A',                            # blo     0x397c
        b'\x02\x00\x54\xE3',                            # cmp     r4, #0x2
        b'\x48\x00\x00\x0A',                            # beq     0x3a9c
        b'\xA8\x00\x00\xEA',                            # b       0x3c20
        b'\x00\x00\x58\xE3',                            # cmp     r8, #0
        b'\x00\xC0\xA0\x03',                            # moveq   r12, #0
        b'\x01\xC0\x0C\x12',                            # andne   r12, r12, #0x1
        b'\x04\xA0\x86\xE2',                            # add     r10, r6, #0x4
        b'\x00\x00\x5C\xE3',                            # cmp     r12, #0
        b'\x0B\x00\x00\x0A',                            # beq     0x39c4
        b'\x06\x00\xA0\xE1',                            # mov     r0, r6
        b'\xD6\xFD\xFF\xEB',                            # bl      0x30f8
        b'\x38\xA0\x85\xE5',                            # str     r10, [r5,  #0x38]
        b'\x00\x40\xA0\xE1',                            # mov     r4, r0
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x32\xF3\xFF\xEB',                            # bl      0x678
        b'\x00\x00\x50\xE3',                            # cmp     r0, #0
        b'\x9A\x00\x00\x0A',                            # beq     0x3c20
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\x0F\x10\xA0\xE3',                            # mov     r1, #0xf
        b'\x04\x20\xA0\xE1',                            # mov     r2, r4
        b'\x93\x00\x00\xEA',                            # b       0x3c14
        b'\x0A\xC0\xA0\xE1',                            # mov     r12, r10
        b'\xCB\xFF\xFF\xEA',                            # b       0x38fc
        b'\x00\x00\x58\xE3',                            # cmp     r8, #0
        b'\x1D\x00\x00\x1A',                            # bne     0x3a4c
        b'\x00\x00\x5C\xE3',                            # cmp     r12, #0
        b'\x2D\x00\x00\x0A',                            # beq     0x3a94
        b'\x04\x30\x96\xE5',                            # ldr     r3, [r6,  #0x4]
        b'\x00\xA0\x96\xE5',                            # ldr     r10, [r6]
        b'\x02\x00\x73\xE3',                            # cmn     r3, #0x2
        b'\xAA\xAF\xA0\xE1',                            # lsr     r10, r10, #0x1f
        b'\x8B\x00\x00\x0A',                            # beq     0x3c20
        b'\x01\x00\x73\xE3',                            # cmn     r3, #0x1
        b'\x58\x20\x85\xE2',                            # add     r2, r5, #0x58
        b'\x10\x20\x8D\xE5',                            # str     r2, [sp,  #0x10]
        b'\x08\x00\x00\x0A',                            # beq     0x3a24
        b'\x04\x00\x86\xE2',                            # add     r0, r6, #0x4
        b'\x59\xFE\xFF\xEB',                            # bl      0x3370
        b'\x0A\x20\xA0\xE1',                            # mov     r2, r10
        b'\x10\x30\x8D\xE2',                            # add     r3, sp, #0x10
        b'\x00\x10\xA0\xE1',                            # mov     r1, r0
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x19\xF3\xFF\xEB',                            # bl      0x684
        b'\x00\x40\x50\xE2',                            # sub.s   r4, r0, #0
        b'\x1B\x00\x00\x0A',                            # beq     0x3a94
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\x0D\x10\xA0\xE3',                            # mov     r1, #0xd
        b'\x2F\xFF\xFF\xEB',                            # bl      0x36f0
        b'\x02\x00\x54\xE3',                            # cmp     r4, #0x2
        b'\x10\x20\x9D\xE5',                            # ldr     r2, [sp,  #0x10]
        b'\x05\x30\xA0\x01',                            # moveq   r3, r5
        b'\x02\x30\xA0\x11',                            # movne   r3, r2
        b'\x20\x00\x85\xE5',                            # str     r0, [r5,  #0x20]
        b'\x2C\x20\xA3\x05',                            # streq   r2, [r3,  #0x2c]!
        b'\x7B\x00\x00\xEA',                            # b       0x3c3c
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\x0D\x10\xA0\xE3',                            # mov     r1, #0xd
        b'\x20\x40\x95\xE5',                            # ldr     r4, [r5,  #0x20]
        b'\x24\xFF\xFF\xEB',                            # bl      0x36f0
        b'\x00\x00\x54\xE1',                            # cmp     r4, r0
        b'\x0B\x00\x00\x1A',                            # bne     0x3a94
        b'\x28\x30\x95\xE5',                            # ldr     r3, [r5,  #0x28]
        b'\x03\x00\x56\xE1',                            # cmp     r6, r3
        b'\x08\x00\x00\x1A',                            # bne     0x3a94
        b'\x06\x00\xA0\xE1',                            # mov     r0, r6
        b'\x9F\xFD\xFF\xEB',                            # bl      0x30f8
        b'\x0F\x10\xA0\xE3',                            # mov     r1, #0xf
        b'\x00\x20\xA0\xE1',                            # mov     r2, r0
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\x3A\xFF\xFF\xEB',                            # bl      0x3774
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\x00\x10\xA0\xE3',                            # mov     r1, #0
        b'\x3B\x00\x00\xEA',                            # b       0x3b84
        b'\x08\xC0\x86\xE2',                            # add     r12, r6, #0x8
        b'\x97\xFF\xFF\xEA',                            # b       0x38fc
        b'\x00\x40\x96\xE5',                            # ldr     r4, [r6]
        b'\x00\x00\x58\xE3',                            # cmp     r8, #0
        b'\x02\x41\xC4\xE3',                            # bic     r4, r4, #0x80000000
        b'\x19\x00\x00\x1A',                            # bne     0x3b14
        b'\x00\x00\x5C\xE3',                            # cmp     r12, #0
        b'\x37\x00\x00\x0A',                            # beq     0x3b94
        b'\x08\x30\x9D\xE5',                            # ldr     r3, [sp,  #0x8]
        b'\x00\x00\x54\xE3',                            # cmp     r4, #0
        b'\x01\x30\x83\x03',                            # orreq   r3, r3, #0x1
        b'\x00\x00\x53\xE3',                            # cmp     r3, #0
        b'\x32\x00\x00\x0A',                            # beq     0x3b94
        b'\x58\xC0\x85\xE2',                            # add     r12, r5, #0x58
        b'\x10\xB0\x8D\xE2',                            # add     r11, sp, #0x10
        b'\x08\xA0\xA0\xE1',                            # mov     r10, r8
        b'\x04\x00\x5A\xE1',                            # cmp     r10, r4
        b'\x52\x00\x00\x0A',                            # beq     0x3c28
        b'\x01\xA0\x8A\xE2',                            # add     r10, r10, #0x1
        b'\x10\xC0\x8D\xE5',                            # str     r12, [sp,  #0x10]
        b'\x0C\xC0\x8D\xE5',                            # str     r12, [sp,  #0xc]
        b'\x0A\x01\x86\xE0',                            # add     r0, r6, r10, lsl  #0x2
        b'\x1F\xFE\xFF\xEB',                            # bl      0x3370
        b'\x00\x20\xA0\xE3',                            # mov     r2, #0
        b'\x0B\x30\xA0\xE1',                            # mov     r3, r11
        b'\x00\x10\xA0\xE1',                            # mov     r1, r0
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\xDF\xF2\xFF\xEB',                            # bl      0x684
        b'\x0C\xC0\x9D\xE5',                            # ldr     r12, [sp,  #0xc]
        b'\x00\x00\x50\xE3',                            # cmp     r0, #0
        b'\xF0\xFF\xFF\x0A',                            # beq     0x3ad4
        b'\x1F\x00\x00\xEA',                            # b       0x3b94
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\x0D\x10\xA0\xE3',                            # mov     r1, #0xd
        b'\x20\xA0\x95\xE5',                            # ldr     r10, [r5,  #0x20]
        b'\xF2\xFE\xFF\xEB',                            # bl      0x36f0
        b'\x00\x00\x5A\xE1',                            # cmp     r10, r0
        b'\x19\x00\x00\x1A',                            # bne     0x3b94
        b'\x28\x30\x95\xE5',                            # ldr     r3, [r5,  #0x28]
        b'\x03\x00\x56\xE1',                            # cmp     r6, r3
        b'\x16\x00\x00\x1A',                            # bne     0x3b94
        b'\x00\xA0\xA0\xE3',                            # mov     r10, #0
        b'\x04\x30\xA0\xE3',                            # mov     r3, #0x4
        b'\x28\x40\x85\xE5',                            # str     r4, [r5,  #0x28]
        b'\x30\x30\x85\xE5',                            # str     r3, [r5,  #0x30]
        b'\x03\x30\x86\xE0',                            # add     r3, r6, r3
        b'\x2C\xA0\x85\xE5',                            # str     r10, [r5,  #0x2c]
        b'\x34\x30\x85\xE5',                            # str     r3, [r5,  #0x34]
        b'\x00\x30\x96\xE5',                            # ldr     r3, [r6]
        b'\x0A\x00\x53\xE1',                            # cmp     r3, r10
        b'\x0A\x00\x00\xAA',                            # bge     0x3b8c
        b'\x01\x00\x84\xE2',                            # add     r0, r4, #0x1
        b'\x00\x01\x86\xE0',                            # add     r0, r6, r0, lsl  #0x2
        b'\x62\xFD\xFF\xEB',                            # bl      0x30f8
        b'\x0F\x10\xA0\xE3',                            # mov     r1, #0xf
        b'\x00\x20\xA0\xE1',                            # mov     r2, r0
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\xFD\xFE\xFF\xEB',                            # bl      0x3774
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\x0A\x10\xA0\xE1',                            # mov     r1, r10
        b'\x05\x20\xA0\xE1',                            # mov     r2, r5
        b'\x21\x00\x00\xEA',                            # b       0x3c14
        b'\x01\x30\xA0\xE3',                            # mov     r3, #0x1
        b'\x04\x30\x8D\xE5',                            # str     r3, [sp,  #0x4]
        b'\x00\x30\x96\xE5',                            # ldr     r3, [r6]
        b'\x01\xC0\x84\xE2',                            # add     r12, r4, #0x1
        b'\x00\x00\x53\xE3',                            # cmp     r3, #0
        b'\x04\x60\x86\xB2',                            # addlt   r6, r6, #0x4
        b'\x0C\xC1\x86\xE0',                            # add     r12, r6, r12, lsl  #0x2
        b'\x53\xFF\xFF\xEA',                            # b       0x38fc
        b'\x00\x30\xA0\xE3',                            # mov     r3, #0
        b'\x04\x30\x8D\xE5',                            # str     r3, [sp,  #0x4]
        b'\x02\x00\x59\xE3',                            # cmp     r9, #0x2
        b'\x01\x00\x00\xDA',                            # ble     0x3bc4
        b'\xF0\xFD\xFF\xEB',                            # bl      0x3384
        b'\x02\x00\x00\xEA',                            # b       0x3bd0
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\x14\x10\x8D\xE2',                            # add     r1, sp, #0x14
        b'\x8B\x01\x00\xEB',                            # bl      0x4200
        b'\x00\x00\x50\xE3',                            # cmp     r0, #0
        b'\x11\x00\x00\x1A',                            # bne     0x3c20
        b'\x04\x30\x9D\xE5',                            # ldr     r3, [sp,  #0x4]
        b'\x00\x00\x53\xE3',                            # cmp     r3, #0
        b'\x08\x00\xA0\x03',                            # moveq   r0, #0x8
        b'\x17\x00\x00\x0A',                            # beq     0x3c48
        b'\x0F\x10\xA0\xE3',                            # mov     r1, #0xf
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\xBE\xFE\xFF\xEB',                            # bl      0x36f0
        b'\x0E\x10\xA0\xE3',                            # mov     r1, #0xe
        b'\x00\x20\xA0\xE1',                            # mov     r2, r0
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\xDB\xFE\xFF\xEB',                            # bl      0x3774
        b'\x44\x20\x9F\xE5',                            # ldr     r2, 0x3c50
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\x0F\x10\xA0\xE3',                            # mov     r1, #0xf
        b'\x02\x20\x9F\xE7',                            # ldr     r2, [pc, r2]
        b'\xD6\xFE\xFF\xEB',                            # bl      0x3774
        b'\x07\x00\xA0\xE3',                            # mov     r0, #0x7
        b'\x09\x00\x00\xEA',                            # b       0x3c48
        b'\x09\x00\xA0\xE3',                            # mov     r0, #0x9
        b'\x07\x00\x00\xEA',                            # b       0x3c48
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\x0D\x10\xA0\xE3',                            # mov     r1, #0xd
        b'\xAE\xFE\xFF\xEB',                            # bl      0x36f0
        b'\x10\x30\x9D\xE5',                            # ldr     r3, [sp,  #0x10]
        b'\x20\x00\x85\xE5',                            # str     r0, [r5,  #0x20]
        b'\x06\x00\xA0\xE3',                            # mov     r0, #0x6
        b'\x24\x30\x85\xE5',                            # str     r3, [r5,  #0x24]
        b'\x28\x60\x85\xE5',                            # str     r6, [r5,  #0x28]
        b'\x24\xD0\x8D\xE2',                            # add     sp, sp, #0x24
        b'\xF0\x8F\xBD\xE8',                            # pop     {r4, r5, r6, r7, r8, r9, r10, r11, pc}
    ],
    'length': 0x3E8
},
{
    'name': '__aeabi_unwind_cpp_pr0',
    'description': 'int32_t __aeabi_unwind_cpp_pr0(int32_t arg1, void* arg2, int32_t* arg3)',
    'address': 0x3C54,
    'instructions': [
        b'\x00\x30\xA0\xE3',                            # mov     r3, #0
        b'\x02\xFF\xFF\xEA',                            # b       0x3868
    ],
    'length': 0x8
},
{
    'name': '__aeabi_unwind_cpp_pr1',
    'description': 'int32_t __aeabi_unwind_cpp_pr1(int32_t arg1, void* arg2, int32_t* arg3)',
    'address': 0x3C5C,
    'instructions': [
        b'\x01\x30\xA0\xE3',                            # mov     r3, #0x1
        b'\x00\xFF\xFF\xEA',                            # b       0x3868
    ],
    'length': 0x8
},
{
    'name': '__aeabi_unwind_cpp_pr2',
    'description': 'int32_t __aeabi_unwind_cpp_pr2(int32_t arg1, void* arg2, int32_t* arg3)',
    'address': 0x3C64,
    'instructions': [
        b'\x02\x30\xA0\xE3',                            # mov     r3, #0x2
        b'\xFE\xFE\xFF\xEA',                            # b       0x3868
    ],
    'length': 0x8
},
{
    'name': '_Unwind_VRS_Pop',
    'description': 'void* _Unwind_VRS_Pop(int32_t* arg1, int32_t arg2, int32_t arg3, int32_t arg4)',
    'address': 0x3C6C,
    'instructions': [
        b'\xF0\x43\x2D\xE9',                            # push    {r4, r5, r6, r7, r8, r9, lr}
        b'\x00\x50\xA0\xE1',                            # mov     r5, r0
        b'\x43\xDF\x4D\xE2',                            # sub     sp, sp, #0x10c
        b'\x02\x40\xA0\xE1',                            # mov     r4, r2
        b'\x04\x00\x51\xE3',                            # cmp     r1, #0x4
        b'\x01\xF1\x8F\x90',                            # addls   pc, pc, r1, lsl  #0x2
        b'\xB9\x00\x00\xEA',                            # b       0x3f70
        b'\x03\x00\x00\xEA',                            # b       0x3c9c
        b'\x14\x00\x00\xEA',                            # b       0x3ce4
        b'\xB6\x00\x00\xEA',                            # b       0x3f70
        b'\x7F\x00\x00\xEA',                            # b       0x3e98
        b'\x9A\x00\x00\xEA',                            # b       0x3f08
        b'\x00\x00\x53\xE3',                            # cmp     r3, #0
        b'\xB2\x00\x00\x1A',                            # bne     0x3f70
        b'\x01\x30\xA0\xE3',                            # mov     r3, #0x1
        b'\x72\x10\xFF\xE6',                            # uxth    r1, r2, ror  #0
        b'\x38\x20\x90\xE5',                            # ldr     r2, [r0,  #0x38]
        b'\x03\x00\xA0\xE1',                            # mov     r0, r3
        b'\x01\xC0\x43\xE2',                            # sub     r12, r3, #0x1
        b'\x10\xCC\x11\xE0',                            # and.s   r12, r1, r0, lsl r12
        b'\x00\xC0\x92\x15',                            # ldrne   r12, [r2]
        b'\x04\x20\x82\x12',                            # addne   r2, r2, #0x4
        b'\x03\xC1\x85\x17',                            # strne   r12, [r5, r3, lsl  #0x2]
        b'\x01\x30\x83\xE2',                            # add     r3, r3, #0x1
        b'\x11\x00\x53\xE3',                            # cmp     r3, #0x11
        b'\xF7\xFF\xFF\x1A',                            # bne     0x3cb4
        b'\x02\x0A\x14\xE2',                            # and.s   r0, r4, #0x2000
        b'\x38\x20\x85\x05',                            # streq   r2, [r5,  #0x38]
        b'\xB8\x00\x00\x0A',                            # beq     0x3fc4
        b'\xA4\x00\x00\xEA',                            # b       0x3f78
        b'\x04\x20\xC3\xE3',                            # bic     r2, r3, #0x4
        b'\x01\x00\x52\xE3',                            # cmp     r2, #0x1
        b'\x9F\x00\x00\x1A',                            # bne     0x3f70
        b'\x01\x00\x53\xE3',                            # cmp     r3, #0x1
        b'\x24\x78\xA0\xE1',                            # lsr     r7, r4, #0x10
        b'\x74\x40\xFF\xE6',                            # uxth    r4, r4, ror  #0
        b'\x07\x60\x84\xE0',                            # add     r6, r4, r7
        b'\x06\x00\x00\x1A',                            # bne     0x3d20
        b'\x10\x00\x56\xE3',                            # cmp     r6, #0x10
        b'\x98\x00\x00\x8A',                            # bhi     0x3f70
        b'\x0F\x00\x57\xE3',                            # cmp     r7, #0xf
        b'\x03\x80\xA0\x91',                            # movls   r8, r3
        b'\x00\x60\xA0\x93',                            # movls   r6, #0
        b'\x94\x00\x00\x8A',                            # bhi     0x3f70
        b'\x05\x00\x00\xEA',                            # b       0x3d38
        b'\x20\x00\x56\xE3',                            # cmp     r6, #0x20
        b'\x91\x00\x00\x8A',                            # bhi     0x3f70
        b'\x0F\x00\x57\xE3',                            # cmp     r7, #0xf
        b'\x93\x00\x00\x9A',                            # bls     0x3f80
        b'\x04\x60\xA0\xE1',                            # mov     r6, r4
        b'\x00\x80\xA0\xE3',                            # mov     r8, #0
        b'\x00\x90\x96\xE2',                            # add.s   r9, r6, #0
        b'\x01\x90\xA0\x13',                            # movne   r9, #0x1
        b'\x05\x00\x53\xE3',                            # cmp     r3, #0x5
        b'\x00\x00\x56\x13',                            # cmpne   r6, #0
        b'\x88\x00\x00\x1A',                            # bne     0x3f70
        b'\x0F\x00\x57\xE3',                            # cmp     r7, #0xf
        b'\x12\x00\x00\x8A',                            # bhi     0x3da0
        b'\x00\x20\x95\xE5',                            # ldr     r2, [r5]
        b'\x01\x00\x12\xE3',                            # tst     r2, #0x1
        b'\x0F\x00\x00\x0A',                            # beq     0x3da0
        b'\x05\x00\x53\xE3',                            # cmp     r3, #0x5
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x01\x10\xC2\xE3',                            # bic     r1, r2, #0x1
        b'\x48\x10\x80\xE4',                            # str     r1, [r0],  #0x48
        b'\x07\x00\x00\x1A',                            # bne     0x3d94
        b'\x02\x10\x81\xE3',                            # orr     r1, r1, #0x2
        b'\x00\x10\x85\xE5',                            # str     r1, [r5]
        b'\x9D\x00\x00\xEB',                            # bl      0x3ff8
        b'\x00\x00\x59\xE3',                            # cmp     r9, #0
        b'\x07\x00\x00\x1A',                            # bne     0x3da8
        b'\x80\x00\x8D\xE2',                            # add     r0, sp, #0x80
        b'\x99\x00\x00\xEB',                            # bl      0x3ff8
        b'\x0F\x00\x00\xEA',                            # b       0x3dd4
        b'\x03\x20\xC2\xE3',                            # bic     r2, r2, #0x3
        b'\x00\x20\x85\xE5',                            # str     r2, [r5]
        b'\x91\x00\x00\xEB',                            # bl      0x3fe8
        b'\x00\x00\x59\xE3',                            # cmp     r9, #0
        b'\x7B\x00\x00\x0A',                            # beq     0x3f98
        b'\x00\x30\x95\xE5',                            # ldr     r3, [r5]
        b'\x04\x00\x13\xE3',                            # tst     r3, #0x4
        b'\x03\x00\x00\x0A',                            # beq     0x3dc4
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x04\x30\xC3\xE3',                            # bic     r3, r3, #0x4
        b'\xD0\x30\x80\xE4',                            # str     r3, [r0],  #0xd0
        b'\x90\x00\x00\xEB',                            # bl      0x4008
        b'\x00\x00\x58\xE3',                            # cmp     r8, #0
        b'\x77\x00\x00\x1A',                            # bne     0x3fac
        b'\x0F\x00\x57\xE3',                            # cmp     r7, #0xf
        b'\xEC\xFF\xFF\x9A',                            # bls     0x3d88
        b'\x00\x00\x59\xE3',                            # cmp     r9, #0
        b'\x02\x00\x00\x0A',                            # beq     0x3de8
        b'\x0D\x00\xA0\xE1',                            # mov     r0, sp
        b'\x88\x00\x00\xEB',                            # bl      0x4008
        b'\x10\x40\x67\xE2',                            # rsb     r4, r7, #0x10
        b'\x38\x20\x95\xE5',                            # ldr     r2, [r5,  #0x38]
        b'\x00\x00\x54\xE3',                            # cmp     r4, #0
        b'\x02\x30\xA0\xE1',                            # mov     r3, r2
        b'\x09\x00\x00\xDA',                            # ble     0x3e20
        b'\x80\x10\x8D\xE2',                            # add     r1, sp, #0x80
        b'\x84\x40\xA0\xE1',                            # lsl     r4, r4, #0x1
        b'\x87\x11\x81\xE0',                            # add     r1, r1, r7, lsl  #0x3
        b'\x00\x30\xA0\xE3',                            # mov     r3, #0
        b'\x04\x00\x53\xE1',                            # cmp     r3, r4
        b'\x03\x01\x92\x17',                            # ldrne   r0, [r2, r3, lsl  #0x2]
        b'\x03\x01\x81\x17',                            # strne   r0, [r1, r3, lsl  #0x2]
        b'\x01\x30\x83\x12',                            # addne   r3, r3, #0x1
        b'\xFA\xFF\xFF\x1A',                            # bne     0x3e08
        b'\x03\x31\x82\xE0',                            # add     r3, r2, r3, lsl  #0x2
        b'\x00\x00\x59\xE3',                            # cmp     r9, #0
        b'\x0A\x00\x00\x0A',                            # beq     0x3e54
        b'\x10\x00\x57\xE3',                            # cmp     r7, #0x10
        b'\x42\x2F\x8D\xE2',                            # add     r2, sp, #0x108
        b'\x86\x61\x83\xE0',                            # add     r6, r3, r6, lsl  #0x3
        b'\x07\x40\xA0\x21',                            # movhs   r4, r7
        b'\x10\x40\xA0\x33',                            # movlo   r4, #0x10
        b'\x84\x41\x82\xE0',                            # add     r4, r2, r4, lsl  #0x3
        b'\x63\x4F\x44\xE2',                            # sub     r4, r4, #0x18c
        b'\x06\x00\x53\xE1',                            # cmp     r3, r6
        b'\x04\x20\x93\x14',                            # ldrne   r2, [r3],  #0x4
        b'\x04\x20\xA4\x15',                            # strne   r2, [r4,  #0x4]!
        b'\xFB\xFF\xFF\x1A',                            # bne     0x3e44
        b'\x00\x00\x58\xE3',                            # cmp     r8, #0
        b'\x04\x30\x83\x12',                            # addne   r3, r3, #0x4
        b'\x00\x00\x58\xE3',                            # cmp     r8, #0
        b'\x38\x30\x85\xE5',                            # str     r3, [r5,  #0x38]
        b'\x02\x00\x00\x0A',                            # beq     0x3e74
        b'\x80\x00\x8D\xE2',                            # add     r0, sp, #0x80
        b'\x5B\x00\x00\xEB',                            # bl      0x3fe0
        b'\x40\x00\x00\xEA',                            # b       0x3f78
        b'\x0F\x00\x57\xE3',                            # cmp     r7, #0xf
        b'\x01\x00\x00\x8A',                            # bhi     0x3e84
        b'\x80\x00\x8D\xE2',                            # add     r0, sp, #0x80
        b'\x5A\x00\x00\xEB',                            # bl      0x3ff0
        b'\x00\x00\x59\xE3',                            # cmp     r9, #0
        b'\x3A\x00\x00\x0A',                            # beq     0x3f78
        b'\x0D\x00\xA0\xE1',                            # mov     r0, sp
        b'\x5A\x00\x00\xEB',                            # bl      0x4000
        b'\x37\x00\x00\xEA',                            # b       0x3f78
        b'\x03\x00\x53\xE3',                            # cmp     r3, #0x3
        b'\x33\x00\x00\x1A',                            # bne     0x3f70
        b'\x22\x68\xA0\xE1',                            # lsr     r6, r2, #0x10
        b'\x72\x40\xFF\xE6',                            # uxth    r4, r2, ror  #0
        b'\x06\x30\x84\xE0',                            # add     r3, r4, r6
        b'\x10\x00\x53\xE3',                            # cmp     r3, #0x10
        b'\x2E\x00\x00\x8A',                            # bhi     0x3f70
        b'\x00\x30\x90\xE5',                            # ldr     r3, [r0]
        b'\x08\x00\x13\xE3',                            # tst     r3, #0x8
        b'\x02\x00\x00\x0A',                            # beq     0x3ecc
        b'\x08\x30\xC3\xE3',                            # bic     r3, r3, #0x8
        b'\x50\x31\x80\xE4',                            # str     r3, [r0],  #0x150
        b'\x61\x00\x00\xEB',                            # bl      0x4054
        b'\x80\x70\x8D\xE2',                            # add     r7, sp, #0x80
        b'\x86\x61\x87\xE0',                            # add     r6, r7, r6, lsl  #0x3
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\x04\x60\x46\xE2',                            # sub     r6, r6, #0x4
        b'\x5C\x00\x00\xEB',                            # bl      0x4054
        b'\x38\x30\x95\xE5',                            # ldr     r3, [r5,  #0x38]
        b'\x84\x41\x83\xE0',                            # add     r4, r3, r4, lsl  #0x3
        b'\x04\x00\x53\xE1',                            # cmp     r3, r4
        b'\x04\x20\x93\x14',                            # ldrne   r2, [r3],  #0x4
        b'\x04\x20\xA6\x15',                            # strne   r2, [r6,  #0x4]!
        b'\xFB\xFF\xFF\x1A',                            # bne     0x3ee8
        b'\x38\x30\x85\xE5',                            # str     r3, [r5,  #0x38]
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\x42\x00\x00\xEB',                            # bl      0x4010
        b'\x1B\x00\x00\xEA',                            # b       0x3f78
        b'\x10\x00\x52\xE3',                            # cmp     r2, #0x10
        b'\x00\x00\x53\x93',                            # cmpls   r3, #0
        b'\x16\x00\x00\x1A',                            # bne     0x3f70
        b'\x00\x30\x90\xE5',                            # ldr     r3, [r0]
        b'\x10\x00\x13\xE3',                            # tst     r3, #0x10
        b'\x02\x00\x00\x0A',                            # beq     0x3f2c
        b'\x10\x30\xC3\xE3',                            # bic     r3, r3, #0x10
        b'\xD0\x31\x80\xE4',                            # str     r3, [r0],  #0x1d0
        b'\x5F\x00\x00\xEB',                            # bl      0x40ac
        b'\x80\x60\x8D\xE2',                            # add     r6, sp, #0x80
        b'\x06\x00\xA0\xE1',                            # mov     r0, r6
        b'\x5C\x00\x00\xEB',                            # bl      0x40ac
        b'\x38\x20\x95\xE5',                            # ldr     r2, [r5,  #0x38]
        b'\x00\x30\xA0\xE3',                            # mov     r3, #0
        b'\x01\x10\xA0\xE3',                            # mov     r1, #0x1
        b'\x11\x03\x14\xE0',                            # and.s   r0, r4, r1, lsl r3
        b'\x00\x00\x92\x15',                            # ldrne   r0, [r2]
        b'\x04\x20\x82\x12',                            # addne   r2, r2, #0x4
        b'\x03\x01\x86\x17',                            # strne   r0, [r6, r3, lsl  #0x2]
        b'\x01\x30\x83\xE2',                            # add     r3, r3, #0x1
        b'\x04\x00\x53\xE3',                            # cmp     r3, #0x4
        b'\xF8\xFF\xFF\x1A',                            # bne     0x3f44
        b'\x38\x20\x85\xE5',                            # str     r2, [r5,  #0x38]
        b'\x06\x00\xA0\xE1',                            # mov     r0, r6
        b'\x4A\x00\x00\xEB',                            # bl      0x4098
        b'\x01\x00\x00\xEA',                            # b       0x3f78
        b'\x02\x00\xA0\xE3',                            # mov     r0, #0x2
        b'\x12\x00\x00\xEA',                            # b       0x3fc4
        b'\x00\x00\xA0\xE3',                            # mov     r0, #0
        b'\x10\x00\x00\xEA',                            # b       0x3fc4
        b'\x10\x00\x56\xE3',                            # cmp     r6, #0x10
        b'\x00\x80\xA0\x93',                            # movls   r8, #0
        b'\x08\x60\xA0\x91',                            # movls   r6, r8
        b'\x69\xFF\xFF\x9A',                            # bls     0x3d38
        b'\x10\x60\x46\xE2',                            # sub     r6, r6, #0x10
        b'\x66\xFF\xFF\xEA',                            # b       0x3d34
        b'\x00\x00\x58\xE3',                            # cmp     r8, #0
        b'\x05\x00\x00\x0A',                            # beq     0x3fb8
        b'\x80\x00\x8D\xE2',                            # add     r0, sp, #0x80
        b'\x0F\x00\x00\xEB',                            # bl      0x3fe8
        b'\x8E\xFF\xFF\xEA',                            # b       0x3de8
        b'\x80\x00\x8D\xE2',                            # add     r0, sp, #0x80
        b'\x0C\x00\x00\xEB',                            # bl      0x3fe8
        b'\x8A\xFF\xFF\xEA',                            # b       0x3de4
        b'\x0F\x00\x57\xE3',                            # cmp     r7, #0xf
        b'\x89\xFF\xFF\x8A',                            # bhi     0x3de8
        b'\x70\xFF\xFF\xEA',                            # b       0x3d88
        b'\x43\xDF\x8D\xE2',                            # add     sp, sp, #0x10c
        b'\xF0\x83\xBD\xE8',                            # pop     {r4, r5, r6, r7, r8, r9, pc}
    ],
    'length': 0x360
},
{
    'name': '__restore_core_regs',
    'description': 'int32_t __restore_core_regs(int32_t* arg1)',
    'address': 0x3FCC,
    'instructions': [
        b'\x34\x10\x80\xE2',                            # add     r1, r0, #0x34
        b'\x38\x00\x91\xE8',                            # ldm     r1, {r3, r4, r5}
        b'\x38\x00\x2D\xE9',                            # push    {r3, r4, r5}
        b'\xFF\x0F\x90\xE8',                            # ldm     r0, {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11}
        b'\x00\xE0\x9D\xE8',                            # ldm     sp, {sp, lr, pc}
    ],
    'length': 0x14
},
{
    'name': '__gnu_Unwind_Restore_VFP',
    'description': 'int32_t __gnu_Unwind_Restore_VFP()',
    'address': 0x3FE0,
    'instructions': [
        b'\x21\x0B\x90\xEC',                            # fldmiax r0, {d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15}
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x8
},
{
    'name': '__gnu_Unwind_Save_VFP',
    'description': 'int32_t __gnu_Unwind_Save_VFP()',
    'address': 0x3FE8,
    'instructions': [
        b'\x21\x0B\x80\xEC',                            # fstmiax r0, {d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15}
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x8
},
{
    'name': '__gnu_Unwind_Restore_VFP_D',
    'description': 'int32_t __gnu_Unwind_Restore_VFP_D()',
    'address': 0x3FF0,
    'instructions': [
        b'\x20\x0B\x90\xEC',                            # vldmia  r0, {d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15}
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x8
},
{
    'name': '__gnu_Unwind_Save_VFP_D',
    'description': 'int32_t __gnu_Unwind_Save_VFP_D()',
    'address': 0x3FF8,
    'instructions': [
        b'\x20\x0B\x80\xEC',                            # vstmia  r0, {d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15}
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x8
},
{
    'name': '__gnu_Unwind_Restore_VFP_D_16_to_31',
    'description': 'int32_t __gnu_Unwind_Restore_VFP_D_16_to_31()',
    'address': 0x4000,
    'instructions': [
        b'\x20\x0B\xD0\xEC',                            # vldmia  r0, {}
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x8
},
{
    'name': '__gnu_Unwind_Save_VFP_D_16_to_31',
    'description': 'int32_t __gnu_Unwind_Save_VFP_D_16_to_31()',
    'address': 0x4008,
    'instructions': [
        b'\x20\x0B\xC0\xEC',                            # vstmia  r0, {}
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x8
},
{
    'name': '__gnu_Unwind_Restore_WMMXD',
    'description': 'int32_t __gnu_Unwind_Restore_WMMXD()',
    'address': 0x4010,
    'instructions': [
        b'\x02\x01\xF0\xEC',                            # ldcl    p1, c0, [r0],  #0x8
        b'\x02\x11\xF0\xEC',                            # ldcl    p1, c1, [r0],  #0x8
        b'\x02\x21\xF0\xEC',                            # ldcl    p1, c2, [r0],  #0x8
        b'\x02\x31\xF0\xEC',                            # ldcl    p1, c3, [r0],  #0x8
        b'\x02\x41\xF0\xEC',                            # ldcl    p1, c4, [r0],  #0x8
        b'\x02\x51\xF0\xEC',                            # ldcl    p1, c5, [r0],  #0x8
        b'\x02\x61\xF0\xEC',                            # ldcl    p1, c6, [r0],  #0x8
        b'\x02\x71\xF0\xEC',                            # ldcl    p1, c7, [r0],  #0x8
        b'\x02\x81\xF0\xEC',                            # ldcl    p1, c8, [r0],  #0x8
        b'\x02\x91\xF0\xEC',                            # ldcl    p1, c9, [r0],  #0x8
        b'\x02\xA1\xF0\xEC',                            # ldcl    p1, c10, [r0],  #0x8
        b'\x02\xB1\xF0\xEC',                            # ldcl    p1, c11, [r0],  #0x8
        b'\x02\xC1\xF0\xEC',                            # ldcl    p1, c12, [r0],  #0x8
        b'\x02\xD1\xF0\xEC',                            # ldcl    p1, c13, [r0],  #0x8
        b'\x02\xE1\xF0\xEC',                            # ldcl    p1, c14, [r0],  #0x8
        b'\x02\xF1\xF0\xEC',                            # ldcl    p1, c15, [r0],  #0x8
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x44
},
{
    'name': '__gnu_Unwind_Save_WMMXD',
    'description': 'int32_t __gnu_Unwind_Save_WMMXD()',
    'address': 0x4054,
    'instructions': [
        b'\x02\x01\xE0\xEC',                            # stcl    p1, c0, [r0],  #0x8
        b'\x02\x11\xE0\xEC',                            # stcl    p1, c1, [r0],  #0x8
        b'\x02\x21\xE0\xEC',                            # stcl    p1, c2, [r0],  #0x8
        b'\x02\x31\xE0\xEC',                            # stcl    p1, c3, [r0],  #0x8
        b'\x02\x41\xE0\xEC',                            # stcl    p1, c4, [r0],  #0x8
        b'\x02\x51\xE0\xEC',                            # stcl    p1, c5, [r0],  #0x8
        b'\x02\x61\xE0\xEC',                            # stcl    p1, c6, [r0],  #0x8
        b'\x02\x71\xE0\xEC',                            # stcl    p1, c7, [r0],  #0x8
        b'\x02\x81\xE0\xEC',                            # stcl    p1, c8, [r0],  #0x8
        b'\x02\x91\xE0\xEC',                            # stcl    p1, c9, [r0],  #0x8
        b'\x02\xA1\xE0\xEC',                            # stcl    p1, c10, [r0],  #0x8
        b'\x02\xB1\xE0\xEC',                            # stcl    p1, c11, [r0],  #0x8
        b'\x02\xC1\xE0\xEC',                            # stcl    p1, c12, [r0],  #0x8
        b'\x02\xD1\xE0\xEC',                            # stcl    p1, c13, [r0],  #0x8
        b'\x02\xE1\xE0\xEC',                            # stcl    p1, c14, [r0],  #0x8
        b'\x02\xF1\xE0\xEC',                            # stcl    p1, c15, [r0],  #0x8
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x44
},
{
    'name': '__gnu_Unwind_Restore_WMMXC',
    'description': 'int32_t __gnu_Unwind_Restore_WMMXC()',
    'address': 0x4098,
    'instructions': [
        b'\x01\x81\xB0\xFC',                            # ldc2    p1, c8, [r0],  #0x4
        b'\x01\x91\xB0\xFC',                            # ldc2    p1, c9, [r0],  #0x4
        b'\x01\xA1\xB0\xFC',                            # ldc2    p1, c10, [r0],  #0x4
        b'\x01\xB1\xB0\xFC',                            # ldc2    p1, c11, [r0],  #0x4
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x14
},
{
    'name': '__gnu_Unwind_Save_WMMXC',
    'description': 'int32_t __gnu_Unwind_Save_WMMXC()',
    'address': 0x40AC,
    'instructions': [
        b'\x01\x81\xA0\xFC',                            # stc2    p1, c8, [r0],  #0x4
        b'\x01\x91\xA0\xFC',                            # stc2    p1, c9, [r0],  #0x4
        b'\x01\xA1\xA0\xFC',                            # stc2    p1, c10, [r0],  #0x4
        b'\x01\xB1\xA0\xFC',                            # stc2    p1, c11, [r0],  #0x4
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x14
},
{
    'name': '_Unwind_RaiseException',
    'description': 'int32_t _Unwind_RaiseException(void* arg1)',
    'address': 0x40C0,
    'instructions': [
        b'\x00\xE0\x2D\xE9',                            # push    {sp, lr, pc}
        b'\xFF\x1F\x2D\xE9',                            # push    {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12}
        b'\x00\x30\xA0\xE3',                            # mov     r3, #0
        b'\x0C\x00\x2D\xE9',                            # push    {r2, r3}
        b'\x04\x10\x8D\xE2',                            # add     r1, sp, #0x4
        b'\x12\xFD\xFF\xEB',                            # bl      0x3524
        b'\x40\xE0\x9D\xE5',                            # ldr     lr, [sp,  #0x40]
        b'\x48\xD0\x8D\xE2',                            # add     sp, sp, #0x48
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x24
},
{
    'name': '_Unwind_Resume',
    'description': 'int32_t _Unwind_Resume(void* arg1) __noreturn',
    'address': 0x40E4,
    'instructions': [
        b'\x00\xE0\x2D\xE9',                            # push    {sp, lr, pc}
        b'\xFF\x1F\x2D\xE9',                            # push    {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12}
        b'\x00\x30\xA0\xE3',                            # mov     r3, #0
        b'\x0C\x00\x2D\xE9',                            # push    {r2, r3}
        b'\x04\x10\x8D\xE2',                            # add     r1, sp, #0x4
        b'\x39\xFD\xFF\xEB',                            # bl      0x35e4
    ],
    'length': 0x18
},
{
    'name': '_Unwind_Resume_or_Rethrow',
    'description': 'int32_t _Unwind_Resume_or_Rethrow(void* arg1)',
    'address': 0x4108,
    'instructions': [
        b'\x00\xE0\x2D\xE9',                            # push    {sp, lr, pc}
        b'\xFF\x1F\x2D\xE9',                            # push    {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12}
        b'\x00\x30\xA0\xE3',                            # mov     r3, #0
        b'\x0C\x00\x2D\xE9',                            # push    {r2, r3}
        b'\x04\x10\x8D\xE2',                            # add     r1, sp, #0x4
        b'\x4D\xFD\xFF\xEB',                            # bl      0x3658
        b'\x40\xE0\x9D\xE5',                            # ldr     lr, [sp,  #0x40]
        b'\x48\xD0\x8D\xE2',                            # add     sp, sp, #0x48
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x24
},
{
    'name': '_Unwind_ForcedUnwind',
    'description': 'int32_t _Unwind_ForcedUnwind(void* arg1, int32_t arg2, int32_t arg3)',
    'address': 0x412C,
    'instructions': [
        b'\x00\xE0\x2D\xE9',                            # push    {sp, lr, pc}
        b'\xFF\x1F\x2D\xE9',                            # push    {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12}
        b'\x00\x30\xA0\xE3',                            # mov     r3, #0
        b'\x0C\x00\x2D\xE9',                            # push    {r2, r3}
        b'\x04\x30\x8D\xE2',                            # add     r3, sp, #0x4
        b'\x20\xFD\xFF\xEB',                            # bl      0x35c8
        b'\x40\xE0\x9D\xE5',                            # ldr     lr, [sp,  #0x40]
        b'\x48\xD0\x8D\xE2',                            # add     sp, sp, #0x48
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x24
},
{
    'name': '_Unwind_Backtrace',
    'description': 'int32_t _Unwind_Backtrace(int32_t arg1, int32_t arg2)',
    'address': 0x4150,
    'instructions': [
        b'\x00\xE0\x2D\xE9',                            # push    {sp, lr, pc}
        b'\xFF\x1F\x2D\xE9',                            # push    {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12}
        b'\x00\x30\xA0\xE3',                            # mov     r3, #0
        b'\x0C\x00\x2D\xE9',                            # push    {r2, r3}
        b'\x04\x20\x8D\xE2',                            # add     r2, sp, #0x4
        b'\x8D\xFD\xFF\xEB',                            # bl      0x37a0
        b'\x40\xE0\x9D\xE5',                            # ldr     lr, [sp,  #0x40]
        b'\x48\xD0\x8D\xE2',                            # add     sp, sp, #0x48
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x24
},
{
    'name': 'next_unwind_byte',
    'description': 'uint32_t next_unwind_byte(int32_t* arg1)',
    'address': 0x4174,
    'instructions': [
        b'\x08\x30\xD0\xE5',                            # ldrb    r3, [r0,  #0x8]
        b'\x00\x00\x53\xE3',                            # cmp     r3, #0
        b'\x0B\x00\x00\x1A',                            # bne     0x41b0
        b'\x09\x30\xD0\xE5',                            # ldrb    r3, [r0,  #0x9]
        b'\x00\x00\x53\xE3',                            # cmp     r3, #0
        b'\x0F\x00\x00\x0A',                            # beq     0x41cc
        b'\x01\x30\x43\xE2',                            # sub     r3, r3, #0x1
        b'\x09\x30\xC0\xE5',                            # strb    r3, [r0,  #0x9]
        b'\x04\x30\x90\xE5',                            # ldr     r3, [r0,  #0x4]
        b'\x04\x20\x83\xE2',                            # add     r2, r3, #0x4
        b'\x04\x20\x80\xE5',                            # str     r2, [r0,  #0x4]
        b'\x00\x30\x93\xE5',                            # ldr     r3, [r3]
        b'\x00\x30\x80\xE5',                            # str     r3, [r0]
        b'\x03\x30\xA0\xE3',                            # mov     r3, #0x3
        b'\x00\x00\x00\xEA',                            # b       0x41b4
        b'\x01\x30\x43\xE2',                            # sub     r3, r3, #0x1
        b'\x08\x30\xC0\xE5',                            # strb    r3, [r0,  #0x8]
        b'\x00\x30\x90\xE5',                            # ldr     r3, [r0]
        b'\x03\x24\xA0\xE1',                            # lsl     r2, r3, #0x8
        b'\x00\x20\x80\xE5',                            # str     r2, [r0]
        b'\x23\x0C\xA0\xE1',                            # lsr     r0, r3, #0x18
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
        b'\xB0\x00\xA0\xE3',                            # mov     r0, #0xb0
        b'\x1E\xFF\x2F\xE1',                            # bx      lr
    ],
    'length': 0x60
},
{
    'name': '_Unwind_GetGR.constprop.0',
    'description': 'int32_t _Unwind_GetGR.constprop.0(int32_t arg1, int32_t arg2, int32_t arg3, int32_t arg4)',
    'address': 0x41D4,
    'instructions': [
        b'\x1F\x40\x2D\xE9',                            # push    {r0, r1, r2, r3, r4, lr}
        b'\x00\x10\xA0\xE3',                            # mov     r1, #0
        b'\x0C\x30\x8D\xE2',                            # add     r3, sp, #0xc
        b'\x0C\x20\xA0\xE3',                            # mov     r2, #0xc
        b'\x00\x30\x8D\xE5',                            # str     r3, [sp]
        b'\x01\x30\xA0\xE1',                            # mov     r3, r1
        b'\x28\xFD\xFF\xEB',                            # bl      0x3694
        b'\x0C\x00\x9D\xE5',                            # ldr     r0, [sp,  #0xc]
        b'\x14\xD0\x8D\xE2',                            # add     sp, sp, #0x14
        b'\x04\xF0\x9D\xE4',                            # ldr     pc, [sp],  #0x4
    ],
    'length': 0x28
},
{
    'name': 'unwind_UCB_from_context',
    'description': 'int32_t unwind_UCB_from_context(int32_t arg1, int32_t arg2, int32_t arg3, int32_t arg4)',
    'address': 0x41FC,
    'instructions': [
        b'\xF4\xFF\xFF\xEA',                            # b       0x41d4
    ],
    'length': 0x4
},
{
    'name': '__gnu_unwind_execute',
    'description': 'int32_t __gnu_unwind_execute(int32_t* arg1, int32_t* arg2)',
    'address': 0x4200,
    'instructions': [
        b'\xF0\x43\x2D\xE9',                            # push    {r4, r5, r6, r7, r8, r9, lr}
        b'\x14\xD0\x4D\xE2',                            # sub     sp, sp, #0x14
        b'\x00\x50\xA0\xE1',                            # mov     r5, r0
        b'\x01\x70\xA0\xE1',                            # mov     r7, r1
        b'\x00\x60\xA0\xE3',                            # mov     r6, #0
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\xD5\xFF\xFF\xEB',                            # bl      0x4174
        b'\xB0\x00\x50\xE3',                            # cmp     r0, #0xb0
        b'\x00\x40\xA0\xE1',                            # mov     r4, r0
        b'\x0F\x00\x00\x1A',                            # bne     0x4268
        b'\x00\x00\x56\xE3',                            # cmp     r6, #0
        b'\xD6\x00\x00\x1A',                            # bne     0x458c
        b'\x0C\x40\x8D\xE2',                            # add     r4, sp, #0xc
        b'\x06\x10\xA0\xE1',                            # mov     r1, r6
        b'\x06\x30\xA0\xE1',                            # mov     r3, r6
        b'\x00\x40\x8D\xE5',                            # str     r4, [sp]
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x0E\x20\xA0\xE3',                            # mov     r2, #0xe
        b'\x11\xFD\xFF\xEB',                            # bl      0x3694
        b'\x00\x40\x8D\xE5',                            # str     r4, [sp]
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x06\x10\xA0\xE1',                            # mov     r1, r6
        b'\x0F\x20\xA0\xE3',                            # mov     r2, #0xf
        b'\x06\x30\xA0\xE1',                            # mov     r3, r6
        b'\x2C\xFD\xFF\xEB',                            # bl      0x3718
        b'\xC8\x00\x00\xEA',                            # b       0x458c
        b'\x7F\x10\xC0\xE3',                            # bic     r1, r0, #0x7f
        b'\xFF\x10\x11\xE2',                            # and.s   r1, r1, #0xff
        b'\x0F\x00\x00\x1A',                            # bne     0x42b4
        b'\x00\x81\xA0\xE1',                            # lsl     r8, r0, #0x2
        b'\x0C\x90\x8D\xE2',                            # add     r9, sp, #0xc
        b'\x01\x30\xA0\xE1',                            # mov     r3, r1
        b'\x00\x90\x8D\xE5',                            # str     r9, [sp]
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x0D\x20\xA0\xE3',                            # mov     r2, #0xd
        b'\x00\xFD\xFF\xEB',                            # bl      0x3694
        b'\x78\x80\xEF\xE6',                            # uxtb    r8, r8, ror  #0
        b'\x0C\x30\x9D\xE5',                            # ldr     r3, [sp,  #0xc]
        b'\x04\x80\x88\xE2',                            # add     r8, r8, #0x4
        b'\x40\x00\x14\xE3',                            # tst     r4, #0x40
        b'\x00\x90\x8D\xE5',                            # str     r9, [sp]
        b'\x03\x80\x68\x10',                            # rsbne   r8, r8, r3
        b'\x03\x80\x88\x00',                            # addeq   r8, r8, r3
        b'\x0C\x80\x8D\xE5',                            # str     r8, [sp,  #0xc]
        b'\x22\x00\x00\xEA',                            # b       0x4340
        b'\xF0\x30\x00\xE2',                            # and     r3, r0, #0xf0
        b'\x80\x00\x53\xE3',                            # cmp     r3, #0x80
        b'\x12\x00\x00\x1A',                            # bne     0x430c
        b'\x00\x44\xA0\xE1',                            # lsl     r4, r0, #0x8
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\xA9\xFF\xFF\xEB',                            # bl      0x4174
        b'\x04\x00\x80\xE1',                            # orr     r0, r0, r4
        b'\x02\x09\x50\xE3',                            # cmp     r0, #0x8000
        b'\x01\x00\x00\x1A',                            # bne     0x42e0
        b'\x09\x00\xA0\xE3',                            # mov     r0, #0x9
        b'\xAB\x00\x00\xEA',                            # b       0x4590
        b'\x00\x42\xA0\xE1',                            # lsl     r4, r0, #0x4
        b'\x00\x10\xA0\xE3',                            # mov     r1, #0
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x01\x30\xA0\xE1',                            # mov     r3, r1
        b'\x74\x20\xFF\xE6',                            # uxth    r2, r4, ror  #0
        b'\x5C\xFE\xFF\xEB',                            # bl      0x3c6c
        b'\x00\x00\x50\xE3',                            # cmp     r0, #0
        b'\xF5\xFF\xFF\x1A',                            # bne     0x42d8
        b'\x02\x09\x14\xE3',                            # tst     r4, #0x8000
        b'\x01\x60\xA0\x13',                            # movne   r6, #0x1
        b'\xC1\xFF\xFF\xEA',                            # b       0x4214
        b'\x90\x00\x53\xE3',                            # cmp     r3, #0x90
        b'\x10\x00\x00\x1A',                            # bne     0x4358
        b'\x0D\x30\x00\xE2',                            # and     r3, r0, #0xd
        b'\x0D\x00\x53\xE3',                            # cmp     r3, #0xd
        b'\xED\xFF\xFF\x0A',                            # beq     0x42d8
        b'\x00\x10\xA0\xE3',                            # mov     r1, #0
        b'\x0C\x80\x8D\xE2',                            # add     r8, sp, #0xc
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x00\x80\x8D\xE5',                            # str     r8, [sp]
        b'\x0F\x20\x04\xE2',                            # and     r2, r4, #0xf
        b'\x01\x30\xA0\xE1',                            # mov     r3, r1
        b'\xD5\xFC\xFF\xEB',                            # bl      0x3694
        b'\x00\x80\x8D\xE5',                            # str     r8, [sp]
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x00\x10\xA0\xE3',                            # mov     r1, #0
        b'\x0D\x20\xA0\xE3',                            # mov     r2, #0xd
        b'\x01\x30\xA0\xE1',                            # mov     r3, r1
        b'\xF0\xFC\xFF\xEB',                            # bl      0x3718
        b'\xAE\xFF\xFF\xEA',                            # b       0x4214
        b'\xA0\x00\x53\xE3',                            # cmp     r3, #0xa0
        b'\x09\x00\x00\x1A',                            # bne     0x4388
        b'\x00\x20\xE0\xE1',                            # mvn     r2, r0
        b'\xFF\x3E\xA0\xE3',                            # mov     r3, #0xff0
        b'\x07\x20\x02\xE2',                            # and     r2, r2, #0x7
        b'\x08\x00\x10\xE3',                            # tst     r0, #0x8
        b'\x53\x22\xA0\xE1',                            # asr     r2, r3, r2
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x03\x20\x02\xE0',                            # and     r2, r2, r3
        b'\x00\x10\xA0\xE3',                            # mov     r1, #0
        b'\x01\x29\x82\x13',                            # orrne   r2, r2, #0x4000
        b'\x0A\x00\x00\xEA',                            # b       0x43b4
        b'\xB0\x00\x53\xE3',                            # cmp     r3, #0xb0
        b'\x39\x00\x00\x1A',                            # bne     0x4478
        b'\xB1\x00\x50\xE3',                            # cmp     r0, #0xb1
        b'\x08\x00\x00\x1A',                            # bne     0x43bc
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\x74\xFF\xFF\xEB',                            # bl      0x4174
        b'\x00\x20\x50\xE2',                            # sub.s   r2, r0, #0
        b'\xCB\xFF\xFF\x0A',                            # beq     0x42d8
        b'\xF0\x10\x12\xE2',                            # and.s   r1, r2, #0xf0
        b'\xC9\xFF\xFF\x1A',                            # bne     0x42d8
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x01\x30\xA0\xE1',                            # mov     r3, r1
        b'\x6F\x00\x00\xEA',                            # b       0x457c
        b'\xB2\x00\x50\xE3',                            # cmp     r0, #0xb2
        b'\x19\x00\x00\x1A',                            # bne     0x442c
        b'\x00\x10\xA0\xE3',                            # mov     r1, #0
        b'\x0D\x20\xA0\xE3',                            # mov     r2, #0xd
        b'\x01\x30\xA0\xE1',                            # mov     r3, r1
        b'\x0C\x40\x8D\xE2',                            # add     r4, sp, #0xc
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x00\x40\x8D\xE5',                            # str     r4, [sp]
        b'\xAC\xFC\xFF\xEB',                            # bl      0x3694
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\x62\xFF\xFF\xEB',                            # bl      0x4174
        b'\x02\x80\xA0\xE3',                            # mov     r8, #0x2
        b'\x80\x10\x10\xE2',                            # and.s   r1, r0, #0x80
        b'\x0C\x30\x9D\xE5',                            # ldr     r3, [sp,  #0xc]
        b'\x7F\x00\x00\xE2',                            # and     r0, r0, #0x7f
        b'\x05\x00\x00\x0A',                            # beq     0x4414
        b'\x10\x38\x83\xE0',                            # add     r3, r3, r0, lsl r8
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\x0C\x30\x8D\xE5',                            # str     r3, [sp,  #0xc]
        b'\x07\x80\x88\xE2',                            # add     r8, r8, #0x7
        b'\x58\xFF\xFF\xEB',                            # bl      0x4174
        b'\xF5\xFF\xFF\xEA',                            # b       0x43ec
        b'\x81\x3F\x83\xE2',                            # add     r3, r3, #0x204
        b'\x00\x40\x8D\xE5',                            # str     r4, [sp]
        b'\x10\x38\x83\xE0',                            # add     r3, r3, r0, lsl r8
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x0C\x30\x8D\xE5',                            # str     r3, [sp,  #0xc]
        b'\xC6\xFF\xFF\xEA',                            # b       0x4348
        b'\xB3\x00\x50\xE3',                            # cmp     r0, #0xb3
        b'\x07\x00\x00\x1A',                            # bne     0x4454
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\x4D\xFF\xFF\xEB',                            # bl      0x4174
        b'\x01\x10\xA0\xE3',                            # mov     r1, #0x1
        b'\x0F\x20\x00\xE2',                            # and     r2, r0, #0xf
        b'\xF0\x30\x00\xE2',                            # and     r3, r0, #0xf0
        b'\x01\x20\x82\xE2',                            # add     r2, r2, #0x1
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x13\x00\x00\xEA',                            # b       0x44a4
        b'\xFC\x30\x00\xE2',                            # and     r3, r0, #0xfc
        b'\xB4\x00\x53\xE3',                            # cmp     r3, #0xb4
        b'\x9D\xFF\xFF\x0A',                            # beq     0x42d8
        b'\x07\x20\x00\xE2',                            # and     r2, r0, #0x7
        b'\x01\x10\xA0\xE3',                            # mov     r1, #0x1
        b'\x01\x20\x82\xE2',                            # add     r2, r2, #0x1
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x02\x27\x82\xE3',                            # orr     r2, r2, #0x80000
        b'\xCE\xFF\xFF\xEA',                            # b       0x43b4
        b'\xC0\x00\x53\xE3',                            # cmp     r3, #0xc0
        b'\x35\x00\x00\x1A',                            # bne     0x4558
        b'\xC6\x00\x50\xE3',                            # cmp     r0, #0xc6
        b'\x08\x00\x00\x1A',                            # bne     0x44ac
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\x38\xFF\xFF\xEB',                            # bl      0x4174
        b'\x03\x10\xA0\xE3',                            # mov     r1, #0x3
        b'\x0F\x20\x00\xE2',                            # and     r2, r0, #0xf
        b'\xF0\x30\x00\xE2',                            # and     r3, r0, #0xf0
        b'\x01\x20\x82\xE2',                            # add     r2, r2, #0x1
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x03\x26\x82\xE1',                            # orr     r2, r2, r3, lsl  #0xc
        b'\xC1\xFF\xFF\xEA',                            # b       0x43b4
        b'\xC7\x00\x50\xE3',                            # cmp     r0, #0xc7
        b'\x08\x00\x00\x1A',                            # bne     0x44d8
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\x2D\xFF\xFF\xEB',                            # bl      0x4174
        b'\x00\x20\x50\xE2',                            # sub.s   r2, r0, #0
        b'\x84\xFF\xFF\x0A',                            # beq     0x42d8
        b'\xF0\x30\x12\xE2',                            # and.s   r3, r2, #0xf0
        b'\x82\xFF\xFF\x1A',                            # bne     0x42d8
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x04\x10\xA0\xE3',                            # mov     r1, #0x4
        b'\x28\x00\x00\xEA',                            # b       0x457c
        b'\xF8\x30\x00\xE2',                            # and     r3, r0, #0xf8
        b'\xC0\x00\x53\xE3',                            # cmp     r3, #0xc0
        b'\x05\x00\x00\x1A',                            # bne     0x44fc
        b'\x0F\x20\x00\xE2',                            # and     r2, r0, #0xf
        b'\x03\x10\xA0\xE3',                            # mov     r1, #0x3
        b'\x01\x20\x82\xE2',                            # add     r2, r2, #0x1
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x0A\x28\x82\xE3',                            # orr     r2, r2, #0xa0000
        b'\xAD\xFF\xFF\xEA',                            # b       0x43b4
        b'\xC8\x00\x50\xE3',                            # cmp     r0, #0xc8
        b'\x09\x00\x00\x1A',                            # bne     0x452c
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\x19\xFF\xFF\xEB',                            # bl      0x4174
        b'\x01\x10\xA0\xE3',                            # mov     r1, #0x1
        b'\xF0\x20\x00\xE2',                            # and     r2, r0, #0xf0
        b'\x0F\x00\x00\xE2',                            # and     r0, r0, #0xf
        b'\x10\x20\x82\xE2',                            # add     r2, r2, #0x10
        b'\x01\x30\x80\xE2',                            # add     r3, r0, #0x1
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x02\x26\x83\xE1',                            # orr     r2, r3, r2, lsl  #0xc
        b'\x12\x00\x00\xEA',                            # b       0x4578
        b'\xC9\x00\x50\xE3',                            # cmp     r0, #0xc9
        b'\x68\xFF\xFF\x1A',                            # bne     0x42d8
        b'\x07\x00\xA0\xE1',                            # mov     r0, r7
        b'\x0D\xFF\xFF\xEB',                            # bl      0x4174
        b'\x01\x10\xA0\xE3',                            # mov     r1, #0x1
        b'\x0F\x20\x00\xE2',                            # and     r2, r0, #0xf
        b'\xF0\x30\x00\xE2',                            # and     r3, r0, #0xf0
        b'\x01\x20\x82\xE2',                            # add     r2, r2, #0x1
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x03\x26\x82\xE1',                            # orr     r2, r2, r3, lsl  #0xc
        b'\x07\x00\x00\xEA',                            # b       0x4578
        b'\xF8\x30\x00\xE2',                            # and     r3, r0, #0xf8
        b'\xD0\x00\x53\xE3',                            # cmp     r3, #0xd0
        b'\x5C\xFF\xFF\x1A',                            # bne     0x42d8
        b'\x07\x20\x00\xE2',                            # and     r2, r0, #0x7
        b'\x01\x10\xA0\xE3',                            # mov     r1, #0x1
        b'\x01\x20\x82\xE2',                            # add     r2, r2, #0x1
        b'\x05\x00\xA0\xE1',                            # mov     r0, r5
        b'\x02\x27\x82\xE3',                            # orr     r2, r2, #0x80000
        b'\x05\x30\xA0\xE3',                            # mov     r3, #0x5
        b'\xBA\xFD\xFF\xEB',                            # bl      0x3c6c
        b'\x00\x00\x50\xE3',                            # cmp     r0, #0
        b'\x53\xFF\xFF\x1A',                            # bne     0x42d8
        b'\x21\xFF\xFF\xEA',                            # b       0x4214
        b'\x00\x00\xA0\xE3',                            # mov     r0, #0
        b'\x14\xD0\x8D\xE2',                            # add     sp, sp, #0x14
        b'\xF0\x83\xBD\xE8',                            # pop     {r4, r5, r6, r7, r8, r9, pc}
    ],
    'length': 0x398
},
{
    'name': '__gnu_unwind_frame',
    'description': 'int32_t __gnu_unwind_frame(void* arg1, int32_t arg2)',
    'address': 0x4598,
    'instructions': [
        b'\x1F\x40\x2D\xE9',                            # push    {r0, r1, r2, r3, r4, lr}
        b'\x4C\x30\x90\xE5',                            # ldr     r3, [r0,  #0x4c]
        b'\x01\x00\xA0\xE1',                            # mov     r0, r1
        b'\x04\x10\x8D\xE2',                            # add     r1, sp, #0x4
        b'\x04\x20\x93\xE5',                            # ldr     r2, [r3,  #0x4]
        b'\x02\x24\xA0\xE1',                            # lsl     r2, r2, #0x8
        b'\x04\x20\x8D\xE5',                            # str     r2, [sp,  #0x4]
        b'\x08\x20\x83\xE2',                            # add     r2, r3, #0x8
        b'\x08\x20\x8D\xE5',                            # str     r2, [sp,  #0x8]
        b'\x03\x20\xA0\xE3',                            # mov     r2, #0x3
        b'\x0C\x20\xCD\xE5',                            # strb    r2, [sp,  #0xc]
        b'\x07\x30\xD3\xE5',                            # ldrb    r3, [r3,  #0x7]
        b'\x0D\x30\xCD\xE5',                            # strb    r3, [sp,  #0xd]
        b'\x0B\xFF\xFF\xEB',                            # bl      0x4200
        b'\x14\xD0\x8D\xE2',                            # add     sp, sp, #0x14
        b'\x04\xF0\x9D\xE4',                            # ldr     pc, [sp],  #0x4
    ],
    'length': 0x40
},
{
    'name': '_Unwind_GetRegionStart',
    'description': 'int32_t _Unwind_GetRegionStart(int32_t arg1, int32_t arg2, int32_t arg3, int32_t arg4)',
    'address': 0x45D8,
    'instructions': [
        b'\x08\x40\x2D\xE9',                            # push    {r3, lr}
        b'\x06\xFF\xFF\xEB',                            # bl      0x41fc
        b'\x48\x00\x90\xE5',                            # ldr     r0, [r0,  #0x48]
        b'\x08\x80\xBD\xE8',                            # pop     {r3, pc}
    ],
    'length': 0x10
},
{
    'name': '_Unwind_GetLanguageSpecificData',
    'description': 'void* _Unwind_GetLanguageSpecificData(int32_t arg1, int32_t arg2, int32_t arg3, int32_t arg4)',
    'address': 0x45E8,
    'instructions': [
        b'\x08\x40\x2D\xE9',                            # push    {r3, lr}
        b'\x02\xFF\xFF\xEB',                            # bl      0x41fc
        b'\x4C\x30\x90\xE5',                            # ldr     r3, [r0,  #0x4c]
        b'\x07\x00\xD3\xE5',                            # ldrb    r0, [r3,  #0x7]
        b'\x00\x01\x83\xE0',                            # add     r0, r3, r0, lsl  #0x2
        b'\x08\x00\x80\xE2',                            # add     r0, r0, #0x8
        b'\x08\x80\xBD\xE8',                            # pop     {r3, pc}
    ],
    'length': 0x1C
},
{
    'name': '_Unwind_GetDataRelBase',
    'description': 'int32_t _Unwind_GetDataRelBase() __noreturn',
    'address': 0x4604,
    'instructions': [
        b'\x08\x40\x2D\xE9',                            # push    {r3, lr}
        b'\x14\xF0\xFF\xEB',                            # bl      0x660
    ],
    'length': 0x8
},
{
    'name': '_Unwind_GetTextRelBase',
    'description': 'int32_t _Unwind_GetTextRelBase() __noreturn',
    'address': 0x460C,
    'instructions': [
        b'\x08\x40\x2D\xE9',                            # push    {r3, lr}
        b'\x12\xF0\xFF\xEB',                            # bl      0x660
    ],
    'length': 0x8
},
]
