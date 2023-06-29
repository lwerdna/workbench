# ../binja-sandbox/dump-functions-for-emulation.py > md5_x64_dump.py
functions = [
{
    'name': '_main',
    'description': 'int64_t _main(int32_t arg1, int64_t arg2)',
    'address': 0x1000025F0,
    'instructions': [
        b'\x55',                                        # push    rbp
        b'\x48\x89\xE5',                                # mov     rbp, rsp
        b'\x48\x83\xEC\x20',                            # sub     rsp, 0x20
        b'\xC7\x45\xFC\x00\x00\x00\x00',                # mov     dword [rbp-0x4], 0x0
        b'\x89\x7D\xF8',                                # mov     dword [rbp-0x8], edi
        b'\x48\x89\x75\xF0',                            # mov     qword [rbp-0x10], rsi
        b'\x83\x7D\xF8\x01',                            # cmp     dword [rbp-0x8], 0x1
        b'\x0F\x8E\xE7\x00\x00\x00',                    # jle     0x1000026f7
        b'\xC7\x45\xEC\x01\x00\x00\x00',                # mov     dword [rbp-0x14], 0x1
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x3B\x45\xF8',                                # cmp     eax, dword [rbp-0x8]
        b'\x0F\x8D\xCF\x00\x00\x00',                    # jge     0x1000026f2
        b'\x48\x8B\x45\xF0',                            # mov     rax, qword [rbp-0x10]
        b'\x48\x63\x4D\xEC',                            # movsxd  rcx, dword [rbp-0x14]
        b'\x48\x8B\x04\xC8',                            # mov     rax, qword [rax+rcx*8]
        b'\x0F\xBE\x00',                                # movsx   eax, byte [rax]
        b'\x83\xF8\x2D',                                # cmp     eax, 0x2d
        b'\x0F\x85\x33\x00\x00\x00',                    # jne     0x10000266e
        b'\x48\x8B\x45\xF0',                            # mov     rax, qword [rbp-0x10]
        b'\x48\x63\x4D\xEC',                            # movsxd  rcx, dword [rbp-0x14]
        b'\x48\x8B\x04\xC8',                            # mov     rax, qword [rax+rcx*8]
        b'\x0F\xBE\x40\x01',                            # movsx   eax, byte [rax+0x1]
        b'\x83\xF8\x73',                                # cmp     eax, 0x73
        b'\x0F\x85\x1A\x00\x00\x00',                    # jne     0x10000266e
        b'\x48\x8B\x45\xF0',                            # mov     rax, qword [rbp-0x10]
        b'\x48\x63\x4D\xEC',                            # movsxd  rcx, dword [rbp-0x14]
        b'\x48\x8B\x3C\xC8',                            # mov     rdi, qword [rax+rcx*8]
        b'\x48\x83\xC7\x02',                            # add     rdi, 0x2
        b'\xE8\xA7\x00\x00\x00',                        # call    0x100002710
        b'\xE9\x71\x00\x00\x00',                        # jmp     0x1000026df
        b'\x48\x8B\x45\xF0',                            # mov     rax, qword [rbp-0x10]
        b'\x48\x63\x4D\xEC',                            # movsxd  rcx, dword [rbp-0x14]
        b'\x48\x8B\x3C\xC8',                            # mov     rdi, qword [rax+rcx*8]
        b'\x48\x8D\x35\xB1\x17\x00\x00',                # lea     rsi, [rel 0x100003e32]
        b'\xE8\x42\x17\x00\x00',                        # call    0x100003dc8
        b'\x83\xF8\x00',                                # cmp     eax, 0x0
        b'\x0F\x85\x0A\x00\x00\x00',                    # jne     0x100002699
        b'\xE8\x4C\x01\x00\x00',                        # call    0x1000027e0
        b'\xE9\x41\x00\x00\x00',                        # jmp     0x1000026da
        b'\x48\x8B\x45\xF0',                            # mov     rax, qword [rbp-0x10]
        b'\x48\x63\x4D\xEC',                            # movsxd  rcx, dword [rbp-0x14]
        b'\x48\x8B\x3C\xC8',                            # mov     rdi, qword [rax+rcx*8]
        b'\x48\x8D\x35\x89\x17\x00\x00',                # lea     rsi, [rel 0x100003e35]
        b'\xE8\x17\x17\x00\x00',                        # call    0x100003dc8
        b'\x83\xF8\x00',                                # cmp     eax, 0x0
        b'\x0F\x85\x0A\x00\x00\x00',                    # jne     0x1000026c4
        b'\xE8\x71\x02\x00\x00',                        # call    0x100002930
        b'\xE9\x11\x00\x00\x00',                        # jmp     0x1000026d5
        b'\x48\x8B\x45\xF0',                            # mov     rax, qword [rbp-0x10]
        b'\x48\x63\x4D\xEC',                            # movsxd  rcx, dword [rbp-0x14]
        b'\x48\x8B\x3C\xC8',                            # mov     rdi, qword [rax+rcx*8]
        b'\xE8\xCB\x02\x00\x00',                        # call    0x1000029a0
        b'\xE9\x00\x00\x00\x00',                        # jmp     0x1000026da
        b'\xE9\x00\x00\x00\x00',                        # jmp     0x1000026df
        b'\xE9\x00\x00\x00\x00',                        # jmp     0x1000026e4
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x83\xC0\x01',                                # add     eax, 0x1
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\xE9\x25\xFF\xFF\xFF',                        # jmp     0x100002617
        b'\xE9\x05\x00\x00\x00',                        # jmp     0x1000026fc
        b'\xE8\x94\x03\x00\x00',                        # call    0x100002a90
        b'\x31\xC0',                                    # xor     eax, eax
        b'\x48\x83\xC4\x20',                            # add     rsp, 0x20
        b'\x5D',                                        # pop     rbp
        b'\xC3',                                        # retn    
    ],
    'length': 0x114
},
{
    'name': '_MDString',
    'description': 'int64_t _MDString(int64_t arg1)',
    'address': 0x100002710,
    'instructions': [
        b'\x55',                                        # push    rbp
        b'\x48\x89\xE5',                                # mov     rbp, rsp
        b'\x48\x81\xEC\x80\x00\x00\x00',                # sub     rsp, 0x80
        b'\x48\x89\x7D\xF8',                            # mov     qword [rbp-0x8], rdi
        b'\x48\x8B\x7D\xF8',                            # mov     rdi, qword [rbp-0x8]
        b'\xE8\xA6\x16\x00\x00',                        # call    0x100003dce
        b'\x89\x45\x8C',                                # mov     dword [rbp-0x74], eax
        b'\x48\x8D\x7D\xA0',                            # lea     rdi, [rbp-0x60]
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\xEA\x03\x00\x00',                        # call    0x100002b20
        b'\x48\x8B\x75\xF8',                            # mov     rsi, qword [rbp-0x8]
        b'\x8B\x55\x8C',                                # mov     edx, dword [rbp-0x74]
        b'\x48\x8D\x7D\xA0',                            # lea     rdi, [rbp-0x60]
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\x28\x04\x00\x00',                        # call    0x100002b70
        b'\x48\x8D\x7D\x90',                            # lea     rdi, [rbp-0x70]
        b'\x48\x8D\x75\xA0',                            # lea     rsi, [rbp-0x60]
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\x39\x05\x00\x00',                        # call    0x100002c90
        b'\x48\x8B\x55\xF8',                            # mov     rdx, qword [rbp-0x8]
        b'\x48\x8D\x3D\xD6\x16\x00\x00',                # lea     rdi, [rel 0x100003e38]
        b'\xBE\x05\x00\x00\x00',                        # mov     esi, 0x5
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\x54\x16\x00\x00',                        # call    0x100003dc2
        b'\x48\x8D\x7D\x90',                            # lea     rdi, [rbp-0x70]
        b'\xE8\x19\x00\x00\x00',                        # call    0x100002790
        b'\x48\x8D\x3D\xC9\x16\x00\x00',                # lea     rdi, [rel 0x100003e47]
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\x3D\x16\x00\x00',                        # call    0x100003dc2
        b'\x48\x81\xC4\x80\x00\x00\x00',                # add     rsp, 0x80
        b'\x5D',                                        # pop     rbp
        b'\xC3',                                        # retn    
    ],
    'length': 0x7E
},
{
    'name': '_MDPrint',
    'description': 'void _MDPrint(int64_t arg1)',
    'address': 0x100002790,
    'instructions': [
        b'\x55',                                        # push    rbp
        b'\x48\x89\xE5',                                # mov     rbp, rsp
        b'\x48\x83\xEC\x10',                            # sub     rsp, 0x10
        b'\x48\x89\x7D\xF8',                            # mov     qword [rbp-0x8], rdi
        b'\xC7\x45\xF4\x00\x00\x00\x00',                # mov     dword [rbp-0xc], 0x0
        b'\x83\x7D\xF4\x10',                            # cmp     dword [rbp-0xc], 0x10
        b'\x0F\x83\x27\x00\x00\x00',                    # jae     0x1000027d4
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\x8B\x4D\xF4',                                # mov     ecx, dword [rbp-0xc]
        b'\x0F\xB6\x34\x08',                            # movzx   esi, byte [rax+rcx]
        b'\x48\x8D\x3D\x8A\x16\x00\x00',                # lea     rdi, [rel 0x100003e49]
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\xFC\x15\x00\x00',                        # call    0x100003dc2
        b'\x8B\x45\xF4',                                # mov     eax, dword [rbp-0xc]
        b'\x83\xC0\x01',                                # add     eax, 0x1
        b'\x89\x45\xF4',                                # mov     dword [rbp-0xc], eax
        b'\xE9\xCF\xFF\xFF\xFF',                        # jmp     0x1000027a3
        b'\x48\x83\xC4\x10',                            # add     rsp, 0x10
        b'\x5D',                                        # pop     rbp
        b'\xC3',                                        # retn    
    ],
    'length': 0x4A
},
{
    'name': '_MDTimeTrial',
    'description': 'int64_t _MDTimeTrial()',
    'address': 0x1000027E0,
    'instructions': [
        b'\x55',                                        # push    rbp
        b'\x48\x89\xE5',                                # mov     rbp, rsp
        b'\x48\x81\xEC\x70\x04\x00\x00',                # sub     rsp, 0x470
        b'\x48\x8D\x3D\x5C\x16\x00\x00',                # lea     rdi, [rel 0x100003e4e]
        b'\xBE\x05\x00\x00\x00',                        # mov     esi, 0x5
        b'\xB9\xE8\x03\x00\x00',                        # mov     ecx, 0x3e8
        b'\x89\xCA',                                    # mov     edx, ecx
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\xBD\x15\x00\x00',                        # call    0x100003dc2
        b'\xC7\x85\x9C\xFB\xFF\xFF\x00\x00\x00\x00',    # mov     dword [rbp-0x464], 0x0
        b'\x81\xBD\x9C\xFB\xFF\xFF\xE8\x03\x00\x00',    # cmp     dword [rbp-0x464], 0x3e8
        b'\x0F\x83\x2E\x00\x00\x00',                    # jae     0x10000284d
        b'\x8B\x85\x9C\xFB\xFF\xFF',                    # mov     eax, dword [rbp-0x464]
        b'\x25\xFF\x00\x00\x00',                        # and     eax, 0xff
        b'\x88\xC1',                                    # mov     cl, al
        b'\x8B\x85\x9C\xFB\xFF\xFF',                    # mov     eax, dword [rbp-0x464]
        b'\x88\x8C\x05\xB0\xFB\xFF\xFF',                # mov     byte [rbp+rax-0x450], cl
        b'\x8B\x85\x9C\xFB\xFF\xFF',                    # mov     eax, dword [rbp-0x464]
        b'\x83\xC0\x01',                                # add     eax, 0x1
        b'\x89\x85\x9C\xFB\xFF\xFF',                    # mov     dword [rbp-0x464], eax
        b'\xE9\xC2\xFF\xFF\xFF',                        # jmp     0x10000280f
        b'\x48\x8D\x7D\x98',                            # lea     rdi, [rbp-0x68]
        b'\xE8\x7E\x15\x00\x00',                        # call    0x100003dd4
        b'\x48\x8D\x7D\xA8',                            # lea     rdi, [rbp-0x58]
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\xBF\x02\x00\x00',                        # call    0x100002b20
        b'\xC7\x85\x9C\xFB\xFF\xFF\x00\x00\x00\x00',    # mov     dword [rbp-0x464], 0x0
        b'\x81\xBD\x9C\xFB\xFF\xFF\xE8\x03\x00\x00',    # cmp     dword [rbp-0x464], 0x3e8
        b'\x0F\x83\x2B\x00\x00\x00',                    # jae     0x1000028a6
        b'\x48\x8D\xB5\xB0\xFB\xFF\xFF',                # lea     rsi, [rbp-0x450]
        b'\x48\x8D\x7D\xA8',                            # lea     rdi, [rbp-0x58]
        b'\xBA\xE8\x03\x00\x00',                        # mov     edx, 0x3e8
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\xDE\x02\x00\x00',                        # call    0x100002b70
        b'\x8B\x85\x9C\xFB\xFF\xFF',                    # mov     eax, dword [rbp-0x464]
        b'\x83\xC0\x01',                                # add     eax, 0x1
        b'\x89\x85\x9C\xFB\xFF\xFF',                    # mov     dword [rbp-0x464], eax
        b'\xE9\xC5\xFF\xFF\xFF',                        # jmp     0x10000286b
        b'\x48\x8D\xBD\xA0\xFB\xFF\xFF',                # lea     rdi, [rbp-0x460]
        b'\x48\x8D\x75\xA8',                            # lea     rsi, [rbp-0x58]
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\xD8\x03\x00\x00',                        # call    0x100002c90
        b'\x48\x8D\x7D\xA0',                            # lea     rdi, [rbp-0x60]
        b'\xE8\x13\x15\x00\x00',                        # call    0x100003dd4
        b'\x48\x8D\x3D\xB7\x15\x00\x00',                # lea     rdi, [rel 0x100003e7f]
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\xF3\x14\x00\x00',                        # call    0x100003dc2
        b'\x48\x8D\x3D\xB0\x15\x00\x00',                # lea     rdi, [rel 0x100003e86]
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\xE5\x14\x00\x00',                        # call    0x100003dc2
        b'\x48\x8D\xBD\xA0\xFB\xFF\xFF',                # lea     rdi, [rbp-0x460]
        b'\xE8\xA7\xFE\xFF\xFF',                        # call    0x100002790
        b'\x48\x8B\x75\xA0',                            # mov     rsi, qword [rbp-0x60]
        b'\x48\x2B\x75\x98',                            # sub     rsi, qword [rbp-0x68]
        b'\x48\x8D\x3D\x98\x15\x00\x00',                # lea     rdi, [rel 0x100003e90]
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\xC3\x14\x00\x00',                        # call    0x100003dc2
        b'\x48\x8B\x4D\xA0',                            # mov     rcx, qword [rbp-0x60]
        b'\x48\x2B\x4D\x98',                            # sub     rcx, qword [rbp-0x68]
        b'\xB8\x40\x42\x0F\x00',                        # mov     eax, 0xf4240
        b'\x48\x99',                                    # cqo     
        b'\x48\xF7\xF9',                                # idiv    rcx
        b'\x48\x89\xC6',                                # mov     rsi, rax
        b'\x48\x8D\x3D\x8A\x15\x00\x00',                # lea     rdi, [rel 0x100003ea5]
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\xA0\x14\x00\x00',                        # call    0x100003dc2
        b'\x48\x81\xC4\x70\x04\x00\x00',                # add     rsp, 0x470
        b'\x5D',                                        # pop     rbp
        b'\xC3',                                        # retn    
    ],
    'length': 0x14B
},
{
    'name': '_MDTestSuite',
    'description': 'int64_t _MDTestSuite()',
    'address': 0x100002930,
    'instructions': [
        b'\x55',                                        # push    rbp
        b'\x48\x89\xE5',                                # mov     rbp, rsp
        b'\x48\x8D\x3D\x84\x15\x00\x00',                # lea     rdi, [rel 0x100003ebf]
        b'\xBE\x05\x00\x00\x00',                        # mov     esi, 0x5
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\x7B\x14\x00\x00',                        # call    0x100003dc2
        b'\x48\x8D\x3D\x83\x15\x00\x00',                # lea     rdi, [rel 0x100003ed1]
        b'\xE8\xBD\xFD\xFF\xFF',                        # call    0x100002710
        b'\x48\x8D\x3D\x78\x15\x00\x00',                # lea     rdi, [rel 0x100003ed2]
        b'\xE8\xB1\xFD\xFF\xFF',                        # call    0x100002710
        b'\x48\x8D\x3D\x6E\x15\x00\x00',                # lea     rdi, [rel 0x100003ed4]
        b'\xE8\xA5\xFD\xFF\xFF',                        # call    0x100002710
        b'\x48\x8D\x3D\x66\x15\x00\x00',                # lea     rdi, [rel 0x100003ed8]
        b'\xE8\x99\xFD\xFF\xFF',                        # call    0x100002710
        b'\x48\x8D\x3D\x69\x15\x00\x00',                # lea     rdi, [rel 0x100003ee7]
        b'\xE8\x8D\xFD\xFF\xFF',                        # call    0x100002710
        b'\x48\x8D\x3D\x78\x15\x00\x00',                # lea     rdi, [rel 0x100003f02]
        b'\xE8\x81\xFD\xFF\xFF',                        # call    0x100002710
        b'\x48\x8D\x3D\xAB\x15\x00\x00',                # lea     rdi, [rel 0x100003f41]
        b'\xE8\x75\xFD\xFF\xFF',                        # call    0x100002710
        b'\x5D',                                        # pop     rbp
        b'\xC3',                                        # retn    
    ],
    'length': 0x6D
},
{
    'name': '_MDFile',
    'description': 'int64_t _MDFile(int64_t arg1)',
    'address': 0x1000029A0,
    'instructions': [
        b'\x55',                                        # push    rbp
        b'\x48\x89\xE5',                                # mov     rbp, rsp
        b'\x48\x81\xEC\x80\x04\x00\x00',                # sub     rsp, 0x480
        b'\x48\x89\x7D\xF8',                            # mov     qword [rbp-0x8], rdi
        b'\x48\x8B\x7D\xF8',                            # mov     rdi, qword [rbp-0x8]
        b'\x48\x8D\x35\xD8\x15\x00\x00',                # lea     rsi, [rel 0x100003f92]
        b'\xE8\xF7\x13\x00\x00',                        # call    0x100003db6
        b'\x48\x89\x45\xF0',                            # mov     qword [rbp-0x10], rax
        b'\x48\x83\xF8\x00',                            # cmp     rax, 0x0
        b'\x0F\x85\x17\x00\x00\x00',                    # jne     0x1000029e4
        b'\x48\x8B\x75\xF8',                            # mov     rsi, qword [rbp-0x8]
        b'\x48\x8D\x3D\xBD\x15\x00\x00',                # lea     rdi, [rel 0x100003f95]
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\xE3\x13\x00\x00',                        # call    0x100003dc2
        b'\xE9\x97\x00\x00\x00',                        # jmp     0x100002a7b
        b'\x48\x8D\x7D\x98',                            # lea     rdi, [rbp-0x68]
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\x31\x01\x00\x00',                        # call    0x100002b20
        b'\x48\x8D\xBD\x90\xFB\xFF\xFF',                # lea     rdi, [rbp-0x470]
        b'\x48\x8B\x4D\xF0',                            # mov     rcx, qword [rbp-0x10]
        b'\xBE\x01\x00\x00\x00',                        # mov     esi, 0x1
        b'\xBA\x00\x04\x00\x00',                        # mov     edx, 0x400
        b'\xE8\xB3\x13\x00\x00',                        # call    0x100003dbc
        b'\x89\x45\x94',                                # mov     dword [rbp-0x6c], eax
        b'\x83\xF8\x00',                                # cmp     eax, 0x0
        b'\x0F\x84\x1A\x00\x00\x00',                    # je      0x100002a2f
        b'\x48\x8D\xB5\x90\xFB\xFF\xFF',                # lea     rsi, [rbp-0x470]
        b'\x8B\x55\x94',                                # mov     edx, dword [rbp-0x6c]
        b'\x48\x8D\x7D\x98',                            # lea     rdi, [rbp-0x68]
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\x46\x01\x00\x00',                        # call    0x100002b70
        b'\xE9\xC0\xFF\xFF\xFF',                        # jmp     0x1000029ef
        b'\x48\x8D\xBD\x80\xFB\xFF\xFF',                # lea     rdi, [rbp-0x480]
        b'\x48\x8D\x75\x98',                            # lea     rsi, [rbp-0x68]
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\x4F\x02\x00\x00',                        # call    0x100002c90
        b'\x48\x8B\x7D\xF0',                            # mov     rdi, qword [rbp-0x10]
        b'\xE8\x66\x13\x00\x00',                        # call    0x100003db0
        b'\x48\x8B\x55\xF8',                            # mov     rdx, qword [rbp-0x8]
        b'\x48\x8D\x3D\x54\x15\x00\x00',                # lea     rdi, [rel 0x100003fa9]
        b'\xBE\x05\x00\x00\x00',                        # mov     esi, 0x5
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\x61\x13\x00\x00',                        # call    0x100003dc2
        b'\x48\x8D\xBD\x80\xFB\xFF\xFF',                # lea     rdi, [rbp-0x480]
        b'\xE8\x23\xFD\xFF\xFF',                        # call    0x100002790
        b'\x48\x8D\x3D\xD3\x13\x00\x00',                # lea     rdi, [rel 0x100003e47]
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\x47\x13\x00\x00',                        # call    0x100003dc2
        b'\x48\x81\xC4\x80\x04\x00\x00',                # add     rsp, 0x480
        b'\x5D',                                        # pop     rbp
        b'\xC3',                                        # retn    
    ],
    'length': 0xE4
},
{
    'name': '_MDFilter',
    'description': 'int64_t _MDFilter()',
    'address': 0x100002A90,
    'instructions': [
        b'\x55',                                        # push    rbp
        b'\x48\x89\xE5',                                # mov     rbp, rsp
        b'\x48\x81\xEC\x80\x00\x00\x00',                # sub     rsp, 0x80
        b'\x48\x8D\x7D\xA8',                            # lea     rdi, [rbp-0x58]
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\x7A\x00\x00\x00',                        # call    0x100002b20
        b'\x48\x8D\x7D\x90',                            # lea     rdi, [rbp-0x70]
        b'\x48\x8B\x05\x4F\x15\x00\x00',                # mov     rax, qword [rel 0x100004000]
        b'\x48\x8B\x08',                                # mov     rcx, qword [rax]
        b'\xBE\x01\x00\x00\x00',                        # mov     esi, 0x1
        b'\xBA\x10\x00\x00\x00',                        # mov     edx, 0x10
        b'\xE8\xF9\x12\x00\x00',                        # call    0x100003dbc
        b'\x89\x45\xA4',                                # mov     dword [rbp-0x5c], eax
        b'\x83\xF8\x00',                                # cmp     eax, 0x0
        b'\x0F\x84\x17\x00\x00\x00',                    # je      0x100002ae6
        b'\x48\x8D\x75\x90',                            # lea     rsi, [rbp-0x70]
        b'\x8B\x55\xA4',                                # mov     edx, dword [rbp-0x5c]
        b'\x48\x8D\x7D\xA8',                            # lea     rdi, [rbp-0x58]
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\x8F\x00\x00\x00',                        # call    0x100002b70
        b'\xE9\xC0\xFF\xFF\xFF',                        # jmp     0x100002aa6
        b'\x48\x8D\x7D\x80',                            # lea     rdi, [rbp-0x80]
        b'\x48\x8D\x75\xA8',                            # lea     rsi, [rbp-0x58]
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\x9B\x01\x00\x00',                        # call    0x100002c90
        b'\x48\x8D\x7D\x80',                            # lea     rdi, [rbp-0x80]
        b'\xE8\x92\xFC\xFF\xFF',                        # call    0x100002790
        b'\x48\x8D\x3D\x42\x13\x00\x00',                # lea     rdi, [rel 0x100003e47]
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\xB6\x12\x00\x00',                        # call    0x100003dc2
        b'\x48\x81\xC4\x80\x00\x00\x00',                # add     rsp, 0x80
        b'\x5D',                                        # pop     rbp
        b'\xC3',                                        # retn    
    ],
    'length': 0x85
},
{
    'name': '_MD5Init',
    'description': 'int32_t* _MD5Init(int32_t* arg1)',
    'address': 0x100002B20,
    'instructions': [
        b'\x55',                                        # push    rbp
        b'\x48\x89\xE5',                                # mov     rbp, rsp
        b'\x48\x89\x7D\xF8',                            # mov     qword [rbp-0x8], rdi
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\xC7\x40\x14\x00\x00\x00\x00',                # mov     dword [rax+0x14], 0x0
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\xC7\x40\x10\x00\x00\x00\x00',                # mov     dword [rax+0x10], 0x0
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\xC7\x00\x01\x23\x45\x67',                    # mov     dword [rax], 0x67452301
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\xC7\x40\x04\x89\xAB\xCD\xEF',                # mov     dword [rax+0x4], 0xefcdab89
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\xC7\x40\x08\xFE\xDC\xBA\x98',                # mov     dword [rax+0x8], 0x98badcfe
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\xC7\x40\x0C\x76\x54\x32\x10',                # mov     dword [rax+0xc], 0x10325476
        b'\x5D',                                        # pop     rbp
        b'\xC3',                                        # retn    
    ],
    'length': 0x4B
},
{
    'name': '_MD5Update',
    'description': 'uint64_t _MD5Update(int32_t* arg1, int64_t arg2, int32_t arg3)',
    'address': 0x100002B70,
    'instructions': [
        b'\x55',                                        # push    rbp
        b'\x48\x89\xE5',                                # mov     rbp, rsp
        b'\x48\x83\xEC\x20',                            # sub     rsp, 0x20
        b'\x48\x89\x7D\xF8',                            # mov     qword [rbp-0x8], rdi
        b'\x48\x89\x75\xF0',                            # mov     qword [rbp-0x10], rsi
        b'\x89\x55\xEC',                                # mov     dword [rbp-0x14], edx
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\x8B\x40\x10',                                # mov     eax, dword [rax+0x10]
        b'\xC1\xE8\x03',                                # shr     eax, 0x3
        b'\x83\xE0\x3F',                                # and     eax, 0x3f
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\xC1\xE0\x03',                                # shl     eax, 0x3
        b'\x48\x8B\x4D\xF8',                            # mov     rcx, qword [rbp-0x8]
        b'\x03\x41\x10',                                # add     eax, dword [rcx+0x10]
        b'\x89\x41\x10',                                # mov     dword [rcx+0x10], eax
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\xC1\xE1\x03',                                # shl     ecx, 0x3
        b'\x39\xC8',                                    # cmp     eax, ecx
        b'\x0F\x83\x0D\x00\x00\x00',                    # jae     0x100002bbe
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\x8B\x48\x14',                                # mov     ecx, dword [rax+0x14]
        b'\x83\xC1\x01',                                # add     ecx, 0x1
        b'\x89\x48\x14',                                # mov     dword [rax+0x14], ecx
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\xC1\xE9\x1D',                                # shr     ecx, 0x1d
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\x03\x48\x14',                                # add     ecx, dword [rax+0x14]
        b'\x89\x48\x14',                                # mov     dword [rax+0x14], ecx
        b'\xB8\x40\x00\x00\x00',                        # mov     eax, 0x40
        b'\x2B\x45\xE4',                                # sub     eax, dword [rbp-0x1c]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x3B\x45\xE0',                                # cmp     eax, dword [rbp-0x20]
        b'\x0F\x82\x6D\x00\x00\x00',                    # jb      0x100002c52
        b'\x48\x8B\x7D\xF8',                            # mov     rdi, qword [rbp-0x8]
        b'\x48\x83\xC7\x18',                            # add     rdi, 0x18
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x48\x01\xC7',                                # add     rdi, rax
        b'\x48\x8B\x75\xF0',                            # mov     rsi, qword [rbp-0x10]
        b'\x8B\x55\xE0',                                # mov     edx, dword [rbp-0x20]
        b'\xE8\x21\x11\x00\x00',                        # call    0x100003d20
        b'\x48\x8B\x7D\xF8',                            # mov     rdi, qword [rbp-0x8]
        b'\x48\x8B\x75\xF8',                            # mov     rsi, qword [rbp-0x8]
        b'\x48\x83\xC6\x18',                            # add     rsi, 0x18
        b'\xE8\x30\x01\x00\x00',                        # call    0x100002d40
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x83\xC0\x3F',                                # add     eax, 0x3f
        b'\x3B\x45\xEC',                                # cmp     eax, dword [rbp-0x14]
        b'\x0F\x83\x21\x00\x00\x00',                    # jae     0x100002c46
        b'\x48\x8B\x7D\xF8',                            # mov     rdi, qword [rbp-0x8]
        b'\x48\x8B\x75\xF0',                            # mov     rsi, qword [rbp-0x10]
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x48\x01\xC6',                                # add     rsi, rax
        b'\xE8\x08\x01\x00\x00',                        # call    0x100002d40
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x83\xC0\x40',                                # add     eax, 0x40
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\xE9\xD0\xFF\xFF\xFF',                        # jmp     0x100002c16
        b'\xC7\x45\xE4\x00\x00\x00\x00',                # mov     dword [rbp-0x1c], 0x0
        b'\xE9\x07\x00\x00\x00',                        # jmp     0x100002c59
        b'\xC7\x45\xE8\x00\x00\x00\x00',                # mov     dword [rbp-0x18], 0x0
        b'\x48\x8B\x7D\xF8',                            # mov     rdi, qword [rbp-0x8]
        b'\x48\x83\xC7\x18',                            # add     rdi, 0x18
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x48\x01\xC7',                                # add     rdi, rax
        b'\x48\x8B\x75\xF0',                            # mov     rsi, qword [rbp-0x10]
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x48\x01\xC6',                                # add     rsi, rax
        b'\x8B\x55\xEC',                                # mov     edx, dword [rbp-0x14]
        b'\x2B\x55\xE8',                                # sub     edx, dword [rbp-0x18]
        b'\xE8\xA4\x10\x00\x00',                        # call    0x100003d20
        b'\x48\x83\xC4\x20',                            # add     rsp, 0x20
        b'\x5D',                                        # pop     rbp
        b'\xC3',                                        # retn    
    ],
    'length': 0x112
},
{
    'name': '_MD5Final',
    'description': 'uint64_t _MD5Final(int64_t arg1, int32_t* arg2)',
    'address': 0x100002C90,
    'instructions': [
        b'\x55',                                        # push    rbp
        b'\x48\x89\xE5',                                # mov     rbp, rsp
        b'\x48\x83\xEC\x30',                            # sub     rsp, 0x30
        b'\x48\x89\x7D\xF8',                            # mov     qword [rbp-0x8], rdi
        b'\x48\x89\x75\xF0',                            # mov     qword [rbp-0x10], rsi
        b'\x48\x8D\x7D\xE8',                            # lea     rdi, [rbp-0x18]
        b'\x48\x8B\x75\xF0',                            # mov     rsi, qword [rbp-0x10]
        b'\x48\x83\xC6\x10',                            # add     rsi, 0x10
        b'\xBA\x08\x00\x00\x00',                        # mov     edx, 0x8
        b'\xE8\x9A\x0F\x00\x00',                        # call    0x100003c50
        b'\x48\x8B\x45\xF0',                            # mov     rax, qword [rbp-0x10]
        b'\x8B\x40\x10',                                # mov     eax, dword [rax+0x10]
        b'\xC1\xE8\x03',                                # shr     eax, 0x3
        b'\x83\xE0\x3F',                                # and     eax, 0x3f
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x83\x7D\xE4\x38',                            # cmp     dword [rbp-0x1c], 0x38
        b'\x0F\x83\x10\x00\x00\x00',                    # jae     0x100002ce0
        b'\xB8\x38\x00\x00\x00',                        # mov     eax, 0x38
        b'\x2B\x45\xE4',                                # sub     eax, dword [rbp-0x1c]
        b'\x89\x45\xDC',                                # mov     dword [rbp-0x24], eax
        b'\xE9\x0B\x00\x00\x00',                        # jmp     0x100002ceb
        b'\xB8\x78\x00\x00\x00',                        # mov     eax, 0x78
        b'\x2B\x45\xE4',                                # sub     eax, dword [rbp-0x1c]
        b'\x89\x45\xDC',                                # mov     dword [rbp-0x24], eax
        b'\x8B\x45\xDC',                                # mov     eax, dword [rbp-0x24]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x48\x8B\x7D\xF0',                            # mov     rdi, qword [rbp-0x10]
        b'\x8B\x55\xE0',                                # mov     edx, dword [rbp-0x20]
        b'\x48\x8D\x35\x51\x53\x00\x00',                # lea     rsi, [rel 0x100008050]
        b'\xE8\x6C\xFE\xFF\xFF',                        # call    0x100002b70
        b'\x48\x8B\x7D\xF0',                            # mov     rdi, qword [rbp-0x10]
        b'\x48\x8D\x75\xE8',                            # lea     rsi, [rbp-0x18]
        b'\xBA\x08\x00\x00\x00',                        # mov     edx, 0x8
        b'\xE8\x5A\xFE\xFF\xFF',                        # call    0x100002b70
        b'\x48\x8B\x7D\xF8',                            # mov     rdi, qword [rbp-0x8]
        b'\x48\x8B\x75\xF0',                            # mov     rsi, qword [rbp-0x10]
        b'\xBA\x10\x00\x00\x00',                        # mov     edx, 0x10
        b'\xE8\x28\x0F\x00\x00',                        # call    0x100003c50
        b'\x48\x8B\x7D\xF0',                            # mov     rdi, qword [rbp-0x10]
        b'\x31\xF6',                                    # xor     esi, esi
        b'\xBA\x58\x00\x00\x00',                        # mov     edx, 0x58
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\x36\x10\x00\x00',                        # call    0x100003d70
        b'\x48\x83\xC4\x30',                            # add     rsp, 0x30
        b'\x5D',                                        # pop     rbp
        b'\xC3',                                        # retn    
    ],
    'length': 0xB0
},
{
    'name': '_MD5Transform',
    'description': 'uint64_t _MD5Transform(int32_t* arg1, int64_t arg2)',
    'address': 0x100002D40,
    'instructions': [
        b'\x55',                                        # push    rbp
        b'\x48\x89\xE5',                                # mov     rbp, rsp
        b'\x48\x83\xEC\x60',                            # sub     rsp, 0x60
        b'\x48\x89\x7D\xF8',                            # mov     qword [rbp-0x8], rdi
        b'\x48\x89\x75\xF0',                            # mov     qword [rbp-0x10], rsi
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\x8B\x00',                                    # mov     eax, dword [rax]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\x8B\x40\x04',                                # mov     eax, dword [rax+0x4]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\x8B\x40\x08',                                # mov     eax, dword [rax+0x8]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\x8B\x40\x0C',                                # mov     eax, dword [rax+0xc]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x48\x8D\x7D\xA0',                            # lea     rdi, [rbp-0x60]
        b'\x48\x8B\x75\xF0',                            # mov     rsi, qword [rbp-0x10]
        b'\xBA\x40\x00\x00\x00',                        # mov     edx, 0x40
        b'\xE8\x27\x0E\x00\x00',                        # call    0x100003bb0
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x23\x45\xE4',                                # and     eax, dword [rbp-0x1c]
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\x83\xF1\xFF',                                # xor     ecx, 0xffffffff
        b'\x23\x4D\xE0',                                # and     ecx, dword [rbp-0x20]
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xA0',                                # add     eax, dword [rbp-0x60]
        b'\x05\x78\xA4\x6A\xD7',                        # add     eax, 0xd76aa478
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\xC1\xE0\x07',                                # shl     eax, 0x7
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\xC1\xE9\x19',                                # shr     ecx, 0x19
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x23\x45\xE8',                                # and     eax, dword [rbp-0x18]
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\x83\xF1\xFF',                                # xor     ecx, 0xffffffff
        b'\x23\x4D\xE4',                                # and     ecx, dword [rbp-0x1c]
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xA4',                                # add     eax, dword [rbp-0x5c]
        b'\x05\x56\xB7\xC7\xE8',                        # add     eax, 0xe8c7b756
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\xC1\xE0\x0C',                                # shl     eax, 0xc
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\xC1\xE9\x14',                                # shr     ecx, 0x14
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x23\x45\xEC',                                # and     eax, dword [rbp-0x14]
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\x83\xF1\xFF',                                # xor     ecx, 0xffffffff
        b'\x23\x4D\xE8',                                # and     ecx, dword [rbp-0x18]
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xA8',                                # add     eax, dword [rbp-0x58]
        b'\x05\xDB\x70\x20\x24',                        # add     eax, 0x242070db
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\xC1\xE0\x11',                                # shl     eax, 0x11
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\xC1\xE9\x0F',                                # shr     ecx, 0xf
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x23\x45\xE0',                                # and     eax, dword [rbp-0x20]
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\x83\xF1\xFF',                                # xor     ecx, 0xffffffff
        b'\x23\x4D\xEC',                                # and     ecx, dword [rbp-0x14]
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xAC',                                # add     eax, dword [rbp-0x54]
        b'\x05\xEE\xCE\xBD\xC1',                        # add     eax, 0xc1bdceee
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\xC1\xE0\x16',                                # shl     eax, 0x16
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\xC1\xE9\x0A',                                # shr     ecx, 0xa
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x23\x45\xE4',                                # and     eax, dword [rbp-0x1c]
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\x83\xF1\xFF',                                # xor     ecx, 0xffffffff
        b'\x23\x4D\xE0',                                # and     ecx, dword [rbp-0x20]
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xB0',                                # add     eax, dword [rbp-0x50]
        b'\x05\xAF\x0F\x7C\xF5',                        # add     eax, 0xf57c0faf
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\xC1\xE0\x07',                                # shl     eax, 0x7
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\xC1\xE9\x19',                                # shr     ecx, 0x19
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x23\x45\xE8',                                # and     eax, dword [rbp-0x18]
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\x83\xF1\xFF',                                # xor     ecx, 0xffffffff
        b'\x23\x4D\xE4',                                # and     ecx, dword [rbp-0x1c]
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xB4',                                # add     eax, dword [rbp-0x4c]
        b'\x05\x2A\xC6\x87\x47',                        # add     eax, 0x4787c62a
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\xC1\xE0\x0C',                                # shl     eax, 0xc
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\xC1\xE9\x14',                                # shr     ecx, 0x14
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x23\x45\xEC',                                # and     eax, dword [rbp-0x14]
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\x83\xF1\xFF',                                # xor     ecx, 0xffffffff
        b'\x23\x4D\xE8',                                # and     ecx, dword [rbp-0x18]
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xB8',                                # add     eax, dword [rbp-0x48]
        b'\x05\x13\x46\x30\xA8',                        # add     eax, 0xa8304613
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\xC1\xE0\x11',                                # shl     eax, 0x11
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\xC1\xE9\x0F',                                # shr     ecx, 0xf
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x23\x45\xE0',                                # and     eax, dword [rbp-0x20]
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\x83\xF1\xFF',                                # xor     ecx, 0xffffffff
        b'\x23\x4D\xEC',                                # and     ecx, dword [rbp-0x14]
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xBC',                                # add     eax, dword [rbp-0x44]
        b'\x05\x01\x95\x46\xFD',                        # add     eax, 0xfd469501
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\xC1\xE0\x16',                                # shl     eax, 0x16
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\xC1\xE9\x0A',                                # shr     ecx, 0xa
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x23\x45\xE4',                                # and     eax, dword [rbp-0x1c]
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\x83\xF1\xFF',                                # xor     ecx, 0xffffffff
        b'\x23\x4D\xE0',                                # and     ecx, dword [rbp-0x20]
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xC0',                                # add     eax, dword [rbp-0x40]
        b'\x05\xD8\x98\x80\x69',                        # add     eax, 0x698098d8
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\xC1\xE0\x07',                                # shl     eax, 0x7
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\xC1\xE9\x19',                                # shr     ecx, 0x19
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x23\x45\xE8',                                # and     eax, dword [rbp-0x18]
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\x83\xF1\xFF',                                # xor     ecx, 0xffffffff
        b'\x23\x4D\xE4',                                # and     ecx, dword [rbp-0x1c]
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xC4',                                # add     eax, dword [rbp-0x3c]
        b'\x05\xAF\xF7\x44\x8B',                        # add     eax, 0x8b44f7af
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\xC1\xE0\x0C',                                # shl     eax, 0xc
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\xC1\xE9\x14',                                # shr     ecx, 0x14
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x23\x45\xEC',                                # and     eax, dword [rbp-0x14]
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\x83\xF1\xFF',                                # xor     ecx, 0xffffffff
        b'\x23\x4D\xE8',                                # and     ecx, dword [rbp-0x18]
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xC8',                                # add     eax, dword [rbp-0x38]
        b'\x05\xB1\x5B\xFF\xFF',                        # add     eax, 0xffff5bb1
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\xC1\xE0\x11',                                # shl     eax, 0x11
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\xC1\xE9\x0F',                                # shr     ecx, 0xf
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x23\x45\xE0',                                # and     eax, dword [rbp-0x20]
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\x83\xF1\xFF',                                # xor     ecx, 0xffffffff
        b'\x23\x4D\xEC',                                # and     ecx, dword [rbp-0x14]
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xCC',                                # add     eax, dword [rbp-0x34]
        b'\x05\xBE\xD7\x5C\x89',                        # add     eax, 0x895cd7be
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\xC1\xE0\x16',                                # shl     eax, 0x16
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\xC1\xE9\x0A',                                # shr     ecx, 0xa
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x23\x45\xE4',                                # and     eax, dword [rbp-0x1c]
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\x83\xF1\xFF',                                # xor     ecx, 0xffffffff
        b'\x23\x4D\xE0',                                # and     ecx, dword [rbp-0x20]
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xD0',                                # add     eax, dword [rbp-0x30]
        b'\x05\x22\x11\x90\x6B',                        # add     eax, 0x6b901122
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\xC1\xE0\x07',                                # shl     eax, 0x7
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\xC1\xE9\x19',                                # shr     ecx, 0x19
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x23\x45\xE8',                                # and     eax, dword [rbp-0x18]
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\x83\xF1\xFF',                                # xor     ecx, 0xffffffff
        b'\x23\x4D\xE4',                                # and     ecx, dword [rbp-0x1c]
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xD4',                                # add     eax, dword [rbp-0x2c]
        b'\x05\x93\x71\x98\xFD',                        # add     eax, 0xfd987193
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\xC1\xE0\x0C',                                # shl     eax, 0xc
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\xC1\xE9\x14',                                # shr     ecx, 0x14
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x23\x45\xEC',                                # and     eax, dword [rbp-0x14]
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\x83\xF1\xFF',                                # xor     ecx, 0xffffffff
        b'\x23\x4D\xE8',                                # and     ecx, dword [rbp-0x18]
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xD8',                                # add     eax, dword [rbp-0x28]
        b'\x05\x8E\x43\x79\xA6',                        # add     eax, 0xa679438e
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\xC1\xE0\x11',                                # shl     eax, 0x11
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\xC1\xE9\x0F',                                # shr     ecx, 0xf
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x23\x45\xE0',                                # and     eax, dword [rbp-0x20]
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\x83\xF1\xFF',                                # xor     ecx, 0xffffffff
        b'\x23\x4D\xEC',                                # and     ecx, dword [rbp-0x14]
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xDC',                                # add     eax, dword [rbp-0x24]
        b'\x05\x21\x08\xB4\x49',                        # add     eax, 0x49b40821
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\xC1\xE0\x16',                                # shl     eax, 0x16
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\xC1\xE9\x0A',                                # shr     ecx, 0xa
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x23\x45\xE0',                                # and     eax, dword [rbp-0x20]
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\x8B\x55\xE0',                                # mov     edx, dword [rbp-0x20]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x21\xD1',                                    # and     ecx, edx
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xA4',                                # add     eax, dword [rbp-0x5c]
        b'\x05\x62\x25\x1E\xF6',                        # add     eax, 0xf61e2562
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\xC1\xE0\x05',                                # shl     eax, 0x5
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\xC1\xE9\x1B',                                # shr     ecx, 0x1b
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x23\x45\xE4',                                # and     eax, dword [rbp-0x1c]
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\x8B\x55\xE4',                                # mov     edx, dword [rbp-0x1c]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x21\xD1',                                    # and     ecx, edx
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xB8',                                # add     eax, dword [rbp-0x48]
        b'\x05\x40\xB3\x40\xC0',                        # add     eax, 0xc040b340
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\xC1\xE0\x09',                                # shl     eax, 0x9
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\xC1\xE9\x17',                                # shr     ecx, 0x17
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x23\x45\xE8',                                # and     eax, dword [rbp-0x18]
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\x8B\x55\xE8',                                # mov     edx, dword [rbp-0x18]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x21\xD1',                                    # and     ecx, edx
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xCC',                                # add     eax, dword [rbp-0x34]
        b'\x05\x51\x5A\x5E\x26',                        # add     eax, 0x265e5a51
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\xC1\xE0\x0E',                                # shl     eax, 0xe
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\xC1\xE9\x12',                                # shr     ecx, 0x12
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x23\x45\xEC',                                # and     eax, dword [rbp-0x14]
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\x8B\x55\xEC',                                # mov     edx, dword [rbp-0x14]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x21\xD1',                                    # and     ecx, edx
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xA0',                                # add     eax, dword [rbp-0x60]
        b'\x05\xAA\xC7\xB6\xE9',                        # add     eax, 0xe9b6c7aa
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\xC1\xE0\x14',                                # shl     eax, 0x14
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\xC1\xE9\x0C',                                # shr     ecx, 0xc
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x23\x45\xE0',                                # and     eax, dword [rbp-0x20]
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\x8B\x55\xE0',                                # mov     edx, dword [rbp-0x20]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x21\xD1',                                    # and     ecx, edx
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xB4',                                # add     eax, dword [rbp-0x4c]
        b'\x05\x5D\x10\x2F\xD6',                        # add     eax, 0xd62f105d
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\xC1\xE0\x05',                                # shl     eax, 0x5
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\xC1\xE9\x1B',                                # shr     ecx, 0x1b
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x23\x45\xE4',                                # and     eax, dword [rbp-0x1c]
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\x8B\x55\xE4',                                # mov     edx, dword [rbp-0x1c]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x21\xD1',                                    # and     ecx, edx
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xC8',                                # add     eax, dword [rbp-0x38]
        b'\x05\x53\x14\x44\x02',                        # add     eax, 0x2441453
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\xC1\xE0\x09',                                # shl     eax, 0x9
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\xC1\xE9\x17',                                # shr     ecx, 0x17
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x23\x45\xE8',                                # and     eax, dword [rbp-0x18]
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\x8B\x55\xE8',                                # mov     edx, dword [rbp-0x18]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x21\xD1',                                    # and     ecx, edx
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xDC',                                # add     eax, dword [rbp-0x24]
        b'\x05\x81\xE6\xA1\xD8',                        # add     eax, 0xd8a1e681
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\xC1\xE0\x0E',                                # shl     eax, 0xe
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\xC1\xE9\x12',                                # shr     ecx, 0x12
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x23\x45\xEC',                                # and     eax, dword [rbp-0x14]
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\x8B\x55\xEC',                                # mov     edx, dword [rbp-0x14]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x21\xD1',                                    # and     ecx, edx
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xB0',                                # add     eax, dword [rbp-0x50]
        b'\x05\xC8\xFB\xD3\xE7',                        # add     eax, 0xe7d3fbc8
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\xC1\xE0\x14',                                # shl     eax, 0x14
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\xC1\xE9\x0C',                                # shr     ecx, 0xc
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x23\x45\xE0',                                # and     eax, dword [rbp-0x20]
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\x8B\x55\xE0',                                # mov     edx, dword [rbp-0x20]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x21\xD1',                                    # and     ecx, edx
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xC4',                                # add     eax, dword [rbp-0x3c]
        b'\x05\xE6\xCD\xE1\x21',                        # add     eax, 0x21e1cde6
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\xC1\xE0\x05',                                # shl     eax, 0x5
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\xC1\xE9\x1B',                                # shr     ecx, 0x1b
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x23\x45\xE4',                                # and     eax, dword [rbp-0x1c]
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\x8B\x55\xE4',                                # mov     edx, dword [rbp-0x1c]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x21\xD1',                                    # and     ecx, edx
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xD8',                                # add     eax, dword [rbp-0x28]
        b'\x05\xD6\x07\x37\xC3',                        # add     eax, 0xc33707d6
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\xC1\xE0\x09',                                # shl     eax, 0x9
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\xC1\xE9\x17',                                # shr     ecx, 0x17
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x23\x45\xE8',                                # and     eax, dword [rbp-0x18]
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\x8B\x55\xE8',                                # mov     edx, dword [rbp-0x18]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x21\xD1',                                    # and     ecx, edx
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xAC',                                # add     eax, dword [rbp-0x54]
        b'\x05\x87\x0D\xD5\xF4',                        # add     eax, 0xf4d50d87
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\xC1\xE0\x0E',                                # shl     eax, 0xe
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\xC1\xE9\x12',                                # shr     ecx, 0x12
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x23\x45\xEC',                                # and     eax, dword [rbp-0x14]
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\x8B\x55\xEC',                                # mov     edx, dword [rbp-0x14]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x21\xD1',                                    # and     ecx, edx
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xC0',                                # add     eax, dword [rbp-0x40]
        b'\x05\xED\x14\x5A\x45',                        # add     eax, 0x455a14ed
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\xC1\xE0\x14',                                # shl     eax, 0x14
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\xC1\xE9\x0C',                                # shr     ecx, 0xc
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x23\x45\xE0',                                # and     eax, dword [rbp-0x20]
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\x8B\x55\xE0',                                # mov     edx, dword [rbp-0x20]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x21\xD1',                                    # and     ecx, edx
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xD4',                                # add     eax, dword [rbp-0x2c]
        b'\x05\x05\xE9\xE3\xA9',                        # add     eax, 0xa9e3e905
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\xC1\xE0\x05',                                # shl     eax, 0x5
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\xC1\xE9\x1B',                                # shr     ecx, 0x1b
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x23\x45\xE4',                                # and     eax, dword [rbp-0x1c]
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\x8B\x55\xE4',                                # mov     edx, dword [rbp-0x1c]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x21\xD1',                                    # and     ecx, edx
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xA8',                                # add     eax, dword [rbp-0x58]
        b'\x05\xF8\xA3\xEF\xFC',                        # add     eax, 0xfcefa3f8
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\xC1\xE0\x09',                                # shl     eax, 0x9
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\xC1\xE9\x17',                                # shr     ecx, 0x17
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x23\x45\xE8',                                # and     eax, dword [rbp-0x18]
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\x8B\x55\xE8',                                # mov     edx, dword [rbp-0x18]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x21\xD1',                                    # and     ecx, edx
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xBC',                                # add     eax, dword [rbp-0x44]
        b'\x05\xD9\x02\x6F\x67',                        # add     eax, 0x676f02d9
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\xC1\xE0\x0E',                                # shl     eax, 0xe
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\xC1\xE9\x12',                                # shr     ecx, 0x12
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x23\x45\xEC',                                # and     eax, dword [rbp-0x14]
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\x8B\x55\xEC',                                # mov     edx, dword [rbp-0x14]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x21\xD1',                                    # and     ecx, edx
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x03\x45\xD0',                                # add     eax, dword [rbp-0x30]
        b'\x05\x8A\x4C\x2A\x8D',                        # add     eax, 0x8d2a4c8a
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\xC1\xE0\x14',                                # shl     eax, 0x14
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\xC1\xE9\x0C',                                # shr     ecx, 0xc
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x33\x45\xE4',                                # xor     eax, dword [rbp-0x1c]
        b'\x33\x45\xE0',                                # xor     eax, dword [rbp-0x20]
        b'\x03\x45\xB4',                                # add     eax, dword [rbp-0x4c]
        b'\x05\x42\x39\xFA\xFF',                        # add     eax, 0xfffa3942
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\xC1\xE0\x04',                                # shl     eax, 0x4
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\xC1\xE9\x1C',                                # shr     ecx, 0x1c
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x33\x45\xE8',                                # xor     eax, dword [rbp-0x18]
        b'\x33\x45\xE4',                                # xor     eax, dword [rbp-0x1c]
        b'\x03\x45\xC0',                                # add     eax, dword [rbp-0x40]
        b'\x05\x81\xF6\x71\x87',                        # add     eax, 0x8771f681
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\xC1\xE0\x0B',                                # shl     eax, 0xb
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\xC1\xE9\x15',                                # shr     ecx, 0x15
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x33\x45\xEC',                                # xor     eax, dword [rbp-0x14]
        b'\x33\x45\xE8',                                # xor     eax, dword [rbp-0x18]
        b'\x03\x45\xCC',                                # add     eax, dword [rbp-0x34]
        b'\x05\x22\x61\x9D\x6D',                        # add     eax, 0x6d9d6122
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\xC1\xE0\x10',                                # shl     eax, 0x10
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\xC1\xE9\x10',                                # shr     ecx, 0x10
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x33\x45\xE0',                                # xor     eax, dword [rbp-0x20]
        b'\x33\x45\xEC',                                # xor     eax, dword [rbp-0x14]
        b'\x03\x45\xD8',                                # add     eax, dword [rbp-0x28]
        b'\x05\x0C\x38\xE5\xFD',                        # add     eax, 0xfde5380c
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\xC1\xE0\x17',                                # shl     eax, 0x17
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\xC1\xE9\x09',                                # shr     ecx, 0x9
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x33\x45\xE4',                                # xor     eax, dword [rbp-0x1c]
        b'\x33\x45\xE0',                                # xor     eax, dword [rbp-0x20]
        b'\x03\x45\xA4',                                # add     eax, dword [rbp-0x5c]
        b'\x05\x44\xEA\xBE\xA4',                        # add     eax, 0xa4beea44
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\xC1\xE0\x04',                                # shl     eax, 0x4
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\xC1\xE9\x1C',                                # shr     ecx, 0x1c
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x33\x45\xE8',                                # xor     eax, dword [rbp-0x18]
        b'\x33\x45\xE4',                                # xor     eax, dword [rbp-0x1c]
        b'\x03\x45\xB0',                                # add     eax, dword [rbp-0x50]
        b'\x05\xA9\xCF\xDE\x4B',                        # add     eax, 0x4bdecfa9
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\xC1\xE0\x0B',                                # shl     eax, 0xb
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\xC1\xE9\x15',                                # shr     ecx, 0x15
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x33\x45\xEC',                                # xor     eax, dword [rbp-0x14]
        b'\x33\x45\xE8',                                # xor     eax, dword [rbp-0x18]
        b'\x03\x45\xBC',                                # add     eax, dword [rbp-0x44]
        b'\x05\x60\x4B\xBB\xF6',                        # add     eax, 0xf6bb4b60
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\xC1\xE0\x10',                                # shl     eax, 0x10
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\xC1\xE9\x10',                                # shr     ecx, 0x10
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x33\x45\xE0',                                # xor     eax, dword [rbp-0x20]
        b'\x33\x45\xEC',                                # xor     eax, dword [rbp-0x14]
        b'\x03\x45\xC8',                                # add     eax, dword [rbp-0x38]
        b'\x05\x70\xBC\xBF\xBE',                        # add     eax, 0xbebfbc70
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\xC1\xE0\x17',                                # shl     eax, 0x17
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\xC1\xE9\x09',                                # shr     ecx, 0x9
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x33\x45\xE4',                                # xor     eax, dword [rbp-0x1c]
        b'\x33\x45\xE0',                                # xor     eax, dword [rbp-0x20]
        b'\x03\x45\xD4',                                # add     eax, dword [rbp-0x2c]
        b'\x05\xC6\x7E\x9B\x28',                        # add     eax, 0x289b7ec6
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\xC1\xE0\x04',                                # shl     eax, 0x4
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\xC1\xE9\x1C',                                # shr     ecx, 0x1c
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x33\x45\xE8',                                # xor     eax, dword [rbp-0x18]
        b'\x33\x45\xE4',                                # xor     eax, dword [rbp-0x1c]
        b'\x03\x45\xA0',                                # add     eax, dword [rbp-0x60]
        b'\x05\xFA\x27\xA1\xEA',                        # add     eax, 0xeaa127fa
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\xC1\xE0\x0B',                                # shl     eax, 0xb
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\xC1\xE9\x15',                                # shr     ecx, 0x15
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x33\x45\xEC',                                # xor     eax, dword [rbp-0x14]
        b'\x33\x45\xE8',                                # xor     eax, dword [rbp-0x18]
        b'\x03\x45\xAC',                                # add     eax, dword [rbp-0x54]
        b'\x05\x85\x30\xEF\xD4',                        # add     eax, 0xd4ef3085
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\xC1\xE0\x10',                                # shl     eax, 0x10
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\xC1\xE9\x10',                                # shr     ecx, 0x10
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x33\x45\xE0',                                # xor     eax, dword [rbp-0x20]
        b'\x33\x45\xEC',                                # xor     eax, dword [rbp-0x14]
        b'\x03\x45\xB8',                                # add     eax, dword [rbp-0x48]
        b'\x05\x05\x1D\x88\x04',                        # add     eax, 0x4881d05
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\xC1\xE0\x17',                                # shl     eax, 0x17
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\xC1\xE9\x09',                                # shr     ecx, 0x9
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x33\x45\xE4',                                # xor     eax, dword [rbp-0x1c]
        b'\x33\x45\xE0',                                # xor     eax, dword [rbp-0x20]
        b'\x03\x45\xC4',                                # add     eax, dword [rbp-0x3c]
        b'\x05\x39\xD0\xD4\xD9',                        # add     eax, 0xd9d4d039
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\xC1\xE0\x04',                                # shl     eax, 0x4
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\xC1\xE9\x1C',                                # shr     ecx, 0x1c
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x33\x45\xE8',                                # xor     eax, dword [rbp-0x18]
        b'\x33\x45\xE4',                                # xor     eax, dword [rbp-0x1c]
        b'\x03\x45\xD0',                                # add     eax, dword [rbp-0x30]
        b'\x05\xE5\x99\xDB\xE6',                        # add     eax, 0xe6db99e5
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\xC1\xE0\x0B',                                # shl     eax, 0xb
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\xC1\xE9\x15',                                # shr     ecx, 0x15
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x33\x45\xEC',                                # xor     eax, dword [rbp-0x14]
        b'\x33\x45\xE8',                                # xor     eax, dword [rbp-0x18]
        b'\x03\x45\xDC',                                # add     eax, dword [rbp-0x24]
        b'\x05\xF8\x7C\xA2\x1F',                        # add     eax, 0x1fa27cf8
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\xC1\xE0\x10',                                # shl     eax, 0x10
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\xC1\xE9\x10',                                # shr     ecx, 0x10
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x33\x45\xE0',                                # xor     eax, dword [rbp-0x20]
        b'\x33\x45\xEC',                                # xor     eax, dword [rbp-0x14]
        b'\x03\x45\xA8',                                # add     eax, dword [rbp-0x58]
        b'\x05\x65\x56\xAC\xC4',                        # add     eax, 0xc4ac5665
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\xC1\xE0\x17',                                # shl     eax, 0x17
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\xC1\xE9\x09',                                # shr     ecx, 0x9
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\x8B\x55\xE0',                                # mov     edx, dword [rbp-0x20]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x09\xD1',                                    # or      ecx, edx
        b'\x31\xC8',                                    # xor     eax, ecx
        b'\x03\x45\xA0',                                # add     eax, dword [rbp-0x60]
        b'\x05\x44\x22\x29\xF4',                        # add     eax, 0xf4292244
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\xC1\xE0\x06',                                # shl     eax, 0x6
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\xC1\xE9\x1A',                                # shr     ecx, 0x1a
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\x8B\x55\xE4',                                # mov     edx, dword [rbp-0x1c]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x09\xD1',                                    # or      ecx, edx
        b'\x31\xC8',                                    # xor     eax, ecx
        b'\x03\x45\xBC',                                # add     eax, dword [rbp-0x44]
        b'\x05\x97\xFF\x2A\x43',                        # add     eax, 0x432aff97
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\xC1\xE0\x0A',                                # shl     eax, 0xa
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\xC1\xE9\x16',                                # shr     ecx, 0x16
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\x8B\x55\xE8',                                # mov     edx, dword [rbp-0x18]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x09\xD1',                                    # or      ecx, edx
        b'\x31\xC8',                                    # xor     eax, ecx
        b'\x03\x45\xD8',                                # add     eax, dword [rbp-0x28]
        b'\x05\xA7\x23\x94\xAB',                        # add     eax, 0xab9423a7
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\xC1\xE0\x0F',                                # shl     eax, 0xf
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\xC1\xE9\x11',                                # shr     ecx, 0x11
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\x8B\x55\xEC',                                # mov     edx, dword [rbp-0x14]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x09\xD1',                                    # or      ecx, edx
        b'\x31\xC8',                                    # xor     eax, ecx
        b'\x03\x45\xB4',                                # add     eax, dword [rbp-0x4c]
        b'\x05\x39\xA0\x93\xFC',                        # add     eax, 0xfc93a039
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\xC1\xE0\x15',                                # shl     eax, 0x15
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\xC1\xE9\x0B',                                # shr     ecx, 0xb
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\x8B\x55\xE0',                                # mov     edx, dword [rbp-0x20]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x09\xD1',                                    # or      ecx, edx
        b'\x31\xC8',                                    # xor     eax, ecx
        b'\x03\x45\xD0',                                # add     eax, dword [rbp-0x30]
        b'\x05\xC3\x59\x5B\x65',                        # add     eax, 0x655b59c3
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\xC1\xE0\x06',                                # shl     eax, 0x6
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\xC1\xE9\x1A',                                # shr     ecx, 0x1a
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\x8B\x55\xE4',                                # mov     edx, dword [rbp-0x1c]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x09\xD1',                                    # or      ecx, edx
        b'\x31\xC8',                                    # xor     eax, ecx
        b'\x03\x45\xAC',                                # add     eax, dword [rbp-0x54]
        b'\x05\x92\xCC\x0C\x8F',                        # add     eax, 0x8f0ccc92
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\xC1\xE0\x0A',                                # shl     eax, 0xa
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\xC1\xE9\x16',                                # shr     ecx, 0x16
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\x8B\x55\xE8',                                # mov     edx, dword [rbp-0x18]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x09\xD1',                                    # or      ecx, edx
        b'\x31\xC8',                                    # xor     eax, ecx
        b'\x03\x45\xC8',                                # add     eax, dword [rbp-0x38]
        b'\x05\x7D\xF4\xEF\xFF',                        # add     eax, 0xffeff47d
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\xC1\xE0\x0F',                                # shl     eax, 0xf
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\xC1\xE9\x11',                                # shr     ecx, 0x11
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\x8B\x55\xEC',                                # mov     edx, dword [rbp-0x14]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x09\xD1',                                    # or      ecx, edx
        b'\x31\xC8',                                    # xor     eax, ecx
        b'\x03\x45\xA4',                                # add     eax, dword [rbp-0x5c]
        b'\x05\xD1\x5D\x84\x85',                        # add     eax, 0x85845dd1
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\xC1\xE0\x15',                                # shl     eax, 0x15
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\xC1\xE9\x0B',                                # shr     ecx, 0xb
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\x8B\x55\xE0',                                # mov     edx, dword [rbp-0x20]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x09\xD1',                                    # or      ecx, edx
        b'\x31\xC8',                                    # xor     eax, ecx
        b'\x03\x45\xC0',                                # add     eax, dword [rbp-0x40]
        b'\x05\x4F\x7E\xA8\x6F',                        # add     eax, 0x6fa87e4f
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\xC1\xE0\x06',                                # shl     eax, 0x6
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\xC1\xE9\x1A',                                # shr     ecx, 0x1a
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\x8B\x55\xE4',                                # mov     edx, dword [rbp-0x1c]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x09\xD1',                                    # or      ecx, edx
        b'\x31\xC8',                                    # xor     eax, ecx
        b'\x03\x45\xDC',                                # add     eax, dword [rbp-0x24]
        b'\x05\xE0\xE6\x2C\xFE',                        # add     eax, 0xfe2ce6e0
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\xC1\xE0\x0A',                                # shl     eax, 0xa
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\xC1\xE9\x16',                                # shr     ecx, 0x16
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\x8B\x55\xE8',                                # mov     edx, dword [rbp-0x18]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x09\xD1',                                    # or      ecx, edx
        b'\x31\xC8',                                    # xor     eax, ecx
        b'\x03\x45\xB8',                                # add     eax, dword [rbp-0x48]
        b'\x05\x14\x43\x01\xA3',                        # add     eax, 0xa3014314
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\xC1\xE0\x0F',                                # shl     eax, 0xf
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\xC1\xE9\x11',                                # shr     ecx, 0x11
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\x8B\x55\xEC',                                # mov     edx, dword [rbp-0x14]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x09\xD1',                                    # or      ecx, edx
        b'\x31\xC8',                                    # xor     eax, ecx
        b'\x03\x45\xD4',                                # add     eax, dword [rbp-0x2c]
        b'\x05\xA1\x11\x08\x4E',                        # add     eax, 0x4e0811a1
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\xC1\xE0\x15',                                # shl     eax, 0x15
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\xC1\xE9\x0B',                                # shr     ecx, 0xb
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\x8B\x55\xE0',                                # mov     edx, dword [rbp-0x20]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x09\xD1',                                    # or      ecx, edx
        b'\x31\xC8',                                    # xor     eax, ecx
        b'\x03\x45\xB0',                                # add     eax, dword [rbp-0x50]
        b'\x05\x82\x7E\x53\xF7',                        # add     eax, 0xf7537e82
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\xC1\xE0\x06',                                # shl     eax, 0x6
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\xC1\xE9\x1A',                                # shr     ecx, 0x1a
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x03\x45\xEC',                                # add     eax, dword [rbp-0x14]
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\x8B\x55\xE4',                                # mov     edx, dword [rbp-0x1c]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x09\xD1',                                    # or      ecx, edx
        b'\x31\xC8',                                    # xor     eax, ecx
        b'\x03\x45\xCC',                                # add     eax, dword [rbp-0x34]
        b'\x05\x35\xF2\x3A\xBD',                        # add     eax, 0xbd3af235
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\xC1\xE0\x0A',                                # shl     eax, 0xa
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\xC1\xE9\x16',                                # shr     ecx, 0x16
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x03\x45\xE0',                                # add     eax, dword [rbp-0x20]
        b'\x89\x45\xE0',                                # mov     dword [rbp-0x20], eax
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\x8B\x55\xE8',                                # mov     edx, dword [rbp-0x18]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x09\xD1',                                    # or      ecx, edx
        b'\x31\xC8',                                    # xor     eax, ecx
        b'\x03\x45\xA8',                                # add     eax, dword [rbp-0x58]
        b'\x05\xBB\xD2\xD7\x2A',                        # add     eax, 0x2ad7d2bb
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\xC1\xE0\x0F',                                # shl     eax, 0xf
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\xC1\xE9\x11',                                # shr     ecx, 0x11
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x03\x45\xE4',                                # add     eax, dword [rbp-0x1c]
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\x8B\x45\xE0',                                # mov     eax, dword [rbp-0x20]
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\x8B\x55\xEC',                                # mov     edx, dword [rbp-0x14]
        b'\x83\xF2\xFF',                                # xor     edx, 0xffffffff
        b'\x09\xD1',                                    # or      ecx, edx
        b'\x31\xC8',                                    # xor     eax, ecx
        b'\x03\x45\xC4',                                # add     eax, dword [rbp-0x3c]
        b'\x05\x91\xD3\x86\xEB',                        # add     eax, 0xeb86d391
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\xC1\xE0\x15',                                # shl     eax, 0x15
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\xC1\xE9\x0B',                                # shr     ecx, 0xb
        b'\x09\xC8',                                    # or      eax, ecx
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x03\x45\xE8',                                # add     eax, dword [rbp-0x18]
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\x03\x08',                                    # add     ecx, dword [rax]
        b'\x89\x08',                                    # mov     dword [rax], ecx
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\x03\x48\x04',                                # add     ecx, dword [rax+0x4]
        b'\x89\x48\x04',                                # mov     dword [rax+0x4], ecx
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\x03\x48\x08',                                # add     ecx, dword [rax+0x8]
        b'\x89\x48\x08',                                # mov     dword [rax+0x8], ecx
        b'\x8B\x4D\xE0',                                # mov     ecx, dword [rbp-0x20]
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\x03\x48\x0C',                                # add     ecx, dword [rax+0xc]
        b'\x89\x48\x0C',                                # mov     dword [rax+0xc], ecx
        b'\x48\x8D\x7D\xA0',                            # lea     rdi, [rbp-0x60]
        b'\x31\xF6',                                    # xor     esi, esi
        b'\xBA\x40\x00\x00\x00',                        # mov     edx, 0x40
        b'\xB0\x00',                                    # mov     al, 0x0
        b'\xE8\xD3\x01\x00\x00',                        # call    0x100003d70
        b'\x48\x83\xC4\x60',                            # add     rsp, 0x60
        b'\x5D',                                        # pop     rbp
        b'\xC3',                                        # retn    
    ],
    'length': 0xE63
},
{
    'name': '_Decode',
    'description': 'uint64_t _Decode(int64_t arg1, int64_t arg2, int32_t arg3)',
    'address': 0x100003BB0,
    'instructions': [
        b'\x55',                                        # push    rbp
        b'\x48\x89\xE5',                                # mov     rbp, rsp
        b'\x48\x89\x7D\xF8',                            # mov     qword [rbp-0x8], rdi
        b'\x48\x89\x75\xF0',                            # mov     qword [rbp-0x10], rsi
        b'\x89\x55\xEC',                                # mov     dword [rbp-0x14], edx
        b'\xC7\x45\xE8\x00\x00\x00\x00',                # mov     dword [rbp-0x18], 0x0
        b'\xC7\x45\xE4\x00\x00\x00\x00',                # mov     dword [rbp-0x1c], 0x0
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x3B\x45\xEC',                                # cmp     eax, dword [rbp-0x14]
        b'\x0F\x83\x6B\x00\x00\x00',                    # jae     0x100003c44
        b'\x48\x8B\x45\xF0',                            # mov     rax, qword [rbp-0x10]
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\x0F\xB6\x14\x08',                            # movzx   edx, byte [rax+rcx]
        b'\x48\x8B\x45\xF0',                            # mov     rax, qword [rbp-0x10]
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\x83\xC1\x01',                                # add     ecx, 0x1
        b'\x89\xC9',                                    # mov     ecx, ecx
        b'\x0F\xB6\x04\x08',                            # movzx   eax, byte [rax+rcx]
        b'\xC1\xE0\x08',                                # shl     eax, 0x8
        b'\x09\xC2',                                    # or      edx, eax
        b'\x48\x8B\x45\xF0',                            # mov     rax, qword [rbp-0x10]
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\x83\xC1\x02',                                # add     ecx, 0x2
        b'\x89\xC9',                                    # mov     ecx, ecx
        b'\x0F\xB6\x04\x08',                            # movzx   eax, byte [rax+rcx]
        b'\xC1\xE0\x10',                                # shl     eax, 0x10
        b'\x09\xC2',                                    # or      edx, eax
        b'\x48\x8B\x45\xF0',                            # mov     rax, qword [rbp-0x10]
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\x83\xC1\x03',                                # add     ecx, 0x3
        b'\x89\xC9',                                    # mov     ecx, ecx
        b'\x0F\xB6\x04\x08',                            # movzx   eax, byte [rax+rcx]
        b'\xC1\xE0\x18',                                # shl     eax, 0x18
        b'\x09\xC2',                                    # or      edx, eax
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\x89\x14\x88',                                # mov     dword [rax+rcx*4], edx
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x83\xC0\x01',                                # add     eax, 0x1
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x83\xC0\x04',                                # add     eax, 0x4
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\xE9\x89\xFF\xFF\xFF',                        # jmp     0x100003bcd
        b'\x5D',                                        # pop     rbp
        b'\xC3',                                        # retn    
    ],
    'length': 0x96
},
{
    'name': '_Encode',
    'description': 'uint64_t _Encode(int64_t arg1, int64_t arg2, int32_t arg3)',
    'address': 0x100003C50,
    'instructions': [
        b'\x55',                                        # push    rbp
        b'\x48\x89\xE5',                                # mov     rbp, rsp
        b'\x48\x89\x7D\xF8',                            # mov     qword [rbp-0x8], rdi
        b'\x48\x89\x75\xF0',                            # mov     qword [rbp-0x10], rsi
        b'\x89\x55\xEC',                                # mov     dword [rbp-0x14], edx
        b'\xC7\x45\xE8\x00\x00\x00\x00',                # mov     dword [rbp-0x18], 0x0
        b'\xC7\x45\xE4\x00\x00\x00\x00',                # mov     dword [rbp-0x1c], 0x0
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x3B\x45\xEC',                                # cmp     eax, dword [rbp-0x14]
        b'\x0F\x83\x9B\x00\x00\x00',                    # jae     0x100003d14
        b'\x48\x8B\x45\xF0',                            # mov     rax, qword [rbp-0x10]
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\x8B\x04\x88',                                # mov     eax, dword [rax+rcx*4]
        b'\x25\xFF\x00\x00\x00',                        # and     eax, 0xff
        b'\x88\xC2',                                    # mov     dl, al
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\x88\x14\x08',                                # mov     byte [rax+rcx], dl
        b'\x48\x8B\x45\xF0',                            # mov     rax, qword [rbp-0x10]
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\x8B\x04\x88',                                # mov     eax, dword [rax+rcx*4]
        b'\xC1\xE8\x08',                                # shr     eax, 0x8
        b'\x25\xFF\x00\x00\x00',                        # and     eax, 0xff
        b'\x88\xC2',                                    # mov     dl, al
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\x83\xC1\x01',                                # add     ecx, 0x1
        b'\x89\xC9',                                    # mov     ecx, ecx
        b'\x88\x14\x08',                                # mov     byte [rax+rcx], dl
        b'\x48\x8B\x45\xF0',                            # mov     rax, qword [rbp-0x10]
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\x8B\x04\x88',                                # mov     eax, dword [rax+rcx*4]
        b'\xC1\xE8\x10',                                # shr     eax, 0x10
        b'\x25\xFF\x00\x00\x00',                        # and     eax, 0xff
        b'\x88\xC2',                                    # mov     dl, al
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\x83\xC1\x02',                                # add     ecx, 0x2
        b'\x89\xC9',                                    # mov     ecx, ecx
        b'\x88\x14\x08',                                # mov     byte [rax+rcx], dl
        b'\x48\x8B\x45\xF0',                            # mov     rax, qword [rbp-0x10]
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\x8B\x04\x88',                                # mov     eax, dword [rax+rcx*4]
        b'\xC1\xE8\x18',                                # shr     eax, 0x18
        b'\x25\xFF\x00\x00\x00',                        # and     eax, 0xff
        b'\x88\xC2',                                    # mov     dl, al
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\x8B\x4D\xE4',                                # mov     ecx, dword [rbp-0x1c]
        b'\x83\xC1\x03',                                # add     ecx, 0x3
        b'\x89\xC9',                                    # mov     ecx, ecx
        b'\x88\x14\x08',                                # mov     byte [rax+rcx], dl
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x83\xC0\x01',                                # add     eax, 0x1
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\x8B\x45\xE4',                                # mov     eax, dword [rbp-0x1c]
        b'\x83\xC0\x04',                                # add     eax, 0x4
        b'\x89\x45\xE4',                                # mov     dword [rbp-0x1c], eax
        b'\xE9\x59\xFF\xFF\xFF',                        # jmp     0x100003c6d
        b'\x5D',                                        # pop     rbp
        b'\xC3',                                        # retn    
    ],
    'length': 0xC6
},
{
    'name': '_MD5_memcpy',
    'description': 'uint64_t _MD5_memcpy(int64_t arg1, int64_t arg2, int32_t arg3)',
    'address': 0x100003D20,
    'instructions': [
        b'\x55',                                        # push    rbp
        b'\x48\x89\xE5',                                # mov     rbp, rsp
        b'\x48\x89\x7D\xF8',                            # mov     qword [rbp-0x8], rdi
        b'\x48\x89\x75\xF0',                            # mov     qword [rbp-0x10], rsi
        b'\x89\x55\xEC',                                # mov     dword [rbp-0x14], edx
        b'\xC7\x45\xE8\x00\x00\x00\x00',                # mov     dword [rbp-0x18], 0x0
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x3B\x45\xEC',                                # cmp     eax, dword [rbp-0x14]
        b'\x0F\x83\x22\x00\x00\x00',                    # jae     0x100003d64
        b'\x48\x8B\x45\xF0',                            # mov     rax, qword [rbp-0x10]
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\x8A\x14\x08',                                # mov     dl, byte [rax+rcx]
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\x8B\x4D\xE8',                                # mov     ecx, dword [rbp-0x18]
        b'\x88\x14\x08',                                # mov     byte [rax+rcx], dl
        b'\x8B\x45\xE8',                                # mov     eax, dword [rbp-0x18]
        b'\x83\xC0\x01',                                # add     eax, 0x1
        b'\x89\x45\xE8',                                # mov     dword [rbp-0x18], eax
        b'\xE9\xD2\xFF\xFF\xFF',                        # jmp     0x100003d36
        b'\x5D',                                        # pop     rbp
        b'\xC3',                                        # retn    
    ],
    'length': 0x46
},
{
    'name': '_MD5_memset',
    'description': 'uint64_t _MD5_memset(int64_t arg1, char arg2, int32_t arg3)',
    'address': 0x100003D70,
    'instructions': [
        b'\x55',                                        # push    rbp
        b'\x48\x89\xE5',                                # mov     rbp, rsp
        b'\x48\x89\x7D\xF8',                            # mov     qword [rbp-0x8], rdi
        b'\x89\x75\xF4',                                # mov     dword [rbp-0xc], esi
        b'\x89\x55\xF0',                                # mov     dword [rbp-0x10], edx
        b'\xC7\x45\xEC\x00\x00\x00\x00',                # mov     dword [rbp-0x14], 0x0
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x3B\x45\xF0',                                # cmp     eax, dword [rbp-0x10]
        b'\x0F\x83\x1D\x00\x00\x00',                    # jae     0x100003dae
        b'\x8B\x45\xF4',                                # mov     eax, dword [rbp-0xc]
        b'\x88\xC2',                                    # mov     dl, al
        b'\x48\x8B\x45\xF8',                            # mov     rax, qword [rbp-0x8]
        b'\x8B\x4D\xEC',                                # mov     ecx, dword [rbp-0x14]
        b'\x88\x14\x08',                                # mov     byte [rax+rcx], dl
        b'\x8B\x45\xEC',                                # mov     eax, dword [rbp-0x14]
        b'\x83\xC0\x01',                                # add     eax, 0x1
        b'\x89\x45\xEC',                                # mov     dword [rbp-0x14], eax
        b'\xE9\xD7\xFF\xFF\xFF',                        # jmp     0x100003d85
        b'\x5D',                                        # pop     rbp
        b'\xC3',                                        # retn    
    ],
    'length': 0x40
},
{
    'name': '_fclose',
    'description': 'int64_t _fclose()',
    'address': 0x100003DB0,
    'instructions': [
        b'\xFF\x25\x4A\x42\x00\x00',                    # jmp     qword [rel 0x100008000]
    ],
    'length': 0x6
},
{
    'name': '_fopen',
    'description': 'int64_t _fopen()',
    'address': 0x100003DB6,
    'instructions': [
        b'\xFF\x25\x4C\x42\x00\x00',                    # jmp     qword [rel 0x100008008]
    ],
    'length': 0x6
},
{
    'name': '_fread',
    'description': 'int64_t _fread()',
    'address': 0x100003DBC,
    'instructions': [
        b'\xFF\x25\x4E\x42\x00\x00',                    # jmp     qword [rel 0x100008010]
    ],
    'length': 0x6
},
{
    'name': '_printf',
    'description': 'int64_t _printf()',
    'address': 0x100003DC2,
    'instructions': [
        b'\xFF\x25\x50\x42\x00\x00',                    # jmp     qword [rel 0x100008018]
    ],
    'length': 0x6
},
{
    'name': '_strcmp',
    'description': 'int64_t _strcmp()',
    'address': 0x100003DC8,
    'instructions': [
        b'\xFF\x25\x52\x42\x00\x00',                    # jmp     qword [rel 0x100008020]
    ],
    'length': 0x6
},
{
    'name': '_strlen',
    'description': 'int64_t _strlen()',
    'address': 0x100003DCE,
    'instructions': [
        b'\xFF\x25\x54\x42\x00\x00',                    # jmp     qword [rel 0x100008028]
    ],
    'length': 0x6
},
{
    'name': '_time',
    'description': 'int64_t _time()',
    'address': 0x100003DD4,
    'instructions': [
        b'\xFF\x25\x56\x42\x00\x00',                    # jmp     qword [rel 0x100008030]
    ],
    'length': 0x6
},
{
    'name': 'sub_100003dec',
    'description': 'int64_t sub_100003dec()',
    'address': 0x100003DEC,
    'instructions': [
        b'\x4C\x8D\x1D\x5D\x42\x00\x00',                # lea     r11, [rel 0x100008040]
        b'\x41\x53',                                    # push    r11
        b'\xFF\x25\x1D\x02\x00\x00',                    # jmp     qword [rel 0x100004008]
        b'\x68\x00\x00\x00\x00',                        # push    0x0
        b'\xE9\xE6\xFF\xFF\xFF',                        # jmp     0x100003ddc
    ],
    'length': 0xA
},
]
