.data

/* Data segment: define our message string and calculate its length. */
msg:
    .ascii      "r2 < r3, 2<3\n"
len = . - msg

.text

/* Our application's entry point. */
.globl _start

/* without this directive, thumb code will still be generated with -mthumb
   passed to as, but the pointer to this entrypoint elf32_hdr.e_entry will
   not have LSB set */
.thumb_func
_start:
    #mov     %r2, $2
    mov     %r2, $99
    mov     %r3, $3

.interesting:
    cmp     %r2, %r3

    nop // space for ittt lt

    nop // space for ldr...
    nop

    nop // space for str...
    nop

    nop // space for b .interesting

//    ittt    lt
//    ldr     r0, [r1], #4
//    str     r0, [r2], #4
//    b       .write_msg

.write_msg:
    /* syscall write(int fd, const void *buf, size_t count) */
    mov     %r0, $1     /* fd := STDOUT_FILENO */
    ldr     %r1, =msg   /* buf := msg */
    ldr     %r2, =len   /* count := len */
    mov     %r7, $4     /* write is syscall #4 */
    swi     $0          /* invoke syscall */

.done:
    /* syscall exit(int status) */
    mov     %r0, $0     /* status := 0 */
    mov     %r7, $1     /* exit is syscall #1 */
    swi     $0          /* invoke syscall */
