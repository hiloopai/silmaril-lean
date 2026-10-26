# write(1, "hel", 3); write(1, "lo\n", 3); exit(0): the bytes of write_hello in two
# write calls. The return values are ignored.
    .text
    .globl _start
_start:
    mov $1, %eax         # b8 01 00 00 00   native x86-64 write
    mov $1, %edi         # bf 01 00 00 00   fd 1 (stdout)
    mov $message, %esi   # be imm32         "hel"
    mov $3, %edx         # ba 03 00 00 00   length 3
    syscall              # 0f 05
    mov $1, %eax         # b8 01 00 00 00   native x86-64 write
    mov $1, %edi         # bf 01 00 00 00   fd 1 (stdout)
    mov $message+3, %esi # be imm32         "lo\n"
    mov $3, %edx         # ba 03 00 00 00   length 3
    syscall              # 0f 05
    mov $60, %eax        # b8 3c 00 00 00   native x86-64 exit
    mov $0, %edi         # bf 00 00 00 00   status 0
    syscall              # 0f 05
message:
    .ascii "hello\n"
