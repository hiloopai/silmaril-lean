# write(1, "hello\n", 6); exit(0). The return value of write is ignored.
    .text
    .globl _start
_start:
    mov $1, %eax         # b8 01 00 00 00   native x86-64 write
    mov $1, %edi         # bf 01 00 00 00   fd 1 (stdout)
    mov $message, %esi   # be imm32         absolute address of the bytes
    mov $6, %edx         # ba 06 00 00 00   length 6
    syscall              # 0f 05
    mov $60, %eax        # b8 3c 00 00 00   native x86-64 exit
    mov $0, %edi         # bf 00 00 00 00   status 0
    syscall              # 0f 05
message:
    .ascii "hello\n"
