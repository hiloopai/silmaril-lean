# Mutant of write_zero: length 1. Linux writes "h" and returns 1, so the
# probe exits with status 1.
    .text
    .globl _start
_start:
    mov $1, %eax         # b8 01 00 00 00   native x86-64 write
    mov $1, %edi         # bf 01 00 00 00   fd 1 (stdout)
    mov $message, %esi   # be imm32         the message
    mov $1, %edx         # ba 01 00 00 00   length 1 (original: 0)
    syscall              # 0f 05
    mov %rax, %rdi       # 48 89 c7         status = the return value
    mov $60, %eax        # b8 3c 00 00 00   native x86-64 exit
    syscall              # 0f 05
message:
    .ascii "hello\n"
