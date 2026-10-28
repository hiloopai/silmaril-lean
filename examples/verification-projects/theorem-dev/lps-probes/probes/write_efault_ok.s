# Mutant of write_efault: the buffer immediate 0x10 becomes the message address.
# Linux writes hello\n and returns 6, so the probe exits with 0 - 6 = 250.
    .text
    .globl _start
_start:
    mov $1, %eax         # b8 01 00 00 00   native x86-64 write
    mov $1, %edi         # bf 01 00 00 00   fd 1 (stdout)
    mov $message, %esi   # be imm32         the message (original: 0x10)
    mov $6, %edx         # ba 06 00 00 00   length 6
    syscall              # 0f 05
    mov $0, %edi         # bf 00 00 00 00
    sub %rax, %rdi       # 48 29 c7         rdi = -rax
    mov $60, %eax        # b8 3c 00 00 00   native x86-64 exit
    syscall              # 0f 05
message:
    .ascii "hello\n"
