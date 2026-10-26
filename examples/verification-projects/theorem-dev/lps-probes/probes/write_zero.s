# write(1, "hello\n", 0) writes nothing and returns 0; the probe exits with
# the return value: exit(rax) = exit(0).
    .text
    .globl _start
_start:
    mov $1, %eax         # b8 01 00 00 00   native x86-64 write
    mov $1, %edi         # bf 01 00 00 00   fd 1 (stdout)
    mov $message, %esi   # be imm32         the message
    mov $0, %edx         # ba 00 00 00 00   length 0
    syscall              # 0f 05
    mov %rax, %rdi       # 48 89 c7         status = the return value
    mov $60, %eax        # b8 3c 00 00 00   native x86-64 exit
    syscall              # 0f 05
message:
    .ascii "hello\n"
