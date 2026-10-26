# Mutant of getrandom8: the flags immediate changed (0 -> 0xdead). Linux rejects
# the unknown flag bits with -EINVAL; LPS fails closed (unmodeled).
    .text
    .globl _start
_start:
    mov %rsp, %rdi       # 48 89 e7         buf = entry stack pointer
    mov $8, %esi         # be 08 00 00 00   8 bytes
    mov $0xdead, %edx    # ba ad de 00 00   flags 0xdead
    mov $318, %eax       # b8 3e 01 00 00   getrandom
    syscall
    mov %rax, %rdi       # 48 89 c7         status = return value
    mov $60, %eax        # b8 3c 00 00 00   exit
    syscall
