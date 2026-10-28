# syscall 999 (no such native call); exit(its return value). Linux returns
# -ENOSYS (status 218 = -38 mod 256); LPS fails closed (unmodeled).
    .text
    .globl _start
_start:
    mov $999, %eax       # b8 e7 03 00 00   no such syscall
    syscall
    mov %rax, %rdi       # 48 89 c7         status = return value
    mov $60, %eax        # b8 3c 00 00 00   exit
    syscall
