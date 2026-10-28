# Mutant of close_twice: the second close is close(1), which succeeds,
# so the probe exits with 0 - 0 = 0.
    .text
    .globl _start
_start:
    mov $3, %eax         # b8 03 00 00 00   native x86-64 close
    mov $0, %edi         # bf 00 00 00 00   fd 0 (stdin)
    syscall              # 0f 05            returns 0
    mov $3, %eax         # b8 03 00 00 00   close again
    mov $1, %edi         # bf 01 00 00 00   fd 1 (original: 0), open
    syscall              # 0f 05            returns 0
    mov $0, %edi         # bf 00 00 00 00
    sub %rax, %rdi       # 48 29 c7         rdi = -rax
    mov $60, %eax        # b8 3c 00 00 00   native x86-64 exit
    syscall              # 0f 05
