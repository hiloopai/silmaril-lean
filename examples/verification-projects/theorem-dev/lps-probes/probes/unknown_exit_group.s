# Mutant of unknown_syscall: the number immediate changed (999 -> 231), so the
# first call is exit_group(0): RDI is zero at entry.
    .text
    .globl _start
_start:
    mov $231, %eax       # b8 e7 00 00 00   exit_group
    syscall
    mov %rax, %rdi       # 48 89 c7         (not reached)
    mov $60, %eax        # b8 3c 00 00 00
    syscall
