# Mutant of exit42: one immediate byte changed (0x2a -> 0x2b).
    .text
    .globl _start
_start:
    mov $60, %eax        # b8 3c 00 00 00   native x86-64 exit
    mov $43, %edi        # bf 2b 00 00 00   status 43
    syscall              # 0f 05
