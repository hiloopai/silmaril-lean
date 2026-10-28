# exit(42): the smallest probe.
    .text
    .globl _start
_start:
    mov $60, %eax        # b8 3c 00 00 00   native x86-64 exit
    mov $42, %edi        # bf 2a 00 00 00   status 42
    syscall              # 0f 05
