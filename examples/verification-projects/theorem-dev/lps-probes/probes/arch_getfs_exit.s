# Mutant of arch_getfs: the second call's number immediate changed (158 -> 60),
# so it is exit(0x1003): status 3.
    .text
    .globl _start
_start:
    mov $158, %eax       # b8 9e 00 00 00   arch_prctl
    mov $0x1002, %edi    # bf 02 10 00 00   ARCH_SET_FS
    mov $0x400078, %esi  # be 78 00 40 00   base = entry point
    syscall
    mov $60, %eax        # b8 3c 00 00 00   mutated: exit
    mov $0x1003, %edi    # bf 03 10 00 00   status 0x1003 & 255 = 3
    mov %rsp, %rsi       # 48 89 e6         (not reached)
    syscall
    mov (%rsp), %rdi     # 48 8b 3c 24      (not reached)
    mov $60, %eax        # b8 3c 00 00 00
    syscall
