# arch_prctl(ARCH_SET_FS, 0x400078), then arch_prctl(ARCH_GET_FS, rsp), and
# exit(the low byte of the value read back). LPS models only ARCH_SET_FS.
    .text
    .globl _start
_start:
    mov $158, %eax       # b8 9e 00 00 00   arch_prctl
    mov $0x1002, %edi    # bf 02 10 00 00   ARCH_SET_FS
    mov $0x400078, %esi  # be 78 00 40 00   base = entry point
    syscall
    mov $158, %eax       # b8 9e 00 00 00   arch_prctl
    mov $0x1003, %edi    # bf 03 10 00 00   ARCH_GET_FS
    mov %rsp, %rsi       # 48 89 e6         store it at the entry stack pointer
    syscall
    mov (%rsp), %rdi     # 48 8b 3c 24      the value read back
    mov $60, %eax        # b8 3c 00 00 00   exit
    syscall
