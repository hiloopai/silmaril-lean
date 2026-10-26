# arch_prctl(ARCH_SET_FS, 0x400000); exit(the byte at %fs:0). The FS base is
# the start of the loaded image, whose first byte is the ELF magic 0x7f.
    .text
    .globl _start
_start:
    mov $158, %eax       # b8 9e 00 00 00   arch_prctl
    mov $0x1002, %edi    # bf 02 10 00 00   ARCH_SET_FS
    mov $0x400000, %esi  # be 00 00 40 00   base = image start
    syscall
    mov %fs:0, %rdi      # 64 48 8b 3c 25 00 00 00 00
    mov $60, %eax        # b8 3c 00 00 00   exit (low byte of RDI)
    syscall
