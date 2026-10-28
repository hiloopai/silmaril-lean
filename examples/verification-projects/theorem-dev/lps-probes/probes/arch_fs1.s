# Mutant of arch_fs: the FS base immediate changed (0x400000 -> 0x400001), so
# %fs:0 reads the second ELF magic byte, 0x45.
    .text
    .globl _start
_start:
    mov $158, %eax       # b8 9e 00 00 00   arch_prctl
    mov $0x1002, %edi    # bf 02 10 00 00   ARCH_SET_FS
    mov $0x400001, %esi  # be 01 00 40 00   base = image start + 1
    syscall
    mov %fs:0, %rdi      # 64 48 8b 3c 25 00 00 00 00
    mov $60, %eax        # b8 3c 00 00 00   exit (low byte of RDI)
    syscall
