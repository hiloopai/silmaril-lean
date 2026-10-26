# openat(AT_FDCWD, "nofile", O_RDONLY) on a file system without it; exit(-ret),
# that is exit(2) for -ENOENT.
    .text
    .globl _start
_start:
    mov $257, %eax       # b8 01 01 00 00   native x86-64 openat
    mov $-100, %edi      # bf 9c ff ff ff   AT_FDCWD
    mov $path, %esi      # be imm32         "nofile"
    mov $0, %edx         # ba 00 00 00 00   O_RDONLY
    syscall              # 0f 05
    mov %rax, %rdi       # 48 89 c7
    neg %rdi             # 48 f7 df         -(-errno)
    mov $60, %eax        # b8 3c 00 00 00   native x86-64 exit
    syscall              # 0f 05
path:
    .asciz "nofile"
