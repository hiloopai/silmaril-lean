# openat(AT_FDCWD, "in.txt", O_RDONLY); read(fd, rsp, 64); write(1, rsp, n) with a
# negative n replaced by 0; close(fd); exit(0). The launch file system holds in.txt.
    .text
    .globl _start
_start:
    mov $0, %ebp         # bd 00 00 00 00   zero, for the cmov below
    mov $257, %eax       # b8 01 01 00 00   native x86-64 openat
    mov $-100, %edi      # bf 9c ff ff ff   AT_FDCWD (as a 32-bit int)
    mov $path, %esi      # be imm32         "in.txt"
    mov $0, %edx         # ba 00 00 00 00   O_RDONLY
    syscall              # 0f 05
    mov %rax, %rbx       # 48 89 c3         keep the descriptor (or -errno)
    mov $0, %eax         # b8 00 00 00 00   native x86-64 read
    mov %rbx, %rdi       # 48 89 df
    mov %rsp, %rsi       # 48 89 e6         the buffer is the entry stack
    mov $64, %edx        # ba 40 00 00 00
    syscall              # 0f 05
    mov %rax, %rdx       # 48 89 c2         bytes read (or -errno)
    cmp $0, %rdx         # 48 83 fa 00      defines every status flag
    cmovl %rbp, %rdx     # 48 0f 4c d5      an error writes nothing
    mov $1, %eax         # b8 01 00 00 00   native x86-64 write
    mov $1, %edi         # bf 01 00 00 00   stdout; RSI still holds the buffer
    syscall              # 0f 05
    mov $3, %eax         # b8 03 00 00 00   native x86-64 close
    mov %rbx, %rdi       # 48 89 df
    syscall              # 0f 05
    mov $60, %eax        # b8 3c 00 00 00   native x86-64 exit
    mov $0, %edi         # bf 00 00 00 00
    syscall              # 0f 05
path:
    .asciz "in.txt"
