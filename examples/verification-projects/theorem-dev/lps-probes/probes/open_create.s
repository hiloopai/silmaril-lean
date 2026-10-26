# openat(AT_FDCWD, "out.txt", O_WRONLY|O_CREAT|O_TRUNC, 0644); write(fd, "ok", 2);
# close(fd); exit(write's return), so exit(2). Afterwards out.txt holds "ok".
    .text
    .globl _start
_start:
    mov $257, %eax       # b8 01 01 00 00   native x86-64 openat
    mov $-100, %edi      # bf 9c ff ff ff   AT_FDCWD
    mov $name, %esi      # be imm32         "out.txt"
    mov $0x241, %edx     # ba 41 02 00 00   O_WRONLY|O_CREAT|O_TRUNC
    mov $0x1a4, %r10d    # 41 ba a4 01 00 00  mode 0644
    syscall              # 0f 05
    mov %rax, %rbx       # 48 89 c3         keep the descriptor (or -errno)
    mov $1, %eax         # b8 01 00 00 00   native x86-64 write
    mov %rbx, %rdi       # 48 89 df
    mov $message, %esi   # be imm32         "ok"
    mov $2, %edx         # ba 02 00 00 00
    syscall              # 0f 05
    mov %rax, %rbp       # 48 89 c5         keep write's return
    mov $3, %eax         # b8 03 00 00 00   native x86-64 close
    mov %rbx, %rdi       # 48 89 df
    syscall              # 0f 05
    mov $60, %eax        # b8 3c 00 00 00   native x86-64 exit
    mov %rbp, %rdi       # 48 89 ef         status: write's return
    syscall              # 0f 05
name:
    .asciz "out.txt"
message:
    .ascii "ok"
