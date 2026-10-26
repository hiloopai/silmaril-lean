# Legacy x86-64 open(2) (musl's open): open("in.txt", O_RDONLY); exit(fd), so exit(3).
    .text
    .globl _start
_start:
    mov $2, %eax         # b8 02 00 00 00   native x86-64 open
    mov $path, %edi      # bf imm32         "in.txt"
    mov $0, %esi         # be 00 00 00 00   O_RDONLY
    syscall              # 0f 05
    mov %rax, %rdi       # 48 89 c7         status: the descriptor
    mov $60, %eax        # b8 3c 00 00 00   native x86-64 exit
    syscall              # 0f 05
path:
    .asciz "in.txt"
