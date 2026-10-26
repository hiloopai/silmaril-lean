# open_read with legacy open(2) in place of openat(AT_FDCWD, ...): open("in.txt",
# O_RDONLY), read 64 bytes into the stack, write them to stdout, close, exit 0. The
# open block has the length of open_read's (the RDX move keeps the layout), so every
# later instruction and the path sit at the same offsets.
    .text
    .globl _start
_start:
    mov $0, %ebp         # bd 00 00 00 00   zero, for the cmov below
    mov $2, %eax         # b8 02 00 00 00   native x86-64 open (legacy)
    mov $path, %edi      # bf imm32         "in.txt"
    mov $0, %esi         # be 00 00 00 00   O_RDONLY
    mov $0, %edx         # ba 00 00 00 00   (layout padding; open ignores it)
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
