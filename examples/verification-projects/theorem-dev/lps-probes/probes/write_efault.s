# write(1, 0x10, 6): the buffer is unmapped, so Linux returns -EFAULT (-14).
# The errno becomes the exit status: exit(0 - rax) = exit(14).
    .text
    .globl _start
_start:
    mov $1, %eax         # b8 01 00 00 00   native x86-64 write
    mov $1, %edi         # bf 01 00 00 00   fd 1 (stdout)
    mov $0x10, %esi      # be 10 00 00 00   unmapped address 0x10
    mov $6, %edx         # ba 06 00 00 00   length 6
    syscall              # 0f 05
    mov $0, %edi         # bf 00 00 00 00
    sub %rax, %rdi       # 48 29 c7         rdi = -rax (the errno)
    mov $60, %eax        # b8 3c 00 00 00   native x86-64 exit
    syscall              # 0f 05
message:
    .ascii "hello\n"
