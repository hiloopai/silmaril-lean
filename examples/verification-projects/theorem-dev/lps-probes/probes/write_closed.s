# close(1); write(1, "hello\n", 6): the descriptor is closed, so the write
# returns -EBADF (-9). The errno becomes the exit status: exit(0 - rax) = exit(9).
    .text
    .globl _start
_start:
    mov $3, %eax         # b8 03 00 00 00   native x86-64 close
    mov $1, %edi         # bf 01 00 00 00   fd 1 (stdout)
    syscall              # 0f 05
    mov $1, %eax         # b8 01 00 00 00   native x86-64 write
    mov $1, %edi         # bf 01 00 00 00   fd 1, now closed
    mov $message, %esi   # be imm32         the message
    mov $6, %edx         # ba 06 00 00 00   length 6
    syscall              # 0f 05
    mov $0, %edi         # bf 00 00 00 00
    sub %rax, %rdi       # 48 29 c7         rdi = -rax (the errno)
    mov $60, %eax        # b8 3c 00 00 00   native x86-64 exit
    syscall              # 0f 05
message:
    .ascii "hello\n"
