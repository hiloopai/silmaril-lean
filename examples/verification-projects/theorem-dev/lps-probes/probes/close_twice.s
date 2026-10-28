# close(0) succeeds; a second close(0) returns -EBADF (-9).
# The second errno becomes the exit status: exit(0 - rax) = exit(9).
    .text
    .globl _start
_start:
    mov $3, %eax         # b8 03 00 00 00   native x86-64 close
    mov $0, %edi         # bf 00 00 00 00   fd 0 (stdin)
    syscall              # 0f 05            returns 0
    mov $3, %eax         # b8 03 00 00 00   close again
    mov $0, %edi         # bf 00 00 00 00   fd 0, now closed
    syscall              # 0f 05            returns -EBADF
    mov $0, %edi         # bf 00 00 00 00
    sub %rax, %rdi       # 48 29 c7         rdi = -rax (the errno)
    mov $60, %eax        # b8 3c 00 00 00   native x86-64 exit
    syscall              # 0f 05
