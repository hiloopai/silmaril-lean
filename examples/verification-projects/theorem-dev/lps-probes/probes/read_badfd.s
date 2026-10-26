# read(99, buffer, 6): descriptor 99 is not open, so Linux returns -EBADF (-9)
# before it looks at the buffer. exit(0 - rax) = exit(9). The image is
# writable ("image": "rwx"): qemu-user checks a read buffer before it forwards
# the call, and answers -EFAULT for a read-only one where Linux says -EBADF.
    .text
    .globl _start
_start:
    mov $0, %eax         # b8 00 00 00 00   native x86-64 read
    mov $99, %edi        # bf 63 00 00 00   fd 99 (not open)
    mov $buffer, %esi    # be imm32         a buffer in the writable image
    mov $6, %edx         # ba 06 00 00 00   length 6
    syscall              # 0f 05
    mov $0, %edi         # bf 00 00 00 00
    sub %rax, %rdi       # 48 29 c7         rdi = -rax (the errno)
    mov $60, %eax        # b8 3c 00 00 00   native x86-64 exit
    syscall              # 0f 05
buffer:
    .ascii "buffer"
