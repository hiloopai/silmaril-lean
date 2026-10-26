# Mutant of read_badfd: fd 0 (stdin) instead of 99. The harness stdin is
# empty, so Linux returns 0 (end of file) and the probe exits with 0.
    .text
    .globl _start
_start:
    mov $0, %eax         # b8 00 00 00 00   native x86-64 read
    mov $0, %edi         # bf 00 00 00 00   fd 0 (original: 99)
    mov $buffer, %esi    # be imm32         a buffer in the writable image
    mov $6, %edx         # ba 06 00 00 00   length 6
    syscall              # 0f 05
    mov $0, %edi         # bf 00 00 00 00
    sub %rax, %rdi       # 48 29 c7         rdi = -rax
    mov $60, %eax        # b8 3c 00 00 00   native x86-64 exit
    syscall              # 0f 05
buffer:
    .ascii "buffer"
