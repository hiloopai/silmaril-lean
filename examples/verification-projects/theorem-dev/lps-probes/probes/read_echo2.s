# Mutant of read_echo: the read length 16 becomes 2, so at most two bytes of
# stdin are echoed. The buffer is in the writable image ("image": "rwx").
    .text
    .globl _start
_start:
    mov $0, %eax         # b8 00 00 00 00   native x86-64 read
    mov $0, %edi         # bf 00 00 00 00   fd 0 (stdin)
    mov $buffer, %esi    # be imm32         the buffer
    mov $2, %edx         # ba 02 00 00 00   at most 2 bytes (original: 16)
    syscall              # 0f 05
    mov %rax, %rdx       # 48 89 c2         count = bytes read
    mov $1, %eax         # b8 01 00 00 00   native x86-64 write
    mov $1, %edi         # bf 01 00 00 00   fd 1 (stdout); rsi is still the buffer
    syscall              # 0f 05
    mov $60, %eax        # b8 3c 00 00 00   native x86-64 exit
    mov $0, %edi         # bf 00 00 00 00   status 0
    syscall              # 0f 05
buffer:
    .zero 16             # 16 zero bytes
