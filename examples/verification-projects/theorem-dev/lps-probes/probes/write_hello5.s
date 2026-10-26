# Mutant of write_hello: the length immediate changed (6 -> 5).
    .text
    .globl _start
_start:
    mov $1, %eax         # b8 01 00 00 00   native x86-64 write
    mov $1, %edi         # bf 01 00 00 00   fd 1 (stdout)
    mov $message, %esi   # be imm32         absolute address of the bytes
    mov $5, %edx         # ba 05 00 00 00   length 5
    syscall              # 0f 05
    mov $60, %eax        # b8 3c 00 00 00   native x86-64 exit
    mov $0, %edi         # bf 00 00 00 00   status 0
    syscall              # 0f 05
message:
    .ascii "hello\n"
