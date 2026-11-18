.section .text.mov,"ax",@progbits
movq %rdi, %rax
jmp .+2

.section .text.add,"ax",@progbits
movq %rdi, %rax
addq %rsi, %rax
jmp .+2

.section .text.je,"ax",@progbits
cmpq %rsi, %rdi
je .+6

.section .text.jne,"ax",@progbits
cmpq %rsi, %rdi
jne .+6
