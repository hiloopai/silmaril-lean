void _start(void) { __asm__ volatile("mov $60, %eax\n xor %edi, %edi\n syscall"); }
