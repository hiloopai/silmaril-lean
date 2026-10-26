/* hello-core: the core-comp form of hello.c. core-comp's Core dynamics implements the
   `printf` builtin and no syscalls, so this source prints with `printf` rather than
   `write(1, ...)`; crt0 writes the output buffer at exit
   (Silmaril/Compile/Examples/LPS/Hello.lean). */
#include <stdio.h>

int main(void) {
  printf("hello, world\n");
  return 0;
}
