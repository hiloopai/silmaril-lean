/* Rung 01: the allocator that never allocates. */
#include "alloc.h"
void *malloc(usize n) { return 0; }
void free(void *p) { }
