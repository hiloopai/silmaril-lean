/* The allocator interface every rung implements (freestanding; no libc). */
#ifndef ALLOC_LADDER_ALLOC_H
#define ALLOC_LADDER_ALLOC_H
#include "rt.h"
void *malloc(usize n);
void free(void *p);
#endif
