# 02-mem-loops

The subject is `../common/libmini.c` (`memcpy`, `memmove`, `memset`, `memcmp`, `strlen`),
linked into every rung. `main.c` tests it for sizes 0..40 at offsets 0..7, including
overlapping `memmove` in both directions.

`Silmaril.X86.Ladder.LibMini` proves `memcpy`, `memset` and `strlen` of the `-O2` build
(`pinned/mem-loops`): total correctness on the open machine for every load address, the
System V separation-logic specs of the byte-loop stencils, and first-return contracts.
`memmove` and `memcmp` are not proved.

`common/flags.sh` passes `-fno-tree-loop-distribute-patterns` so that GCC cannot turn a loop
into a `memset`/`memcpy` call (inside `memset` that would be a self-call). With GCC 13.3
`-O2 -ffreestanding -fno-builtin` the code is the same without it.
