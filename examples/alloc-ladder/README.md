# Allocator ladder

Small freestanding allocators (`<rung>/alloc.c`), each linked with the shared self-test driver
`common/driver.c` and the elf-ladder runtime (`common/{start.S,rt.c,libmini.c}`, copied from
silmaril-lean `examples/elf-ladder/common`, MIT) into a static non-PIE x86-64 executable.

| rung | allocator | Lean |
|---|---|---|
| `01-never` | `malloc` returns NULL | `Silmaril.Libc.X86Alloc.Ladder.Never` |
| `02-bump` | bump over a 4096-byte static arena, `free` a no-op | `….Ladder.Bump` |
| `03-bump-align` | the same, 16-byte aligned | `….Ladder.BumpAlign` |
| `04-pool` | 64 blocks of 64 bytes, LIFO free list, lazy bump of fresh blocks | `….Ladder.Pool` |
| `05-firstfit` | first fit over headed blocks, splitting, no coalescing | `….Ladder.FirstFit` |
| `06-coalesce` | the same with an address-ordered list and coalescing | `….Ladder.Coalesce` |
| `07-sizeclass` | four size classes (16/32/64/128) with LIFO lists, 16-byte headers, a 4096-byte bump arena | `….Ladder.SizeClass` |
| `08-boundary` | boundary tags (headers, footers on free blocks), one doubly linked free list, first fit, constant-time coalescing via first/last granule tables | `….Ladder.Boundary` |
| `08t-boundary-textbook` | textbook boundary tags (allocated bit in every header and footer; free reads both neighbours' tags) | `….Ladder.BoundaryTextbook` (open: needs ghost state) |

Toolchain: GCC 13.3.0 (Ubuntu 13.3.0-6ubuntu2~24.04.1), GNU binutils 2.42; flags in
`common/flags.sh` (the elf-ladder flags). `bash <rung>/build.sh` builds `-O1` and `-O2` under
`<rung>/build/` and runs the self-test. The `-O2` executables are pinned under `<rung>/pinned/`
with their `.sha256`; the build reproduces them byte for byte (checked for every rung on
2026-11-09). `bash pin.sh` regenerates `Silmaril/Libc/X86Alloc/Pinned/<Rung>.lean` (the files
as `Blob` literals); `bash pin.sh --check` checks the modules against the files.
