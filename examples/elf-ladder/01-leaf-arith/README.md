# 01-leaf-arith

Leaf functions in `arith.c`: they make no calls and use no memory beyond registers.
`main.c` tests them and exits 0 on success.

`Silmaril.X86.Ladder.LeafArith` proves four of them in the `-O2` build (`pinned/leaf-arith`):
`sat_add_u32`, `bswap32_manual`, `clamp_i32` (when `lo <= hi`) and `gcd_u32`, as total
System V function contracts on the open machine for every load address, and as integer
`Silmaril.Machine.SystemV.Realizes` certificates. `popcount32`, `isqrt_u32` and `ilog2_u32`
are not proved here. `Silmaril.X86.AbiFunction.LeafArith` checks the assembler reading of the
same functions against the bytes of the pinned file.

Codegen notes (`-O2`): `bswap32_manual` becomes a single `bswap`; `sat_add_u32` jumps back to a
shared return block, a jump to a lower address that is not a loop.
