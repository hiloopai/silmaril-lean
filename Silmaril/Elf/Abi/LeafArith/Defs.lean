module

public import Silmaril.Elf.Abi.Defs
public import Silmaril.Elf.Staged.Pinned.LeafArith.Bytes
public import Silmaril.Machine.Abi.Conformance.LeafArith.Defs

/-! # ABI conformance rows: `arith.h` and the pinned `leaf-arith`

The rows of `silmaril.shapes.elf.abi_conforms.sysv_int_open` for the functions of
`examples/elf-ladder/01-leaf-arith/arith.h` in the pinned executable
`examples/elf-ladder/01-leaf-arith/pinned/leaf-arith` (gcc 13.3 `-O2`, static, `.symtab`), and
the partial header row (`silmaril.shapes.elf.abi_header_sat_partial.sysv_int_open`). The header, code, specs and
coverage are `Silmaril.Machine.Abi.Conformance.LeafArith`; the file is the per-part reader's
`Silmaril.Elf.Staged.Pinned.LeafArith.F` (its `include_bytes`).

| row | function | status |
| --- | --- | --- |
| `silmaril.elf.abi.leaf_arith.clamp_i32` | `int clamp_i32(int, int, int)`; total, frame 0, no precondition | proved |
| `silmaril.elf.abi.leaf_arith.sat_add_u32` | `u32 sat_add_u32(u32, u32)`; total, frame 0, no precondition | proved |
| `silmaril.elf.abi.leaf_arith.gcd_u32` | `u32 gcd_u32(u32, u32)`; total, frame 0 | open |
| `silmaril.elf.abi.leaf_arith.bswap32_manual` | `u32 bswap32_manual(u32)`; total, frame 0 | open |
| `silmaril.elf.abi.leaf_arith.arith_h` | the header, **partial**: the two proved functions claimed, the rest excluded (absent ones checked absent, unclaimed ones checked present) | proved |

All rows are on the open machine model `Open`, not real x86 (`Conforms.onRef` reads them on a
reference machine under `Faithful`).
-/

@[expose] public section

namespace Silmaril.Elf.Abi.LeafArith

/-- The functions are found in `.symtab`. -/
def bind (_ : String) : Silmaril.Elf.Abi.Binding := .symtab

/-- `clamp_i32`'s code region with the byte at its entry changed to `0x90` (`nop`): the
wrong-bytes negative test. -/
def patched : Silmaril.Machine.Abi.Conformance.Code :=
  { Silmaril.Machine.Abi.Conformance.LeafArith.clampCode with
    bytes := Silmaril.X86.Ladder.LeafArith.code.set 0x30 0x90 }

end Silmaril.Elf.Abi.LeafArith

end

silmaril instance silmaril.elf.abi.leaf_arith.clamp_i32
    (title := "leaf-arith clamp_i32 conforms to System V AMD64 (INTEGER fragment) on Open as arith.h declares it: total, frame 0") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open (mode := .total)
    (hdr := Silmaril.Machine.Abi.Conformance.LeafArith.hdr) (f := "clamp_i32")
    (p := Silmaril.Machine.Abi.Conformance.LeafArith.clampProto) (F := Silmaril.Elf.Staged.Pinned.LeafArith.F)
    (b := .symtab)
    (c := Silmaril.Machine.Abi.Conformance.LeafArith.clampCode) (frame := 0)
    (S := Silmaril.Machine.Abi.Conformance.LeafArith.clampS)
silmaril instance silmaril.elf.abi.leaf_arith.sat_add_u32
    (title := "leaf-arith sat_add_u32 conforms to System V AMD64 (INTEGER fragment) on Open as arith.h declares it: total, frame 0") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open (mode := .total)
    (hdr := Silmaril.Machine.Abi.Conformance.LeafArith.hdr) (f := "sat_add_u32")
    (p := Silmaril.Machine.Abi.Conformance.LeafArith.satProto) (F := Silmaril.Elf.Staged.Pinned.LeafArith.F)
    (b := .symtab)
    (c := Silmaril.Machine.Abi.Conformance.LeafArith.satCode) (frame := 0)
    (S := Silmaril.Machine.Abi.Conformance.LeafArith.satS)
silmaril instance silmaril.elf.abi.leaf_arith.gcd_u32
    (title := "leaf-arith gcd_u32 conforms to System V AMD64 (INTEGER fragment) on Open as arith.h declares it: total, frame 0 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open (mode := .total)
    (hdr := Silmaril.Machine.Abi.Conformance.LeafArith.hdr) (f := "gcd_u32")
    (p := Silmaril.Machine.Abi.Conformance.LeafArith.satProto) (F := Silmaril.Elf.Staged.Pinned.LeafArith.F)
    (b := .symtab)
    (c := Silmaril.Machine.Abi.Conformance.LeafArith.region 0 37) (frame := 0)
    (S := Silmaril.Machine.Abi.Conformance.LeafArith.gcdS)
silmaril instance silmaril.elf.abi.leaf_arith.bswap32_manual
    (title := "leaf-arith bswap32_manual conforms to System V AMD64 (INTEGER fragment) on Open as arith.h declares it: total, frame 0 (open)") :=
  silmaril.shapes.elf.abi_conforms.sysv_int_open (mode := .total)
    (hdr := Silmaril.Machine.Abi.Conformance.LeafArith.hdr) (f := "bswap32_manual")
    (p := Silmaril.Machine.Abi.Conformance.LeafArith.bswapProto)
    (F := Silmaril.Elf.Staged.Pinned.LeafArith.F)
    (b := .symtab)
    (c := Silmaril.Machine.Abi.Conformance.LeafArith.region 0xb0 5) (frame := 0)
    (S := Silmaril.Machine.Abi.Conformance.LeafArith.bswapS)
silmaril instance silmaril.elf.abi.leaf_arith.arith_h
    (title := "leaf-arith satisfies part of arith.h (2 functions claimed, total) under System V AMD64 on Open") :=
  silmaril.shapes.elf.abi_header_sat_partial.sysv_int_open
    (hdr := Silmaril.Machine.Abi.Conformance.LeafArith.hdr)
    (cov := Silmaril.Machine.Abi.Conformance.LeafArith.coverage)
    (F := Silmaril.Elf.Staged.Pinned.LeafArith.F) (bind := Silmaril.Elf.Abi.LeafArith.bind)
    (impl := Silmaril.Machine.Abi.Conformance.LeafArith.impl)
