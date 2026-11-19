module

public import Silmaril.Machine.Abi.Conformance.Defs
public import Silmaril.X86.Ladder.LeafArith.Defs
public import Silmaril.X86.Open.Thms

/-!
# ABI conformance, worked example: rung 01 `leaf-arith` (gcc -O2)

The header is the repository's `examples/elf-ladder/01-leaf-arith/arith.h` (which includes
`examples/elf-ladder/common/rt.h`), read as text (`include_str`) by `Data.Layout.Header.read`.
The code is the 181-byte region `[0x401370, 0x401425)` of the pinned executable
`examples/elf-ladder/01-leaf-arith/pinned/leaf-arith` (SHA-256 `d9cf1e5d…`), transcribed as
`Silmaril.X86.Ladder.LeafArith.code`; the symbol table gives each function's offset and size:

| function | `st_value` | `st_size` | offset in the region |
| --- | --- | --- | --- |
| `gcd_u32` | `0x401370` | 37 | `0x00` |
| `clamp_i32` | `0x4013a0` | 19 | `0x30` |
| `isqrt_u32` | `0x4013c0` | 61 | `0x50` |
| `sat_add_u32` | `0x401400` | 29 | `0x90` |
| `bswap32_manual` | `0x401420` | 5 | `0xb0` |

(`popcount32` at `0x401330` and `ilog2_u32` at `0x401430` are outside the region.)
The C-level specs are the source functions (`Silmaril.X86.Ladder.LeafArith.clampSpec`,
`satAddSpec`, `gcdSpec`, `bswap32Spec`), with no memory written. The prototypes are the
INTEGER-fragment values the header lowers to (`clamp_declared`, …); they are the values of
`Machine.Abi.OpenMachine.clampProto` and `satProto`.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance.LeafArith

open Silmaril.Machine.Abi.Conformance
open Silmaril.X86.Ladder.LeafArith (sigU1 sigU2 sigI3 clampResult satResult gcdResult bswapResult)

/-- `examples/elf-ladder/common/rt.h`. -/
def rtH : String := include_str "../../../../../examples/elf-ladder/common/rt.h"

/-- `examples/elf-ladder/01-leaf-arith/arith.h`. -/
def arithH : String := include_str "../../../../../examples/elf-ladder/01-leaf-arith/arith.h"

/-- The header `arith.h`, with the file it includes. -/
def hdr : HeaderSrc := ⟨[("rt.h", rtH), ("arith.h", arithH)], "arith.h"⟩

/-- The image of the pinned `leaf-arith`: its four `PT_LOAD` ranges (start, `p_memsz`), as the
file's parse gives them (`Silmaril.Elf.Abi.LeafArith`'s `CodeOf` checks this). -/
def image : List (Silmaril.X86.Word × Nat) :=
  [(0x400000, 344), (0x401000, 2038), (0x402000, 204), (0x4030cc, 4)]

/-- The transcribed region at `0x401370`, entered at offset `off`, function size `len`. -/
def region (off len : Nat) : Code :=
  ⟨Silmaril.X86.Ladder.LeafArith.base, Silmaril.X86.Ladder.LeafArith.code, off, len, [], image⟩

/-- `clamp_i32`: `0x4013a0`, 19 bytes. -/
def clampCode : Code := region 0x30 19

/-- `sat_add_u32`: `0x401400`, 29 bytes. -/
def satCode : Code := region 0x90 29

/-- `int clamp_i32(int, int, int)`. -/
def clampProto : Silmaril.Machine.Abi.SystemV.Proto := ⟨sigI3, by decide⟩

/-- `u32 sat_add_u32(u32, u32)` and `u32 gcd_u32(u32, u32)`. -/
def satProto : Silmaril.Machine.Abi.SystemV.Proto := ⟨sigU2, by decide⟩

/-- `u32 bswap32_manual(u32)`. -/
def bswapProto : Silmaril.Machine.Abi.SystemV.Proto := ⟨sigU1, by decide⟩

/-- The C spec of `clamp_i32`: every call returns the source function's result. -/
def clampS : CallSpec sysvInt.V clampProto where
  pre _ _ := True
  post a _ r _ := r = clampResult a

/-- The C spec of `sat_add_u32`. -/
def satS : CallSpec sysvInt.V satProto where
  pre _ _ := True
  post a _ r _ := r = satResult a

/-- A *wrong* spec of `clamp_i32` (it returns its first argument), which the code does not
meet (`Thms.clamp_rejects_first`). -/
def clampFirstS : CallSpec sysvInt.V clampProto where
  pre _ _ := True
  post a _ r _ := match a with | .cons x _ => r = x

/-- The C spec of `gcd_u32`: Euclid's result (`Nat.gcd`). -/
def gcdS : CallSpec sysvInt.V satProto where
  pre _ _ := True
  post a _ r _ := r = gcdResult a

/-- The C spec of `bswap32_manual`: the byte reversal. -/
def bswapS : CallSpec sysvInt.V bswapProto where
  pre _ _ := True
  post a _ r _ := r = bswapResult a

/-- **Open**: `gcd_u32` (`0x401370`, 37 bytes) conforms. Its block certificate (`gcdCert`, a loop
with Euclid's invariant) is proved; the first-return form is not. -/
def Task.gcd_conforms : Prop :=
  Conforms sysvInt (Mach.ofInt Silmaril.X86.Open.isa) .total hdr "gcd_u32" satProto (region 0 37) 0 gcdS

/-- **Open**: `bswap32_manual` (`0x401420`, 5 bytes: `mov %edi,%eax; bswap %eax; ret`)
conforms. -/
def Task.bswap_conforms : Prop :=
  Conforms sysvInt (Mach.ofInt Silmaril.X86.Open.isa) .total hdr "bswap32_manual" bswapProto (region 0xb0 5) 0 bswapS

/-- The coverage of `arith.h` by the pinned `leaf-arith` that this example proves: the two
functions with first-return proofs, and every other declaration excluded with its reason. -/
def coverage : Coverage where
  claimed := ["clamp_i32", "sat_add_u32"]
  excluded :=
    [("sc3", .unclaimed "rt.h runtime (raw syscall), not a subject of arith.h"),
     ("rt_write", .absent "not linked into leaf-arith"), ("rt_read", .absent "not linked into leaf-arith"),
     ("rt_puts", .absent "not linked into leaf-arith"), ("rt_put_hex", .absent "not linked into leaf-arith"),
     ("rt_check", .unclaimed "rt.h runtime"), ("rt_failures", .absent "not linked into leaf-arith"),
     ("rt_finish", .unclaimed "rt.h runtime"), ("memcpy", .absent "not linked into leaf-arith"),
     ("memset", .absent "not linked into leaf-arith"), ("memmove", .absent "not linked into leaf-arith"),
     ("memcmp", .absent "not linked into leaf-arith"),
     ("strlen", .unclaimed "rt.h memory functions (rung 02)"),
     ("popcount32", .unclaimed "imul r32, r/m32, imm32 is outside the open machine (X86.Ext/Ext8)"),
     ("gcd_u32", .unclaimed "block certificate proved; first-return form open: Task.gcd_conforms"),
     ("isqrt_u32", .unclaimed "lifted, not certified"),
     ("bswap32_manual", .unclaimed "block certificate proved; first-return form open: Task.bswap_conforms"),
     ("ilog2_u32", .unclaimed "bsr is outside the open machine (X86.Ext/Ext8)")]

/-- The implementations claimed. -/
def impl : String → Option (Impl sysvInt)
  | "clamp_i32" => some ⟨clampProto, clampCode, 0, clampS, .total⟩
  | "sat_add_u32" => some ⟨satProto, satCode, 0, satS, .total⟩
  | _ => none

end Silmaril.Machine.Abi.Conformance.LeafArith

end
