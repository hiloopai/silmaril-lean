module

public import Silmaril.X86.Sep.Defs
public import Silmaril.X86.Ext.Syntax

/-!
# Indirect `call`/`jmp`: encodings and operand assertions

The separation-logic step laws of the indirect branches (`Sep/Ind/Thms.lean`) are proved on
`Open9.isa`, whose decoder has the `Ext9` forms `callInd`/`jmpInd`, and stated on every
machine `I` with `Open9.isa.Extends I`. A consumer never looks at a decoder, so a better x86
model only has to extend `Open9.isa`.

Forms (Intel SDM Vol. 2, `FF /2` and `FF /4`, 64-bit operand size by default):

| form | bytes | encoder |
| --- | --- | --- |
| `call *%r` | `REX.B? FF (11 010 r)` | `encCallR r` |
| `call *d8(%b)` | `REX.B? FF (01 010 b) [24] d8` | `encCallM b d` |
| `jmp *%r` | `REX.B? FF (11 100 r)` | `encJmpR r` |
| `jmp *d8(%b)` | `REX.B? FF (01 100 b) [24] d8` | `encJmpM b d` |

`REX.B` (`41`) is present exactly for `r8`–`r15`; the SIB byte `24` (no index, base = `b`) is
present exactly when the low three bits of `b` are `100` (`rsp`, `r12`). Only the `disp8`
memory form is covered: `[b]` with `mod = 00`, `disp32`, index registers, RIP-relative and
`notrack` (`3E`) forms are not.

* The call pushes the address of the next instruction into the eight bytes below `rsp` and
  jumps to the target, which is read *before* the push.
* The jump sets `rip` to the target.

The memory operand is an eight-byte little-endian word owned at any permission `need` that
implies readability (`wordAt need`), so a `.rodata` method table (`RO`) and a writable
`jmp_buf` (`RW`) use the same law; the permission is returned unchanged.

A law whose precondition owns a location twice (for example `call *%rsp`, or
`call *d(%rsp)` with `regPt .rsp` and `regPt base` both on `rsp`) is vacuous: the
precondition is unsatisfiable. No side condition excludes it.
-/

@[expose] public section

namespace Silmaril.X86.Sep.Ind

open Silmaril.X86 (MState Word Byte Reg)
open Silmaril.X86.Ext (RM Mem)
open Silmaril.Process (Permissions)

/-! ## Encodings -/

/-- The `REX.B` prefix (`41`) for an extended register, nothing otherwise. -/
def rexB (r : Reg) : List Byte := if r.toBitVec.getLsbD 3 then [0x41#8] else []

/-- `FF /digit` with a register operand (`mod = 11`). -/
def encR (digit : Nat) (r : Reg) : List Byte :=
  rexB r ++ [0xFF#8, BitVec.ofNat 8 (0xC0 + digit * 8 + r.lo.toNat)]

/-- `FF /digit` with a `[base + disp8]` operand (`mod = 01`, SIB `24` when `base.lo = 100`). -/
def encM (digit : Nat) (base : Reg) (d : BitVec 8) : List Byte :=
  rexB base ++ [0xFF#8, BitVec.ofNat 8 (0x40 + digit * 8 + base.lo.toNat)] ++
    (if base.lo = 4#3 then [0x24#8] else []) ++ [d]

/-- `call *%r`. -/
def encCallR (r : Reg) : List Byte := encR 2 r
/-- `call *d(%base)`. -/
def encCallM (base : Reg) (d : BitVec 8) : List Byte := encM 2 base d
/-- `jmp *%r`. -/
def encJmpR (r : Reg) : List Byte := encR 4 r
/-- `jmp *d(%base)`. -/
def encJmpM (base : Reg) (d : BitVec 8) : List Byte := encM 4 base d

/-- The decoded `r/m` operand of `encM`: `[base + sext(d)]`. -/
def memOp (base : Reg) (d : BitVec 8) : RM := .mem (Mem.ofReg base none (d.signExtend 32))

/-- The effective address of `[base + d]` when `base` holds `v`. -/
def ea (v : Word) (d : BitVec 8) : Word := v + d.signExtend 64

/-- The address after an instruction of length `bs.length` at `pc`. -/
def nextPc (pc : Word) (bs : List Byte) : Word := pc + BitVec.ofNat 64 bs.length

/-! ## Assertions -/

/-- An eight-byte little-endian word at `a`, each byte with permissions satisfying `need`. -/
def wordAt (need : Permissions → Prop) (a : Nat) (w : Word) : SProp :=
  bytesAt need a (Silmaril.Machine.LittleEndian.encodeWords [w])

end Silmaril.X86.Sep.Ind
