module

public import Silmaril.X86.Flow.Defs

/-!
# `X64`: a length decoder and flow classifier of x86-64 encodings

`X64.dec` is the flow decoder of the CFG certificates. It reads one instruction of 64-bit mode:
legacy prefixes, `REX`, the one-byte map, the `0F`, `0F 38` and `0F 3A` maps, `VEX` (`C4`/`C5`)
and `EVEX` (`62`) with their maps 1 to 3 (and the `EVEX` maps 5 and 6), the `ModRM`/`SIB`/
displacement bytes and the immediate (Intel SDM Vol. 2, chapter 2 and appendix A). It returns the
instruction's **flow information** (`Info`: its `Kind` and its `RaxT`) and its length. It does not
say what an instruction computes; that is the machine's business, tied to this classification by
the flow law (`FlowLaw M X64.dec`, a per-machine theorem).

It is written in a reader monad (`Rd`) of byte lists that the kernel can run (`decide`) over the
bytes of a certificate. `decode` returns the shortest prefix that the reader consumes entirely, so
its answer on a slice holding the instruction does not depend on the bytes after it
(`FlowDec.Stable`, `Thms.stable`).

## Choices

* Undefined one-byte opcodes of 64-bit mode (`06`, `07`, `0E`, `16`, `17`, `1E`, `1F`, `27`,
  `2F`, `37`, `3F`, `60`, `61`, `82`, `9A`, `C4`/`C5` as `LES`/`LDS`, `CE`, `D4`–`D6`, `EA`) and
  3DNow! (`0F 0F`) do not decode.
* `ret imm16` is `other` (it is not the `ret` of `Admits`: it pops more than 8 bytes); so are far
  transfers, `iret`, `sysret`, `sysexit`, `xbegin`, port string I/O, `jmp`/`call rel` with a `66`
  prefix.
* `loop`, `loope`, `loopne` and `jrcxz` are conditional branches (`jcc`).
* `syscall` is `syscall`; `sysenter` and every `int n` are `sysOther`; `int3`, `int1`, `hlt`,
  `ud0`, `ud1`, `ud2` are traps.
* A string form with an `F3` or `F2` prefix is `rep`; without one it is `seq`.
* `RaxT` is a whitelist. `set n`: `mov $imm32,%eax`, `mov $imm64,%rax`, `mov $imm32,%rax`
  (`C7 C0`, sign-extended), `xor %eax,%eax` / `sub %eax,%eax` (also with `REX.W`). `keep`: the
  common integer forms whose destination register is not `rax` (by the `ModRM` encoding, with
  `AH` counted as `rax` when there is no `REX`), compares and tests, `push`, `pop` to another
  register, `nop`, `endbr64`, the prefetch and hint forms, branches, calls and returns. Every
  other instruction (in particular every vector form) is `clobber`.
-/

@[expose] public section

namespace Silmaril.X86.Flow.X64

open Silmaril.X86 (Byte)

/-- **The flow information of an instruction.** -/
structure Info where
  kind : Kind
  rax : RaxT
  deriving DecidableEq, Repr

/-! ## The reader -/

/-- A reader of a byte list: a value and the bytes left. -/
abbrev Rd (α : Type) := List Byte → Option (α × List Byte)

namespace Rd

def pure {α : Type} (a : α) : Rd α := fun w => some (a, w)

def bind {α β : Type} (p : Rd α) (f : α → Rd β) : Rd β := fun w =>
  match p w with
  | some (a, r) => f a r
  | none => none

def fail {α : Type} : Rd α := fun _ => none

/-- One byte, as a number. -/
def byte : Rd Nat := fun w =>
  match w with
  | b :: r => some (b.toNat, r)
  | [] => none

/-- `n` bytes, little-endian. -/
def le : Nat → Rd Nat
  | 0 => pure 0
  | n + 1 => bind byte fun b => bind (le n) fun v => pure (b + 256 * v)

end Rd

/-- A signed value of `n` bytes. -/
def sx (n v : Nat) : Int := if v < 2 ^ (8 * n - 1) then v else (v : Int) - 2 ^ (8 * n)

/-! ## Prefixes and `ModRM` -/

/-- The prefixes read so far. -/
structure Pfx where
  /-- `66`. -/
  opsz : Bool := false
  /-- `67`. -/
  adsz : Bool := false
  /-- `F2` or `F3`. -/
  rep : Bool := false
  /-- A `REX` byte (`40`–`4F`), when present. -/
  rex : Option Nat := none
  deriving DecidableEq, Repr

def Pfx.w (p : Pfx) : Bool := match p.rex with | some r => r / 8 % 2 == 1 | none => false
def Pfx.r (p : Pfx) : Nat := match p.rex with | some r => r / 4 % 2 | none => 0
def Pfx.b (p : Pfx) : Nat := match p.rex with | some r => r % 2 | none => 0

/-- A legacy prefix byte. -/
def isLegacy (b : Nat) : Bool :=
  b == 0x26 || b == 0x2E || b == 0x36 || b == 0x3E || b == 0x64 || b == 0x65 || b == 0x66 ||
    b == 0x67 || b == 0xF0 || b == 0xF2 || b == 0xF3

/-- A decoded `ModRM` (with its `SIB` and displacement). -/
structure ModRM where
  md : Nat
  reg : Nat
  rm : Nat
  /-- `disp32(%rip)` (`md = 0`, `rm = 5`). -/
  rip : Bool
  disp : Int
  deriving DecidableEq, Repr

/-- The displacement of a memory operand: `0`, `1` or `4` bytes. -/
def dispLen (md rm : Nat) (sibBase : Nat) : Nat :=
  if md = 1 then 1 else if md = 2 then 4 else if md = 0 && (rm == 5 || (rm == 4 && sibBase == 5)) then 4 else 0

/-- Read a `ModRM`, its `SIB` and displacement. -/
def modrm : Rd ModRM :=
  Rd.bind Rd.byte fun m =>
    let md := m / 64
    let reg := m / 8 % 8
    let rm := m % 8
    if md = 3 then Rd.pure ⟨md, reg, rm, false, 0⟩ else
    Rd.bind (if rm = 4 then Rd.byte else Rd.pure 0) fun sib =>
      let n := dispLen md rm (sib % 8)
      Rd.bind (Rd.le n) fun d =>
        Rd.pure ⟨md, reg, rm, md == 0 && rm == 5, sx n d⟩

/-! ## Classification helpers -/

/-- `rax` survives a write to register `idx` (`0`–`15`) of an operand of `byte` width. -/
def keepIfNot (p : Pfx) (byte : Bool) (idx : Nat) : RaxT :=
  if idx = 0 || (byte && p.rex.isNone && idx = 4) then .clobber else .keep

/-- `rax` after a write to the `r/m` operand. -/
def rmDest (p : Pfx) (byte : Bool) (m : ModRM) : RaxT :=
  if m.md = 3 then keepIfNot p byte (m.rm + 8 * p.b) else .keep

/-- `rax` after a write to the `reg` operand. -/
def regDest (p : Pfx) (byte : Bool) (m : ModRM) : RaxT := keepIfNot p byte (m.reg + 8 * p.r)

/-- The operand of an indirect branch. -/
def opnd (p : Pfx) (m : ModRM) : Opnd :=
  if m.md = 3 then .reg (Silmaril.X86.Reg.ofBitVec (BitVec.ofNat 4 (m.rm + 8 * p.b))) else
  if m.rip && !p.adsz then .ripMem m.disp else .mem

def seqI (r : RaxT) : Info := ⟨.seq, r⟩

/-- The size of a `z` immediate (`2` with `66`, else `4`). -/
def immZ (p : Pfx) : Nat := if p.opsz then 2 else 4

/-! ## The maps -/

/-- An instruction with a `ModRM` operand and an immediate of `n` bytes. -/
def withModrm (n : Nat) (f : ModRM → RaxT) : Rd Info :=
  Rd.bind modrm fun m => Rd.bind (Rd.le n) fun _ => Rd.pure (seqI (f m))

/-- An instruction with an immediate of `n` bytes and no `ModRM`. -/
def withImm (n : Nat) (i : Info) : Rd Info := Rd.bind (Rd.le n) fun _ => Rd.pure i

/-- The arithmetic group `00`–`3D` (`op = 8 * k + j`, `j < 6`). -/
def alu (p : Pfx) (op : Nat) : Rd Info :=
  let k := op / 8
  let j := op % 8
  let isCmp := k == 7
  let dst (m : ModRM) : RaxT :=
    if isCmp then .keep else
    -- `xor`/`sub` of a register with itself sets it to zero.
    if (k == 6 || k == 5) && m.md = 3 && m.reg + 8 * p.r = m.rm + 8 * p.b && m.reg + 8 * p.r = 0 &&
        j % 2 == 1 && !p.opsz then .set 0 else
    if j < 2 then rmDest p (j == 0) m else regDest p (j == 2) m
  if j < 4 then withModrm 0 dst
  else if j = 4 then withImm 1 (seqI (if isCmp then .keep else .clobber))
  else withImm (immZ p) (seqI (if isCmp then .keep else .clobber))

/-- The one-byte map, after the prefixes (`p`) and opcode `op`. -/
def map1 (p : Pfx) (op : Nat) : Rd Info :=
  if op < 0x40 then
    (if op % 8 < 6 then alu p op else Rd.fail)
  else if op < 0x50 then Rd.fail
  else if op < 0x58 then Rd.pure (seqI .keep)
  else if op < 0x60 then Rd.pure (seqI (keepIfNot p false (op - 0x58 + 8 * p.b)))
  else if op = 0x63 then withModrm 0 (regDest p false)
  else if op = 0x68 then withImm (immZ p) (seqI .keep)
  else if op = 0x69 then withModrm (immZ p) (regDest p false)
  else if op = 0x6A then withImm 1 (seqI .keep)
  else if op = 0x6B then withModrm 1 (regDest p false)
  else if op < 0x70 then (if op < 0x6C then Rd.fail else Rd.pure ⟨.other, .clobber⟩)
  else if op < 0x80 then Rd.bind Rd.byte fun d => Rd.pure ⟨.jcc (sx 1 d), .keep⟩
  else if op = 0x80 || op = 0x83 then
    withModrm 1 fun m => if m.reg = 7 then .keep else rmDest p (op == 0x80) m
  else if op = 0x81 then withModrm (immZ p) fun m => if m.reg = 7 then .keep else rmDest p false m
  else if op = 0x82 then Rd.fail
  else if op = 0x84 || op = 0x85 then withModrm 0 fun _ => .keep
  else if op = 0x86 || op = 0x87 then withModrm 0 fun m =>
    match rmDest p (op == 0x86) m, regDest p (op == 0x86) m with
    | .keep, .keep => .keep
    | _, _ => .clobber
  else if op = 0x88 || op = 0x89 then withModrm 0 (rmDest p (op == 0x88))
  else if op = 0x8A || op = 0x8B then withModrm 0 (regDest p (op == 0x8A))
  else if op = 0x8C then withModrm 0 (rmDest p false)
  else if op = 0x8D then withModrm 0 (regDest p false)
  else if op = 0x8E then withModrm 0 fun _ => .keep
  else if op = 0x8F then withModrm 0 (rmDest p false)
  else if op = 0x90 then Rd.pure (seqI (if p.b = 1 then .clobber else .keep))
  else if op < 0x98 then Rd.pure (seqI .clobber)
  else if op = 0x9A then Rd.fail
  else if op = 0x9C then Rd.pure (seqI .keep)
  else if op < 0xA0 then Rd.pure (seqI .clobber)
  else if op < 0xA4 then
    withImm (if p.adsz then 4 else 8) (seqI (if op = 0xA2 || op = 0xA3 then .keep else .clobber))
  else if op = 0xA8 then withImm 1 (seqI .keep)
  else if op = 0xA9 then withImm (immZ p) (seqI .keep)
  else if op < 0xB0 then
    -- `movs`, `cmps`, `stos`, `lods`, `scas`: `lods` writes `rax`.
    Rd.pure ⟨if p.rep then .rep else .seq, if op = 0xAC || op = 0xAD then .clobber else .keep⟩
  else if op < 0xB8 then withImm 1 (seqI (keepIfNot p true (op - 0xB0 + 8 * p.b)))
  else if op < 0xC0 then
    let n := if p.w then 8 else immZ p
    Rd.bind (Rd.le n) fun v =>
      Rd.pure (seqI (if op = 0xB8 && p.b = 0 then (if p.opsz then .clobber else .set v)
        else .keep))
  else if op = 0xC0 || op = 0xC1 then withModrm 1 (rmDest p (op == 0xC0))
  else if op = 0xC2 then withImm 2 ⟨.other, .clobber⟩
  else if op = 0xC3 then Rd.pure ⟨.ret, .keep⟩
  else if op = 0xC4 || op = 0xC5 then Rd.fail
  else if op = 0xC6 then withModrm 1 (rmDest p true)
  else if op = 0xC7 then
    Rd.bind modrm fun m =>
      if m.md = 3 && m.reg = 7 then
        Rd.bind (Rd.le (immZ p)) fun _ => Rd.pure ⟨.other, .clobber⟩
      else Rd.bind (Rd.le (immZ p)) fun v =>
        Rd.pure (seqI (if m.md = 3 && m.rm + 8 * p.b = 0 && !p.opsz then
          (if p.w then .set (if v < 2 ^ 31 then v else v + (2 ^ 64 - 2 ^ 32)) else .set v)
          else rmDest p false m))
  else if op = 0xC8 then withImm 3 (seqI .keep)
  else if op = 0xC9 then Rd.pure (seqI .keep)
  else if op = 0xCA then withImm 2 ⟨.other, .clobber⟩
  else if op = 0xCB then Rd.pure ⟨.other, .clobber⟩
  else if op = 0xCC then Rd.pure ⟨.trap, .keep⟩
  else if op = 0xCD then withImm 1 ⟨.sysOther, .clobber⟩
  else if op = 0xCE then Rd.fail
  else if op = 0xCF then Rd.pure ⟨.other, .clobber⟩
  else if op < 0xD4 then withModrm 0 (rmDest p (op == 0xD0 || op == 0xD2))
  else if op < 0xD7 then Rd.fail
  else if op = 0xD7 then Rd.pure (seqI .clobber)
  else if op < 0xE0 then withModrm 0 fun _ => .clobber
  else if op < 0xE4 then Rd.bind Rd.byte fun d => Rd.pure ⟨.jcc (sx 1 d), .keep⟩
  else if op < 0xE8 then withImm 1 ⟨.other, .clobber⟩
  else if op = 0xE8 then
    Rd.bind (Rd.le 4) fun d => Rd.pure (if p.opsz then ⟨.other, .clobber⟩ else ⟨.call (sx 4 d), .keep⟩)
  else if op = 0xE9 then
    Rd.bind (Rd.le 4) fun d => Rd.pure (if p.opsz then ⟨.other, .clobber⟩ else ⟨.jmp (sx 4 d), .keep⟩)
  else if op = 0xEA then Rd.fail
  else if op = 0xEB then Rd.bind Rd.byte fun d => Rd.pure ⟨.jmp (sx 1 d), .keep⟩
  else if op < 0xF0 then Rd.pure ⟨.other, .clobber⟩
  else if op = 0xF1 then Rd.pure ⟨.trap, .keep⟩
  else if op = 0xF4 then Rd.pure ⟨.trap, .keep⟩
  else if op = 0xF5 then Rd.pure (seqI .keep)
  else if op = 0xF6 || op = 0xF7 then
    Rd.bind modrm fun m =>
      let n := if m.reg < 2 then (if op = 0xF6 then 1 else immZ p) else 0
      Rd.bind (Rd.le n) fun _ => Rd.pure (seqI
        (if m.reg < 2 then .keep else if m.reg < 4 then rmDest p (op == 0xF6) m else .clobber))
  else if op < 0xFE then Rd.pure (seqI .keep)
  else if op = 0xFE then withModrm 0 fun m => if m.reg < 2 then rmDest p true m else .clobber
  else if op = 0xFF then
    Rd.bind modrm fun m =>
      if m.reg = 2 then Rd.pure ⟨.callInd (opnd p m), .keep⟩
      else if m.reg = 4 then Rd.pure ⟨.jmpInd (opnd p m), .keep⟩
      else if m.reg = 3 || m.reg = 5 then Rd.pure ⟨.other, .clobber⟩
      else if m.reg = 6 then Rd.pure (seqI .keep)
      else if m.reg = 7 then Rd.fail
      else Rd.pure (seqI (rmDest p false m))
  else Rd.fail

/-- The `0F` map, after `0F` (`op` is the second opcode byte). -/
def map0F (p : Pfx) (op : Nat) : Rd Info :=
  if op = 0x05 then Rd.pure ⟨.syscall, .clobber⟩
  else if op = 0x0B then Rd.pure ⟨.trap, .keep⟩
  else if op = 0x34 then Rd.pure ⟨.sysOther, .clobber⟩
  else if op = 0x07 || op = 0x35 then Rd.pure ⟨.other, .clobber⟩
  else if op = 0x0F || op = 0x04 || op = 0x0A || op = 0x0C || op = 0x24 || op = 0x25 ||
      op = 0x26 || op = 0x27 || op = 0x36 || op = 0x39 || op = 0x3B || op = 0x3C || op = 0x3D ||
      op = 0x3E || op = 0x3F || op = 0x7A || op = 0x7B || op = 0xA6 || op = 0xA7 then Rd.fail
  else if op = 0x06 || op = 0x08 || op = 0x09 || op = 0x0E || op = 0x30 || op = 0x37 || op = 0xAA then
    Rd.pure ⟨.other, .clobber⟩
  else if op = 0x31 || op = 0x32 || op = 0x33 || op = 0xA2 then Rd.pure (seqI .clobber)
  else if op = 0x77 then Rd.pure (seqI .keep)
  else if op = 0xA0 || op = 0xA8 then Rd.pure (seqI .keep)
  else if op = 0xA1 || op = 0xA9 then Rd.pure (seqI .keep)
  else if 0x80 ≤ op && op < 0x90 then
    Rd.bind (Rd.le 4) fun d => Rd.pure (if p.opsz then ⟨.other, .clobber⟩ else ⟨.jcc (sx 4 d), .keep⟩)
  else if 0xC8 ≤ op && op < 0xD0 then Rd.pure (seqI (keepIfNot p false (op - 0xC8 + 8 * p.b)))
  else if 0x20 ≤ op && op < 0x24 then withModrm 0 fun _ => .clobber
  else if op = 0xB9 || op = 0xFF then Rd.bind modrm fun _ => Rd.pure ⟨.trap, .keep⟩
  else if op = 0x0D || (0x18 ≤ op && op < 0x20) then withModrm 0 fun _ => .keep
  else if (0x70 ≤ op && op < 0x74) || op = 0xA4 || op = 0xAC || op = 0xBA || op = 0xC2 ||
      op = 0xC4 || op = 0xC5 || op = 0xC6 then
    withModrm 1 fun m => if op = 0xA4 || op = 0xAC then rmDest p false m
      else if op = 0xBA then (if m.reg = 4 then .keep else rmDest p false m) else .clobber
  else if 0x40 ≤ op && op < 0x50 then withModrm 0 (regDest p false)
  else if 0x90 ≤ op && op < 0xA0 then withModrm 0 (rmDest p true)
  else if op = 0xA3 then withModrm 0 fun _ => .keep
  else if op = 0xAB || op = 0xB3 || op = 0xBB || op = 0xA5 || op = 0xAD then withModrm 0 (rmDest p false)
  else if op = 0xAF || op = 0xB6 || op = 0xB7 || op = 0xBE || op = 0xBF || op = 0xBC || op = 0xBD ||
      op = 0xB8 then withModrm 0 (regDest p (false))
  else withModrm 0 fun _ => .clobber

/-- The `VEX`/`EVEX` operand: a `ModRM`, then an `imm8` for map 3 and the map-1 forms
`70`–`73`, `C2`, `C4`–`C6`. -/
def vexBody (map op : Nat) : Rd Info :=
  if map = 1 && op = 0x77 then Rd.pure (seqI .keep) else
  let imm := map = 3 || (map = 1 && ((0x70 ≤ op && op < 0x74) || op = 0xC2 || op = 0xC4 || op = 0xC5 || op = 0xC6))
  withModrm (if imm then 1 else 0) fun _ => .clobber

/-- `C4`/`C5` (`VEX`) and `62` (`EVEX`), after the escape byte. -/
def vex (esc : Nat) : Rd Info :=
  if esc = 0xC5 then Rd.bind Rd.byte fun _ => Rd.bind Rd.byte fun op => vexBody 1 op
  else if esc = 0xC4 then
    Rd.bind Rd.byte fun b1 => Rd.bind Rd.byte fun _ => Rd.bind Rd.byte fun op =>
      let map := b1 % 32
      if map = 1 || map = 2 || map = 3 then vexBody map op else Rd.fail
  else
    Rd.bind Rd.byte fun p0 => Rd.bind Rd.byte fun _ => Rd.bind Rd.byte fun _ => Rd.bind Rd.byte fun op =>
      let map := p0 % 8
      if map = 1 || map = 2 || map = 3 || map = 5 || map = 6 then vexBody map op else Rd.fail

/-- After the prefixes: `REX`, then the opcode. -/
def afterPfx (p : Pfx) (b : Nat) : Rd Info :=
  if b = 0x0F then
    Rd.bind Rd.byte fun op =>
      if op = 0x38 then Rd.bind Rd.byte fun _ => withModrm 0 fun _ => .clobber
      else if op = 0x3A then Rd.bind Rd.byte fun _ => withModrm 1 fun _ => .clobber
      else map0F p op
  else if (b = 0xC4 || b = 0xC5 || b = 0x62) && p.rex.isNone && !p.opsz && !p.rep then vex b
  else map1 p b

/-- The `REX` byte, if any, then the opcode. -/
def rexThen (p : Pfx) (b : Nat) : Rd Info :=
  if 0x40 ≤ b && b < 0x50 then Rd.bind Rd.byte fun op => afterPfx { p with rex := some b } op
  else afterPfx p b

/-- Legacy prefixes (at most `k`), then the rest. -/
def pfx : Nat → Pfx → Rd Info
  | 0, _ => Rd.fail
  | k + 1, p => Rd.bind Rd.byte fun b =>
    if isLegacy b then
      pfx k { p with opsz := p.opsz || b == 0x66, adsz := p.adsz || b == 0x67,
                     rep := p.rep || b == 0xF2 || b == 0xF3 }
    else rexThen p b

/-- **One instruction.** -/
def instr : Rd Info := pfx 15 {}

/-- Try the prefixes of `w` of lengths `l`, `l + 1`, … (at most `k` of them): the first one that
`instr` reads entirely. -/
def scan (w : List Byte) : Nat → Nat → Option (Info × Nat)
  | 0, _ => none
  | k + 1, l =>
    if l ≤ w.length then
      match instr (w.take l) with
      | some (i, []) => some (i, l)
      | _ => scan w k (l + 1)
    else none

/-- **The decoder**: the information and the length of the shortest prefix (at most 15 bytes)
that `instr` reads entirely. Reading prefixes makes the answer independent of the bytes after the
instruction by construction (`Thms.stable`). -/
def decode (w : List Byte) : Option (Info × Nat) := scan w 15 1

/-- **The flow decoder of x86-64 encodings.** -/
def dec : FlowDec where
  Instr := Info
  decode := decode
  kind := Info.kind
  rax := Info.rax

end Silmaril.X86.Flow.X64
