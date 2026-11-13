module

public import Silmaril.X86.Str9V.Defs

/-!
# `Str9D`: `Str9V` with the direction flag, `std`/`cld` and backward string forms

Every machine of the `Str9` tower assumes the direction flag (DF, RFLAGS bit 10) clear: the
System V ABI requires it on function entry and exit, `Silmaril.X86.State` has no DF bit, the
string forms move their pointers upwards, and `std` is decoded by no layer. glibc breaks the
assumption inside one function: `__memmove_erms` copies an overlapping buffer downwards with

    lea -1(%rdi,%rcx), %rdi ; lea -1(%rsi,%rcx), %rsi ; std ; rep movsb ; cld ; ret

`Str9D` models exactly this.

**State.** `DState` is a `Str9V.VState` (`v`) and the direction flag (`df`).

**Forms.** `std` (`FD`) sets DF and `cld` (`FC`) clears it; both only advance RIP otherwise
(they are not decoded by any lower layer). The string forms of the tower are, as encoded
there,

| form | bytes | element | layer that decodes it forwards |
| --- | --- | --- | --- |
| `movsb` | `A4` | 1 byte, no `rep` | `Str9` |
| `rep movsb` | `F3 A4` | 1 byte | `Str9V` |
| `rep movsq` | `F3 48 A5` | 8 bytes | `Str9` |
| `rep stosb` | `F3 AA` | 1 byte | `Str9V` |
| `rep stosd` | `F3 AB` | 4 bytes | `Str9FsX` |
| `rep stosq` | `F3 48 AB` | 8 bytes | `Str9` |

**Step.** With DF clear, `step` is `Str9V.step` (DF kept), and on bytes `Str9V` does not step
`std` or `cld`. With DF set, bytes whose first opcode byte after the legacy and REX prefixes
is a string opcode (`6C`–`6F`, `A4`–`A7`, `AA`–`AF`; `strClaims`) are this layer's: one of the
six forms above, executed **downwards** (each pointer decreases by the element size after
the element), and no step for any other string instruction (`cmps`, `scas`, `lods`, `ins`,
`outs`, other prefixes and widths). Every other instruction reads no DF and is `Str9V.step`
again. The element-by-element reading, the `rcx = 0` case, the fault-before-update rule and
the 64-bit address size are `Str9`'s (see its documentation); `execStr false` is the forward
reading of the same forms.

**What lifts.** A lower machine's step is a step here only from a state with DF clear, so
there is no `Isa.Extends` from `Str9V` (whose lens would have to hold at DF-set states too).
Instead `Thms.step_of_str9v`, `Thms.run_of_str9v` and `Thms.reaches_of_str9v` lift every
`Str9V` step and run from DF clear, and `Thms.isa` lists `Str9V`'s integer instructions that
are not string forms, whose law holds at either DF value.

This is a handwritten model of the SDM (Vol. 1 §3.4.3.1, Vol. 2 `MOVS`, `STOS`, `REP`,
`STD`, `CLD`); `Str9D.Vectors` compares it with hardware.
-/

@[expose] public section

namespace Silmaril.X86.Str9D

open Silmaril.X86 (Reg Word State Byte fetchWindow maxInstrLength)
open Silmaril.X86.Ext (loadN storeN)
open Silmaril.X86.Str9V (VState)
open Silmaril.Process (Memory)

/-! ## State -/

/-- **The state**: a `Str9V` state and the direction flag. -/
structure DState where
  v : VState
  df : Bool

/-- The core. -/
abbrev DState.core (d : DState) : State := d.v.g.x.m.core

/-- The memory. -/
abbrev DState.memory (d : DState) : Memory := d.v.g.x.m.memory

/-- Replace the core and the memory, keeping the vector registers, the ghost state and DF. -/
def DState.upd (d : DState) (c : State) (memory : Memory) : DState :=
  ⟨Str9V.coreV d.v c memory, d.df⟩

/-! ## Forms -/

/-- The string forms of the tower. -/
inductive Str where
  | movsb
  | repMovsb
  | repMovsq
  | repStosb
  | repStosd
  | repStosq
  deriving DecidableEq, Repr

/-- The element size in bytes. -/
def Str.width : Str → Nat
  | .movsb | .repMovsb | .repStosb => 1
  | .repStosd => 4
  | .repMovsq | .repStosq => 8

/-- A move (reads `[rsi]`) rather than a store of `rax`. -/
def Str.src : Str → Bool
  | .movsb | .repMovsb | .repMovsq => true
  | _ => false

/-- A `rep` form (counts `rcx` down). -/
def Str.rep : Str → Bool
  | .movsb => false
  | _ => true

/-- The encoding of a string form. -/
def Str.bytes : Str → List Byte
  | .movsb => [0xA4]
  | .repMovsb => [0xF3, 0xA4]
  | .repMovsq => [0xF3, 0x48, 0xA5]
  | .repStosb => [0xF3, 0xAA]
  | .repStosd => [0xF3, 0xAB]
  | .repStosq => [0xF3, 0x48, 0xAB]

/-- Decode a string form: the form and its length. -/
def decodeStr : List Byte → Option (Str × Nat)
  | 0xA4 :: _ => some (.movsb, 1)
  | 0xF3 :: 0xA4 :: _ => some (.repMovsb, 2)
  | 0xF3 :: 0x48 :: 0xA5 :: _ => some (.repMovsq, 3)
  | 0xF3 :: 0xAA :: _ => some (.repStosb, 2)
  | 0xF3 :: 0xAB :: _ => some (.repStosd, 2)
  | 0xF3 :: 0x48 :: 0xAB :: _ => some (.repStosq, 3)
  | _ => none

/-- Decode `std` (`true`) or `cld` (`false`). -/
def decodeFlag : List Byte → Option (Bool × Nat)
  | 0xFD :: _ => some (true, 1)
  | 0xFC :: _ => some (false, 1)
  | _ => none

/-- A legacy prefix (`F0 F2 F3`, segment overrides, `66`, `67`) or a REX byte. -/
def isPrefix (b : Byte) : Bool :=
  b = 0xF0#8 || b = 0xF2#8 || b = 0xF3#8 || b = 0x2E#8 || b = 0x36#8 || b = 0x3E#8 ||
    b = 0x26#8 || b = 0x64#8 || b = 0x65#8 || b = 0x66#8 || b = 0x67#8 ||
    (b >>> 4) = 0x4#8

/-- A one-byte string opcode: `ins`/`outs` (`6C`–`6F`), `movs`/`cmps` (`A4`–`A7`),
`stos`/`lods`/`scas` (`AA`–`AF`). -/
def isStrOpcode (b : Byte) : Bool :=
  (0x6C#8 ≤ b && b ≤ 0x6F#8) || (0xA4#8 ≤ b && b ≤ 0xA7#8) || (0xAA#8 ≤ b && b ≤ 0xAF#8)

/-- **The bytes may be a string instruction**: the first byte after the prefixes is a string
opcode, or the bytes end before one (so a `false` stays `false` whatever bytes follow). -/
def strClaims : List Byte → Bool
  | [] => true
  | b :: t => if isPrefix b then strClaims t else isStrOpcode b

/-! ## Semantics -/

/-- The pointer step of an element of `k` bytes: `+k` forwards, `-k` with DF set. -/
def delta (back : Bool) (k : Nat) : Word :=
  if back then 0 - BitVec.ofNat 64 k else BitVec.ofNat 64 k

/-- **One step of a string form** in the direction `back`, on a core and a memory, given the
address of the next instruction: a `rep` form with `rcx = 0` only advances RIP; otherwise
one element is read (`[rsi]`, or the low bytes of `rax`) and stored at `[rdi]`, then `rdi`
(and `rsi` for a move) move by `delta back k` and a `rep` form decreases `rcx`, staying on
the instruction unless the new `rcx` is `0`. A fault leaves no step. -/
def execStr (back : Bool) (f : Str) (s : State) (memory : Memory) (next : Word) :
    Option (State × Memory) :=
  if f.rep ∧ s.read .rcx = 0 then some ({ s with rip := next }, memory)
  else
    let k := f.width
    let val : Option Word :=
      if f.src then loadN memory (s.read .rsi) k
      else some (((s.read .rax).setWidth (8 * k)).setWidth 64)
    match val with
    | none => none
    | some w =>
      match storeN memory (s.read .rdi) k w with
      | none => none
      | some memory' =>
        let δ := delta back k
        let t := ((if f.src then s.write .rsi (s.read .rsi + δ) else s).write .rdi
          (s.read .rdi + δ))
        let t := if f.rep then t.write .rcx (s.read .rcx - 1) else t
        let rip := if f.rep ∧ s.read .rcx - 1 ≠ 0 then s.rip else next
        some ({ t with rip := rip }, memory')

/-! ## The listing decoders -/

/-- `Str9V`'s own parser rejects the slice (stable under appending). -/
def vBad (w : List Byte) : Bool :=
  match Str9V.pNew w with
  | .bad => true
  | _ => false

/-- `rep stosd` (`F3 AB`) does not start with this byte (`Str9G.stosdBad` asks for two bytes). -/
def stosdNo : List Byte → Bool
  | [] => false
  | b :: _ => b != 0xF3#8

/-- **No layer of `Str9V` reads the slice**, in a way no following byte changes: the
conditions of `Str9V.decodeL` (with `stosdNo` for `Str9G.stosdBad`) and `Str9V`'s own
parser rejecting. Checked by `decide`. -/
def lowerBad (w : List Byte) : Bool :=
  decide (Silmaril.X86.Ext.decode w = none) && Silmaril.X86.Open9.newBad w &&
    Silmaril.X86.Open9.rawNotEof w && Silmaril.X86.Str9.ext9Bad w &&
    Silmaril.X86.Str9Fs.strBad w && Silmaril.X86.Str9FsX.atomicBad w &&
    Silmaril.X86.Str9FsX.fsBad w && Silmaril.X86.Str9FsX.sseBad w &&
    stosdNo w && Str9V.gBad w && vBad w

/-- The listing decoder of the machine's `SegVC` instance: `Str9FsX`'s integer instructions
that are not string forms (`strClaims` false), of at most 15 bytes. Their meaning reads no
DF. -/
def decode (w : List Byte) : Option (Silmaril.X86.Str9FsX.Instr × Nat) :=
  match Silmaril.X86.Str9FsX.decode w with
  | some (i, n) => if strClaims w = false ∧ n ≤ maxInstrLength then some (i, n) else none
  | none => none

/-! ## Fetch and step -/

/-- Fetch a string form (`none`: not one; `some none`: not executable). -/
def fetchStr (memory : Memory) (address : Nat) : Option (Option (Str × Nat)) :=
  (decodeStr (fetchWindow memory maxInstrLength address)).map fun (i, n) =>
    if memory.Permitted .execute address n then some (i, n) else none

/-- Fetch `std` or `cld`. -/
def fetchFlag (memory : Memory) (address : Nat) : Option (Option (Bool × Nat)) :=
  (decodeFlag (fetchWindow memory maxInstrLength address)).map fun (b, n) =>
    if memory.Permitted .execute address n then some (b, n) else none

/-- `Str9V`'s step, DF kept; on bytes it does not step, `std` or `cld`. -/
def stepLower (d : DState) : Option DState :=
  match Str9V.step d.v with
  | some v' => some ⟨v', d.df⟩
  | none =>
    match fetchFlag d.memory d.core.rip.toNat with
    | some (some (b, n)) =>
      some ⟨Str9V.coreV d.v { d.core with rip := d.core.rip + BitVec.ofNat 64 n } d.memory, b⟩
    | _ => none

/-- **One step.** With DF set, a string form is executed downwards and any other string
instruction has no step; everything else is `stepLower`. -/
def step (d : DState) : Option DState :=
  if d.df && strClaims (fetchWindow d.memory maxInstrLength d.core.rip.toNat) then
    match fetchStr d.memory d.core.rip.toNat with
    | some (some (f, n)) =>
      (execStr true f d.core d.memory (d.core.rip + BitVec.ofNat 64 n)).map fun (c, m) => d.upd c m
    | _ => none
  else stepLower d

end Silmaril.X86.Str9D
