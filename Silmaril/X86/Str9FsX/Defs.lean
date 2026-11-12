module

public import Silmaril.X86.Str9Fs.Defs
public import Silmaril.X86.Sse9.Defs

/-!
# `Str9FsX`: `Str9Fs` with the XMM file, silmaril's SSE subset and `rep stosd`

The glibc functions still blocked on `Str9Fs` mostly need SSE2 data movement: the varargs prologue
of `printf`, `scanf`, `__printf_chk` and `error` saves `xmm0`–`xmm7` with `movaps`, and
`__libc_sigaction` and `pthread_sigmask` copy signal sets with `movdqu`. silmaril's `Sse9` has
these forms and their semantics over `XState` (an `MState` beside sixteen XMM registers).
`abort` also needs `rep stos` at 32 bits.

`Str9FsX` stacks them onto `Str9Fs`, on `Sse9`'s state `XState`, as **new forms on bytes the
lower decoders reject**. The fetch chain is `Ext8` → `Ext9` → string forms → `Str9Fs`'s
atomic and FS forms → `Sse9`'s SSE forms → `rep stosd`. Integer steps keep the XMM file.
`Thms` proves both conservative extensions: `Str9Fs` along the lens `x ↦ x.m`, with the XMM
file as the frame, and `Sse9` on the same states. The second holds because no lower decoder
reads an SSE form: the SSE forms are `0F`-escaped without an FS override, the string forms
start with `A4` or `F3 48`, and `Atomic9`'s two-byte opcodes are `C1`, `B1`, `B0`, `BA` and
`AE`.

**`rep stosd`** (`F3 AB`, no REX.W) is `Str9`'s `rep stosq` at four bytes: with `rcx = 0` it
only advances `rip`. Otherwise one step stores `eax` at `rdi`, adds 4 to `rdi`, subtracts 1
from `rcx`, and leaves `rip` on the instruction unless `rcx` reaches `0`. DF is clear, as in
`Str9`.

The `SegVC` machine `isa` has the integer instructions (`Str9Fs`'s and `rep stosd`). The SSE
forms have their own listing law (`Thms.step_of_listed_sse`), as in `Sse9`, because a
`SegVC` instruction sees only the core and the memory.
-/

@[expose] public section

namespace Silmaril.X86.Str9FsX

open Silmaril.X86 (Reg Word State Byte MState fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Result storeN)
open Silmaril.X86.Sse9 (XState XFile XResult)
open Silmaril.Process (Memory)

/-! ## `rep stosd` -/

/-- `rep stosd` is `F3 AB`. -/
def decodeStosd : List Byte → Option Nat
  | 0xF3 :: 0xAB :: _ => some 2
  | _ => none

/-- The core after one element: `rdi + 4`, `rcx - 1`, `rip` on the instruction unless `rcx`
reaches `0`. -/
def stosdCore (s : State) (next : Word) : State :=
  let t := (s.write .rdi (s.read .rdi + 4)).write .rcx (s.read .rcx - 1)
  { t with rip := if s.read .rcx - 1 = 0 then next else s.rip }

/-- One step of `rep stosd`. -/
def execStosd (s : State) (memory : Memory) (next : Word) : Result :=
  if s.read .rcx = 0 then .ok { s with rip := next } memory
  else
    match storeN memory (s.read .rdi) 4 ((s.read .rax).setWidth 32 |>.setWidth 64) with
    | none => .dataFault
    | some memory' => .ok (stosdCore s next) memory'

/-! ## Listing decoders -/

/-- `Atomic9`'s parser rejects (and so rejects every extension). -/
def atomicBad (w : List Byte) : Bool :=
  match Silmaril.X86.Atomic9.pNew w with | .bad => true | _ => false

/-- The FS-form parser rejects. -/
def fsBad (w : List Byte) : Bool :=
  match Silmaril.X86.Str9Fs.pFs w with | .bad => true | _ => false

/-- The SSE parser rejects. -/
def sseBad (w : List Byte) : Bool :=
  match Silmaril.X86.Sse9.pSse w with | .bad => true | _ => false

/-- The listing decoder of an SSE form: `Sse9.decodeL`, and no string, atomic or FS form
reads the slice. -/
def decodeSseL (w : List Byte) : Option (Silmaril.X86.Sse9.Instr × Nat) :=
  match Silmaril.X86.Sse9.decodeL w with
  | some (i, n) =>
    if Silmaril.X86.Str9Fs.strBad w = true ∧ atomicBad w = true ∧ fsBad w = true then
      some (i, n) else none
  | none => none

/-- The listing decoder of `rep stosd`: the slice is `F3 AB`, and every other decoder rejects
it. -/
def decodeStosdL (w : List Byte) : Option Nat :=
  if decodeStosd w = some 2 ∧ Silmaril.X86.Ext.decode w = none ∧
      Silmaril.X86.Open9.newBad w = true ∧ Silmaril.X86.Open9.rawNotEof w = true ∧
      Silmaril.X86.Str9.ext9Bad w = true ∧ Silmaril.X86.Str9Fs.strBad w = true ∧
      atomicBad w = true ∧ fsBad w = true ∧ sseBad w = true then some 2 else none

/-! ## The integer instructions -/

/-- The integer instructions of the machine: `Str9Fs`'s, and `rep stosd`. -/
inductive Instr where
  | base (i : Silmaril.X86.Str9Fs.Instr)
  | stosd
  deriving DecidableEq, Repr

/-- The listing decoder of the integer instructions. -/
def decode (w : List Byte) : Option (Instr × Nat) :=
  match Silmaril.X86.Str9Fs.decode w with
  | some (i, n) => some (.base i, n)
  | none => (decodeStosdL w).map fun n => (.stosd, n)

/-- The executor of the integer instructions. -/
def exec (i : Instr) (s : State) (memory : Memory) (length : Nat) : Result :=
  match i with
  | .base i => Silmaril.X86.Str9Fs.exec i s memory length
  | .stosd => execStosd s memory (s.rip + BitVec.ofNat 64 length)

/-! ## Fetch and step -/

/-- Fetch `rep stosd`. -/
def fetchStosd (memory : Memory) (address : Nat) : Option (Option Nat) :=
  (decodeStosd (fetchWindow memory maxInstrLength address)).map fun n =>
    if memory.Permitted .execute address n then some n else none

/-- An integer result with the XMM file kept. -/
def keep (x : XState) (r : Result) : Option XState :=
  (Silmaril.X86.Open.ofResult r).map fun m' => ⟨m', x.xmm⟩

/-- **One step**: the `Str9Fs` chain with the XMM file kept, then an SSE form, then
`rep stosd`. -/
def step (x : XState) : Option XState :=
  match Silmaril.X86.Ext8.fetch x.m.memory x.m.core.rip.toNat with
  | .inl .undecodable =>
    match Silmaril.X86.Ext9.fetchNew x.m.memory x.m.core.rip.toNat with
    | some (some (i, n)) =>
      keep x (Silmaril.X86.Ext9.execNew i x.m.core x.m.memory (x.m.core.rip + BitVec.ofNat 64 n))
    | some none => none
    | none =>
      match Silmaril.X86.Str9.fetchStr x.m.memory x.m.core.rip.toNat with
      | some (some (i, n)) =>
        keep x (Silmaril.X86.Str9.execStr i x.m.core x.m.memory (x.m.core.rip + BitVec.ofNat 64 n))
      | some none => none
      | none =>
        match Silmaril.X86.Str9Fs.fetchNew x.m.memory x.m.core.rip.toNat with
        | some (some (i, n)) => keep x (Silmaril.X86.Str9Fs.execNew i x.m.core x.m.memory n)
        | some none => none
        | none =>
          match Silmaril.X86.Sse9.fetchSse x.m.memory x.m.core.rip.toNat with
          | some (some (i, n)) =>
            (Silmaril.X86.Sse9.exec i x.m.core x.xmm x.m.memory
              (x.m.core.rip + BitVec.ofNat 64 n)).toOption
          | some none => none
          | none =>
            match fetchStosd x.m.memory x.m.core.rip.toNat with
            | some (some n) =>
              keep x (execStosd x.m.core x.m.memory (x.m.core.rip + BitVec.ofNat 64 n))
            | _ => none
  | _ => (Silmaril.X86.Open.step x.m).map fun m' => ⟨m', x.xmm⟩

end Silmaril.X86.Str9FsX
