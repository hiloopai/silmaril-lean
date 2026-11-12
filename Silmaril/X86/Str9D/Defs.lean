module

public import Silmaril.X86.Str9FsXN.Defs

/-!
# `Str9D`: `Str9FsXN` with the direction flag, `std`, `cld` and `rep movsb`

Every machine of the `Str9` tower assumes that RFLAGS.DF is clear, so its string forms always
increment `rsi` and `rdi`. The System V ABI requires DF to be clear at function entry and exit,
but a function may set it in between. musl's `memmove` does this for an overlapping copy to a
higher address:

```
std                  FD
rep movsb            F3 A4      (rsi, rdi at the last byte; copies downwards)
cld                  FC
```

gzip's `gzprintf`/`gzvprintf` reach it through `gz_write`'s `memmove`. `Str9D` models this
sequence.

**State.** `DState` is an `XState` (`x`) and the direction flag (`df`).

**Step.** When `df = false` the step is `Str9FsXN.step` (DF unchanged), and on bytes that
`Str9FsXN` rejects, `std`, `cld` or a forward `rep movsb`. When `df = true` the string forms run
**downwards**: where `Ext8` and `Ext9` reject the fetch window and it holds a string form (`A4`
`movsb`, `F3 A4` `rep movsb`, `F3 48 A5` `rep movsq`, `F3 48 AB` `rep stosq`, `F3 AB` `rep
stosd`), the form decrements its pointers by the element size. On every other instruction the
step is `Str9FsXN.step`, then `std`/`cld`.

| Form | Bytes | `DForm` |
| --- | --- | --- |
| `std` (DF := 1) | `FD` | `std` |
| `cld` (DF := 0) | `FC` | `cld` |
| `movsb`, `rep movsb`, `rep movsq`, `rep stosq`, `rep stosd` with the direction of DF | `A4`, `F3 A4`, `F3 48 A5`, `F3 48 AB`, `F3 AB` | `str` |

**Relation to `Str9FsXN`.** This is **not** an `Isa.Extends` lens extension, and cannot be one.
With DF set, `Str9FsXN`'s forward string steps are wrong, so not every `Str9FsXN` step is a
step here. Instead (`Thms`):
* every `Str9FsXN` step from a DF-clear state is a step that keeps DF clear (`step_of_lower`);
* so every `Str9FsXN` run lifts from a DF-clear state (`run_of_lower`);
* `std` and `cld` are the only steps that change DF.

Without `std`, DF therefore stays clear and the two machines agree.

**Semantics** (SDM Vol. 2, MOVS/STOS and REP). The string forms follow `Str9`:
* one element per step, so a `rep` form with `rcx = 0` only advances RIP;
* an element reads, then writes, and faults (no step) before any register changes;
* RIP stays on a `rep` instruction until `rcx` reaches `0`.

With DF set, the pointers move by `-1`, `-8` or `-4` (wrapping at `2^64`). `std`/`cld` change no
other flag. `rep movsb` copies one byte per step, as `Str9V`'s forward form does.

A handwritten model, **trusted**. `Str9D/Vectors.lean` compares `std; rep movsb; cld` and the
single string forms with an Intel Core i7-8700, in both directions.
-/

@[expose] public section

namespace Silmaril.X86.Str9D

open Silmaril.X86 (Reg Word State Byte MState fetchWindow maxInstrLength)
open Silmaril.X86.Ext (Result loadN storeN)
open Silmaril.X86.Sse9 (XState)
open Silmaril.Process (Memory)

/-! ## State -/

/-- **The state**: an `XState` and RFLAGS.DF. -/
structure DState where
  x : XState
  df : Bool

/-! ## The forms -/

/-- A string form, which runs in the direction of DF. -/
inductive Str where
  /-- `movsb` (`A4`). -/
  | movsb
  /-- `rep movsb` (`F3 A4`). -/
  | repMovsb
  /-- `rep movsq` (`F3 48 A5`). -/
  | repMovsq
  /-- `rep stosq` (`F3 48 AB`). -/
  | repStosq
  /-- `rep stosd` (`F3 AB`). -/
  | repStosd
  deriving DecidableEq, Repr

/-- The forms of `Str9D`. -/
inductive DForm where
  | std
  | cld
  | str (i : Str)
  deriving DecidableEq, Repr

/-- Decode a string form. -/
def decodeStr : List Byte → Option (Str × Nat)
  | 0xA4 :: _ => some (.movsb, 1)
  | 0xF3 :: 0xA4 :: _ => some (.repMovsb, 2)
  | 0xF3 :: 0x48 :: 0xA5 :: _ => some (.repMovsq, 3)
  | 0xF3 :: 0x48 :: 0xAB :: _ => some (.repStosq, 3)
  | 0xF3 :: 0xAB :: _ => some (.repStosd, 2)
  | _ => none

/-- Decode a form. -/
def decodeD : List Byte → Option (DForm × Nat)
  | 0xFD :: _ => some (.std, 1)
  | 0xFC :: _ => some (.cld, 1)
  | w => (decodeStr w).map fun (i, n) => (.str i, n)

/-- Fetch a string form at an address (`some none`: not executable). -/
def fetchStr (memory : Memory) (address : Nat) : Option (Option (Str × Nat)) :=
  (decodeStr (fetchWindow memory maxInstrLength address)).map fun (i, n) =>
    if memory.Permitted .execute address n then some (i, n) else none

/-- Fetch a form at an address (`some none`: not executable). -/
def fetchD (memory : Memory) (address : Nat) : Option (Option (DForm × Nat)) :=
  (decodeD (fetchWindow memory maxInstrLength address)).map fun (i, n) =>
    if memory.Permitted .execute address n then some (i, n) else none

/-! ## Semantics -/

/-- The element size of a string form, in bytes. -/
def Str.size : Str → Nat
  | .movsb | .repMovsb => 1
  | .repMovsq | .repStosq => 8
  | .repStosd => 4

/-- The form repeats (`rep`). -/
def Str.rep : Str → Bool
  | .movsb => false
  | _ => true

/-- The form copies from `[rsi]` (MOVS) rather than storing the accumulator (STOS). -/
def Str.src : Str → Bool
  | .repStosq | .repStosd => false
  | _ => true

/-- The pointer step: `+size` with DF clear, `-size` with DF set. -/
def delta (df : Bool) (size : Nat) : Word :=
  if df then 0 - BitVec.ofNat 64 size else BitVec.ofNat 64 size

/-- The core after one element: the pointers moved by `delta`; for a `rep` form, `rcx`
decreased and RIP on the instruction unless `rcx` reaches `0`. -/
def elemCore (i : Str) (df : Bool) (s : State) (next : Word) : State :=
  let d := delta df i.size
  let t := (if i.src then s.write .rsi (s.read .rsi + d) else s).write .rdi (s.read .rdi + d)
  if i.rep then
    let t := t.write .rcx (s.read .rcx - 1)
    { t with rip := if s.read .rcx - 1 = 0 then next else s.rip }
  else { t with rip := next }

/-- **One step of a string form** in the direction `df`. -/
def execStr (i : Str) (df : Bool) (s : State) (memory : Memory) (next : Word) : Result :=
  if i.rep ∧ s.read .rcx = 0 then .ok { s with rip := next } memory
  else
    let v : Option Word :=
      if i.src then loadN memory (s.read .rsi) i.size
      else some (if i.size = 8 then s.read .rax else (s.read .rax).setWidth 32 |>.setWidth 64)
    match v with
    | none => .dataFault
    | some v =>
      match storeN memory (s.read .rdi) i.size v with
      | none => .dataFault
      | some memory' => .ok (elemCore i df s next) memory'

/-- A core result with the XMM file kept and DF set to `df`. -/
def keep (d : DState) (df : Bool) (r : Result) : Option DState :=
  (Silmaril.X86.Open.ofResult r).map fun m' => ⟨⟨m', d.x.xmm⟩, df⟩

/-- Execute a form. -/
def execD (i : DForm) (d : DState) (n : Nat) : Option DState :=
  let next := d.x.m.core.rip + BitVec.ofNat 64 n
  match i with
  | .std => some ⟨⟨⟨{ d.x.m.core with rip := next }, d.x.m.memory⟩, d.x.xmm⟩, true⟩
  | .cld => some ⟨⟨⟨{ d.x.m.core with rip := next }, d.x.m.memory⟩, d.x.xmm⟩, false⟩
  | .str i => keep d d.df (execStr i d.df d.x.m.core d.x.m.memory next)

/-! ## Step -/

/-- `Str9FsXN.step` with DF kept, then a form on bytes it rejects. -/
def lowerThen (d : DState) : Option DState :=
  match Silmaril.X86.Str9FsXN.step d.x with
  | some y => some ⟨y, d.df⟩
  | none =>
    match fetchD d.x.m.memory d.x.m.core.rip.toNat with
    | some (some (i, n)) => execD i d n
    | _ => none

/-- **One step.** With DF clear: `lowerThen`. With DF set: a string form where `Ext8` and
`Ext9` reject the fetch window (downwards), else `lowerThen`. -/
def step (d : DState) : Option DState :=
  if d.df then
    match Silmaril.X86.Ext8.fetch d.x.m.memory d.x.m.core.rip.toNat with
    | .inl .undecodable =>
      match Silmaril.X86.Ext9.fetchNew d.x.m.memory d.x.m.core.rip.toNat with
      | none =>
        match fetchStr d.x.m.memory d.x.m.core.rip.toNat with
        | some (some (i, n)) =>
          keep d true (execStr i true d.x.m.core d.x.m.memory
            (d.x.m.core.rip + BitVec.ofNat 64 n))
        | some none => none
        | none => lowerThen d
      | _ => lowerThen d
    | _ => lowerThen d
  else lowerThen d

end Silmaril.X86.Str9D
