module

public import Silmaril.Process.Mt.Drf.Defs

/-!
# Litmus tests for the memory-model bridge

A small straight-line language of x86 instructions, run as a `Sys`, and two classic litmus
shapes, each in a racy and a synchronised version:

* **`SB`** (store buffering, Dekker). Thread `0`: `[0] := 1; r0 := [8]`. Thread `1`:
  `[8] := 1; r0 := [0]`. Racy: the stores are plain `mov`s. Locked: the stores are `xchg`.
  The outcome "both loads read `0`" is the x86-TSO weak behaviour.
* **`MP`** (message passing). Thread `0`: `[0] :=nt 1` (data, a non-temporal store), then the
  flag `[8] := 1`. Thread `1`: `r0 := [8]; if r0 = 0 goto end; r1 := [0]`. Racy: the flag is a
  plain `mov`. Locked: the flag is an `xchg`. The outcome `r0 = 1, r1 = 0` is an XL weak
  behaviour (the non-temporal store is overtaken by the flag store).

Addresses `0` and `8` are cells; register `9` is a scratch register for `xchg`.
-/

@[expose] public section

namespace Silmaril.Process.Mt.Drf.Litmus

open Silmaril.Process.Mt.Drf

/-- Instructions. -/
inductive Ins where
  /-- `mov [a], v`. -/
  | st (a v : Nat)
  /-- `movnti [a], v`. -/
  | stnt (a v : Nat)
  /-- `mov r, [a]`. -/
  | ld (r a : Nat)
  | sfence
  | mfence
  /-- `xchg [a], r` with `r = v`: the old value goes to register `r`. -/
  | xchg (r a v : Nat)
  /-- `if reg r = 0 then goto k`. -/
  | brz (r k : Nat)

/-- A thread state: program counter and registers. -/
structure TS where
  pc : Nat
  reg : Nat → Nat

/-- A program: thread and program counter to the instruction there. -/
abbrev Prog := Nat → Nat → Option Ins

/-- Thread-local steps. -/
inductive LLoc (P : Prog) : Nat → TS → Lab → TS → Prop
  | st {t s a v} (h : P t s.pc = some (.st a v)) :
      LLoc P t s (.plain [] [(a, v)] false) ⟨s.pc + 1, s.reg⟩
  | stnt {t s a v} (h : P t s.pc = some (.stnt a v)) :
      LLoc P t s (.plain [] [(a, v)] true) ⟨s.pc + 1, s.reg⟩
  | ld {t s r a} (x : Nat) (h : P t s.pc = some (.ld r a)) :
      LLoc P t s (.plain [(a, x)] [] false) ⟨s.pc + 1, upd s.reg r x⟩
  | sfence {t s} (h : P t s.pc = some .sfence) : LLoc P t s .sfence ⟨s.pc + 1, s.reg⟩
  | brz {t s r k} (h : P t s.pc = some (.brz r k)) :
      LLoc P t s (.plain [] [] false) ⟨if s.reg r = 0 then k else s.pc + 1, s.reg⟩

/-- Synchronising steps. -/
inductive LSync (P : Prog) : Nat → (Nat → TS) → List (Nat × Nat) → List (Nat × Nat) →
    (Nat → TS) → Prop
  | mfence {t ts} (h : P t (ts t).pc = some .mfence) :
      LSync P t ts [] [] (upd ts t ⟨(ts t).pc + 1, (ts t).reg⟩)
  | xchg {t ts r a v} (x : Nat) (h : P t (ts t).pc = some (.xchg r a v)) :
      LSync P t ts [(a, x)] [(a, v)] (upd ts t ⟨(ts t).pc + 1, upd (ts t).reg r x⟩)

/-- The program as a system. -/
def sys (P : Prog) : Sys := ⟨TS, LLoc P, LSync P⟩

/-- The start: every thread at `0` with zero registers, memory all `0`. -/
def init (P : Prog) : Cfg (sys P) := ⟨fun _ => ⟨0, fun _ => 0⟩, fun _ => 0⟩

/-! ## SB -/

/-- `SB`; `lk` makes the stores `xchg`s. -/
def sb (lk : Bool) : Prog
  | 0, 0 => some (if lk then .xchg 9 0 1 else .st 0 1)
  | 0, 1 => some (.ld 0 8)
  | 1, 0 => some (if lk then .xchg 9 8 1 else .st 8 1)
  | 1, 1 => some (.ld 0 0)
  | _, _ => none

/-- `SB`'s weak outcome: both threads finished, both loads read `0`. -/
def sbWeak (ts : Nat → TS) : Prop :=
  (ts 0).pc = 2 ∧ (ts 1).pc = 2 ∧ (ts 0).reg 0 = 0 ∧ (ts 1).reg 0 = 0

/-! ## MP -/

/-- `MP`; `lk` makes the flag store an `xchg`. -/
def mp (lk : Bool) : Prog
  | 0, 0 => some (.stnt 0 1)
  | 0, 1 => some (if lk then .xchg 9 8 1 else .st 8 1)
  | 1, 0 => some (.ld 0 8)
  | 1, 1 => some (.brz 0 3)
  | 1, 2 => some (.ld 1 0)
  | _, _ => none

/-- `MP`'s weak outcome: thread `1` finished, it saw the flag but not the data. -/
def mpWeak (ts : Nat → TS) : Prop := (ts 1).pc = 3 ∧ (ts 1).reg 0 = 1 ∧ (ts 1).reg 1 = 0

/-- Ownership in locked `MP`: the data cell `0` belongs to thread `0` until its `xchg` of the
flag, then to thread `1` once it has read the flag set. -/
def mpOwn (C : Cfg (sys (mp true))) : Own := fun t a =>
  a = 0 ∧ ((t = 0 ∧ (C.ts 0).pc < 2) ∨ (t = 1 ∧ 1 ≤ (C.ts 1).pc ∧ (C.ts 1).reg 0 ≠ 0))

/-- Locked `MP`'s certificate invariant. -/
def MpR (C : Cfg (sys (mp true))) (o : Own) : Prop :=
  o = mpOwn C ∧ (C.mem 8 ≠ 0 → 2 ≤ (C.ts 0).pc) ∧
  (1 ≤ (C.ts 1).pc → (C.ts 1).reg 0 ≠ 0 → 2 ≤ (C.ts 0).pc) ∧
  ((C.ts 1).pc = 2 → (C.ts 1).reg 0 ≠ 0)

end Silmaril.Process.Mt.Drf.Litmus
