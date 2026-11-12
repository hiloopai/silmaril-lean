module

public import Silmaril.X86.Str9D.Defs

/-!
# `Str9D`: agreement with `Str9FsXN` while DF is clear, `std` and `cld`

* `step_of_lower`, `run_of_lower`: **from a DF-clear state, every `Str9FsXN` step or run is a
  step or run here that keeps DF clear** (the `XState` is the same). This is the conditional
  form of an `Isa.Extends` lens (see the module documentation of `Str9D.Defs` for why the
  unconditional one cannot hold).
* `step_eq_lowerThen`: where no string form is fetched, the step is `lowerThen` whatever DF is.
* `step_std`, `step_cld`: on bytes `Str9FsXN` rejects, `FD` sets DF and `FC` clears it, and
  nothing else changes but RIP.
* Kernel-checked vectors at the end: decoding, and the downward and upward elements.
-/

@[expose] public section

namespace Silmaril.X86.Str9D

open Silmaril.X86 (State MState Word Byte)
open Silmaril.X86.Sse9 (XState)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (run)

/-- **Every `Str9FsXN` step from a DF-clear state is a step**, and DF stays clear. -/
theorem step_of_lower {x y : XState} (h : Str9FsXN.step x = some y) :
    step ⟨x, false⟩ = some ⟨y, false⟩ := by
  simp [step, lowerThen, h]

/-- **Every `Str9FsXN` run from a DF-clear state is a run of the same length**, ending with DF
clear. -/
theorem run_of_lower (n : Nat) {x y : XState} (h : run Str9FsXN.step n x = some y) :
    run step n ⟨x, false⟩ = some ⟨y, false⟩ := by
  induction n generalizing x with
  | zero => simp only [Silmaril.Machine.Execution.run_zero, Option.some.injEq] at h ⊢; rw [h]
  | succ n ih =>
    rw [Silmaril.Machine.Execution.run_succ] at h ⊢
    cases hs : Str9FsXN.step x with
    | none => rw [hs] at h; cases h
    | some x' => rw [hs] at h; rw [step_of_lower hs]; exact ih h

/-- Where no string form is fetched, the step is `lowerThen`, whatever DF is. -/
theorem step_eq_lowerThen {d : DState} (h : fetchStr d.x.m.memory d.x.m.core.rip.toNat = none) :
    step d = lowerThen d := by
  unfold step
  split
  · split
    · split
      · rw [h]
      · rfl
    · rfl
  · rfl

theorem decodeD_of_decodeStr {w : List Byte} {j : Str} {m : Nat} (h : decodeStr w = some (j, m)) :
    decodeD w = some (.str j, m) := by
  unfold decodeStr at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    (try obtain ⟨rfl, rfl⟩ := h) <;> rfl

theorem fetchStr_none_of_fetchD {mem : Memory} {a : Nat} {i : DForm} {n : Nat}
    (h : fetchD mem a = some (some (i, n))) (hi : i = .std ∨ i = .cld) : fetchStr mem a = none := by
  unfold fetchD at h
  unfold fetchStr
  cases hd : decodeStr (fetchWindow mem maxInstrLength a) with
  | none => rfl
  | some p =>
    rw [decodeD_of_decodeStr hd] at h
    simp only [Option.map_some, Option.some.injEq] at h
    split at h <;> (simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h) <;>
      (obtain ⟨rfl, -⟩ := h; rcases hi with h | h <;> cases h)

/-- **`std`**: on bytes `Str9FsXN` rejects, a fetched `FD` sets DF. -/
theorem step_std {d : DState} {n : Nat} (hlow : Str9FsXN.step d.x = none)
    (hf : fetchD d.x.m.memory d.x.m.core.rip.toNat = some (some (.std, n))) :
    step d = some ⟨⟨⟨{ d.x.m.core with rip := d.x.m.core.rip + BitVec.ofNat 64 n },
      d.x.m.memory⟩, d.x.xmm⟩, true⟩ := by
  rw [step_eq_lowerThen (fetchStr_none_of_fetchD hf (.inl rfl))]
  simp [lowerThen, hlow, hf, execD]

/-- **`cld`**: on bytes `Str9FsXN` rejects, a fetched `FC` clears DF. -/
theorem step_cld {d : DState} {n : Nat} (hlow : Str9FsXN.step d.x = none)
    (hf : fetchD d.x.m.memory d.x.m.core.rip.toNat = some (some (.cld, n))) :
    step d = some ⟨⟨⟨{ d.x.m.core with rip := d.x.m.core.rip + BitVec.ofNat 64 n },
      d.x.m.memory⟩, d.x.xmm⟩, false⟩ := by
  rw [step_eq_lowerThen (fetchStr_none_of_fetchD hf (.inr rfl))]
  simp [lowerThen, hlow, hf, execD]

/-! ## Vectors (kernel-checked) -/

example : decodeD [0xFD] = some (.std, 1) ∧ decodeD [0xFC] = some (.cld, 1) ∧
    decodeD [0xF3, 0xA4] = some (.str .repMovsb, 2) ∧ decodeD [0xA4] = some (.str .movsb, 1) ∧
    decodeD [0xF3, 0xAB] = some (.str .repStosd, 2) ∧ decodeD [0xF3, 0x48, 0xA5] =
      some (.str .repMovsq, 3) ∧ decodeD [0xF2, 0xA4] = none ∧ decodeD [0xF3, 0x49, 0xA5] = none := by
  decide

/-- `Str9FsXN` rejects `std`, `cld` and `rep movsb`, so they reach `Str9D`'s forms. -/
example : [[0xFD], [0xFC], [0xF3, 0xA4]].all (fun (w : List Byte) => Str9FsXN.decode w == none) =
    true := by decide

/-- A core with `rsi = 0x1010`, `rdi = 0x2010`, `rcx = n`. -/
private def vcore (n : Word) : State :=
  ((({ regs := fun _ => 0, rip := 0x401000, flags := ⟨none, none, none, none, none, none⟩ } :
    State).write .rsi 0x1010).write .rdi 0x2010).write .rcx n

/-- Downwards, `rep movsb` decrements both pointers by one; upwards it increments them. -/
example : let c := elemCore .repMovsb true (vcore 3) 0x401002
    c.read .rsi = 0x100f ∧ c.read .rdi = 0x200f ∧ c.read .rcx = 2 ∧ c.rip = 0x401000 := by decide

example : let c := elemCore .repMovsb false (vcore 1) 0x401002
    c.read .rsi = 0x1011 ∧ c.read .rdi = 0x2011 ∧ c.read .rcx = 0 ∧ c.rip = 0x401002 := by decide

/-- Downwards, `rep stosq` moves only `rdi`, by `-8`; `movsb` does not touch `rcx`. -/
example : let c := elemCore .repStosq true (vcore 3) 0x401003
    c.read .rsi = 0x1010 ∧ c.read .rdi = 0x2008 := by decide

example : let c := elemCore .movsb true (vcore 3) 0x401001
    c.read .rsi = 0x100f ∧ c.read .rcx = 3 ∧ c.rip = 0x401001 := by decide

end Silmaril.X86.Str9D
