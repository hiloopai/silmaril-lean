module

public import Silmaril.Apps.Sha256sum.X86Sys
public import Silmaril.Process.CLI.X86Linux8
public import Silmaril.Apps.Sha256sum.X86Sys.Silent

/-! # x86-64 Linux as a `Sys.Machine`, over the `Ext8` variant

`X86Sys.x86Machine` runs `Process.CLI.X86Linux.step`, which is stuck (`unmodeled`)
at the 27 instructions of `sha256sum-min` outside `X86.Ext` (8-bit ALU forms with
a register source, `xor al, imm8`, `shr r/m8, imm8`, and `movzbl %ah, %ebx`).
`x86Machine8` is the same machine over `Process.CLI.X86Linux8.step`, which decodes
them. `stepWith` is `X86Sys.step` with the ISA step as a parameter
(`step_eq_stepWith`, by `rfl`), and `step8_eq_or_stuck` says the variant machine
agrees with the original at every state where the original is not stuck.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.X86Sys

open Silmaril.Apps.Sha256sum
open Silmaril.Apps.Sha256sum.Sys
open Silmaril.Process (Byte Memory)
open Silmaril.Process.CLI
open Silmaril.X86 (Word Reg MState)

/-- `X86Sys.step` over an arbitrary ISA step. -/
def stepWith (isaStep : Core → Memory → Step Core) (r11Of : Core → Word) (s : XState) :
    Action XState :=
  if s.faulted then .stuck else
  match isaStep s.core s.memory with
  | .retired c m => .tau { s with core := c, memory := m }
  | .fault _ => .stuck
  | .syscall c =>
    match decode c s.memory with
    | none => .stuck
    | some (.exit n) => .exit n
    | some (.brk addr) => .tau (brkStep r11Of s c addr)
    | some (.call call) => .call call (resume r11Of s c call)

theorem step_eq_stepWith (r11Of : Core → Word) : step r11Of = stepWith X86Linux.step r11Of := rfl

/-- The system step over the `Ext8` variant. -/
def step8 (r11Of : Core → Word) : XState → Action XState := stepWith X86Linux8.step r11Of

/-- The `Sys.Machine` of `sha256sum-min` over the `Ext8` variant. -/
def x86Machine8 (r11Of : Core → Word) : Machine := ⟨XState, step8 r11Of⟩

/-- **Agreement**: the variant's system step is the original's wherever the
original is not stuck. -/
theorem step8_eq_or_stuck (r11Of : Core → Word) (s : XState) :
    step8 r11Of s = step r11Of s ∨ step r11Of s = .stuck := by
  rw [step_eq_stepWith]
  unfold step8 stepWith
  by_cases hf : s.faulted = true
  · simp [hf]
  · rcases X86Linux8.step_eq_or_unmodeled s.core s.memory with e | e
    · left; rw [e]
    · right; simp [hf, e]

theorem step8_of_step {r11Of : Core → Word} {s : XState} {a : Action XState}
    (h : step r11Of s = a) (ha : a ≠ .stuck) : step8 r11Of s = a := by
  rcases step8_eq_or_stuck r11Of s with e | e
  · rw [e, h]
  · exact absurd (h ▸ e) ha


/-! ## Transfer of runs -/

/-- Every completed run of the original machine is a completed run of the variant. -/
theorem exec8_of_exec {r11Of : Core → Word} {E : Sys.Env} {s : (x86Machine r11Of).State}
    {k : KState}
    {evs : List Event} {n : Nat} (h : Exec (x86Machine r11Of) E s k evs n) :
    Exec (x86Machine8 r11Of) E s k evs n := by
  induction h with
  | exit e => exact .exit (step8_of_step e (fun h => by cases h))
  | tau e _ ih => exact .tau (step8_of_step e (fun h => by cases h)) ih
  | call e he _ ih => exact .call (step8_of_step e (fun h => by cases h)) he ih

/-- Every partial run of the original machine is a partial run of the variant. -/
theorem reach8_of_reach {r11Of : Core → Word} {E : Sys.Env} {n : Nat}
    {s t : (x86Machine r11Of).State}
    {k kt : KState} (h : Reach (x86Machine r11Of) E n s k t kt) :
    Reach (x86Machine8 r11Of) E n s k t kt := by
  induction h with
  | refl => exact .refl
  | tau e _ ih => exact .tau (step8_of_step e (fun h => by cases h)) ih
  | call e he _ ih => exact .call (step8_of_step e (fun h => by cases h)) he ih

/-- Exactly `n` internal steps of the variant machine. -/
inductive TauRun8 (r11Of : Core → Word) : Nat → XState → XState → Prop where
  | refl {s} : TauRun8 r11Of 0 s s
  | cons {n s mid final} : (x86Machine8 r11Of).step s = .tau mid →
      TauRun8 r11Of n mid final → TauRun8 r11Of (n + 1) s final

namespace TauRun8

theorem single {r11Of : Core → Word} {s t : XState}
    (head : (x86Machine8 r11Of).step s = .tau t) : TauRun8 r11Of 1 s t :=
  .cons head .refl

theorem append {r11Of : Core → Word} {n m : Nat} {s t u : XState}
    (first : TauRun8 r11Of n s t) (second : TauRun8 r11Of m t u) :
    TauRun8 r11Of (n + m) s u := by
  induction first with
  | refl => simpa using second
  | cons head _ ih =>
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using TauRun8.cons head (ih second)

theorem reach {r11Of : Core → Word} {n : Nat} {s t : XState}
    (run : TauRun8 r11Of n s t) (E : Sys.Env) (k : KState) :
    Reach (x86Machine8 r11Of) E n s k t k := by
  induction run with
  | refl => exact .refl
  | cons head _ ih => exact .tau head ih

theorem exec_iff {r11Of : Core → Word} {n : Nat} {s t : XState}
    (run : TauRun8 r11Of n s t) {E : Sys.Env} {k : KState}
    {events : List Event} {status : Nat} :
    Exec (x86Machine8 r11Of) E s k events status ↔
      Exec (x86Machine8 r11Of) E t k events status := by
  induction run with
  | refl => rfl
  | cons head _ ih =>
    refine Iff.trans ⟨fun run => ?_, fun run => .tau head run⟩ ih
    cases run with
    | exit exited => rw [head] at exited; cases exited
    | tau stepped tail => rw [head] at stepped; cases stepped; exact tail
    | call called _ _ => rw [head] at called; cases called

end TauRun8

/-- An original silent run is a variant silent run. -/
theorem tauRun8_of_tauRun {r11Of : Core → Word} {n : Nat} {s t : XState}
    (h : TauRun r11Of n s t) : TauRun8 r11Of n s t := by
  induction h with
  | refl => exact .refl
  | cons e _ ih => exact .cons (step8_of_step e (fun h => by cases h)) ih

/-- **Call bridge over the variant**: a completed `X86.Ext` function call (for
example `sha256_compress`, `Binary.compress_contract`) is `n + 1` internal steps
of the variant machine. -/
theorem ext_returns_tauRun8 {r11Of : Core → Word} {exit : Word}
    {s : XState} {final : MState} (running : s.faulted = false)
    (returned : X86.Ext.Returns exit (toExtState s) final) :
    ∃ n, TauRun8 r11Of (n + 1) s (withExtState s final) := by
  obtain ⟨n, h⟩ := ext_returns_tauRun (r11Of := r11Of) running returned
  exact ⟨n, tauRun8_of_tauRun h⟩

/-- A completed `X86.Ext` call may be replaced by its final state inside every
completed run of the variant machine. -/
theorem exec8_iff_of_ext_returns {r11Of : Core → Word} {exit : Word}
    {s : XState} {final : MState} (running : s.faulted = false)
    (returned : X86.Ext.Returns exit (toExtState s) final) {E : Sys.Env} {k : KState}
    {events : List Event} {status : Nat} :
    Exec (x86Machine8 r11Of) E s k events status ↔
      Exec (x86Machine8 r11Of) E (withExtState s final) k events status := by
  obtain ⟨_, segment⟩ := ext_returns_tauRun8 (r11Of := r11Of) running returned
  exact segment.exec_iff

end Silmaril.Apps.Sha256sum.X86Sys
