module

public import Silmaril.X86.MemoryModel.Refinement.Defs
public import Silmaril.X86.Concurrency.Lift.Thms

/-! # A successful finite prefix acquires a one-thread event certificate -/

public section

namespace Silmaril.Proofs.X86.MemoryModel.Refinement

open Silmaril.Semantics.MemoryRefinement
open Silmaril.Machine.Execution (run)
open Silmaril.X86.Concurrency
open Silmaril.X86.MemoryModel.Axiomatic (Exec)
open Silmaril.X86.MemoryModel.Litmus (XAct)
open Silmaril.X86.MemoryModel.Refinement

theorem singleThread_sound {State Obs : Type} {step : State → Option State} {mem : State → Cir.Mem}
    {events : State → List XAct → Prop} {model : Exec → Prop} (flat : Lift.FlatStep step mem events)
    (lower : Cir.MLe Exec.Sc model) (upper : Cir.MLe model Exec.Xl) (count : Nat) (see : State → State → Obs)
    (start : State) : SoundAt (sequential step count see) (under step mem events model count see) start start := by
  intro safe
  cases ran : run step count start with
  | none => exact False.elim (safe (by simp [sequential, ofEval, ran]))
  | some stop =>
    have cert := Lift.runUnder_of_reaches flat lower upper (s := start) (t := stop) ⟨count, ran⟩
    refine ⟨fun missing => missing ⟨stop, ran, cert⟩, ?_⟩
    rintro _ ⟨last, ⟨hit, _⟩, rfl⟩
    simp [sequential, ofEval, hit]

end Silmaril.Proofs.X86.MemoryModel.Refinement
