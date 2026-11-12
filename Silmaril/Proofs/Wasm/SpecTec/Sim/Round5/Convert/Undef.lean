module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.Cond1a
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.Cond1b
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.Cond2
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.Cond3

/-!
# Round 5: `$vcvtop__`'s clauses definitely fail, so `VecConvertR` holds

The three leading conditions evaluate for every operator (`Cond1a`, `Cond1b`, `Cond2`, `Cond3`),
so every clause of `$vcvtop__` definitely fails at every shape pair, operator and operand
(`tryClausesUndef_vcvtop`), and `vecConvertR_of_undef` gives the restated conversion
field at the concrete builtins.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Convert

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (TryClausesUndef)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Scripts.Wasm30
open Round4Int (BI)
open Simd (clausesOf encConvert)

variable {H : Type} {P : Profile} {hn : H → String} {host : HostSemantics H}

/-- The leading conditions evaluate at the concrete builtins, for every operator. -/
theorem condsOk_builtins (op : VecConvertOp) (l₁ m₁ l₂ m₂ w : Value) :
    CondsOk (simEnv (BI P hn host)) l₁ m₁ l₂ m₂ (Vec.vConvertOpV op) w where
  c₁ h := by
    subst h
    rcases op with ⟨h, sx⟩ | ⟨h, sx⟩ | _ | _ | _ | _
    · exact evals_cond₁_extend P hn host h sx _ _ _ _
    · exact evals_cond₁_convert P hn host h sx _ _ _ _
    all_goals
      refine evals_cond₁_trunc P hn host _ ?_ ?_ _ _ _ _ <;>
      intro _ _ h <;> exact VecConvertOp.noConfusion h
  c₂ := evals_cond₂ P hn host op _ _ _ _ _
  c₃ := evals_cond₃ P hn host op _ _ _ _ _

/-- **Every clause of `$vcvtop__` definitely fails** at the concrete builtins, for every pair of
shapes, operator and operand. -/
theorem undef_vcvtop (s t : Shape) (op : VecConvertOp) (a : V128) :
    TryClausesUndef (simEnv (BI P hn host)) (clausesOf Original.d539)
      (encConvert (s, t, op, a)) := by
  obtain ⟨l₁, m₁, h₁⟩ := shapeV_split s
  obtain ⟨l₂, m₂, h₂⟩ := shapeV_split t
  have he : encConvert (s, t, op, a) = cvtArgs l₁ m₁ l₂ m₂ (Vec.vConvertOpV op) (Vec.vecV a) := by
    simp only [encConvert, h₁, h₂]
  rw [he]
  exact tryClausesUndef_vcvtop (condsOk_builtins op _ _ _ _ _)

/-- **`Simd.VecConvertR` at the concrete builtins**: SpecTec's `$vcvtop__` denotes exactly the
allowed result `vecOpCall` picks, so it is sound and total for Core's `VecConvertRel`. -/
theorem vecConvertR_builtins : Simd.VecConvertR (simEnv (BI P hn host)) P :=
  Simd.vecConvertR_of_undef undef_vcvtop

end Silmaril.Wasm.SpecTec.Sim.Round5.Convert
