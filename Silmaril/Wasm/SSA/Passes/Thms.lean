module

public import Silmaril.Wasm.SSA.Passes.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Thms
public import Silmaril.Wasm.SSA.Contract.Defs
import Silmaril.Proofs.Wasm.SSA.Passes.Backward

/-!
# SSA optimisation passes: equivalence and the pass monoid

* `simpR_sound` / `simpR_complete`: for an environment satisfying the facts
  (`FactsOK`) and, backwards, the types (`TysOK`), a region and its
  simplification have the same evaluations (all `SimpCfg` flag combinations:
  constant folding/propagation and branch folding, typed algebraic
  identities, copy propagation, common subexpressions).
* `dce_sound` / `dce_complete`: the same for dead-binding elimination.
* `SFunc.simp_iff`, `SFunc.dce_iff`, `ssaPipeline_iff`: function-level
  equivalences (`Run` requires arguments of the parameter types, which seeds
  the types); `run_deterministic`: at most one terminating outcome per
  argument list. Together: a function and its optimisation have the same
  terminating outcomes, so one diverges or is stuck exactly when the other is.

Backward soundness needs the two restrictions in `Passes/Defs`: algebraic
rules fire only on operands of known type, and `dce` only removes bindings
of total terms.

The passes are packaged as `Silmaril.Compile.PassAPI.Pass` values for
`ssaIR.contract`, and `ssaPipeline` is their monoid product.
-/

@[expose] public section

namespace Silmaril.Wasm.SSA

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env InstrDeterministic)
open Silmaril.Compile.PassAPI

theorem factsOK_nil (env : Env WVal) : FactsOK [] env := FactsOK.nil env

/-- The dialect's primitives are deterministic. -/
theorem instr_deterministic : InstrDeterministic instr :=
  Silmaril.Proofs.Wasm.SSA.Passes.instr_deterministic

/-- Soundness of the simplifier. -/
theorem simpR_sound (cfg : SimpCfg) {F : Facts} (T : Tys) {env : Env WVal} (hF : FactsOK F env)
    {r : Region Prim} {l : Nat} {v : SVal}
    (h : Semantics.Region.Eval instr env r () l v ()) :
    Semantics.Region.Eval instr env (simpR cfg F T r) () l v () :=
  Silmaril.Proofs.Wasm.SSA.Passes.simpR_sound cfg h hF

/-- Completeness of the simplifier: every evaluation of the simplified region is
an evaluation of the original. -/
theorem simpR_complete (cfg : SimpCfg) {F : Facts} {T : Tys} {env : Env WVal}
    (hF : FactsOK F env) (hT : TysOK T env) {r : Region Prim} {l : Nat} {v : SVal}
    (h : Semantics.Region.Eval instr env (simpR cfg F T r) () l v ()) :
    Semantics.Region.Eval instr env r () l v () :=
  Silmaril.Proofs.Wasm.SSA.Passes.simpR_complete cfg r hF hT h

/-- Completeness of dead-binding elimination. -/
theorem dce_complete {env : Env WVal} {r : Region Prim} {l : Nat} {v : SVal}
    (h : Semantics.Region.Eval instr env (dce r) () l v ()) :
    Semantics.Region.Eval instr env r () l v () :=
  Silmaril.Proofs.Wasm.SSA.Passes.dce_complete r h

/-- Soundness of dead-binding elimination. -/
theorem dce_sound {env : Env WVal} {r : Region Prim} {l : Nat} {v : SVal}
    (h : Semantics.Region.Eval instr env r () l v ()) :
    Semantics.Region.Eval instr env (dce r) () l v () :=
  Silmaril.Proofs.Wasm.SSA.Passes.dce_sound h

theorem SFunc.simp_run (cfg : SimpCfg) {f : SFunc} {args : List WVal} {o : FOut}
    (h : f.Run args o) : (f.simp cfg).Run args o :=
  Silmaril.Proofs.Wasm.SSA.Passes.simp_run cfg h

theorem SFunc.dce_run {f : SFunc} {args : List WVal} {o : FOut}
    (h : f.Run args o) : f.dce.Run args o :=
  Silmaril.Proofs.Wasm.SSA.Passes.dce_run h

/-- The simplifier preserves and reflects terminating outcomes. -/
theorem SFunc.simp_iff (cfg : SimpCfg) {f : SFunc} {args : List WVal} {o : FOut} :
    (f.simp cfg).Run args o ↔ f.Run args o :=
  ⟨Silmaril.Proofs.Wasm.SSA.Passes.simp_complete cfg, Silmaril.Proofs.Wasm.SSA.Passes.simp_run cfg⟩

/-- Dead-binding elimination preserves and reflects terminating outcomes. -/
theorem SFunc.dce_iff {f : SFunc} {args : List WVal} {o : FOut} :
    f.dce.Run args o ↔ f.Run args o :=
  ⟨Silmaril.Proofs.Wasm.SSA.Passes.dce_complete_run, Silmaril.Proofs.Wasm.SSA.Passes.dce_run⟩

/-- SSA functions are deterministic. -/
theorem SFunc.run_deterministic {f : SFunc} {args : List WVal} {o₁ o₂ : FOut}
    (h₁ : f.Run args o₁) (h₂ : f.Run args o₂) : o₁ = o₂ :=
  Silmaril.Proofs.Wasm.SSA.Passes.run_deterministic h₁ h₂

/-! ## Passes -/

/-- The simplifier as a verified pass. -/
def simpPass (cfg : SimpCfg) : Pass ssaIR.contract where
  run := SFunc.simp cfg
  inv_run _ := trivial
  sound _ := fun _ _ h => SFunc.simp_run cfg h

/-- Dead-binding elimination as a verified pass. -/
def dcePass : Pass ssaIR.contract where
  run := SFunc.dce
  inv_run _ := trivial
  sound _ := fun _ _ h => SFunc.dce_run h

/-- Constant propagation and folding (with branch folding) only. -/
def constFoldPass : Pass ssaIR.contract :=
  simpPass { fold := true, alg := false, copy := false, cse := false }

/-- Algebraic simplification only. -/
def algebraicPass : Pass ssaIR.contract :=
  simpPass { fold := false, alg := true, copy := false, cse := false }

/-- Copy propagation only. -/
def copyPropPass : Pass ssaIR.contract :=
  simpPass { fold := false, alg := false, copy := true, cse := false }

/-- Common-subexpression elimination only. -/
def csePass : Pass ssaIR.contract :=
  simpPass { fold := false, alg := false, copy := false, cse := true }

/-- The SSA pipeline: two rounds of simplification and dead-binding elimination. -/
def ssaPipeline : Pass ssaIR.contract :=
  Pass.pipeline [simpPass {}, dcePass, simpPass {}, dcePass]

theorem ssaPipeline_run (f : SFunc) :
    ssaPipeline.run f = (((f.simp {}).dce.simp {}).dce) := rfl

/-- The pipeline preserves and reflects terminating outcomes. -/
theorem ssaPipeline_iff {f : SFunc} {args : List WVal} {o : FOut} :
    (ssaPipeline.run f).Run args o ↔ f.Run args o := by
  rw [ssaPipeline_run, SFunc.dce_iff, SFunc.simp_iff, SFunc.dce_iff, SFunc.simp_iff]

theorem ssaPipeline_eq_prod :
    ssaPipeline = [simpPass {}, dcePass, simpPass {}, dcePass].prod :=
  Pass.pipeline_eq_prod _

end Silmaril.Wasm.SSA
