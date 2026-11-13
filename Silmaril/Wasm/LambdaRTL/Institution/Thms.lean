module

public import Silmaril.Wasm.LambdaRTL.Institution.Defs
public import Silmaril.Wasm.FnInst.IR.Lang.Thms
public import Silmaril.SSA.LambdaRTL.Institution.Defs

/-!
# Loop-free fragment → λRTL: comorphism properties and the λRTL judgement institution

* `toRTL_modelExpansive`, `toRTL_valid_iff`: the comorphism of `toRTL` (over any signature
  frame) is model-expansive, so a fragment body sentence (refinements and equivalences of
  loop-free bodies) is valid exactly when its translation to λRTL bodies is valid.
* `toRTL_equiv_iff`: two loop-free bodies of the same hole have the same outcomes exactly when
  their λRTL translations do.
* `run_iff_of_rtlObs`: a λRTL equivalence judgement `Γ ⊢ trBody f ⋈ trBody f'` satisfied in
  the Wasm model of the observational λRTL institution `Institution.rtlObs`
  (`Silmaril.SSA.LambdaRTL.Institution`, relation `Eq`, signature `WOp`) gives the equivalence of
  the loop-free functions `f`, `f'` when they have the same parameters and declared locals. The
  judgement quantifies over every store, the function equivalence only over call stores, so
  this is an implication, not an equivalence of the two notions.
-/

@[expose] public section

namespace Silmaril.Wasm.LambdaRTL

open CategoryTheory
open Silmaril.Wasm.SSA (WVal FragFunc FOut)
open Silmaril.Wasm.FnInst.IR (Hole Frame Lang Beh)

variable {Sig : Type} [Category.{0} Sig]

/-- The comorphism of `toRTL` is model-expansive. -/
theorem toRTL_modelExpansive (E : Type) (F : Frame Sig) :
    ((toRTL E).comorphism F).ModelExpansive :=
  (toRTL E).modelExpansive F (fun e => ⟨e, rfl⟩)

/-- **Borrowing along `toRTL`**: validity of a loop-free fragment body sentence is validity of
its λRTL translation. -/
theorem toRTL_valid_iff (E : Type) (F : Frame Sig) {S : Sig} (φ : ((fragLF E).inst F).Sen S) :
    ((fragLF E).inst F).Valid φ ↔ ((rtl E).inst F).Valid (((toRTL E).comorphism F).sen S φ) :=
  (toRTL E).valid_iff F (fun e => ⟨e, rfl⟩) φ

/-- Equivalence of loop-free bodies is equivalence of their λRTL translations. -/
theorem toRTL_equiv_iff (E : Type) (e : E) (h : Hole) (b b' : (fragLF E).Body h) :
    Beh.Equiv ((rtl E).den e h ((toRTL E).body h b)) ((rtl E).den e h ((toRTL E).body h b')) ↔
      Beh.Equiv ((fragLF E).den e h b) ((fragLF E).den e h b') :=
  (toRTL E).equiv_iff e h b b'

theorem initStore_congr {f f' : FragFunc} (hl : f.locals = f'.locals) (args : List WVal) :
    initStore f args = initStore f' args := by
  funext x
  cases x <;> simp [initStore, FragFunc.initLocals, hl]

open Silmaril.SSA.LambdaRTL.Institution in
/-- A λRTL equivalence judgement between translated bodies, satisfied in the Wasm model,
implies the equivalence of the source functions (same parameters and declared locals). -/
theorem run_iff_of_rtlObs {f f' : FragFunc} (hlf : loopFreeL f.body = true)
    (hlf' : loopFreeL f'.body = true) (hp : f.params = f'.params) (hl : f.locals = f'.locals)
    (Γ : Finset WReg)
    (hsat : (rtlObsRoom WReg WLab WM RVal Eq ⟨WOp⟩).Sat (Discrete.mk model)
      ⟨Γ, trBody f, trBody f'⟩) :
    ∀ args o, f.Run args o ↔ f'.Run args o := by
  intro args o
  have hf : trFunc f = some (trBody f) := by simp [trFunc, hlf]
  have hf' : trFunc f' = some (trBody f') := by simp [trFunc, hlf']
  by_cases hargs : args.map WVal.type = f.params
  · have hargs' : args.map WVal.type = f'.params := hargs.trans hp
    rw [trFunc_run_iff hf hargs (initStore_spec f args) o,
      trFunc_run_iff hf' hargs' (initStore_spec f' args) o, ← initStore_congr hl args]
    have := hsat (initStore f args)
    exact Iff.of_eq (congrArg (· = obsOf o) this)
  · constructor
    · intro hr
      exact absurd hr.1 hargs
    · intro hr
      exact absurd (hr.1.trans hp.symm) hargs

end Silmaril.Wasm.LambdaRTL
