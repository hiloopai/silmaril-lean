module

public import Silmaril.Wasm.Component.FXRefX.Defs
public import Silmaril.Wasm.Component.FXRefE.Thms

/-!
# The reference-machine half over `fxE P` with FX functions: the case without FX functions

`Task.refToSpecFXE` (`Defs`) is open. Its restriction to components with no FX functions holds:

* **`refToSpecFXE_nil`**: for `c : SimpleFX` with `c.fxs = []`, the conclusion of
  `RefToSpecFXE P` holds, without `TypedE`. Such a component is the `Simple` component
  `c.toSimple` with the core module map `FXRef.ofCoreFX`, so this is `FXRefE.refToSpecE_fx`.

So the frozen target is consistent with what is proved, and its content is exactly the
components whose modules carry FX functions. No result depends on `Task.refToSpecFXE`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRefX

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXRefV Silmaril.Wasm.Component.FXRef
open Silmaril.Wasm.Numerics (Profile)

/-- **`RefToSpecFXE` without FX functions** (unconditional). -/
theorem refToSpecFXE_nil (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : SimpleFX) (hnil : c.fxs = []) (hc : c.toSimple.Good) (hf : c.toSimple.FloatFree)
    (hi : c.Inst) (ha : c.toSimple.Arity) :
    ∀ x ∈ c.exports, ∀ vs, ValTy.checkList x.ty.params vs = true →
      exportBehaviours prof (refHostE (fxE P)) () (c.toSimple.toRef.map c.ofCore) [] x.name
          (vs.map toRefVal) ⊆
        exportSpecE (fxE P) c.emb c.toSimple x vs := by
  obtain ⟨core, fxs, exports⟩ := c
  subst hnil
  have hmod : (SimpleFX.mod ⟨core, [], exports⟩) = core := by
    simp [SimpleFX.mod, fxIface]
  have hinst : (SimpleFX.toSimple ⟨core, [], exports⟩).Inst := by
    have h := hi.core
    simp only [SimpleFX.coreSimple] at h
    exact ⟨by rw [SimpleFX.toSimple, hmod]; exact h.inst,
      by rw [SimpleFX.toSimple, hmod]; exact h.names⟩
  have hofCore : SimpleFX.ofCore ⟨core, [], exports⟩ = ofCoreFX := rfl
  have hemb : SimpleFX.emb ⟨core, [], exports⟩ = ofNum := rfl
  rw [hofCore, hemb]
  exact Silmaril.Wasm.Component.FXRefE.refToSpecE_fx P prof _ hc hf hinst ha

/-- info: 'Silmaril.Wasm.Component.FXRefX.refToSpecFXE_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms refToSpecFXE_nil

end Silmaril.Wasm.Component.FXRefX
