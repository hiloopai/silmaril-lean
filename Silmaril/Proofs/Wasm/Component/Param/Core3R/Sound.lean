module

public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Inst
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Call
public import Silmaril.Proofs.Wasm.Component.Reference.RefToSpec

/-!
# The reference-machine half over `core3R P V IR`, and over restrictions of `core3P P`

* `refToSpec_of_phases`: the two phases give the reference-machine half (a copy of
  `Reference.refToSpec_of_phases` over `core3R P V IR`);
* `refToSpec_core3R`: `RefToSpec (core3R P V IR) id P` for every `V` and every `IR` contained in
  `InternalP P`;
* `refToSpec_restrict_core3P`: `RefToSpec (restrict (core3P P) r) id P` for every restriction
  `r` of the Core 3.0 engine, since `restrict (core3P P) r` is `core3R P _ _` with an internal
  step contained in `InternalP P`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Param.Core3R

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Numerics (Profile)

/-- **The reference half from its phases** over `core3R P V IR`, for components within the
flat arities. -/
theorem refToSpec_of_phases (hA : InstPhase) (hB : CallPhase) (P : Profile)
    (V : Silmaril.Wasm.Module → Prop) (IR : {H : Type} → Cfg3 H → Cfg3 H → Prop)
    (hIR : Sub P IR) (prof : ProfileKind) (c : Simple) (hc : c.Good) (hf : c.FloatFree)
    (hi : c.Inst) (ha : c.Arity) (x : SimpleExport) (hx : x ∈ c.exports)
    (vs : List Silmaril.Wasm.Component.Val) (hvs : ValTy.checkList x.ty.params vs = true) :
    exportBehaviours prof (refHostR P V IR) () c.toRef [] x.name (vs.map toRefVal) ⊆
      exportSpec P c x vs := by
  obtain ⟨j, hj, rfl⟩ : ∃ j, ∃ hj : j < c.exports.length, c.exports[j] = x :=
    List.getElem_of_mem hx
  obtain ⟨I, cs, hI, hcs, hinst⟩ := hA P V IR prof c hc hi
  have hcall := hB P V IR hIR prof c hc hf ha I cs hI hcs j hj vs hvs
  intro b hb
  rcases hb with ⟨m₁, inst, es, f, hr, hl, hb⟩ | ⟨-, hr⟩ | ⟨-, hr⟩
  · have he : InstResult.instance m₁ inst es = .instance (afterInst P V IR cs
        (liftedFuncs P V IR (fun k => I.addrs.getD k 0) c)) ⟨0⟩ (exportMap c) := hinst _ hr
    obtain ⟨rfl, rfl, rfl⟩ : m₁ = afterInst P V IR cs
        (liftedFuncs P V IR (fun k => I.addrs.getD k 0) c) ∧ inst = ⟨0⟩ ∧ es = exportMap c := by
      simpa only [InstResult.instance.injEq] using he
    have hf' : f = ⟨j⟩ := Option.some.inj (hl.symm.trans (exportMap_lookup hc j hj))
    exact hcall (hf' ▸ hb)
  · exact absurd (hinst _ hr) (by simp)
  · exact absurd (hinst _ hr) (by simp)

/-- **The reference-machine half over `core3R P V IR`**, for an internal step contained in
`InternalP P`. -/
theorem refToSpec_core3R (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Cfg3 H → Cfg3 H → Prop) (hIR : Sub P IR) :
    RefToSpec (core3R P V IR) id P := by
  intro prof c hc hf hi ha x hx vs hvs
  have hm : Silmaril.Wasm.Component.Syntax.Component.map (N := (core3R P V IR).Module) id
      c.toRef = c.toRef := Silmaril.Wasm.Component.Syntax.Component.map_id _
  erw [hm]
  exact refToSpec_of_phases instPhase callPhase P V IR hIR prof c hc hf hi ha x hx vs hvs

/-- The internal step of a restriction of `core3P P` is contained in `InternalP P`. -/
theorem sub_restrict (P : Profile) (r : Restriction (core3P P)) :
    Sub P (fun c c' => (core3P P).Internal c c' ∧ r.Rt c') :=
  fun h => h.1

/-- **The reference-machine half for every restriction of the Core 3.0 engine.** -/
theorem refToSpec_restrict_core3P (P : Profile) (r : Restriction (core3P P)) :
    RefToSpec (restrict (core3P P) r) id P :=
  refToSpec_core3R P (fun m => (core3P P).Valid m ∧ r.Mod m)
    (fun c c' => (core3P P).Internal c c' ∧ r.Rt c') (sub_restrict P r)

end Silmaril.Proofs.Wasm.Component.Param.Core3R
