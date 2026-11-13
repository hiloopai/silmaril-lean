module

public import Silmaril.Wasm.Unified.Versions.OwnNeq.Defs
public import Silmaril.Wasm.Unified.Versions.OwnV.Thms

/-!
# The own models are strictly below the Core reducts

The own-model refinements of `Silmaril.Wasm.Unified.Versions.OwnV.Thms` are not equations of
observations. Core 3.0 reads every opcode with every immediate it can carry; an own semantics only
the immediates its syntax has.

* `selAny_beh`: from any store and frame, Core 3.0 runs `selAny` on `v, v, 1` to `returns [v]`;
* `not_trL`, `not_tr10`, `not_tr20`: no own Lime1, 1.0 or 2.0 code translates to `[selAny]`;
* `mapCode_selCode`: the version code `selCode S h` is the encoding of `[selAny]` in `sig30`;
* `not_refines_reduct`: generic: a version code whose 3.0 image is an encoded Core program no own
  program translates to, with a Core behaviour, refutes the converse refinement on that version
  signature;
* **`lime1_not_refined`**, **`v10_not_refined`**, **`v20_not_refined`** (refutations): the reducts
  of `model30` (validation `okTrue`, any profile where the version model has one, any Core point
  and frame) do not refine the own models: `lime1At`, `v20At` and every `coreSAt v10` (in
  particular `v10At`) observe `returns [v]` on the call `(selCode, [v, v, 1])`, where the own
  models observe nothing. So the own models and the reducts of `model30` are **not** equal in
  observations, whatever the points.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions.Own

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Unified Silmaril.Wasm.Unified.Core30
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Models
open CategoryTheory

variable {H : Type}

/-- **Core 3.0 runs `selAny`.** -/
theorem selAny_beh (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) (v : Val) :
    Behaviour.returns [v] ∈ behCode P host s f [selAny] [v, v, Val.i32 1] := by
  have st : Step P host ⟨s, f, vals [v, v, Val.i32 1] ++ expression [selAny]⟩ ⟨s, f, [v.toAdmin]⟩ :=
    Step.parametric (ParametricStep.selectTrue (by decide))
  exact mem_behavioursOf (r := .values [v]) (Relation.ReflTransGen.single st) rfl

/-- Lime1 has no instruction translating to `selAny`. -/
theorem lime1_ne_selAny (j : Lime1.Instr) : j.toCore ≠ selAny := fun h => by
  have e := Lime1.Instr.ofCore?_toCore j
  rw [h] at e
  exact absurd e (by simp [selAny, Lime1.Instr.ofCore?])

/-- A translation of `[i]` is a translation of one instruction. -/
theorem tr_single {L : Syn} {js : List L.J} {i : Instr} (h : L.Tr js [i]) :
    ∃ j, L.tr j = some i := by
  obtain ⟨j, _, hj, -, -⟩ := List.forall₂_cons_right_iff.1 h
  exact ⟨j, hj⟩

theorem not_trL (js : List Lime1.Instr) : ¬ synL.Tr js [selAny] := fun h =>
  let ⟨j, hj⟩ := tr_single h
  lime1_ne_selAny j (Option.some.inj hj)

theorem not_tr10 (js : List V1.Instr) : ¬ syn10.Tr js [selAny] := fun h =>
  let ⟨j, hj⟩ := tr_single h
  lime1_ne_selAny j.toLime (Option.some.inj hj)

theorem not_tr20 (js : List V2.Instr) : ¬ syn20.Tr js [selAny] := fun h => by
  obtain ⟨j, hj⟩ := tr_single h
  have e := V2.Instr.ofCore?_toCore (i := j) hj
  exact absurd e (by simp [selAny, anyRef, V2.Instr.ofCore?, V2.ResultType.ofCore?,
    V2.ValType.ofCore?, V2.RefType.ofCore?])

/-- The version code `selCode` is the encoding of `[selAny]`. -/
theorem mapCode_selCode (S : FeatureSet) (h : head (.select none) ∈ (nsig S).ops) :
    UInstr.mapCode (FSig.incl (nsig_sub30 S)).f (selCode S h) = encCode [selAny] := rfl

/-- **The converse refinement fails** on a version signature, at a version code whose 3.0 image
is an encoded Core program with a behaviour that no own program translates to. -/
theorem not_refines_reduct {L : Syn} (hc : L.Coh) {okJ : List L.J → Prop}
    {beh : List L.J → UIn → Set UObs} {P : Profile} {host : HostSemantics H} {s : Store H}
    {f : Frame} {okc : List Instr → Prop} {K : FSig} (σ : K ⟶ sig30) {c : K.Code}
    {is : List Instr} (he : UInstr.mapCode σ.f c = encCode is) (h : ∀ js, ¬ L.Tr js is)
    (hok : okc is) {vs : UIn} {b : UObs} (hb : b ∈ behCode P host s f is vs) :
    ¬ Refines ((model30 P host s f okc).reduct σ) ((ownModel L okJ beh).reduct σ) := fun hr => by
  have hm := hr (c, vs) (by
    rw [Model.obs_reduct, he, obs_encCode]
    exact ⟨hok, hb⟩)
  rw [Model.obs_reduct, he, obs_encCode_empty hc h] at hm
  exact hm

theorem select_mem (S : FeatureSet) (hS : S.has .control = true) :
    head (.select none) ∈ (nsig S).ops :=
  ⟨.select none, rfl, hS⟩

/-- **Refutation (Lime1)**: the Lime1 version model does not refine Lime1's own semantics. -/
theorem lime1_not_refined (okJ : List Lime1.Instr → Prop) (f : Silmaril.Wasm.Execution.Runtime.Frame)
    (p : Lime1Core.Pt H) (fC : Frame) :
    ¬ Refines (lime1At fC okTrue p) (lime1ownAt okJ f p) :=
  not_refines_reduct cohL _ (mapCode_selCode lime1 (select_mem lime1 (by decide))) not_trL trivial
    (selAny_beh _ _ _ _ (Val.i32 0))

/-- **Refutation (1.0)**: no 1.0 reduct of `model30` refines Wasm 1.0's own semantics (in
particular neither `v10At` nor the reduct at the Lime1 image). -/
theorem v10_not_refined (okJ : List V1.Instr → Prop) (f : Silmaril.Wasm.Execution.Runtime.Frame)
    (p : V10.Pt H) (P : Profile) (fC : Frame) (x : Silmaril.Wasm.Atlas.Core.Pt H) :
    ¬ Refines (coreSAt v10 P fC okTrue x) (v10ownAt okJ f p) :=
  not_refines_reduct coh10 _ (mapCode_selCode v10 (select_mem v10 (by decide))) not_tr10 trivial
    (selAny_beh _ _ _ _ (Val.i32 0))

/-- **Refutation (2.0)**: the 2.0 version model does not refine Wasm 2.0's own semantics. -/
theorem v20_not_refined (P : Profile) (okJ : List V2.Instr → Prop) (f : V2.Execution.Frame)
    (p : V2Core.Pt H) (fC : Frame) :
    ¬ Refines (v20At P fC okTrue p) (v20ownAt P okJ f p) :=
  not_refines_reduct coh20 _ (mapCode_selCode v20 (select_mem v20 (by decide))) not_tr20 trivial
    (selAny_beh _ _ _ _ (Val.i32 0))

end Silmaril.Wasm.Unified.Versions.Own
