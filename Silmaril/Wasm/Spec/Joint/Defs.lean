module

public import Silmaril.Wasm.Spec.Joint.Base.Thms

@[expose] public section

/-!
# Joint institutions: comorphisms along a change of base, and joint models

For a change of base (`Silmaril.Wasm.Spec.Joint.Base`: an injective map of function types
`τ : Ty → Ty'` and payload maps `α : A → A'`, `β : R → R'`), a logic `L'` over the target base
and a semantics `S` over the source base:

* `pushCoHom L' S hτ : Inst.CoHom (inst (L'.pull τ α β) S) (inst L' (S.push τ α β))`, the
  **comorphism of a change of base**: interfaces along `Iface.mapF τ`, sentences unchanged (their
  scopes mapped), models of the pushed semantics read back as models of `S` (`pushModel`). Its
  satisfaction condition is `reduct_evImage` (observation commutes with translation); it is
  model-expansive (`pushCoHom_modelExpansive`), so entailment between pulled sentences is
  entailment in the target (`push_entails_iff`).
* `Semantics.sum S₁ S₂` (joint models, in `Silmaril.Wasm.Spec.Joint.Base.Defs`) with its injections
  `SemMap.inl`, `SemMap.inr`, hence the comorphisms `sumInlCoHom`, `sumInrCoHom` from the
  institution of joint models to that of each kind; `Logic.sum` with `LogicMap.inl/inr/copair`
  joins logics.

The instance for Wasm (core modules wrapped as components) is in `Silmaril.Wasm.Spec.Joint.Wrap`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Spec

open CategoryTheory Silmaril.Logic.Institution

variable {Ty Ty' A A' R R' : Type}

/-! ## The comorphism of a change of base -/

/-- A model of the pushed semantics at an image interface, read as a model of `S`. -/
def pushModel {S : Semantics Ty A R} {τ : Ty → Ty'} {α : A → A'} {β : R → R'}
    (hτ : Function.Injective τ) {X : Iface Ty} (M : Model (S.push τ α β) (X.map τ)) : Model S X :=
  ⟨M.prog.src, Iface.unmapHom hτ (M.obs ≫ eqToHom M.prog.eq.symm), M.prog.prog⟩

/-- A sentence of the pulled logic as a sentence at the image interface. -/
def pushSen {L' : Logic Ty' A' R'} {τ : Ty → Ty'} {α : A → A'} {β : R → R'} {X : Iface Ty}
    (s : Sen (L'.pull τ α β) X) : Sen L' (X.map τ) :=
  ⟨s.scope.map τ, Iface.mapHom τ s.obs, s.φ⟩

/-- **The satisfaction condition of a change of base.** -/
theorem push_sat_iff (L' : Logic Ty' A' R') (S : Semantics Ty A R) {τ : Ty → Ty'} {α : A → A'}
    {β : R → R'} (hτ : Function.Injective τ) {X : Iface Ty} (M : Model (S.push τ α β) (X.map τ))
    (s : Sen (L'.pull τ α β) X) :
    Sat L' (S.push τ α β) M (pushSen s) ↔ Sat (L'.pull τ α β) S (pushModel hτ M) s := by
  obtain ⟨_, obs, ⟨Y, p, h⟩⟩ := M
  subst h
  show L'.Sat (reduct (Iface.mapHom τ s.obs ≫ obs) (evImage τ α β (S.traces p))) s.φ ↔
    L'.Sat (evImage τ α β (reduct (s.obs ≫ Iface.unmapHom hτ obs) (S.traces p))) s.φ
  rw [Iface.mapHom_comp_eq hτ, reduct_evImage]

/-- The corridor of a change of base at an interface. -/
def pushCorridor (L' : Logic Ty' A' R') (S : Semantics Ty A R) {τ : Ty → Ty'} {α : A → A'}
    {β : R → R'} (hτ : Function.Injective τ) (X : Iface Ty) :
    room (L'.pull τ α β) S X ⟶ room L' (S.push τ α β) (X.map τ) where
  sen := pushSen
  mod :=
    { obj := pushModel hτ
      map := fun h => ⟨congrArg (pushModel hτ) h.down⟩ }
  sat M s := push_sat_iff L' S hτ M s

/-- **The comorphism of a change of base**: from the institution of pulled `L'`-specifications of
`S`-programs to that of `L'`-specifications of the pushed programs. -/
def pushCoHom (L' : Logic Ty' A' R') (S : Semantics Ty A R) {τ : Ty → Ty'} (α : A → A')
    (β : R → R') (hτ : Function.Injective τ) :
    Inst.CoHom (inst (L'.pull τ α β) S) (inst L' (S.push τ α β)) where
  Φ := Iface.mapF τ
  ρ :=
    { app := pushCorridor L' S hτ
      naturality := fun _ _ _ => Room.hom_ext (funext fun s => by cases s; rfl)
        (Functor.ext (fun M => by obtain ⟨_, obs, ⟨Y, p, h⟩⟩ := M; subst h; rfl)
          (fun _ _ _ => rfl)) }

/-- Every `S`-model is the reading of a model of the pushed semantics. -/
theorem pushModel_surjective {S : Semantics Ty A R} {τ : Ty → Ty'} {α : A → A'} {β : R → R'}
    (hτ : Function.Injective τ) {X : Iface Ty} :
    Function.Surjective (pushModel (S := S) (α := α) (β := β) hτ (X := X)) := by
  rintro ⟨Y, obs, p⟩
  exact ⟨⟨Y.map τ, Iface.mapHom τ obs, ⟨Y, p, rfl⟩⟩, by
    show (⟨Y, Iface.unmapHom hτ (Iface.mapHom τ obs), p⟩ : Model S X) = ⟨Y, obs, p⟩
    rw [Iface.unmapHom_mapHom]⟩

/-- The comorphism of a change of base is model-expansive. -/
theorem pushCoHom_modelExpansive (L' : Logic Ty' A' R') (S : Semantics Ty A R) {τ : Ty → Ty'}
    (α : A → A') (β : R → R') (hτ : Function.Injective τ) :
    (pushCoHom L' S α β hτ).ModelExpansive :=
  fun _ => pushModel_surjective hτ

/-- **Borrowing along a change of base**: consequence between pulled sentences about
`S`-programs is consequence of their images about the pushed programs. -/
theorem push_entails_iff (L' : Logic Ty' A' R') (S : Semantics Ty A R) {τ : Ty → Ty'}
    (α : A → A') (β : R → R') (hτ : Function.Injective τ) (X : Iface Ty)
    (Γ : Set (Sen (L'.pull τ α β) X)) (s : Sen (L'.pull τ α β) X) :
    (room (L'.pull τ α β) S X).Entails Γ s ↔
      (room L' (S.push τ α β) (X.map τ)).Entails (pushSen '' Γ) (pushSen s) :=
  (pushCoHom L' S α β hτ).entails_iff (pushCoHom_modelExpansive L' S α β hτ) X Γ s

/-- A pushed program satisfies a formula iff the program satisfies the pulled formula. -/
theorem models_push_iff (L' : Logic Ty' A' R') (S : Semantics Ty A R) (τ : Ty → Ty')
    (α : A → A') (β : R → R') {X : Iface Ty} (p : S.Prog X) (φ : L'.Fm (X.map τ)) :
    Models L' (S.push τ α β) (PushProg.ofProg p) φ ↔ Models (L'.pull τ α β) S p φ := by
  rw [models_iff, models_iff]
  rfl

/-! ## Joint models -/

/-- From the institution of joint models to that of the first kind. -/
def sumInlCoHom (L : Logic Ty A R) (S₁ S₂ : Semantics Ty A R) :
    Inst.CoHom (inst L (S₁.sum S₂)) (inst L S₁) :=
  (SemMap.inl S₁ S₂).coHom L

/-- From the institution of joint models to that of the second kind. -/
def sumInrCoHom (L : Logic Ty A R) (S₁ S₂ : Semantics Ty A R) :
    Inst.CoHom (inst L (S₁.sum S₂)) (inst L S₂) :=
  (SemMap.inr S₁ S₂).coHom L

/-- A sentence follows in the joint institution iff it follows for each kind of program. -/
theorem sum_entails_iff (L : Logic Ty A R) (S₁ S₂ : Semantics Ty A R) (X : Iface Ty)
    (Γ : Set (Sen L X)) (s : Sen L X) :
    (room L (S₁.sum S₂) X).Entails Γ s ↔
      (room L S₁ X).Entails Γ s ∧ (room L S₂ X).Entails Γ s := by
  constructor
  · intro h
    exact ⟨fun M hM => h ⟨M.iface, M.obs, .inl M.prog⟩ hM,
      fun M hM => h ⟨M.iface, M.obs, .inr M.prog⟩ hM⟩
  · rintro ⟨h₁, h₂⟩ ⟨Y, obs, p | q⟩ hM
    · exact h₁ ⟨Y, obs, p⟩ hM
    · exact h₂ ⟨Y, obs, q⟩ hM

end Silmaril.Wasm.Spec
