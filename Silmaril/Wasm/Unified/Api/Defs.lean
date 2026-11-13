module

public import Silmaril.Wasm.Unified.Inst.Thms
public import Silmaril.Wasm.Institution.Api.Defs

@[expose] public section

/-!
# The unified Wasm institution through the institution API

* `UInst`: the facade's `Silmaril.Inst.Institution.{0, 0, 0, 0, 1}` (silmaril's
  `Inst.{0, 0, 0, 0, 1}`), the type of `Unified.inst In B`; `inst_eq_ofFunctor`: the unified
  institution is the facade's `Institution.ofFunctor` of its room functor.
* `M ⊨ φ` (the canonical notation of `Silmaril.Inst`, class `Satisfies`) for unified models and
  sentences;
  `sat_def` unfolds it, and `sat_iff_inst` says it is the facade's `M ⊨[inst In B] φ`.
* Facade forms: `sat_map_iff_inst` (the facade's `Institution.sat_map_iff` at the unified
  institution), `equiv_iff_inst` (elementary equivalence through the facade satisfaction),
  `Valid.map` for unified sentences (`valid_map`).
* Transfer lemmas: `sat_map_iff` is now `@[simp]` (it moves a translated sentence to the
  reduct), `sat_map_iff'` is its `⊨` form (`M ⊨ φ.map σ ↔ M.reduct σ ⊨ φ`); `inst_I_obj`,
  `room_Sat`, `inst_I_map_sen` are `@[simp]`.
* Elementary equivalence `Equiv` as an equivalence relation (`equiv_refl`, `equiv_symm`,
  `equiv_trans`, `equiv_equivalence`; the names avoid `Equiv.refl` etc., which would clash
  with Mathlib's `Equiv` under `open Silmaril.Wasm.Unified`) and its builder from equal
  observations (`equiv_of_obs`).
-/

namespace Silmaril.Wasm.Unified

open CategoryTheory Silmaril.Logic.Institution Silmaril.Wasm.Atlas Silmaril.Wasm.Institution
open scoped Silmaril.Inst

/-- The type of the unified institution `Unified.inst In B`: facade institutions with
signatures, morphisms and sentences in `Type` and models in `Type 1`. -/
abbrev UInst : Type 2 := Silmaril.Inst.Institution.{0, 0, 0, 0, 1}

variable {In B : Type}

/-- The unified institution is the facade institution of its room functor. -/
theorem inst_eq_ofFunctor (In B : Type) :
    (inst In B : UInst) = Silmaril.Inst.Institution.ofFunctor (institution In B) := rfl

/-- Unified models and sentences: `M ⊨ φ` is `Sat M φ`. -/
instance instSatisfies (S : FSig) : Silmaril.Inst.Satisfies (Model In B S) (Sen In B S) := ⟨Sat⟩

@[simp] theorem sat_def {S : FSig} (M : Model In B S) (φ : Sen In B S) :
    M ⊨ φ ↔ Sat M φ := Iff.rfl

@[simp] theorem inst_I_obj (S : FSig) : (inst In B).I.obj S = room In B S := rfl

@[simp] theorem room_Sat (S : FSig) : (room In B S).Sat = Sat := rfl

@[simp] theorem inst_I_map_sen {S S' : FSig} (σ : S ⟶ S') (φ : Sen In B S) :
    ((inst In B).I.map σ).sen φ = φ.map σ := rfl

attribute [simp] sat_map_iff

/-- **The satisfaction condition**, in `⊨` form. (`simp` unfolds `⊨` by `sat_def` and uses
`sat_map_iff`, which is a `simp` lemma.) -/
theorem sat_map_iff' {S S' : FSig} (σ : S ⟶ S') (M : Model In B S') (φ : Sen In B S) :
    M ⊨ φ.map σ ↔ M.reduct σ ⊨ φ :=
  sat_map_iff σ M φ

section Facade

/-- **`⊨` is the facade's satisfaction** of the unified institution. -/
theorem sat_iff_inst {S : FSig} (M : Model In B S) (φ : Sen In B S) :
    M ⊨ φ ↔ M ⊨[inst In B] φ := Iff.rfl

/-- The satisfaction condition of the unified institution is the facade's
`Institution.sat_map_iff` (the facade's `map` is `Sen.map`, its `reduct` is `Model.reduct`). -/
theorem sat_map_iff_inst {S S' : FSig} (σ : S ⟶ S') (M : Model In B S') (φ : Sen In B S) :
    M ⊨[inst In B] Silmaril.Inst.Institution.map (inst In B) σ φ ↔
      Silmaril.Inst.Institution.reduct (inst In B) σ M ⊨[inst In B] φ :=
  Silmaril.Inst.Institution.sat_map_iff (A := inst In B) σ M φ

/-- Validity of unified sentences is preserved along signature morphisms (the facade's
`Institution.Valid.map`). -/
theorem valid_map {S S' : FSig} (σ : S ⟶ S') {φ : Sen In B S}
    (h : Silmaril.Inst.Institution.Valid (inst In B) φ) :
    Silmaril.Inst.Institution.Valid (inst In B) (φ.map σ) :=
  Silmaril.Inst.Institution.Valid.map (A := inst In B) σ h

end Facade

/-! ## Elementary equivalence -/

theorem equiv_refl {S : FSig} (M : Model In B S) : Equiv M M := fun _ => Iff.rfl

theorem equiv_symm {S : FSig} {M M' : Model In B S} (h : Equiv M M') : Equiv M' M :=
  fun φ => (h φ).symm

theorem equiv_trans {S : FSig} {M M' M'' : Model In B S} (h : Equiv M M') (h' : Equiv M' M'') :
    Equiv M M'' := fun φ => (h φ).trans (h' φ)

open scoped Silmaril.Inst in
/-- Elementary equivalence through the facade satisfaction. -/
theorem equiv_iff_inst {S : FSig} (M M' : Model In B S) :
    Equiv M M' ↔ ∀ φ : Sen In B S, (M ⊨[inst In B] φ ↔ M' ⊨[inst In B] φ) := Iff.rfl

/-- Elementary equivalence is an equivalence relation. -/
theorem equiv_equivalence (S : FSig) : Equivalence (@Equiv In B S) :=
  ⟨equiv_refl, equiv_symm, equiv_trans⟩

/-- **Models with the same observations are elementarily equivalent.** -/
theorem equiv_of_obs {S : FSig} {M M' : Model In B S} (h : ∀ x, M.obs x = M'.obs x) :
    Equiv M M' := fun φ => BSen.sat_congr h φ

end Silmaril.Wasm.Unified
