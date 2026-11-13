module

public import Silmaril.Wasm.Unified.Model.Defs
public import Silmaril.Wasm.Atlas.Defs
public import Silmaril.Logic.Institution.Morphism

/-!
# The unified Wasm institution

One institution for every Wasm dialect, over the universal syntax
(`Silmaril.Wasm.Unified.Syntax`). It is parametric in the inputs `In` of a call and the
observations `B` of a run; the Wasm instance (`Silmaril.Wasm.Unified.Core30`) takes argument
lists and `Behaviour Val` of silmaril's Core 3.0 values.

* **Signatures**: feature signatures `FSig` with opcode renamings (`FSig.category`).
* **Sentences** `Sen In B S`: the Atlas behaviour sentences `BSen` (`always`, `may`, `and`,
  `top`) over calls `S.Code × In`: a code sequence over the opcodes of `S` and an input.
  Translation along `σ` renames the opcodes of the calls (`Sen.map`).
* **Models** `Model In B S`: opcode interpretations with validation and behaviours, as a
  discrete category; reducts precompose with the renaming (`Model.reduct`).
* **Satisfaction** `Sat M φ`: `φ` holds of the observation map `M.obs` (behaviours of validated
  code; invalid code has none, so `always` holds of it vacuously and `may` fails).
* `sat_map_iff`: **the satisfaction condition**, `M' ⊨ σ(φ) ↔ M'|σ ⊨ φ`. It is the homomorphism
  lemma `Alg.evalCode_comap` and the Atlas condition for renamings of calls `BSen.sat_rename`.
* `institution`: the functor `FSig ⥤ Room` and `inst`, the bundled silmaril `Inst`.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified

open CategoryTheory Silmaril.Logic.Institution Silmaril.Wasm.Atlas

variable {In B : Type}

/-- Calls of a signature: code over its opcodes and an input. -/
abbrev Call (In : Type) (S : FSig) : Type := S.Code × In

/-- **Sentences**: behaviour sentences over calls. -/
abbrev Sen (In B : Type) (S : FSig) : Type := BSen (Call In S) B

/-- Rename the opcodes of a call. -/
def Call.map {S S' : FSig} (σ : S ⟶ S') (x : Call In S) : Call In S' :=
  (UInstr.mapCode σ.f x.1, x.2)

/-- **Sentence translation** along a signature morphism. -/
def Sen.map {S S' : FSig} (σ : S ⟶ S') (φ : Sen In B S) : Sen In B S' :=
  φ.rename (Call.map σ)

theorem Call.map_id {S : FSig} (x : Call In S) : x.map (𝟙 S) = x := by
  obtain ⟨c, i⟩ := x
  simp only [Call.map, FSig.id_f, UInstr.mapCode_id]

theorem Call.map_comp {S S' S'' : FSig} (σ : S ⟶ S') (τ : S' ⟶ S'') (x : Call In S) :
    x.map (σ ≫ τ) = (x.map σ).map τ := by
  obtain ⟨c, i⟩ := x
  simp only [Call.map, FSig.comp_f, UInstr.mapCode_map]

theorem Sen.map_id {S : FSig} (φ : Sen In B S) : φ.map (𝟙 S) = φ := by
  unfold Sen.map
  rw [show Call.map (𝟙 S) = (id : Call In S → Call In S) from funext Call.map_id]
  exact BSen.rename_id φ

theorem Sen.map_comp {S S' S'' : FSig} (σ : S ⟶ S') (τ : S' ⟶ S'') (φ : Sen In B S) :
    φ.map (σ ≫ τ) = (φ.map σ).map τ := by
  unfold Sen.map
  rw [BSen.rename_rename]
  congr 1
  exact funext (Call.map_comp σ τ)

/-- **Satisfaction**: the sentence holds of the model's observations. -/
def Sat {S : FSig} (M : Model In B S) (φ : Sen In B S) : Prop := φ.Sat M.obs

/-- **The satisfaction condition** of the unified institution. -/
theorem sat_map_iff {S S' : FSig} (σ : S ⟶ S') (M : Model In B S') (φ : Sen In B S) :
    Sat M (φ.map σ) ↔ Sat (M.reduct σ) φ := by
  unfold Sat Sen.map
  rw [BSen.sat_rename]
  refine BSen.sat_congr (fun x => ?_) φ
  obtain ⟨c, i⟩ := x
  exact (Model.obs_reduct σ M c i).symm

/-- The discrete category of models (morphisms are equalities). -/
instance Model.category (S : FSig) : Category.{0} (Model In B S) where
  Hom M M' := PLift (M = M')
  id _ := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩

/-- The reduct functor. -/
def reductF {S S' : FSig} (σ : S ⟶ S') : Model In B S' ⥤ Model In B S where
  obj M := M.reduct σ
  map h := ⟨congrArg (Model.reduct σ) h.down⟩

/-- The room of a signature. -/
def room (In B : Type) (S : FSig) : Room.{0, 0, 1} :=
  ⟨Sen In B S, Cat.of (Model In B S), Sat⟩

/-- The corridor of a signature morphism. -/
def corridor {S S' : FSig} (σ : S ⟶ S') : room In B S ⟶ room In B S' :=
  ⟨Sen.map σ, reductF σ, fun M φ => sat_map_iff σ M φ⟩

/-- **The unified Wasm institution**, as a functor into rooms. -/
def institution (In B : Type) : FSig ⥤ Room.{0, 0, 1} where
  obj := room In B
  map := corridor
  map_id _ := Room.hom_ext (funext fun φ => Sen.map_id φ)
    (Functor.ext (fun M => Model.reduct_id M) (fun _ _ _ => rfl))
  map_comp σ τ := Room.hom_ext (funext fun φ => Sen.map_comp σ τ φ)
    (Functor.ext (fun M => Model.reduct_comp σ τ M) (fun _ _ _ => rfl))

/-- The unified institution, bundled. -/
def inst (In B : Type) : Inst.{0, 0, 0, 0, 1} := ⟨FSig, institution In B⟩

/-! ## Signature-level vocabulary -/

/-- Every call of the sentence satisfies `P`. -/
def callsIn {C : Type} (P : C → Prop) : BSen C B → Prop
  | .always c _ => P c
  | .may c _ => P c
  | .and s t => callsIn P s ∧ callsIn P t
  | .top => True

/-- The sentence never mentions the opcode `o`. -/
def Sen.Avoids {S : FSig} (o : S.Op) (φ : Sen In B S) : Prop :=
  callsIn (fun x : Call In S => o ∉ UInstr.opsCode x.1) φ

/-- Two models of one signature are **elementarily equivalent**: they satisfy the same
sentences. -/
def Equiv {S : FSig} (M M' : Model In B S) : Prop := ∀ φ : Sen In B S, Sat M φ ↔ Sat M' φ

/-- The **behaviour chart** of a signature: points are its models. It places each signature of
the institution in the Atlas vocabulary (`Silmaril.Wasm.Atlas.Chart`). -/
def chart (In B : Type) (S : FSig) : Chart :=
  BChart (Model In B S) (Call In S) B (fun _ => True) Model.obs

end Silmaril.Wasm.Unified
