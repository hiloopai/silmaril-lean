module

public import Silmaril.Wasm.Institution.SpecGInst.Base
public import Silmaril.Games.InstFacade.Defs
import Silmaril.Proofs.Wasm.Institution.SpecGInst.Traces

/-!
# The trace institutions of `Spec.Format` in the institution of game semantics

`Silmaril.Wasm.Institution.GameInst.Defs` records why the corridors `specCorridor` from
`Spec.Format.inst L stratSemantics` to `GInst` are not a comorphism: Spec models carry their
observation (so the model square does not commute strictly), and a Spec interface morphism
erases unobserved imports, which no lens-like `GInst` lower renaming does. This module removes
both obstacles and builds the comorphism.

* **Observation quotient.** `traceInst L : Inst` has the signatures of `IfaceB` (interfaces with
  import-bijective morphisms), the sentences of `Spec.Format.inst L _`, and as models the good
  trace sets (`TModel X`), reducted by `Spec.reduct`. A Spec model satisfies a sentence iff its
  trace set does (`sat_traces_iff`), and taking traces commutes with reducts
  (`Model.traces_reduct`), so `traceInst L` is `Spec.Format.inst L S` quotiented by
  observation, for every semantics `S`.
* **Imports.** Along an import-bijective morphism, `Spec` observation renames imports and
  erases none, and the `GInst` lower renaming is the inverse renaming (`specHom`).
* **The comorphism** `specCoHom L : Inst.CoHom (traceInst L) GInst`, the comorphism of the game
  reading `reading L : GInst.Reading (traceInst L)` (`Silmaril.Games.InstFacade.Defs`). Signatures
  go to their games (`specΦ`), a strategy to its traces, and a Spec sentence `(τ, φ)` to "`φ`
  holds of the traces observed through `τ`". The reading is natural by `traces_reduct`: **the
  traces of the `GInst` reduct are the `Spec` observation of the traces** (corridors
  `(reading L).corridor X`, naturality `(reading L).sen_map f s`). Its proof uses the
  play-level description of the reduct, `Game.mem_reduct_iff_rel`.
* `sat_ofProg_iff`: for a strategy read as a `stratSemantics` program, Spec satisfaction is
  `GInst` satisfaction of the translated sentence.

Morphisms that erase imports (`Spec` interface morphisms whose import map is not onto) remain
outside: their observation is not the reduct along any game morphism of the form `specHom`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.SpecGInst

open CategoryTheory Silmaril.Logic.Institution Silmaril.Games Silmaril.Wasm.Spec
open Silmaril.Wasm.Institution.GameInst

variable {Ty A R : Type}

/-- **The traces of the `GInst` reduct are the `Spec` observation of the traces.** -/
theorem traces_reduct {Z X : IfaceB Ty} (f : Z ⟶ X) (σ : (specGame A R X.X).Model) :
    stratTraces (Game.reduct (specHom f) σ) = Silmaril.Wasm.Spec.reduct (BHom.hom f) (stratTraces σ) :=
  Silmaril.Proofs.Wasm.Institution.SpecGInst.traces_reduct f σ

/-! ## The observation quotient -/

/-- Trace models at an interface: good trace sets, with equalities as morphisms. -/
def TModel (A R : Type) (X : IfaceB Ty) : Type := {T : Set (List (Event A R X.X)) // Good T}

instance TModel.category (X : IfaceB Ty) : Category.{0} (TModel A R X) where
  Hom T T' := PLift (T = T')
  id _ := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩

/-- Satisfaction by a trace set: the formula holds of the traces observed through the scope. -/
def TSat (L : Logic Ty A R) {X : IfaceB Ty} (T : TModel A R X) (s : Sen L X.X) : Prop :=
  L.Sat (Silmaril.Wasm.Spec.reduct s.obs T.1) s.φ

/-- The reduct of trace models. -/
def treduct (A R : Type) {Z X : IfaceB Ty} (f : Z ⟶ X) : TModel A R X ⥤ TModel A R Z where
  obj T := ⟨Silmaril.Wasm.Spec.reduct (BHom.hom f) T.1, T.2.reduct _⟩
  map h := ⟨congrArg (fun T : TModel A R X =>
    (⟨Silmaril.Wasm.Spec.reduct (BHom.hom f) T.1, T.2.reduct _⟩ : TModel A R Z)) h.down⟩

/-- The room of an interface. -/
def troom (L : Logic Ty A R) (X : IfaceB Ty) : Room.{0, 0, 0} :=
  ⟨Sen L X.X, Cat.of (TModel A R X), TSat L⟩

/-- The corridor of a morphism; the satisfaction condition is functoriality of observation. -/
def tcorridor (L : Logic Ty A R) {Z X : IfaceB Ty} (f : Z ⟶ X) : troom L Z ⟶ troom L X :=
  ⟨Sen.map (BHom.hom f), treduct A R f, fun T s => by
    change L.Sat (Silmaril.Wasm.Spec.reduct (s.obs ≫ BHom.hom f) T.1) s.φ ↔
      L.Sat (Silmaril.Wasm.Spec.reduct s.obs (Silmaril.Wasm.Spec.reduct (BHom.hom f) T.1)) s.φ
    rw [Silmaril.Wasm.Spec.reduct_comp]⟩

/-- The trace institution of `L`-specifications, as a functor into rooms. -/
def tinstitution (L : Logic Ty A R) : IfaceB Ty ⥤ Room.{0, 0, 0} where
  obj := troom L
  map := tcorridor L
  map_id _ := Room.hom_ext (funext fun s => by cases s; rfl)
    (CategoryTheory.Functor.ext (fun T => Subtype.ext (Silmaril.Wasm.Spec.reduct_id T.1))
      (fun _ _ _ => rfl))
  map_comp f g := Room.hom_ext (funext fun s => by cases s; rfl)
    (CategoryTheory.Functor.ext
      (fun T => Subtype.ext (Silmaril.Wasm.Spec.reduct_comp (BHom.hom f) (BHom.hom g) T.1))
      (fun _ _ _ => rfl))

/-- **The trace institution of `L`-specifications** over interfaces with import-bijective
morphisms: `Spec.Format.inst L _` quotiented by observation. -/
def traceInst (L : Logic Ty A R) : Inst.{0, 0, 0, 0, 0} := ⟨IfaceB Ty, tinstitution L⟩

/-- **A Spec model satisfies a sentence iff its trace set does.** -/
theorem sat_traces_iff (L : Logic Ty A R) (S : Semantics Ty A R) {X : IfaceB Ty}
    (M : Model S X.X) (s : Sen L X.X) :
    Silmaril.Wasm.Spec.Sat L S M s ↔ TSat L (⟨M.traces, M.good⟩ : TModel A R X) s :=
  Silmaril.Wasm.Spec.sat_iff L S M s

/-! ## The comorphism into `GInst` -/

/-- The traces of a strategy, as a trace model. -/
def traceModel (X : IfaceB Ty) : (specGame A R X.X).DModel ⥤ TModel A R X where
  obj σ := ⟨stratTraces (σ : (specGame A R X.X).Model), stratTraces_good σ⟩
  map h := ⟨congrArg (fun σ : (specGame A R X.X).Model =>
    (⟨stratTraces σ, stratTraces_good σ⟩ : TModel A R X)) h.down⟩

/-- **The game reading of the trace institution**: a strategy is read as its traces. -/
def reading (L : Logic Ty A R) : GInst.Reading (traceInst L) where
  game := specΦ A R
  mod (X : IfaceB Ty) := (traceModel (A := A) (R := R) X).obj
  mod_reduct f σ := Subtype.ext (traces_reduct f σ).symm

/-- The sentence translation: `φ` holds of the strategy's traces observed through the scope.
It is the sentence translation of `reading L`. -/
def senOf (L : Logic Ty A R) (X : IfaceB Ty) (s : Sen L X.X) :
    GSen (specGame A R X.X).E (specGame A R X.X).F :=
  (reading L).sen X s

/-- **The comorphism from the trace institution of `L`-specifications into `GInst`**: the
comorphism of the game reading `reading L`. -/
def specCoHom (L : Logic Ty A R) : Inst.CoHom (traceInst L) GInst :=
  (reading L).coHom

/-- **Spec satisfaction of a strategy is `GInst` satisfaction of the translated sentence.** -/
theorem sat_ofProg_iff (L : Logic Ty A R) {X : IfaceB Ty} (σ : (specGame A R X.X).Model)
    (s : Sen L X.X) :
    Silmaril.Wasm.Spec.Sat L (stratSemantics Ty A R) (Model.ofProg σ) s ↔ (senOf L X s).holds σ := by
  change L.Sat (Silmaril.Wasm.Spec.reduct (s.obs ≫ 𝟙 X.X) (stratTraces σ)) s.φ ↔
    L.Sat (Silmaril.Wasm.Spec.reduct s.obs (stratTraces σ)) s.φ
  rw [Category.comp_id]

end Silmaril.Wasm.Institution.SpecGInst
