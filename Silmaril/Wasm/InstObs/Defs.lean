module

public import Silmaril.Logic.Inst.Thms
public import Silmaril.Wasm.Institution.Generic.Defs

/-!
# Facade builders for observational semantics

The institution facade `Silmaril.Inst` (`Silmaril.Logic.Inst`) for the generic construction of
`Silmaril.Wasm.Institution.Generic`: an `ObsSemantics` gives an institution, a `Translation` a
comorphism, and a translation over the identity interface functor a morphism.

* `Institution.ofObs S : Institution₁` (silmaril's `S.inst : Inst.{1, 0, 0, 0, 0}`);
* `Comorphism.ofObs T : Comorphism (.ofObs A) (.ofObs B)` (`T.coHom`);
* `Morphism.ofObs T : Morphism (.ofObs B) (.ofObs A)` (`T.toHom`);
* `sat_ofObs_iff`, `Comorphism.ofObs_sen`, `Comorphism.ofObs_mod`: the facade notions are the
  generic ones (`rfl`);
* `Comorphism.ofObs_modelExpansive`, `Morphism.ofObs_sound`: surjective semantic maps give
  borrowing.

These are abbreviations, so `Comorphism.ofObs T` *is* `T.coHom` and every existing statement
about `T.coHom` applies.

**Reducible and noncomputable output.** All three builders are reducible (`abbrev`), so `rw`,
`simp`, `ext` and instance search see through them to the observational semantics. The
comorphism and morphism builders are `noncomputable`: comorphisms are only used in statements
and proofs, so no code is generated for them. (an earlier step of the guide reported a code-generator
failure, `unknown join point`, on a concrete translation; an earlier step did not reproduce it.) A
computable definition that names one is rejected with Lean's ordinary hint (mark it
`noncomputable`); a `noncomputable def`, a `theorem` or an `example` use them directly. The
semantics passed in should itself be reducible (declare it with `abbrev`): otherwise
`[1] : natOut.Prog` does not elaborate under `rw`, and instance search does not see
`intOut.Sem X = Set ℤ`.

The comorphism and morphism of a model-expansive translation are
`ObsSemantics.ExpTranslation.comorphism` and `.morphism`, and the canonical `β ⊨ s` instance is
`ObsSemantics.instSatisfies`, both in `Silmaril.Wasm.Institution.Api.Defs`, which imports this
module.
-/

@[expose] public section

namespace Silmaril.Inst

open CategoryTheory
open Silmaril.Wasm.Institution (ObsSemantics Sig)
open Silmaril.Wasm.Institution.ObsSemantics (Translation)

variable {I J : Type} [Category.{0} I] [Category.{0} J]

/-- The institution of an observational semantics. -/
abbrev Institution.ofObs (S : ObsSemantics I) : Institution₁ where
  Sign := Sig I
  I :=
    { obj := fun K => ⟨ObsSemantics.Sen S K, Cat.of (S.Model K), S.Sat K⟩
      map := S.corridor
      map_id := S.institution.map_id
      map_comp := S.institution.map_comp }

/-- `Institution.ofObs S` is `S.inst`. It is written out as constructors so that its signatures,
sentences, models and satisfaction are `Sig I`, `S.Sen K`, `S.Model K` and `S.Sat K` at reducible
transparency (`S.inst`, `S.institution` and `S.room` are `def`s): `simp`, `rw` and instance
search see through `(Institution.ofObs S).Sign`, `.Sen K` and `.Mod K`. -/
theorem Institution.ofObs_eq_inst (S : ObsSemantics I) : Institution.ofObs S = S.inst := rfl

/-- The comorphism of a translation of observational semantics (reducible, noncomputable). -/
noncomputable abbrev Comorphism.ofObs {F : I ⥤ J} {A : ObsSemantics I} {B : ObsSemantics J}
    (T : Translation F A B) : Comorphism (Institution.ofObs A) (Institution.ofObs B) :=
  T.coHom

/-- The institution morphism of a translation over the identity interface functor (reducible,
noncomputable). -/
noncomputable abbrev Morphism.ofObs {A B : ObsSemantics I} (T : Translation (𝟭 I) A B) :
    Morphism (Institution.ofObs B) (Institution.ofObs A) :=
  T.toHom

/-- Satisfaction in `Institution.ofObs S` is the generic satisfaction. Its `simp` priority is
low, so that the transfer lemmas (`Comorphism.sat_sen_iff`, `Institution.sat_map_iff`) fire
first on translated sentences. -/
@[simp low] theorem sat_ofObs_iff (S : ObsSemantics I) {K : Sig I} (β : S.Model K)
    (s : ObsSemantics.Sen S K) : β ⊨[Institution.ofObs S] s ↔ S.Sat K β s :=
  Iff.rfl

/-- Validity in `Institution.ofObs S` is the generic validity. -/
theorem valid_ofObs_iff (S : ObsSemantics I) {K : Sig I} (s : ObsSemantics.Sen S K) :
    (Institution.ofObs S).Valid s ↔ S.Valid s := by
  rw [S.valid_iff]
  rfl

@[simp] theorem Comorphism.ofObs_sig {F : I ⥤ J} {A : ObsSemantics I} {B : ObsSemantics J}
    (T : Translation F A B) (K : Sig I) : (Comorphism.ofObs T).sig K = (Sig.map F).obj K :=
  rfl

@[simp] theorem Comorphism.ofObs_sen {F : I ⥤ J} {A : ObsSemantics I} {B : ObsSemantics J}
    (T : Translation F A B) (K : Sig I) (s : ObsSemantics.Sen A K) :
    (Comorphism.ofObs T).sen K s = T.sen s :=
  rfl

@[simp] theorem Comorphism.ofObs_mod {F : I ⥤ J} {A : ObsSemantics I} {B : ObsSemantics J}
    (T : Translation F A B) (K : Sig I) (β : B.Model ((Sig.map F).obj K)) :
    (Comorphism.ofObs T).mod K β = (T.modFun K).obj β :=
  rfl

/-- Surjective semantic maps make the comorphism of a translation model-expansive. -/
theorem Comorphism.ofObs_modelExpansive {F : I ⥤ J} {A : ObsSemantics I} {B : ObsSemantics J}
    (T : Translation F A B) (h : ∀ X, Function.Surjective (T.sem X)) :
    (Comorphism.ofObs T).ModelExpansive :=
  T.coHom_modelExpansive h

/-- Surjective semantic maps make the morphism of a translation sound. -/
theorem Morphism.ofObs_sound {A B : ObsSemantics I} (T : Translation (𝟭 I) A B)
    (h : ∀ X, Function.Surjective (T.sem X)) : (Morphism.ofObs T).Sound :=
  T.toHom_sound h

/-- The facade transfer lemma specialises to the generic one. -/
example {F : I ⥤ J} {A : ObsSemantics I} {B : ObsSemantics J} (T : Translation F A B)
    (K : Sig I) (β : B.Model ((Sig.map F).obj K)) (s : ObsSemantics.Sen A K) :
    β ⊨[Institution.ofObs B] T.sen s ↔ (T.modFun K).obj β ⊨[Institution.ofObs A] s :=
  (Comorphism.ofObs T).sat_sen_iff K β s

/-- Borrowing validity along a translation, through the facade. -/
example {F : I ⥤ J} {A : ObsSemantics I} {B : ObsSemantics J} (T : Translation F A B)
    (h : ∀ X, Function.Surjective (T.sem X)) {K : Sig I} (s : ObsSemantics.Sen A K) :
    (Institution.ofObs A).Valid s ↔ (Institution.ofObs B).Valid (T.sen s) :=
  (Comorphism.ofObs T).valid_iff (Comorphism.ofObs_modelExpansive T h) s

end Silmaril.Inst
