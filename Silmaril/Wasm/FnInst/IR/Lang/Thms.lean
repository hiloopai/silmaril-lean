module

public import Silmaril.Wasm.FnInst.IR.Lang.Defs
public import Silmaril.Logic.Inst.Thms

/-!
# Function-body institutions: satisfaction, translations, borrowing

* `sat_le_iff`, `sat_eq_iff`, `sat_and_iff`: what the sentences mean.
* `sat_ctx_irrel`: satisfaction does not read the context part of a model. So every sentence
  is monotone (in both directions) in any information order on contexts: knowing more or less
  about the other functions of the module changes nothing for these call-free languages.
* `valid_eq_iff`: validity of `b ≐ b'` is equivalence of denotations in every environment
  (for an inhabited context type).
* `valid_transfer`: the satisfaction condition, read as transfer of validity along a
  signature morphism (from a small context to a bigger one).
* `Tr.sat_sen_iff`, `Tr.equiv_iff`, `Tr.le_iff`: a translation preserves and reflects
  refinement and equivalence of bodies.
* `Tr.modelExpansive`, `Tr.valid_iff`: borrowing validity along a translation whose
  environment map is surjective.
* `Tr.comorphism_comp_sen`, `Tr.comorphism_comp_mod`: the comorphism of a composite
  translation is the composite comorphism (sentences and models).
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst.IR

open CategoryTheory
open Silmaril.Inst
open Silmaril.Wasm.Institution (Formula)

namespace Lang

variable (L : Lang) {Sig : Type} [Category.{0} Sig] (F : Frame Sig)

theorem sat_iff {S : Sig} (M : (L.inst F).Mod S) (φ : (L.inst F).Sen S) :
    M ⊨[L.inst F] φ ↔ Formula.Holds (L.Le M.2 (F.hole S)) φ := Iff.rfl

@[simp] theorem sat_le_iff {S : Sig} (M : (L.inst F).Mod S) (b b' : L.Body (F.hole S)) :
    M ⊨[L.inst F] (Formula.le b b' : (L.inst F).Sen S) ↔
      Beh.Le (L.den M.2 _ b) (L.den M.2 _ b') := Iff.rfl

theorem Beh.equiv_iff_le {B B' : Beh} : Beh.Equiv B B' ↔ Beh.Le B B' ∧ Beh.Le B' B :=
  ⟨fun h => ⟨fun a o => (h a o).1, fun a o => (h a o).2⟩,
    fun h a o => ⟨h.1 a o, h.2 a o⟩⟩

@[simp] theorem sat_eq_iff {S : Sig} (M : (L.inst F).Mod S) (b b' : L.Body (F.hole S)) :
    M ⊨[L.inst F] (Formula.eq b b' : (L.inst F).Sen S) ↔
      Beh.Equiv (L.den M.2 _ b) (L.den M.2 _ b') := Beh.equiv_iff_le.symm

@[simp] theorem sat_and_iff {S : Sig} (M : (L.inst F).Mod S) (φ ψ : (L.inst F).Sen S) :
    M ⊨[L.inst F] (Formula.and φ ψ : (L.inst F).Sen S) ↔
      M ⊨[L.inst F] φ ∧ M ⊨[L.inst F] ψ := Iff.rfl

/-- Satisfaction does not depend on the context part of a model. -/
theorem sat_ctx_irrel {S : Sig} (c c' : F.Ctx S) (e : L.Env) (φ : (L.inst F).Sen S) :
    ((c, e) : (L.inst F).Mod S) ⊨[L.inst F] φ ↔ ((c', e) : (L.inst F).Mod S) ⊨[L.inst F] φ :=
  Iff.rfl

/-- **Monotonicity in information** about the rest of the module, for these languages: for any
relation `info` between contexts (for example "specifies more bodies"), a sentence satisfied
with less information is satisfied with more, and conversely. -/
theorem sat_mono {S : Sig} (info : F.Ctx S → F.Ctx S → Prop) {c c' : F.Ctx S} (_ : info c c')
    (e : L.Env) (φ : (L.inst F).Sen S) :
    ((c, e) : (L.inst F).Mod S) ⊨[L.inst F] φ ↔ ((c', e) : (L.inst F).Mod S) ⊨[L.inst F] φ :=
  Iff.rfl

theorem valid_eq_iff {S : Sig} [Nonempty (F.Ctx S)] (b b' : L.Body (F.hole S)) :
    (L.inst F).Valid (Formula.eq b b' : (L.inst F).Sen S) ↔
      ∀ e, Beh.Equiv (L.den e _ b) (L.den e _ b') := by
  constructor
  · intro h e
    exact (L.sat_eq_iff F (Classical.arbitrary _, e) b b').1 (h _)
  · intro h M
    exact (L.sat_eq_iff F M b b').2 (h M.2)

/-- **Transfer along an embedding**: a sentence valid over a signature is valid, translated,
over every signature it maps into. -/
theorem valid_transfer {S S' : Sig} (σ : S ⟶ S') {φ : (L.inst F).Sen S}
    (h : (L.inst F).Valid φ) : (L.inst F).Valid ((L.inst F).map σ φ) :=
  Institution.Valid.map σ h

namespace Tr

variable {L₁ L₂ L₃ : Lang} (T : Tr L₁ L₂)

@[simp] theorem comorphism_sen (S : Sig) (φ : (L₁.inst F).Sen S) :
    (T.comorphism F).sen S φ = φ.map (T.body _) := rfl

@[simp] theorem comorphism_mod (S : Sig) (M : (L₂.inst F).Mod S) :
    (T.comorphism F).mod S M = (M.1, T.env M.2) := rfl

theorem le_iff (e : L₂.Env) (h : Hole) (b b' : L₁.Body h) :
    Beh.Le (L₂.den e h (T.body h b)) (L₂.den e h (T.body h b')) ↔
      Beh.Le (L₁.den (T.env e) h b) (L₁.den (T.env e) h b') := by
  rw [T.den_body, T.den_body]

/-- **A translation preserves and reflects equivalence of bodies.** -/
theorem equiv_iff (e : L₂.Env) (h : Hole) (b b' : L₁.Body h) :
    Beh.Equiv (L₂.den e h (T.body h b)) (L₂.den e h (T.body h b')) ↔
      Beh.Equiv (L₁.den (T.env e) h b) (L₁.den (T.env e) h b') := by
  rw [T.den_body, T.den_body]

/-- The satisfaction condition of the comorphism of a translation. -/
theorem sat_sen_iff {S : Sig} (M : (L₂.inst F).Mod S) (φ : (L₁.inst F).Sen S) :
    M ⊨[L₂.inst F] ((T.comorphism F).sen S φ) ↔
      ((M.1, T.env M.2) : (L₁.inst F).Mod S) ⊨[L₁.inst F] φ :=
  Comorphism.sat_sen_iff (T.comorphism F) S M φ

/-- The comorphism of a translation with a surjective environment map is model-expansive. -/
theorem modelExpansive (hs : Function.Surjective T.env) : (T.comorphism F).ModelExpansive := by
  rw [Comorphism.modelExpansive_iff]
  intro S M
  obtain ⟨e, he⟩ := hs M.2
  refine ⟨(M.1, e), ?_⟩
  change ((M.1, T.env e) : F.Ctx S × L₁.Env) = M
  rw [he]
  rfl

/-- **Borrowing**: validity in `L₁` is validity of the translated sentence in `L₂`. -/
theorem valid_iff (hs : Function.Surjective T.env) {S : Sig} (φ : (L₁.inst F).Sen S) :
    (L₁.inst F).Valid φ ↔ (L₂.inst F).Valid ((T.comorphism F).sen S φ) :=
  Comorphism.valid_iff (T.comorphism F) (T.modelExpansive F hs) φ

theorem comorphism_comp_sen (U : Tr L₂ L₃) (S : Sig) (φ : (L₁.inst F).Sen S) :
    ((T.comp U).comorphism F).sen S φ = (T.comorphism F ≫ᶜ U.comorphism F).sen S φ := by
  exact (Formula.map_map (T.body _) (U.body _) (φ : Formula (L₁.Body (F.hole S)))).symm

theorem comorphism_comp_mod (U : Tr L₂ L₃) (S : Sig) (M : (L₃.inst F).Mod S) :
    ((T.comp U).comorphism F).mod S M = (T.comorphism F ≫ᶜ U.comorphism F).mod S M := rfl

theorem id_env_surjective (L : Lang) : Function.Surjective (Tr.id L).env :=
  fun e => ⟨e, rfl⟩

end Tr

end Lang

end Silmaril.Wasm.FnInst.IR
