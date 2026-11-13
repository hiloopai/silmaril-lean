module

public import Silmaril.Wasm.Category.Institution.Defs

@[expose] public section

/-!
# Realisers through the institution API

A realiser with a surjective read-back is a model-expansive translation
(`Realiser.expTranslation`), so its comorphism, borrowing and validity transfer come from
`ExpTranslation` without carrying the surjectivity proof around. Everything is stated through
the institution facade `Silmaril.Inst`: `behInst L` is a facade `Institution₁`,
`Realiser.comorphism` is a facade `Comorphism` (`Realiser.coHom`, which is the comorphism of
the realiser's model-expansive translation, `Realiser.expTranslation_comorphism`), and the
facade lemmas give borrowing (`Realiser.valid_iff'`, `Realiser.entails_iff'`) and the
satisfaction condition (`Realiser.sat_sen_iff`). `valid_leSen_iff'` reads validity of `p ⊑ q`
as behaviour inclusion with the `⊨` notation, and `valid_leSen_iff_inst` with the facade's
`Valid`.
-/

namespace Silmaril.Wasm.Category

open CategoryTheory Silmaril.Compile.Category Silmaril.Wasm.Institution ObsSemantics
open scoped Silmaril.Inst

namespace Realiser

variable {L L' : Language.{0}} (T : Realiser L L')

/-- The comorphism of behavioural institutions of a realiser (`Realiser.coHom`), as a facade
comorphism. -/
abbrev comorphism : Silmaril.Inst.Comorphism (behInst L) (behInst L') := T.coHom

open scoped Silmaril.Inst in
/-- **The satisfaction condition of a realiser**, in the facade's notation. -/
theorem sat_sen_iff (K : Sig (Discrete L.Iface)) (β : (behInst L').Mod (T.comorphism.sig K))
    (s : (behInst L).Sen K) :
    β ⊨[behInst L'] T.comorphism.sen K s ↔ T.comorphism.mod K β ⊨[behInst L] s :=
  T.comorphism.sat_sen_iff K β s

/-- **A realiser with a surjective read-back is a model-expansive translation.** -/
def expTranslation (hg : Function.Surjective T.g) :
    ExpTranslation T.ifaceFunctor (obsSem L) (obsSem L') :=
  ⟨T.translation, T.sem_surjective hg⟩

theorem expTranslation_comorphism (hg : Function.Surjective T.g) :
    (T.expTranslation hg).comorphism = T.comorphism := rfl

/-- The comorphism of a realiser with a surjective read-back is model-expansive. -/
theorem comorphism_modelExpansive (hg : Function.Surjective T.g) :
    T.comorphism.ModelExpansive :=
  (T.expTranslation hg).modelExpansive

/-- Borrowing validity along a realiser with a surjective read-back, in the facade's terms. -/
theorem valid_iff' (hg : Function.Surjective T.g) {K : Sig (Discrete L.Iface)}
    (s : (behInst L).Sen K) :
    (behInst L).Valid s ↔ (behInst L').Valid (T.comorphism.sen K s) :=
  T.comorphism.valid_iff (T.comorphism_modelExpansive hg) s

/-- Borrowing consequence along a realiser with a surjective read-back, in the facade's
terms. -/
theorem entails_iff' (hg : Function.Surjective T.g) (K : Sig (Discrete L.Iface))
    (Γ : Set ((behInst L).Sen K)) (s : (behInst L).Sen K) :
    (behInst L).Entails Γ s ↔
      (behInst L').Entails (T.comorphism.sen K '' Γ) (T.comorphism.sen K s) :=
  T.comorphism.entails_iff (T.comorphism_modelExpansive hg) K Γ s

end Realiser

/-- Validity of `p ⊑ q` in the behavioural institution, with the `⊨` notation: every model of
the closed signature satisfies it iff `beh p ⊆ beh q`. -/
theorem valid_leSen_iff' (L : Language.{0}) (X : Discrete L.Iface) (p q : L.Prog) :
    (∀ β : (obsSem L).Model (Sig.closed X), β ⊨ (obsSem L).leSen X p q) ↔ L.beh p ⊆ L.beh q :=
  ((obsSem L).valid_iff _).symm.trans (valid_leSen_iff L X p q)

/-- Validity of `p ⊑ q` in the facade's terms: `Valid` in the facade institution `behInst L`
is behaviour inclusion. -/
theorem valid_leSen_iff_inst (L : Language.{0}) (X : Discrete L.Iface) (p q : L.Prog) :
    (behInst L).Valid ((obsSem L).leSen X p q) ↔ L.beh p ⊆ L.beh q :=
  (Silmaril.Inst.valid_ofObs_iff (obsSem L) _).trans (valid_leSen_iff L X p q)

end Silmaril.Wasm.Category
