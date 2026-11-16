module

public import Silmaril.Logic.Consequence.Institution.Defs
public import Silmaril.Logic.Consequence.Refutation.Thms
public import Silmaril.Logic.Consequence.Gentzen.Thms
import Silmaril.Proofs.Logic.Consequence.Institution.Basic

/-!
# Institutions and logics as list-premise consequence systems: laws

**Agreement.** `roomSeq_iff_entails`: `roomSeq R Γ φ` is `Room.Entails` on the members of `Γ`
(so `roomSeq` is `roomSys` restricted to finite contexts). `roomMulti_eq_valid`: `roomMulti R` is
`Gentzen.Valid R.Sat`. `roomMulti_single_eq`: its singleton-succedent part is `roomSeq R`.
`listSys_semanticER`: the semantic entailment relation of `R` gives `roomSeq R` again.

**Closure (exactly these rules).**

* `roomSeq_closed`, `listSys_closed`, `entails_localSat_closed`: `Structural.Closed tarskiRules`,
  that is reflexivity (`c ∈ Γ → Γ ⊢ c`), weakening along list inclusion (hence exchange and
  contraction, `Structural.WeakSubset.exchange`, `.contraction`) and finite multi-cut with
  concatenated contexts. The closure is idempotent: these systems are fixed points of
  `Structural.closure tarskiRules` (`roomSeq_derives_eq`).
* `roomMulti_closed`, `valid_localSat_closed`: `Gentzen.Closed defaultRules`: reflexivity
  (a shared formula), weakening of both sides along list inclusion, and cut
  `Γ ⊢ a, Δ` / `a, Γ' ⊢ Δ'` ⟹ `Γ, Γ' ⊢ Δ, Δ'`.
* **Reflection.** `corridorSeq_reflect`: along a corridor whose model reduct is surjective on
  objects, `roomSeq` is reflected as well as preserved.
* **Translation (reindexing along signature morphisms).** `corridorSeq`, `institutionSeq`,
  `corridorMulti` (existing) and `LogicalSystem.seqTranslation` are sound translations
  (definitions in `Defs`). `institutionSeq_id`: the identity signature morphism translates by the
  identity.

**Transfer.** `valid_map_of_sat`, `entails_map_of_sat`: a map of formulas with a backwards
map of points satisfying the satisfaction condition preserves both systems. Substitutions
(with a semantic substitution lemma) and signature morphisms (with reducts) are instances.

**Local versus global.** `entails_localSat_le_validIn`: point-wise single-conclusion
consequence implies model-wise consequence. The converse and the multiple-conclusion analogue
fail (`Silmaril.Logic.Consequence.Institution.Examples`).

**Soundness of a logic.** `listSys_le_roomSeq`: if `L` is sound, its derivability is below
semantic consequence at every signature.
-/

@[expose] public section

namespace Silmaril.Consequence

open CategoryTheory Silmaril.Logic Silmaril.Logic.Institution

universe u v w t m₁ m₂

section Room

variable (R : Room.{w, m₁, m₂})

theorem roomSeq_iff_entails (Γ : List R.Sen) (φ : R.Sen) :
    roomSeq R Γ φ ↔ R.Entails {x | x ∈ Γ} φ := Iff.rfl

theorem roomSeq_closed : Structural.Closed Structural.tarskiRules (roomSeq R) :=
  Refutation.entails_closed

theorem roomSeq_derives_eq :
    Structural.Derives Structural.tarskiRules (roomSeq R) = roomSeq R :=
  Structural.derives_eq_self (roomSeq_closed R)

theorem roomSeq_exchange : Structural.Exchange (roomSeq R) :=
  Structural.WeakSubset.exchange (roomSeq_closed R).weak

theorem roomSeq_contraction : Structural.Contraction (roomSeq R) :=
  Structural.WeakSubset.contraction (roomSeq_closed R).weak

theorem roomMulti_eq_valid : roomMulti R = Gentzen.Valid R.Sat := rfl

theorem roomMulti_closed : Gentzen.Closed Gentzen.defaultRules (roomMulti R) :=
  Gentzen.valid_closed

theorem roomMulti_single_eq : (roomMulti R).single = roomSeq R :=
  funext fun _ => funext fun _ => propext Gentzen.entails_iff_valid.symm

theorem listSys_semanticER : ER.listSys R.semanticER = roomSeq R := rfl

end Room

/-- A corridor whose model reduct is surjective on objects **reflects** `roomSeq`: the translation
is conservative. -/
theorem corridorSeq_reflect {R₁ R₂ : Room.{w, m₁, m₂}} (f : Corridor R₁ R₂)
    (hs : Function.Surjective f.mod.obj) {Γ : List R₁.Sen} {φ : R₁.Sen}
    (h : roomSeq R₂ (Γ.map f.sen) (f.sen φ)) : roomSeq R₁ Γ φ := fun M hM => by
  obtain ⟨N, rfl⟩ := hs M
  exact (f.sat N φ).1 (h N fun c hc => by
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc; exact (f.sat N c').2 (hM c' hc'))

theorem institutionSeq_id {Sign : Type u} [Category.{v} Sign] (I : Sign ⥤ Room.{w, m₁, m₂})
    (S : Sign) : (institutionSeq I (𝟙 S)).ax = id ∧ (institutionSeq I (𝟙 S)).c = id := by
  simp [institutionSeq, corridorSeq, I.map_id, Room.id_sen]

section Local

variable {Mod : Type u} {Pt : Mod → Type v} {C : Type w} (sat : (m : Mod) → Pt m → C → Prop)

theorem entails_localSat_closed :
    Structural.Closed Structural.tarskiRules (Refutation.Entails (localSat sat)) :=
  Refutation.entails_closed

theorem valid_localSat_closed : Gentzen.Closed Gentzen.defaultRules (Gentzen.Valid (localSat sat)) :=
  Gentzen.valid_closed

/-- Point-wise single-conclusion consequence implies model-wise consequence. -/
theorem entails_localSat_le_validIn :
    Refutation.Entails (localSat sat) ≤ Refutation.Entails (validIn sat) :=
  fun _ _ h m hm p => h ⟨m, p⟩ fun x hx => hm x hx p

end Local

section Transfer

variable {M : Type u} {M' : Type v} {C : Type w} {C' : Type t}
  {sat : M → C → Prop} {sat' : M' → C' → Prop}

/-- **Closure under a map of formulas** `g` with a backwards map of points `f` satisfying the
satisfaction condition `sat' m (g c) ↔ sat (f m) c` (a substitution with its semantic
substitution lemma, or a signature morphism with its reduct). -/
theorem valid_map_of_sat (g : C → C') (f : M' → M) (h : ∀ m c, sat' m (g c) ↔ sat (f m) c)
    {Γ Δ : List C} (hv : Gentzen.Valid sat Γ Δ) : Gentzen.Valid sat' (Γ.map g) (Δ.map g) :=
  fun m hm => let ⟨d, hd, hs⟩ := hv (f m) fun c hc => (h m c).1 (hm _ (List.mem_map_of_mem hc))
    ⟨g d, List.mem_map_of_mem hd, (h m d).2 hs⟩

theorem entails_map_of_sat (g : C → C') (f : M' → M) (h : ∀ m c, sat' m (g c) ↔ sat (f m) c)
    {Γ : List C} {c : C} (he : Refutation.Entails sat Γ c) :
    Refutation.Entails sat' (Γ.map g) (g c) :=
  Gentzen.entails_iff_valid.2 (valid_map_of_sat g f h (Gentzen.entails_iff_valid.1 he))

end Transfer

theorem listSys_closed (E : Metatheory.ER.{w}) :
    Structural.Closed Structural.tarskiRules (ER.listSys E) :=
  Proofs.Logic.Consequence.Institution.listSys_closed E

/-- A sound logic derives only semantic consequences, at every signature. -/
theorem listSys_le_roomSeq {Sign : Type u} [Category.{v} Sign]
    {L : Metatheory.LogicalSystem.{u, v, w, m₁, m₂} Sign} (h : L.Sound) (S : Sign) :
    LogicalSystem.listSys L S ≤ roomSeq (L.I.obj S) :=
  fun Γ φ d => h S {x | x ∈ Γ} φ d

end Silmaril.Consequence
