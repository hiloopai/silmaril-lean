module

public import Silmaril.Logic.HOLLight.Soundness
public import Silmaril.Logic.HOLLight.Kernel.Structural
public import Mathlib.CategoryTheory.Category.Preorder

@[expose] public section

/-!
# HOL signatures, sequents and syntactic metatheory

Foundations for `Metatheory.HOL`: HOL signatures ordered by extension (`HolSig`), well-typed
sequents (`HOL.Seq`) and their translation along extensions, and the syntactic facts about the
existing kernel `Silmaril.Logic.HOLLight.Derives` needed to package it as a logic: typing and
derivability are preserved by signature extension (`HOL.hasType_of_le`, `HOL.derives_of_le`),
the kernel only derives well-typed sequents (`HOL.derives_typed`), and axioms can be cut
(`HOL.derives_cut_axioms`).
-/

namespace Silmaril.Logic.Institution.Metatheory

open CategoryTheory Silmaril.Logic.HOLLight

universe u
/-- HOL signatures, ordered by extension. -/
structure HolSig where
  /-- The underlying HOL Light signature. -/
  sig : Signature

namespace HolSig

/-- `Σ ≤ Σ'` when `Σ'` extends `Σ`: both the type operators and the constants of `Σ` are a
prefix of those of `Σ'` (so positions, which name symbols in `HOLLight.Tm`, are kept). -/
instance : Preorder HolSig where
  le S T := S.sig.tyOps <+: T.sig.tyOps ∧ S.sig.consts <+: T.sig.consts
  le_refl S := ⟨List.prefix_refl _, List.prefix_refl _⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

end HolSig

namespace HOL

/-- A lookup in a prefix of a list is a lookup in the list. -/
theorem lookup_of_prefix {α : Type*} {l l' : List α} (h : l <+: l') {n : Nat} {a : α}
    (hn : l[n]? = some a) : l'[n]? = some a := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hn).1]
  exact hn

/-- Well-formedness of types is preserved by extending the type operators. -/
theorem Ty.wellFormed_of_prefix {ops ops' : List Nat} (h : ops <+: ops') {A : Ty}
    (hA : A.WellFormed ops) : A.WellFormed ops' := by
  induction A using Ty.induction_on with
  | var | bool | ind => trivial
  | arr A B ihA ihB =>
    simp only [Ty.WellFormed] at hA ⊢
    exact ⟨ihA hA.1, ihB hA.2⟩
  | app c args ih =>
    simp only [Ty.WellFormed, Ty.wellFormedList_iff] at hA ⊢
    exact ⟨lookup_of_prefix h hA.1, fun B hB => ih B hB (hA.2 B hB)⟩

/-- Typing is preserved by signature extension. -/
theorem hasType_of_le {S T : HolSig} (h : S ≤ T) {Γ : List Ty} {t : Tm} {A : Ty}
    (ht : HasType S.sig Γ t A) : HasType T.sig Γ t A := by
  have hty : ∀ {B : Ty}, B.WellFormed S.sig.tyOps → B.WellFormed T.sig.tyOps :=
    fun hB => Ty.wellFormed_of_prefix h.1 hB
  induction ht with
  | bvar lookup wf => exact .bvar lookup (hty wf)
  | fvar n wf => exact .fvar n (hty wf)
  | const hc =>
    refine .const ?_
    cases hc with
    | eq wf => exact .eq (hty wf)
    | select wf => exact .select (hty wf)
    | user lookup scheme arity args =>
      exact .user (lookup_of_prefix h.2 lookup) ⟨hty scheme.1, scheme.2⟩ arity
        (fun B hB => hty (args B hB))
  | app _ _ ihf ihx => exact .app ihf ihx
  | lam wf _ ih => exact .lam (hty wf) ih

/-- The kernel only derives well-typed sequents: the conclusion and every hypothesis of a
derivable `H ⊢ p` have type `bool`. Needed to turn an arbitrary `HOLLight.Derives` derivation
into a sentence `HOL.Seq` (`sound_iff_derives_sound`, direction `→`) and to restrict the
substitution of an `inst` step to the smaller signature (`derives_of_le`). By induction, with
`HasType.tySubst` and `HasType.freeSubst` for the instantiation rules. -/
theorem derives_typed {sig : Signature} {theory : HOLLight.Theory} {H : Hyps} {p : Tm}
    (d : Derives sig theory H p) : HasType sig [] p .bool ∧ TypedHyps sig [] H := by
  exact ⟨d.typing, d.typedHyps⟩

/-- The types of the free variables of a typed term are well formed. -/
theorem freeVars_wellFormed {sig : Signature} {Γ : List Ty} {t : Tm} {A : Ty}
    (ht : HasType sig Γ t A) {n : Nat} {B : Ty} (hn : (n, B) ∈ t.freeVars) :
    B.WellFormed sig.tyOps := by
  induction ht with
  | bvar | const => simp [Tm.freeVars] at hn
  | fvar m wf =>
    simp only [Tm.freeVars, List.mem_singleton, Prod.mk.injEq] at hn
    obtain ⟨rfl, rfl⟩ := hn
    exact wf
  | app _ _ ihf ihx =>
    rcases List.mem_append.mp hn with hn | hn
    · exact ihf hn
    · exact ihx hn
  | lam _ _ ih => exact ih hn

/-- Kernel derivability is preserved by signature extension. The `inst` rule's typing premise
is contravariant in the type operators (it quantifies over types well-formed in the larger
signature), so the substitution is first restricted to types well-formed in `S` (identity
`fvar n A` elsewhere), which does not change `p` or `H` by `derives_typed`. -/
theorem derives_of_le {S T : HolSig} (h : S ≤ T) {theory : HOLLight.Theory} {H : Hyps} {p : Tm}
    (d : Derives S.sig theory H p) : Derives T.sig theory H p := by
  classical
  have hty : ∀ {B : Ty}, B.WellFormed S.sig.tyOps → B.WellFormed T.sig.tyOps :=
    fun hB => Ty.wellFormed_of_prefix h.1 hB
  induction d with
  | «axiom» member typing => exact .axiom member (hasType_of_le h typing)
  | refl typing => exact .refl (hasType_of_le h typing)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | mkComb _ _ ih₁ ih₂ => exact .mkComb ih₁ ih₂
  | abs name domain fresh _ ih => exact .abs name (hty domain) fresh ih
  | beta name domain typing fresh =>
    exact .beta name (hty domain) (hasType_of_le h typing) fresh
  | assume typing => exact .assume (hasType_of_le h typing)
  | eqMp _ _ ih₁ ih₂ => exact .eqMp ih₁ ih₂
  | deductAntisym _ _ ih₁ ih₂ => exact .deductAntisym ih₁ ih₂
  | @inst H p σ typing d ih =>
    let σ' : Nat → Ty → Tm := fun n A =>
      if A.WellFormed S.sig.tyOps then σ n A else .fvar n A
    have hσ' : ∀ n A, A.WellFormed T.sig.tyOps → HasType T.sig [] (σ' n A) A := by
      intro n A hA
      simp only [σ']
      split
      · exact hasType_of_le h (typing n A ‹_›)
      · exact .fvar n hA
    have hcongr : ∀ q : Tm, HasType S.sig [] q .bool → q.freeSubst σ' = q.freeSubst σ := by
      intro q hq
      apply Tm.freeSubst_congr
      intro n A hn
      simp [σ', freeVars_wellFormed hq hn]
    have d' := Derives.inst (theory := theory) σ' hσ' ih
    rw [hcongr p d.typing] at d'
    rwa [Finset.image_congr (g := Tm.freeSubst σ)
      (fun q hq => hcongr q (d.typedHyps q hq))] at d'
  | instType σ typing _ ih => exact .instType σ (fun n => hty (typing n)) ih

/-- Axioms can be replaced by their derivations: if every axiom of `theory` is derivable without
hypotheses from axioms satisfying `P`, then so is everything derivable from `theory`. -/
theorem derives_cut_axioms {sig : Signature} {theory : HOLLight.Theory} {H : Hyps} {p : Tm}
    (P : Tm → Prop) (d : Derives sig theory H p)
    (hT : ∀ a ∈ theory, ∃ T' : HOLLight.Theory, (∀ b ∈ T', P b) ∧ Derives sig T' ∅ a) :
    ∃ T' : HOLLight.Theory, (∀ b ∈ T', P b) ∧ Derives sig T' H p := by
  induction d with
  | «axiom» member _ => exact hT _ member
  | refl typing => exact ⟨[], by simp, .refl typing⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨T₁, hP₁, d₁⟩ := ih₁
    obtain ⟨T₂, hP₂, d₂⟩ := ih₂
    exact ⟨T₁ ++ T₂, fun b hb => (List.mem_append.mp hb).elim (hP₁ b) (hP₂ b),
      .trans (d₁.mono_theory fun _ hb => List.mem_append_left _ hb)
        (d₂.mono_theory fun _ hb => List.mem_append_right _ hb)⟩
  | mkComb _ _ ih₁ ih₂ =>
    obtain ⟨T₁, hP₁, d₁⟩ := ih₁
    obtain ⟨T₂, hP₂, d₂⟩ := ih₂
    exact ⟨T₁ ++ T₂, fun b hb => (List.mem_append.mp hb).elim (hP₁ b) (hP₂ b),
      .mkComb (d₁.mono_theory fun _ hb => List.mem_append_left _ hb)
        (d₂.mono_theory fun _ hb => List.mem_append_right _ hb)⟩
  | abs name domain fresh _ ih =>
    obtain ⟨T₁, hP₁, d₁⟩ := ih
    exact ⟨T₁, hP₁, .abs name domain fresh d₁⟩
  | beta name domain typing fresh => exact ⟨[], by simp, .beta name domain typing fresh⟩
  | assume typing => exact ⟨[], by simp, .assume typing⟩
  | eqMp _ _ ih₁ ih₂ =>
    obtain ⟨T₁, hP₁, d₁⟩ := ih₁
    obtain ⟨T₂, hP₂, d₂⟩ := ih₂
    exact ⟨T₁ ++ T₂, fun b hb => (List.mem_append.mp hb).elim (hP₁ b) (hP₂ b),
      .eqMp (d₁.mono_theory fun _ hb => List.mem_append_left _ hb)
        (d₂.mono_theory fun _ hb => List.mem_append_right _ hb)⟩
  | deductAntisym _ _ ih₁ ih₂ =>
    obtain ⟨T₁, hP₁, d₁⟩ := ih₁
    obtain ⟨T₂, hP₂, d₂⟩ := ih₂
    exact ⟨T₁ ++ T₂, fun b hb => (List.mem_append.mp hb).elim (hP₁ b) (hP₂ b),
      .deductAntisym (d₁.mono_theory fun _ hb => List.mem_append_left _ hb)
        (d₂.mono_theory fun _ hb => List.mem_append_right _ hb)⟩
  | inst σ typing _ ih =>
    obtain ⟨T₁, hP₁, d₁⟩ := ih
    exact ⟨T₁, hP₁, .inst σ typing d₁⟩
  | instType σ typing _ ih =>
    obtain ⟨T₁, hP₁, d₁⟩ := ih
    exact ⟨T₁, hP₁, .instType σ typing d₁⟩

/-- A well-typed HOL sequent `H ⊢ p` over the signature `S`. -/
@[ext]
structure Seq (S : HolSig) where
  /-- The hypotheses. -/
  hyps : Hyps
  /-- The conclusion. -/
  concl : Tm
  typing : HasType S.sig [] concl .bool
  typedHyps : TypedHyps S.sig [] hyps

/-- Translation of sequents along a signature extension: the identity on syntax. -/
def Seq.map {S T : HolSig} (h : S ≤ T) (s : Seq S) : Seq T where
  hyps := s.hyps
  concl := s.concl
  typing := hasType_of_le h s.typing
  typedHyps p hp := hasType_of_le h (s.typedHyps p hp)

/-- A hypothesis-free sequent `⊢ a`. -/
def Seq.closed {S : HolSig} (a : Tm) (ha : HasType S.sig [] a .bool) : Seq S :=
  ⟨∅, a, ha, fun _ hp => by simp at hp⟩

end HOL

end Silmaril.Logic.Institution.Metatheory
