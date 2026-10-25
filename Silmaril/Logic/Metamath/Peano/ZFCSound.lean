module

public import Silmaril.Logic.Metamath.Peano.Interpretation

@[expose] public section

/-!
# Arithmetical soundness of ZFC

The translation of a closed arithmetic formula `φ` of `peano.mm` into set
theory (`Peano.ToZF.tr`) becomes a Metamath sentence of set.mm's language
(`Peano.ToZF.trSentence`): `|- tr φ` with a floating hypothesis `setvar v` for
each of its variables, all declared pairwise disjoint.

Every system of well-formed axioms in set.mm's ZFC language whose environment
model over `ZFSet` is a model is arithmetically sound for this translation
(`Peano.ToZF.arithSound_of_isModel`): if it proves the translation of `φ`,
then `φ` is true in ℕ. The proof evaluates the translation in the model under
injective names, with the object variables at von Neumann numerals, and
applies the correctness of the translation (`Peano.ToZF.S_tr`).

In particular set.mm's ZFC is arithmetically sound, as a tree system and as a
string system (`Peano.ToZF.arithSound_ZFC`, `Peano.ToZF.arithSound_ZFC_str`),
hence Σ₁-sound and ω-consistent for the translation
(`Peano.ToZF.omegaConsistent_ZFC`). So is every subsystem, such as ZF
(`Peano.ToZF.arithSound_of_subset`, `Peano.ToZF.arithSound_ZF`).
-/

namespace Silmaril.Logic.Metamath.Peano.ToZF

open Silmaril.Logic.Metamath Silmaril.Logic.Metatheory Grammar Grammar.TAssertion
  Silmaril.Logic.SetTheory Function ZF.T Env

/-! ## Purity of the translation -/

section Pure

open ZF

theorem isPure_wn {a : Tree ZF.L ZF.V} (ha : IsPure a) : IsPure (wn a) :=
  .node rfl (by simp [ZF.grammar, ZF.rules]; exact ha)

theorem isPure_bin {l : ZF.L} (hl : l = .wi ∨ l = .wb ∨ l = .wa ∨ l = .wo) {a b : Tree ZF.L ZF.V}
    (ha : IsPure a) (hb : IsPure b) : IsPure (.node l [a, b]) := by
  rcases hl with rfl | rfl | rfl | rfl <;>
    exact .node rfl (by simp [ZF.grammar, ZF.rules]; exact ⟨ha, hb⟩)

theorem isPure_wi {a b : Tree ZF.L ZF.V} (ha : IsPure a) (hb : IsPure b) : IsPure (wi a b) :=
  isPure_bin (.inl rfl) ha hb

theorem isPure_wb {a b : Tree ZF.L ZF.V} (ha : IsPure a) (hb : IsPure b) : IsPure (wb a b) :=
  isPure_bin (.inr (.inl rfl)) ha hb

theorem isPure_wa {a b : Tree ZF.L ZF.V} (ha : IsPure a) (hb : IsPure b) : IsPure (wa a b) :=
  isPure_bin (.inr (.inr (.inl rfl))) ha hb

theorem isPure_wo {a b : Tree ZF.L ZF.V} (ha : IsPure a) (hb : IsPure b) : IsPure (wo a b) :=
  isPure_bin (.inr (.inr (.inr rfl))) ha hb

theorem isPure_wal (c : ZF.V) {a : Tree ZF.L ZF.V} (ha : IsPure a) : IsPure (wal c a) :=
  .node rfl (by simp [ZF.grammar, ZF.rules]; exact ⟨ha, rfl⟩)

theorem isPure_wex (c : ZF.V) {a : Tree ZF.L ZF.V} (ha : IsPure a) : IsPure (wex c a) :=
  .node rfl (by simp [ZF.grammar, ZF.rules]; exact ⟨ha, rfl⟩)

theorem isPure_weq (c d : ZF.V) : IsPure (weq c d) :=
  .node rfl (by simp [ZF.grammar, ZF.rules]; exact ⟨.node rfl (by simp [ZF.rules]; rfl),
    .node rfl (by simp [ZF.rules]; rfl)⟩)

theorem isPure_wel (c d : ZF.V) : IsPure (wel c d) :=
  .node rfl (by simp [ZF.grammar, ZF.rules]; exact ⟨.node rfl (by simp [ZF.rules]; rfl),
    .node rfl (by simp [ZF.rules]; rfl)⟩)


/-- Prove that a formula built from the connectives and the building blocks is pure. -/
macro "pure_tac" : tactic => `(tactic| repeat (first
  | apply isPure_wn | apply isPure_wi | apply isPure_wb | apply isPure_wa | apply isPure_wo
  | apply isPure_wal | apply isPure_wex | exact isPure_weq _ _ | exact isPure_wel _ _
  | assumption))

theorem isPure_empty (r : ZF.V) (d : ℕ) : IsPure (empty r d) := by unfold empty; pure_tac
theorem isPure_suc (a r : ZF.V) (d : ℕ) : IsPure (suc a r d) := by unfold suc; pure_tac
theorem isPure_sing (s a : ZF.V) (d : ℕ) : IsPure (sing s a d) := by unfold sing; pure_tac
theorem isPure_dbl (s a b : ZF.V) (d : ℕ) : IsPure (dbl s a b d) := by unfold dbl; pure_tac
theorem isPure_isPair (p a b : ZF.V) (d : ℕ) : IsPure (isPair p a b d) := by
  unfold isPair; pure_tac
theorem isPure_tripIn (a b c g : ZF.V) (d : ℕ) : IsPure (tripIn a b c g d) := by
  unfold tripIn; pure_tac
theorem isPure_ind (c : ZF.V) (d : ℕ) : IsPure (ind c d) := by unfold ind; pure_tac
theorem isPure_nat (a : ZF.V) (d : ℕ) : IsPure (nat a d) := by unfold nat; pure_tac
theorem isPure_addClosed (a g : ZF.V) (d : ℕ) : IsPure (addClosed a g d) := by
  unfold addClosed; pure_tac
theorem isPure_addRel (a b r : ZF.V) (d : ℕ) : IsPure (addRel a b r d) := by
  unfold addRel; pure_tac
theorem isPure_mulClosed (a g : ZF.V) (d : ℕ) : IsPure (mulClosed a g d) := by
  unfold mulClosed; pure_tac
theorem isPure_mulRel (a b r : ZF.V) (d : ℕ) : IsPure (mulRel a b r d) := by
  unfold mulRel; pure_tac

theorem isPure_val (t : Tree L V) (r : ZF.V) (d : ℕ) : IsPure (val t r d) := by
  fun_induction val t r d <;> pure_tac

theorem isPure_tr (φ : Tree L V) (d : ℕ) : IsPure (tr φ d) := by
  have hval := isPure_val
  have hnat := isPure_nat
  fun_induction tr φ d <;> repeat (first
    | apply isPure_wn | apply isPure_wi | apply isPure_wb | apply isPure_wa | apply isPure_wo
    | apply isPure_wal | apply isPure_wex | exact isPure_weq _ _ | exact isPure_wel _ _
    | exact hval _ _ _ | exact hnat _ _ | assumption)

end Pure

/-! ## Names -/

/-- The Tarski semantics under injective names is the semantics of the
assignment of sets to variables through the names. -/
theorem sem_comp {D' N' : Type*} [Membership D' D'] [DecidableEq N'] {nm : ZF.V → N'}
    (hnm : Injective nm) (t : Tree ZF.L ZF.V) (E : N' → D') :
    ZF.sem nm t E ↔ ZF.sem id t (E ∘ nm) := by
  fun_induction ZF.sem nm t E <;> simp only [ZF.sem, id, Function.comp_apply]
  all_goals first
    | rfl
    | (rename_i ih; exact not_congr ih)
    | (rename_i ih₁ ih₂; exact imp_congr ih₁ ih₂)
    | (rename_i ih₁ ih₂; exact iff_congr ih₁ ih₂)
    | (rename_i ih₁ ih₂; exact and_congr ih₁ ih₂)
    | (rename_i ih₁ ih₂; exact or_congr ih₁ ih₂)
    | (rename_i ih
       exact forall_congr' fun m => (ih m).trans (by rw [update_comp_eq_of_injective _ hnm]))
    | (rename_i ih
       exact exists_congr fun m => (ih m).trans (by rw [update_comp_eq_of_injective _ hnm]))

/-- An injective encoding of the variables of set.mm's language by natural numbers. -/
def zcode : ZF.V → ℕ
  | .ph => 0 | .ps => 1 | .ch => 2 | .x => 3 | .y => 4 | .z => 5 | .w => 6 | .v => 7
  | .u => 8 | .t => 9 | .A => 10 | .B => 11 | .var n => n + 12

theorem zcode_injective : Injective zcode := by
  intro a b h
  cases a <;> cases b <;> simp_all [zcode]

/-! ## Sentences -/

theorem mem_dvs {l : List ZF.V} {p : ZF.V × ZF.V} (h : p ∈ ZF.dvs l) : p.1 ∈ l ∧ p.2 ∈ l := by
  induction l with
  | nil => simp [ZF.dvs] at h
  | cons a l ih =>
    simp only [ZF.dvs, List.mem_append, List.mem_map] at h
    rcases h with ⟨b, hb, rfl⟩ | h
    · exact ⟨by simp, by simp [hb]⟩
    · exact ⟨by simp [(ih h).1], by simp [(ih h).2]⟩

theorem ne_of_mem_dvs {l : List ZF.V} (hl : l.Nodup) {p : ZF.V × ZF.V} (h : p ∈ ZF.dvs l) :
    p.1 ≠ p.2 := by
  induction l with
  | nil => simp [ZF.dvs] at h
  | cons a l ih =>
    simp only [List.nodup_cons] at hl
    simp only [ZF.dvs, List.mem_append, List.mem_map] at h
    rcases h with ⟨b, hb, rfl⟩ | h
    · exact fun e => hl.1 (by rw [show a = b from e]; exact hb)
    · exact ih hl.2 h

/-- The sentence of the translation of `φ`: `|- tr φ`, with a floating
hypothesis `setvar v` for each of its variables, pairwise disjoint. -/
def trSentence (φ : Tree L V) : TAssertion ZF.L ZF.C ZF.V :=
  ⟨ZF.dvs (tr φ 0).vars.dedup, (tr φ 0).vars.dedup.map fun a => .float .setvar a, pf (tr φ 0)⟩

theorem ctx_trSentence {φ : Tree L V} {a : ZF.V} {c : ZF.C} :
    (trSentence φ).ctx a c ↔ a ∈ (tr φ 0).vars ∧ c = .setvar := by
  simp [trSentence, TAssertion.ctx, and_comm, eq_comm]

theorem wellFormed_trSentence (φ : Tree L V) : (trSentence φ).WellFormed ZF.grammar where
  floats_nodup := by
    simp only [trSentence, TAssertion.floats, List.filterMap_map]
    simpa [Function.comp_def] using List.nodup_dedup _
  float_sort a c h := by
    rw [(ctx_trSentence.1 h).2]
    decide
  ess_wellTyped e he := by simp [trSentence, TAssertion.essentials] at he
  concl_wellTyped := ⟨.wff, rfl,
    (isPure_tr φ 0).congr_ctx fun a ha c hc => ctx_trSentence.2 ⟨ha, hc⟩⟩
  dv_irrefl a b h := ne_of_mem_dvs (List.nodup_dedup _) h
  dv_float a b h := by
    obtain ⟨ha, hb⟩ := mem_dvs h
    exact ⟨⟨.setvar, ctx_trSentence.2 ⟨List.mem_dedup.1 ha, rfl⟩⟩,
      ⟨.setvar, ctx_trSentence.2 ⟨List.mem_dedup.1 hb, rfl⟩⟩⟩

/-- If the environment model over `ZFSet` satisfies the sentence of the
translation of an arithmetic formula, the formula is true in ℕ. -/
theorem evalWff_of_satisfies {N : Type 1} [DecidableEq N] [Infinite N] {φ : Tree L V}
    (hφ : IsArith φ) (h : (ZF.model ZFSet.{0} N).Satisfies (trSentence φ)) (e : V → ℕ) :
    evalWff e φ := by
  classical
  let ι : ZF.V → N := Infinite.natEmbedding N ∘ zcode
  have hι : Injective ι := (Infinite.natEmbedding N).injective.comp zcode_injective
  let ρ : (ZF.model ZFSet.{0} N).Valuation (trSentence φ).ctx := fun a c hc =>
    match c, (ctx_trSentence.1 hc.1).2 with | .setvar, rfl => (ι a : N)
  have hdv : (ZF.model ZFSet.{0} N).DVHolds ρ (trSentence φ).dv := by
    intro a b _ hne c d ha hb
    obtain rfl := (ctx_trSentence.1 ha.1).2
    obtain rfl := (ctx_trSentence.1 hb.1).2
    exact Kind.fresh_name_name.2 fun e => hne (hι e)
  obtain ⟨s, hs, ht, hv⟩ := h ρ hdv (by simp [trSentence, TAssertion.essentials])
  obtain rfl : (.wff : ZF.C) = s := Option.some.inj hs
  let F : ZF.V → ZFSet.{0} := fun c => if hc : ∃ a, pv a = c then numeral (e hc.choose) else ∅
  have hF : ∀ a, F (pv a) = numeral (e a) := fun a => by
    have hc : ∃ b, pv b = pv a := ⟨a, rfl⟩
    simp only [F, hc, ↓reduceDIte]
    rw [pv_inj.1 hc.choose_spec]
  let E : SetTheory.Env ZFSet.{0} N := fun n => if hn : ∃ c, ι c = n then F hn.choose else ∅
  have hE : E ∘ ι = F := funext fun c => by
    have hn : ∃ b, ι b = ι c := ⟨c, rfl⟩
    simp only [Function.comp_apply, E, hn, ↓reduceDIte]
    rw [hι hn.choose_spec]
  have hval := (ZF.value_pure ρ ι (fun _ _ => rfl) ZF.extensional_zfset (tr φ 0) (isPure_tr φ 0)
    ht E).1 (hv E)
  rw [sem_comp hι, hE] at hval
  exact (S_tr φ hφ 0 e F fun a _ => hF a).1 hval

/-! ## Arithmetical soundness -/

/-- Every system of well-formed axioms in set.mm's language that holds in the
environment model over `ZFSet` is arithmetically sound for the translation. -/
theorem arithSound_of_isModel {Γ : Set (TAssertion ZF.L ZF.C ZF.V)}
    (hΓ : ∀ B ∈ Γ, B.WellFormed ZF.grammar) {N : Type 1} [DecidableEq N] [Infinite N]
    (hM : (ZF.model ZFSet.{0} N).IsModel Γ) :
    arithLanguage.ArithSound (TDerivable ZF.grammar Γ) fun φ => trSentence φ.1 :=
  fun φ h => evalWff_of_satisfies φ.2.1 ((ZF.model ZFSet.{0} N).sound hΓ hM h)

/-- The same for string derivability from the syntax axioms and the flattened
axioms. -/
theorem arithSound_str_of_isModel {Γ : Set (TAssertion ZF.L ZF.C ZF.V)}
    (hΓ : ∀ B ∈ Γ, B.WellFormed ZF.grammar) {N : Type 1} [DecidableEq N] [Infinite N]
    (hM : (ZF.model ZFSet.{0} N).IsModel Γ) :
    arithLanguage.ArithSound (Derivable (ZF.grammar.axioms Γ))
      fun φ => (trSentence φ.1).flatten ZF.grammar :=
  fun φ h => evalWff_of_satisfies φ.2.1
    ((ZF.model ZFSet.{0} N).sound_derivable ZF.unambiguous hΓ hM (wellFormed_trSentence _) h)

/-- set.mm's ZFC is arithmetically sound: every closed arithmetic formula whose
translation ZFC proves is true in ℕ. -/
theorem arithSound_ZFC :
    arithLanguage.ArithSound (TDerivable ZF.grammar ZF.ZFC) fun φ => trSentence φ.1 :=
  arithSound_of_isModel (N := ULift.{1} ℕ) ZF.wellFormed_ZFC ZF.isModel_ZFC

/-- set.mm's ZFC is arithmetically sound as a string system. -/
theorem arithSound_ZFC_str :
    arithLanguage.ArithSound (Derivable (ZF.grammar.axioms ZF.ZFC))
      fun φ => (trSentence φ.1).flatten ZF.grammar :=
  arithSound_str_of_isModel (N := ULift.{1} ℕ) ZF.wellFormed_ZFC ZF.isModel_ZFC

/-- set.mm's ZFC is Σ₁-sound for the translation. -/
theorem sigma1Sound_ZFC :
    arithLanguage.Sigma1Sound (TDerivable ZF.grammar ZF.ZFC) fun φ => trSentence φ.1 :=
  arithSound_ZFC.sigma1Sound

/-- set.mm's ZFC is ω-consistent for the translation. -/
theorem omegaConsistent_ZFC :
    omegaLanguage.OmegaConsistent (TDerivable ZF.grammar ZF.ZFC) fun φ => trSentence φ.1 :=
  OmegaLanguage.omegaConsistent_of_arithSound (A := omegaLanguage) arithSound_ZFC

/-- Every subsystem of ZFC, such as ZF (`ZF.ZF0`), is arithmetically sound. -/
theorem arithSound_of_subset {Γ : Set (TAssertion ZF.L ZF.C ZF.V)} (h : Γ ⊆ ZF.ZFC) :
    arithLanguage.ArithSound (TDerivable ZF.grammar Γ) fun φ => trSentence φ.1 :=
  arithSound_ZFC.mono fun _ hd => hd.mono h

/-- set.mm's ZF is arithmetically sound. -/
theorem arithSound_ZF :
    arithLanguage.ArithSound (TDerivable ZF.grammar ZF.ZF0) fun φ => trSentence φ.1 :=
  arithSound_of_subset ZF.ZF0_subset_ZFC

end Silmaril.Logic.Metamath.Peano.ToZF
