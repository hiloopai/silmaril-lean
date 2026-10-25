module

public import Silmaril.Logic.Metamath.Peano.Soundness
public import Silmaril.Logic.Metatheory.ArithmeticSoundness
public import Silmaril.Logic.Metamath.Model.Interpretation

@[expose] public section

/-!
# Arithmetical soundness of `peano.mm`

An arithmetic formula (`Peano.IsArith`) has a truth value in ℕ under an
assignment of numbers to its object variables (`Peano.evalWff`). As a
Metamath assertion, the formula `φ` is the sentence `|- φ` with a floating
hypothesis `var v` for each variable `v` of `φ` and all these variables
declared pairwise disjoint (`Peano.sentence`), following `peano.mm`'s reading
of theorems. The standard model satisfies the sentence of `φ` exactly when
`φ` is true in ℕ under every assignment (`Peano.satisfies_sentence_iff`): the
standard model is the standard interpretation of arithmetic.

The closed arithmetic formulas form an arithmetic language
(`Peano.arithLanguage`, `Metatheory.ArithLanguage`), whose Σ₁ sentences are
taken to be the existential ones (`Peano.IsExistential`): existential
quantifiers over a quantifier-free formula. Every closed formula whose sentence
`PA` proves is true in ℕ, for tree and for string derivability
(`Peano.arithSound`, `Peano.arithSound_str`). With numeral instances
`forall x implies = x n phi`, negation and existential quantification, the
language satisfies the Tarski clauses (`Peano.omegaLanguage`), and `PA` is
ω-consistent (`Peano.omegaConsistent`).
-/

namespace Silmaril.Logic.Metamath.Peano

open Silmaril.Logic.Metamath Silmaril.Logic.Metatheory Grammar Grammar.TAssertion
  Silmaril.Logic.SetTheory Function Env

/-! ## Inversion of arithmetic syntax -/

section Inversion

theorem hasSort_objCtx_var {t : Tree L V} (h : grammar.HasSort objCtx t .var) :
    ∃ a, t = .var a := by
  generalize hs : (.var : C) = s at h
  cases h with
  | var => exact ⟨_, rfl⟩
  | node => rename_i l _ _ _; cases l <;> exact absurd hs (by decide)

theorem hasSort_objCtx_binop {t : Tree L V} (h : grammar.HasSort objCtx t .binop) :
    t = .node .binopPlus [] ∨ t = .node .binopTimes [] := by
  generalize hs : (.binop : C) = s at h
  cases h with
  | var hv => cases hs; cases hv
  | node hlen =>
    rename_i l args _
    cases l <;> first | exact absurd hs (by decide) | skip
    · match args, hlen with
      | [], _ => exact .inl rfl
    · match args, hlen with
      | [], _ => exact .inr rfl

theorem hasSort_objCtx_binpred {t : Tree L V} (h : grammar.HasSort objCtx t .binpred) :
    t = .node .binpredEquals [] ∨ t = .node .binpredLessThan [] := by
  generalize hs : (.binpred : C) = s at h
  cases h with
  | var hv => cases hs; cases hv
  | node hlen =>
    rename_i l args _
    cases l <;> first | exact absurd hs (by decide) | skip
    · match args, hlen with
      | [], _ => exact .inl rfl
    · match args, hlen with
      | [], _ => exact .inr rfl

theorem hasSort_objCtx_logbinop {t : Tree L V} (h : grammar.HasSort objCtx t .logbinop) :
    t = .node .logbinopOr [] ∨ t = .node .logbinopAnd [] ∨ t = .node .logbinopImplies [] ∨
      t = .node .logbinopIff [] := by
  generalize hs : (.logbinop : C) = s at h
  cases h with
  | var hv => cases hs; cases hv
  | node hlen =>
    rename_i l args _
    cases l <;> first | exact absurd hs (by decide) | skip
    · match args, hlen with
      | [], _ => exact .inl rfl
    · match args, hlen with
      | [], _ => exact .inr (.inl rfl)
    · match args, hlen with
      | [], _ => exact .inr (.inr (.inl rfl))
    · match args, hlen with
      | [], _ => exact .inr (.inr (.inr rfl))

theorem hasSort_objCtx_quant {t : Tree L V} (h : grammar.HasSort objCtx t .quant) :
    t = .node .quantAll [] ∨ t = .node .quantEx [] := by
  generalize hs : (.quant : C) = s at h
  cases h with
  | var hv => cases hs; cases hv
  | node hlen =>
    rename_i l args _
    cases l <;> first | exact absurd hs (by decide) | skip
    · match args, hlen with
      | [], _ => exact .inl rfl
    · match args, hlen with
      | [], _ => exact .inr rfl

/-- The shapes of arithmetic terms. -/
theorem IsArithTerm.cases {t : Tree L V} (h : IsArithTerm t) :
    (∃ a, t = T.tv a) ∨ t = T.zero ∨ (∃ a, t = T.succ a ∧ IsArithTerm a) ∨
      (∃ a b, t = T.plus a b ∧ IsArithTerm a ∧ IsArithTerm b) ∨
      (∃ a b, t = T.times a b ∧ IsArithTerm a ∧ IsArithTerm b) := by
  unfold IsArithTerm at h
  generalize hs : (.term : C) = s at h
  cases h with
  | var hv => cases hs; cases hv
  | node hlen hargs =>
    rename_i l args
    cases l <;> first | exact absurd hs (by decide) | skip
    · obtain ⟨c, rfl⟩ : ∃ c, args = [c] := match args, hlen with | [c], _ => ⟨c, rfl⟩
      obtain ⟨a, rfl⟩ := hasSort_objCtx_var (hargs (c, (.var, .v)) (by simp [grammar, rules]))
      exact .inl ⟨a, rfl⟩
    · obtain rfl : args = [] := match args, hlen with | [], _ => rfl
      exact .inr (.inl rfl)
    · obtain ⟨a, rfl⟩ : ∃ a, args = [a] := match args, hlen with | [a], _ => ⟨a, rfl⟩
      exact .inr (.inr (.inl ⟨a, rfl, hargs (a, (.term, .s)) (by simp [grammar, rules])⟩))
    · obtain ⟨a, b, c, rfl⟩ : ∃ a b c, args = [a, b, c] :=
        match args, hlen with | [a, b, c], _ => ⟨a, b, c, rfl⟩
      have ha : IsArithTerm a := hargs (a, (.term, .s)) (by simp [grammar, rules])
      have hb : IsArithTerm b := hargs (b, (.term, .t)) (by simp [grammar, rules])
      rcases hasSort_objCtx_binop (hargs (c, (.binop, .binop)) (by simp [grammar, rules]))
        with rfl | rfl
      · exact .inr (.inr (.inr (.inl ⟨a, b, rfl, ha, hb⟩)))
      · exact .inr (.inr (.inr (.inr ⟨a, b, rfl, ha, hb⟩)))

/-- The shapes of arithmetic formulas. -/
theorem IsArith.cases {t : Tree L V} (h : IsArith t) :
    (∃ a b, t = T.eq a b ∧ IsArithTerm a ∧ IsArithTerm b) ∨
      (∃ a b, t = T.lt a b ∧ IsArithTerm a ∧ IsArithTerm b) ∨
      (∃ a, t = T.not a ∧ IsArith a) ∨
      (∃ l a b, t = T.lop l a b ∧ (l = .node .logbinopOr [] ∨ l = .node .logbinopAnd [] ∨
        l = .node .logbinopImplies [] ∨ l = .node .logbinopIff []) ∧ IsArith a ∧ IsArith b) ∨
      (∃ q w a, t = T.qnt q w a ∧ (q = .node .quantAll [] ∨ q = .node .quantEx []) ∧
        IsArith a) := by
  unfold IsArith at h
  generalize hs : (.wff : C) = s at h
  cases h with
  | var hv => cases hs; cases hv
  | node hlen hargs =>
    rename_i l args
    cases l <;> first | exact absurd hs (by decide) | skip
    · obtain ⟨a, b, c, rfl⟩ : ∃ a b c, args = [a, b, c] :=
        match args, hlen with | [a, b, c], _ => ⟨a, b, c, rfl⟩
      have ha : IsArithTerm a := hargs (a, (.term, .s)) (by simp [grammar, rules])
      have hb : IsArithTerm b := hargs (b, (.term, .t)) (by simp [grammar, rules])
      rcases hasSort_objCtx_binpred (hargs (c, (.binpred, .binpred)) (by simp [grammar, rules]))
        with rfl | rfl
      · exact .inl ⟨a, b, rfl, ha, hb⟩
      · exact .inr (.inl ⟨a, b, rfl, ha, hb⟩)
    · obtain ⟨a, rfl⟩ : ∃ a, args = [a] := match args, hlen with | [a], _ => ⟨a, rfl⟩
      exact .inr (.inr (.inl ⟨a, rfl, hargs (a, (.wff, .psi)) (by simp [grammar, rules])⟩))
    · obtain ⟨l, b, a, rfl⟩ : ∃ l b a, args = [l, b, a] :=
        match args, hlen with | [l, b, a], _ => ⟨l, b, a, rfl⟩
      exact .inr (.inr (.inr (.inl ⟨l, a, b, rfl,
        hasSort_objCtx_logbinop (hargs (l, (.logbinop, .logbinop)) (by simp [grammar, rules])),
        hargs (a, (.wff, .psi)) (by simp [grammar, rules]),
        hargs (b, (.wff, .phi)) (by simp [grammar, rules])⟩)))
    · obtain ⟨c, q, a, rfl⟩ : ∃ c q a, args = [c, q, a] :=
        match args, hlen with | [c, q, a], _ => ⟨c, q, a, rfl⟩
      obtain ⟨w, rfl⟩ := hasSort_objCtx_var (hargs (c, (.var, .v)) (by simp [grammar, rules]))
      exact .inr (.inr (.inr (.inr ⟨q, w, a, rfl,
        hasSort_objCtx_quant (hargs (q, (.quant, .quant)) (by simp [grammar, rules])),
        hargs (a, (.wff, .phi)) (by simp [grammar, rules])⟩)))

end Inversion

/-! ## Values of arithmetic formulas in the standard model -/

section Values

variable {N : Type} [DecidableEq N] [Infinite N] {ctx : V → C → Prop}
  (ρ : (stdModel N).Valuation ctx) (nm : V → N) (hnm : ∀ a h, ρ a .var h = nm a)

include hnm

/-- The value of an arithmetic term is its value in ℕ, reading the variables
through the names given by the valuation. -/
theorem value_arithTerm : ∀ (t : Tree L V), IsArithTerm t →
    ∀ (h : grammar.HasSort (grammar.synCtx ctx) t .term) (E : SetTheory.Env ℕ N),
      ((stdModel N).value ρ t h : Term ℕ N ℕ).1 E = evalTerm (E ∘ nm) t := by
  intro t
  induction t using Tree.induction with
  | var a => intro ht; cases ht with | var hv => cases hv
  | node l args ih =>
    intro ht h E
    rcases ht.cases with ⟨a, e⟩ | e | ⟨a, e, ha⟩ | ⟨a, b, e, ha, hb⟩ | ⟨a, b, e, ha, hb⟩ <;>
      cases e
    · value_simp; simp [hnm]
    · value_simp; rfl
    · value_simp; rw [ih a (by simp) ha]; rfl
    · value_simp; rw [ih a (by simp) ha, ih b (by simp) hb]; rfl
    · value_simp; rw [ih a (by simp) ha, ih b (by simp) hb]; rfl

/-- The value of an arithmetic formula is its truth value in ℕ, when distinct
variables of the formula have distinct names. -/
theorem value_arith : ∀ (t : Tree L V), IsArith t →
    (∀ a ∈ t.vars, ∀ b ∈ t.vars, nm a = nm b → a = b) →
    ∀ (h : grammar.HasSort (grammar.synCtx ctx) t .wff) (E : SetTheory.Env ℕ N),
      ((stdModel N).value ρ t h : Term ℕ N Prop).1 E ↔ evalWff (E ∘ nm) t := by
  intro t
  induction t using Tree.induction with
  | var a => intro ht; cases ht with | var hv => cases hv
  | node l args ih =>
    intro ht hinj h E
    have sub : ∀ {a}, a ∈ args → ∀ c ∈ a.vars, ∀ d ∈ a.vars, nm c = nm d → c = d :=
      fun ha c hc d hd => hinj c (by simpa using ⟨_, ha, hc⟩) d (by simpa using ⟨_, ha, hd⟩)
    rcases ht.cases with ⟨a, b, e, ha, hb⟩ | ⟨a, b, e, ha, hb⟩ | ⟨a, e, ha⟩ |
      ⟨l', a, b, e, hl, ha, hb⟩ | ⟨q, w, a, e, hq, ha⟩ <;> cases e
    · value_simp
      rw [value_arithTerm ρ nm hnm a ha, value_arithTerm ρ nm hnm b hb]
      rfl
    · value_simp
      rw [value_arithTerm ρ nm hnm a ha, value_arithTerm ρ nm hnm b hb]
      rfl
    · value_simp
      exact not_congr (ih a (by simp) ha (sub (by simp)) _ E)
    · have iha := ih a (by simp) ha (sub (by simp)) (show grammar.HasSort _ a .wff from
        h.child ⟨2, by decide⟩) E
      have ihb := ih b (by simp) hb (sub (by simp)) (show grammar.HasSort _ b .wff from
        h.child ⟨1, by decide⟩) E
      rcases hl with rfl | rfl | rfl | rfl <;> value_simp <;> rw [iha, ihb] <;> rfl
    · have key : ∀ n, ((stdModel N).value ρ a (show grammar.HasSort _ a .wff from
          h.child ⟨2, by decide⟩) : Term ℕ N Prop).1 (update E (nm w) n) ↔
          evalWff (update (E ∘ nm) w n) a := by
        intro n
        rw [ih a (by simp) ha (sub (by simp)) _ _]
        refine evalWff_congr a fun c hc => ?_
        by_cases hcw : c = w
        · subst hcw; simp
        · have hne : nm c ≠ nm w := fun e => hcw (hinj c (by simp [hc]) w (by simp) e)
          simp [update_of_ne hne, update_of_ne hcw]
      rcases hq with rfl | rfl <;> value_simp <;> simp only [hnm]
      · exact forall_congr' key
      · exact exists_congr key

end Values

/-! ## Sentences -/

/-- The variables of a tree, without repetition. -/
def objVars (φ : Tree L V) : List V := φ.vars.dedup

/-- The ordered pairs `(a, b)` of a list with `a` before `b`. -/
def distinctPairs : List V → List (V × V)
  | [] => []
  | a :: as => as.map (a, ·) ++ distinctPairs as

theorem mem_distinctPairs {l : List V} {p : V × V} (h : p ∈ distinctPairs l) :
    p.1 ∈ l ∧ p.2 ∈ l := by
  induction l with
  | nil => simp [distinctPairs] at h
  | cons a l ih =>
    simp only [distinctPairs, List.mem_append, List.mem_map] at h
    rcases h with ⟨b, hb, rfl⟩ | h
    · exact ⟨by simp, by simp [hb]⟩
    · exact ⟨by simp [(ih h).1], by simp [(ih h).2]⟩

theorem ne_of_mem_distinctPairs {l : List V} (hl : l.Nodup) {p : V × V}
    (h : p ∈ distinctPairs l) : p.1 ≠ p.2 := by
  induction l with
  | nil => simp [distinctPairs] at h
  | cons a l ih =>
    simp only [List.nodup_cons] at hl
    simp only [distinctPairs, List.mem_append, List.mem_map] at h
    rcases h with ⟨b, hb, rfl⟩ | h
    · exact fun e => hl.1 (by rw [show a = b from e]; exact hb)
    · exact ih hl.2 h

theorem mem_distinctPairs_of_ne {l : List V} {a b : V} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    (a, b) ∈ distinctPairs l ∨ (b, a) ∈ distinctPairs l := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    simp only [distinctPairs, List.mem_append, List.mem_map, Prod.mk.injEq]
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact absurd rfl hne
    · exact .inl (.inl ⟨b, hb', rfl, rfl⟩)
    · exact .inr (.inl ⟨a, ha', rfl, rfl⟩)
    · exact (ih ha' hb').imp .inr .inr

/-- The sentence `|- φ`: a floating hypothesis `var v` for each variable `v` of
`φ`, with all its variables pairwise disjoint. -/
def sentence (φ : Tree L V) : TAssertion L C V :=
  ⟨distinctPairs (objVars φ), (objVars φ).map fun a => .float .var a, T.pf φ⟩

theorem ctx_sentence {φ : Tree L V} {a : V} {c : C} :
    (sentence φ).ctx a c ↔ a ∈ φ.vars ∧ c = .var := by
  simp [sentence, TAssertion.ctx, objVars, and_comm, eq_comm]

theorem floats_sentence (φ : Tree L V) :
    (sentence φ).floats = (objVars φ).map fun a => (.var, a) := by
  simp [sentence, TAssertion.floats, List.filterMap_map]

theorem wellFormed_sentence {φ : Tree L V} (hφ : IsArith φ) :
    (sentence φ).WellFormed grammar where
  floats_nodup := by
    rw [floats_sentence, List.map_map]
    exact (List.nodup_dedup _).map_on fun _ _ _ _ h => h
  float_sort a c h := by
    rw [(ctx_sentence.1 h).2]
    decide
  ess_wellTyped e he := by simp [sentence, TAssertion.essentials] at he
  concl_wellTyped := ⟨.wff, rfl, hφ.congr_ctx fun a ha c hc => ctx_sentence.2 ⟨ha, hc⟩⟩
  dv_irrefl a b h := ne_of_mem_distinctPairs (List.nodup_dedup _) h
  dv_float a b h := by
    obtain ⟨ha, hb⟩ := mem_distinctPairs h
    exact ⟨⟨.var, ctx_sentence.2 ⟨List.mem_dedup.1 ha, rfl⟩⟩,
      ⟨.var, ctx_sentence.2 ⟨List.mem_dedup.1 hb, rfl⟩⟩⟩

/-- An injective encoding of the variables by natural numbers. -/
def V.code : V → ℕ
  | .s => 0 | .t => 1 | .u => 2 | .s0 => 3 | .s1 => 4 | .t0 => 5 | .t1 => 6
  | .v => 7 | .x => 8 | .y => 9 | .z => 10
  | .binop => 11 | .logbinop => 12 | .binpred => 13 | .quant => 14
  | .phi => 15 | .psi => 16 | .chi => 17
  | .obj n => n + 18

theorem V.code_injective : Function.Injective V.code := by
  intro a b h
  cases a <;> cases b <;> simp_all [V.code]

section Satisfies

variable {N : Type} [DecidableEq N] [Infinite N]

/-- The standard model satisfies the sentence of an arithmetic formula exactly
when the formula is true in ℕ under every assignment, provided there are at
least as many names as variables. -/
theorem satisfies_sentence_iff {φ : Tree L V} (hφ : IsArith φ) {ι : V → N}
    (hι : Function.Injective ι) :
    (stdModel N).Satisfies (sentence φ) ↔ ∀ e : V → ℕ, evalWff e φ := by
  classical
  constructor
  · intro h e
    let ρ : (stdModel N).Valuation (sentence φ).ctx := fun a c hc =>
      match c, (ctx_sentence.1 hc.1).2 with | .var, rfl => (ι a : N)
    have hρ : ∀ a hc, ρ a .var hc = ι a := fun _ _ => rfl
    have hdv : (stdModel N).DVHolds ρ (sentence φ).dv := by
      intro a b _ hne c d ha hb
      obtain rfl := (ctx_sentence.1 ha.1).2
      obtain rfl := (ctx_sentence.1 hb.1).2
      exact Kind.fresh_name_name.2 fun e => hne (hι e)
    obtain ⟨s, hs, ht, hv⟩ := h ρ hdv (by simp [sentence, TAssertion.essentials])
    obtain rfl : (.wff : C) = s := Option.some.inj hs
    let E : SetTheory.Env ℕ N := fun n => if hn : ∃ a, ι a = n then e hn.choose else 0
    have hE : ∀ a, E (ι a) = e a := fun a => by
      have hn : ∃ c, ι c = ι a := ⟨a, rfl⟩
      simp only [E, hn, ↓reduceDIte]
      exact congrArg e (hι hn.choose_spec)
    have := (value_arith ρ ι hρ φ hφ (fun a _ b _ h => hι h) ht E).1 (hv E)
    exact (evalWff_congr φ fun a _ => hE a).1 this
  · intro h ρ hdv _
    let nm : V → N := fun a =>
      if hc : grammar.synCtx (sentence φ).ctx a .var then ρ a .var hc else Classical.arbitrary N
    have hnm : ∀ a hc, ρ a .var hc = nm a := fun a hc => by simp [nm, hc]
    have hinj : ∀ a ∈ φ.vars, ∀ b ∈ φ.vars, nm a = nm b → a = b := by
      intro a ha b hb hab
      by_contra hne
      have hca : grammar.synCtx (sentence φ).ctx a .var := ⟨ctx_sentence.2 ⟨ha, rfl⟩, by decide⟩
      have hcb : grammar.synCtx (sentence φ).ctx b .var := ⟨ctx_sentence.2 ⟨hb, rfl⟩, by decide⟩
      rw [← hnm a hca, ← hnm b hcb] at hab
      rcases mem_distinctPairs_of_ne (List.mem_dedup.2 ha) (List.mem_dedup.2 hb) hne with hd | hd
      · exact Kind.fresh_name_name.1 (hdv a b hd hne _ _ hca hcb) hab
      · exact Kind.fresh_name_name.1 (hdv b a hd (Ne.symm hne) _ _ hcb hca) hab.symm
    have ht : grammar.HasSort (grammar.synCtx (sentence φ).ctx) φ .wff :=
      (hφ.congr_ctx fun a ha c hc => ctx_sentence.2 ⟨ha, hc⟩).synCtx rfl
    exact ⟨.wff, rfl, ht, fun E => (value_arith ρ nm hnm φ hφ hinj ht E).2 (h _)⟩

omit [DecidableEq N] in
/-- Distinct names for the variables. -/
theorem exists_injective_names : ∃ ι : V → N, Function.Injective ι :=
  ⟨Infinite.natEmbedding N ∘ V.code, (Infinite.natEmbedding N).injective.comp V.code_injective⟩

end Satisfies

/-! ## Closed formulas and arithmetical soundness -/

/-- The free variables of a formula. -/
def fvWff : Tree L V → List V
  | .node .wffAtom [a, b, _] => a.vars ++ b.vars
  | .node .wffNot [a] => fvWff a
  | .node .wffLogbinop [_, b, a] => fvWff a ++ fvWff b
  | .node .wffQuant [.var w, _, a] => (fvWff a).filter (· ≠ w)
  | _ => []

/-- The truth value of a formula only depends on its free variables. -/
theorem evalWff_congr_fv {e e' : V → ℕ} (t : Tree L V) (h : ∀ a ∈ fvWff t, e a = e' a) :
    evalWff e t ↔ evalWff e' t := by
  fun_induction evalWff e t generalizing e' <;> simp only [evalWff] <;>
    simp only [fvWff, List.mem_append, List.mem_filter, decide_eq_true_eq] at h
  all_goals first
    | rfl
    | (rename_i a b
       rw [evalTerm_congr a fun w hw => h w (.inl hw), evalTerm_congr b fun w hw => h w (.inr hw)])
    | (rename_i ih; exact not_congr (ih h))
    | (rename_i ih₁ ih₂
       exact imp_congr (ih₁ fun w hw => h w (.inl hw)) (ih₂ fun w hw => h w (.inr hw)))
    | (rename_i ih₁ ih₂
       exact or_congr (ih₁ fun w hw => h w (.inl hw)) (ih₂ fun w hw => h w (.inr hw)))
    | (rename_i ih₁ ih₂
       exact and_congr (ih₁ fun w hw => h w (.inl hw)) (ih₂ fun w hw => h w (.inr hw)))
    | (rename_i ih₁ ih₂
       exact iff_congr (ih₁ fun w hw => h w (.inl hw)) (ih₂ fun w hw => h w (.inr hw)))
    | (rename_i w a ih
       refine (forall_congr' fun n => ih n fun c hc => ?_)
       by_cases hcw : c = w
       · subst hcw; simp
       · simp [update_of_ne hcw, h c ⟨hc, hcw⟩])
    | (rename_i w a ih
       refine (exists_congr fun n => ih n fun c hc => ?_)
       by_cases hcw : c = w
       · subst hcw; simp
       · simp [update_of_ne hcw, h c ⟨hc, hcw⟩])

/-- A closed formula has the same truth value under every assignment. -/
theorem evalWff_closed {t : Tree L V} (h : fvWff t = []) (e e' : V → ℕ) :
    evalWff e t ↔ evalWff e' t :=
  evalWff_congr_fv t fun a ha => by simp [h] at ha

/-- A formula without quantifiers. -/
def quantFree : Tree L V → Bool
  | .node .wffQuant _ => false
  | .node .wffNot [a] => quantFree a
  | .node .wffLogbinop [_, b, a] => quantFree a && quantFree b
  | _ => true

/-- An existential formula: existential quantifiers over a quantifier-free formula. -/
inductive IsExistential : Tree L V → Prop
  | qf {φ : Tree L V} : quantFree φ = true → IsExistential φ
  | ex {φ : Tree L V} (w : V) : IsExistential φ → IsExistential (T.ex w φ)

/-- The closed arithmetic formulas of `peano.mm`, with their truth in ℕ; the Σ₁
sentences are taken to be the existential ones. -/
def arithLanguage : ArithLanguage where
  Sentence := {φ : Tree L V // IsArith φ ∧ fvWff φ = []}
  IsSigma1 φ := IsExistential φ.1
  TrueInNat φ := ∀ e : V → ℕ, evalWff e φ.1

/-- Arithmetical soundness of `PA`: every closed formula whose sentence `PA`
proves is true in ℕ. -/
theorem arithSound :
    arithLanguage.ArithSound (TDerivable grammar PA) fun φ => sentence φ.1 := fun φ h => by
  obtain ⟨ι, hι⟩ := exists_injective_names (N := ℕ)
  exact (satisfies_sentence_iff φ.2.1 hι).1 (sound h)

/-- Arithmetical soundness of `PA` as a string system. -/
theorem arithSound_str :
    arithLanguage.ArithSound (Derivable (grammar.axioms PA))
      fun φ => (sentence φ.1).flatten grammar := fun φ h => by
  obtain ⟨ι, hι⟩ := exists_injective_names (N := ℕ)
  exact (satisfies_sentence_iff φ.2.1 hι).1
    ((stdModel ℕ).sound_derivable unambiguous wellFormed_PA isModel_PA
      (wellFormed_sentence φ.2.1) h)

/-- In particular `PA` is Σ₁-sound. -/
theorem sigma1Sound :
    arithLanguage.Sigma1Sound (TDerivable grammar PA) fun φ => sentence φ.1 :=
  arithSound.sigma1Sound

/-- The general arithmetical soundness theorem of the models package
(`Model.arithSound_of_iso`), for the identity interpretation of `peano.mm` in
itself and the standard model: every well-formed assertion that `PA` proves
holds in the standard model. -/
theorem arithSound_std :
    (Model.stdLanguage grammar (stdModel ℕ) fun A => IsExistential A.concl.tree).ArithSound
      (TDerivable grammar PA)
      fun A => (Grammar.Interp.id grammar).trAssertion A.1 :=
  Model.arithSound_of_iso (stdModel ℕ) wellFormed_PA isModel_PA _ (stdModel ℕ)
    (Grammar.Interp.pullIdIso (stdModel ℕ)) _

/-! ## ω-consistency -/

/-- The numeral `S ... S 0`. -/
def num : ℕ → Tree L V
  | 0 => T.zero
  | n + 1 => T.succ (num n)

@[simp] theorem vars_num (n : ℕ) : (num n).vars = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [num, ih]

@[simp] theorem evalTerm_num (e : V → ℕ) (n : ℕ) : evalTerm e (num n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [num, ih]

theorem isArithTerm_num (n : ℕ) : IsArithTerm (num n) := by
  induction n with
  | zero => exact .node rfl (by simp)
  | succ n ih => exact .node rfl (by simp [grammar, rules]; exact ih)

theorem isArithTerm_tv (a : V) : IsArithTerm (T.tv a) :=
  .node rfl (by simp [grammar, rules]; rfl)

theorem isArith_eq {a b : Tree L V} (ha : IsArithTerm a) (hb : IsArithTerm b) :
    IsArith (T.eq a b) :=
  .node rfl (by simp [grammar, rules]; exact ⟨ha, hb, .node rfl (by simp)⟩)

theorem isArith_not {a : Tree L V} (ha : IsArith a) : IsArith (T.not a) :=
  .node rfl (by simp [grammar, rules]; exact ha)

theorem isArith_imp {a b : Tree L V} (ha : IsArith a) (hb : IsArith b) :
    IsArith (T.imp a b) :=
  .node rfl (by simp [grammar, rules]; exact ⟨.node rfl (by simp), hb, ha⟩)

theorem isArith_qnt {q : Tree L V} (hq : grammar.HasSort objCtx q .quant) (w : V)
    {a : Tree L V} (ha : IsArith a) : IsArith (T.qnt q w a) :=
  .node rfl (by simp [grammar, rules]; exact ⟨rfl, hq, ha⟩)

/-- The arithmetic language of `peano.mm` with formulas in one free variable,
numeral instances `forall x implies = x n phi`, negation and existential
quantification. -/
def omegaLanguage : OmegaLanguage where
  toArithLanguage := arithLanguage
  Formula := {p : V × Tree L V // IsArith p.2 ∧ ∀ a ∈ fvWff p.2, a = p.1}
  inst p n := ⟨T.all p.1.1 (T.imp (T.eq (T.tv p.1.1) (num n)) p.1.2),
    isArith_qnt (.node rfl (by simp)) _
      (isArith_imp (isArith_eq (isArithTerm_tv _) (isArithTerm_num n)) p.2.1),
    by
      simp only [fvWff, T.tv, Tree.vars_node, List.flatMap_cons, Tree.vars_var, vars_num,
        List.flatMap_nil, List.append_nil, List.filter_eq_nil_iff, List.mem_append,
        List.mem_singleton, decide_eq_true_eq]
      rintro a (rfl | ha) hne
      · exact hne rfl
      · exact hne (p.2.2 a ha)⟩
  neg φ := ⟨T.not φ.1, isArith_not φ.2.1, by simpa [fvWff] using φ.2.2⟩
  ex p := ⟨T.ex p.1.1 p.1.2, isArith_qnt (.node rfl (by simp)) _ p.2.1, by
    simp only [fvWff, List.filter_eq_nil_iff, decide_eq_true_eq]
    exact fun a ha hne => hne (p.2.2 a ha)⟩
  true_neg φ := ⟨fun h hall => h (fun _ => 0) (hall _),
    fun h e he => h fun e' => (evalWff_closed φ.2.2 e e').1 he⟩
  true_ex p := by
    obtain ⟨⟨w, φ⟩, -, hφ⟩ := p
    have key : ∀ (e e' : V → ℕ) (n : ℕ),
        evalWff (update e w n) φ ↔ evalWff (update e' w n) φ := fun e e' n =>
      evalWff_congr_fv φ fun a ha => by rw [hφ a ha]; simp
    simp only [arithLanguage, evalWff_ex, evalWff_all, evalWff_imp, evalWff_eq, evalTerm_tv,
      evalTerm_num, update_self]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := h fun _ => 0
      exact ⟨n, fun e m hm => hm ▸ (key _ _ n).1 hn⟩
    · rintro ⟨n, hn⟩ e
      exact ⟨n, hn e n rfl⟩

/-- `PA` is ω-consistent: it never proves `exists x phi` together with every
`not forall x implies = x n phi`. -/
theorem omegaConsistent :
    omegaLanguage.OmegaConsistent (TDerivable grammar PA) fun φ => sentence φ.1 :=
  OmegaLanguage.omegaConsistent_of_arithSound (A := omegaLanguage) arithSound

end Silmaril.Logic.Metamath.Peano
