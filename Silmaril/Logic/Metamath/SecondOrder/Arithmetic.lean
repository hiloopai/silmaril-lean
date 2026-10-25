module

public import Silmaril.Logic.Metamath.SecondOrder.Consistency
public import Silmaril.Logic.Metamath.Model.Env
public import Silmaril.Logic.Metatheory.ArithmeticSoundness

@[expose] public section

/-!
# Arithmetical soundness of second-order arithmetic

The language of first-order arithmetic is the part of the grammar of
`z2.mm` without set variables (`arithGrammar`, rules labelled by `AL`): terms
from number variables, `0`, `S`, `+`, `x.`, and formulas from `=`, `<`,
connectives and number quantifiers. It is unambiguous, and its standard model
`stdModel N` is Carneiro's environment model over `ℕ`
(`Silmaril.Logic.Metamath.EnvModel`): a sentence is true in `ℕ` when it
holds for every assignment of numbers to its variables. Its trees embed into
those of `z2.mm` (`embTree`, `embAssertion`).

An arithmetic sentence (`ArithSentence`) is a well-formed assertion of this
language whose variables are number variables; its free variables are read
universally. The value of an embedded tree in an ω-model depends only on the
numbers assigned to its variables and agrees with its value in `ℕ`
(`corr`). Hence every ω-model of a system makes it arithmetically sound: an
arithmetic sentence whose embedding the system derives is true in `ℕ`
(`arithSound_of_isModel`). In particular `Z2`, and so each of its subsystems,
is arithmetically sound (`arithSound_Z2`), both for tree derivations and for
string derivations from the syntax axioms and the flattened axioms
(`arithSound_Z2_derivable`).
-/

namespace Silmaril.Logic.Metamath.SecondOrder

open Grammar Function Silmaril.Logic.Metatheory

/-! ## The language of first-order arithmetic -/

/-- The labels of the syntax rules of first-order arithmetic. -/
inductive AL
  | tvar | t0 | tS | tpl | tmu | wn | wi | wb | wa | wal | wex | weq | wlt
  deriving DecidableEq, Repr

instance : Fintype AL :=
  .ofList [.tvar, .t0, .tS, .tpl, .tmu, .wn, .wi, .wb, .wa, .wal, .wex, .weq, .wlt]
    (by intro l; cases l <;> simp)

/-- The corresponding rule of `z2.mm`. -/
def AL.emb : AL → L
  | .tvar => .tvar
  | .t0 => .t0
  | .tS => .tS
  | .tpl => .tpl
  | .tmu => .tmu
  | .wn => .wn
  | .wi => .wi
  | .wb => .wb
  | .wa => .wa
  | .wal => .wal
  | .wex => .wex
  | .weq => .weq
  | .wlt => .wlt

/-- The syntax typecodes of first-order arithmetic. -/
def isSortA : C → Bool
  | .wff | .term | .nvar => true
  | _ => false

/-- The grammar of first-order arithmetic; only `|-` is provable. -/
def arithGrammar : Grammar AL C V where
  sorts := {c | isSortA c}
  prov := fun
    | .turnstile => some .wff
    | _ => none
  rule l := rules l.emb
  rule_tc l := by cases l <;> rfl
  rule_args l := by cases l <;> decide
  prov_sort {c s} h := by cases c <;> cases h; rfl
  prov_not_sort {c s} h := by cases c <;> cases h; decide

instance : DecidablePred (· ∈ arithGrammar.sorts) :=
  fun c => inferInstanceAs (Decidable (isSortA c))

open C in
/-- The symbol classes that can begin a string of each sort. -/
def firstA : C → List (C ⊕ C)
  | .term => [.inr term, .inr nvar, .inl zero, .inl succ, .inl lb]
  | .wff => [.inr wff, .inl not, .inl lp, .inl all, .inl ex, .inr term, .inr nvar, .inl zero,
      .inl succ, .inl lb]
  | c => [.inr c]

theorem arithGrammar_unambiguous : arithGrammar.Unambiguous :=
  LLCert.unambiguous (F := firstA) (by decide)

/-! ## Embedding into second-order arithmetic -/

mutual

/-- A tree of first-order arithmetic as a tree of `z2.mm`. -/
def embTree : Tree AL V → Tree L V
  | .var q => .var q
  | .node l args => .node l.emb (embTreeList args)

/-- Embed each tree of a list. -/
def embTreeList : List (Tree AL V) → List (Tree L V)
  | [] => []
  | t :: ts => embTree t :: embTreeList ts

end

theorem embTreeList_eq (ts : List (Tree AL V)) : embTreeList ts = ts.map embTree := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [embTreeList, ih]

theorem embTree_node (l : AL) (args : List (Tree AL V)) :
    embTree (.node l args) = .node l.emb (args.map embTree) := by
  rw [embTree, embTreeList_eq]

/-- Embedding preserves sorts. -/
theorem hasSort_embTree {ctx : V → C → Prop} {t : Tree AL V} {s : C}
    (h : arithGrammar.HasSort ctx t s) : grammar.HasSort ctx (embTree t) s := by
  induction h with
  | var hv => exact .var hv
  | @node l args hlen _ ih =>
    rw [embTree_node]
    refine .node (by rw [List.length_map]; exact hlen) fun p hp => ?_
    rw [List.zip_map_left, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact ih q hq

/-- A tree expression of first-order arithmetic as one of `z2.mm`. -/
def embExpr (e : TExpr AL C V) : TExpr L C V := ⟨e.tc, embTree e.tree⟩

/-- A hypothesis of first-order arithmetic as one of `z2.mm`. -/
def embHyp : THyp AL C V → THyp L C V
  | .float c q => .float c q
  | .ess e => .ess (embExpr e)

/-- An assertion of first-order arithmetic as one of `z2.mm`. -/
def embAssertion (A : TAssertion AL C V) : TAssertion L C V :=
  ⟨A.dv, A.hyps.map embHyp, embExpr A.concl⟩

theorem ctx_embAssertion {A : TAssertion AL C V} {q : V} {c : C} :
    (embAssertion A).ctx q c ↔ A.ctx q c := by
  simp only [TAssertion.ctx, embAssertion, List.mem_map]
  constructor
  · rintro ⟨h, hh, he⟩
    cases h with
    | float c' q' =>
      simp only [embHyp, THyp.float.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hh
    | ess e => simp [embHyp] at he
  · exact fun h => ⟨_, h, rfl⟩

theorem mem_essentials_embAssertion {A : TAssertion AL C V} {e : TExpr L C V} :
    e ∈ (embAssertion A).essentials ↔ ∃ e' ∈ A.essentials, embExpr e' = e := by
  simp only [TAssertion.essentials, embAssertion]
  rw [List.filterMap_map, List.mem_filterMap]
  constructor
  · rintro ⟨h, hh, he⟩
    cases h with
    | float c q => simp [embHyp] at he
    | ess e' =>
      simp only [embHyp, Function.comp_apply, Option.some.injEq] at he
      exact ⟨e', TAssertion.mem_essentials.2 hh, he⟩
  · rintro ⟨e', he', rfl⟩
    exact ⟨_, TAssertion.mem_essentials.1 he', rfl⟩

/-! ## The standard model of arithmetic -/

/-- The kinds of the typecodes: number variables are names, terms are
numbers, formulas are formulas. -/
abbrev kindA : C → Metamath.Env.Kind.{0}
  | .nvar => .name
  | .wff => .formula
  | .term => .term ℕ 0
  | _ => .term PUnit PUnit.unit

open Metamath.Env

variable (N : Type) [DecidableEq N]

/-- The standard environment model of first-order arithmetic over `ℕ`. -/
abbrev envModelA : EnvModel arithGrammar ℕ N where
  kind := kindA
  op {s} o a := match s, o, a with
    | _, ⟨.tvar, rfl⟩, a => Term.name (a ⟨0, by decide⟩) id
    | _, ⟨.t0, rfl⟩, _ => Term.const 0
    | _, ⟨.tS, rfl⟩, a => (a ⟨0, by decide⟩).map (· + 1)
    | _, ⟨.tpl, rfl⟩, a => Term.map₂ (· + ·) (a ⟨0, by decide⟩) (a ⟨1, by decide⟩)
    | _, ⟨.tmu, rfl⟩, a => Term.map₂ (· * ·) (a ⟨0, by decide⟩) (a ⟨1, by decide⟩)
    | _, ⟨.wn, rfl⟩, a => (a ⟨0, by decide⟩).map Not
    | _, ⟨.wi, rfl⟩, a => Term.map₂ (· → ·) (a ⟨0, by decide⟩) (a ⟨1, by decide⟩)
    | _, ⟨.wb, rfl⟩, a => Term.map₂ Iff (a ⟨0, by decide⟩) (a ⟨1, by decide⟩)
    | _, ⟨.wa, rfl⟩, a => Term.map₂ And (a ⟨0, by decide⟩) (a ⟨1, by decide⟩)
    | _, ⟨.wal, rfl⟩, a => (a ⟨0, by decide⟩).bind (a ⟨1, by decide⟩) fun P => ∀ m, P m
    | _, ⟨.wex, rfl⟩, a => (a ⟨0, by decide⟩).bind (a ⟨1, by decide⟩) fun P => ∃ m, P m
    | _, ⟨.weq, rfl⟩, a => Term.map₂ (· = ·) (a ⟨0, by decide⟩) (a ⟨1, by decide⟩)
    | _, ⟨.wlt, rfl⟩, a => Term.map₂ (· < ·) (a ⟨0, by decide⟩) (a ⟨1, by decide⟩)
  fresh_op {s t} a o args h := by
    obtain ⟨l, rfl⟩ := o
    refine Metamath.Env.Kind.fresh_of_ignores (by cases l <;> rfl) fun x hx => ?_
    have hj := fun j => (h j).of_name hx
    cases l with
    | tvar => exact Term.notFree_name ((hj ⟨0, by decide⟩).1 _ rfl)
    | t0 => exact fun _ _ => rfl
    | tS => exact Term.notFree_map (hj ⟨0, by decide⟩).2
    | tpl => exact Term.notFree_map₂ (hj ⟨0, by decide⟩).2 (hj ⟨1, by decide⟩).2
    | tmu => exact Term.notFree_map₂ (hj ⟨0, by decide⟩).2 (hj ⟨1, by decide⟩).2
    | wn => exact Term.notFree_map (hj ⟨0, by decide⟩).2
    | wi => exact Term.notFree_map₂ (hj ⟨0, by decide⟩).2 (hj ⟨1, by decide⟩).2
    | wb => exact Term.notFree_map₂ (hj ⟨0, by decide⟩).2 (hj ⟨1, by decide⟩).2
    | wa => exact Term.notFree_map₂ (hj ⟨0, by decide⟩).2 (hj ⟨1, by decide⟩).2
    | wal => exact Term.notFree_bind ((hj ⟨1, by decide⟩).1 _ rfl) (hj ⟨0, by decide⟩).2
    | wex => exact Term.notFree_bind ((hj ⟨1, by decide⟩).1 _ rfl) (hj ⟨0, by decide⟩).2
    | weq => exact Term.notFree_map₂ (hj ⟨0, by decide⟩).2 (hj ⟨1, by decide⟩).2
    | wlt => exact Term.notFree_map₂ (hj ⟨0, by decide⟩).2 (hj ⟨1, by decide⟩).2
  IsTrue {c s} _ a := match c, s, a with
    | .turnstile, .wff, (φ : Term ℕ N Prop) => SetTheory.Valid φ.1
    | _, _, _ => False

variable [Infinite N]

/-- The standard model of first-order arithmetic: `ℕ` with its operations. -/
abbrev stdModel : Model arithGrammar := (envModelA N).toModel

variable {N}

/-! ### Values in the standard model -/

section Values

variable {ctx : V → C → Prop}

/-- Sorting in the context `ctx`. -/
local notation "HA" t:max s:max => arithGrammar.HasSort ctx t s


theorem tvar_0A {a : Tree AL V} (h : HA (.node .tvar [a]) .term) : HA a .nvar :=
  h.child ⟨0, by decide⟩

theorem tS_0A {a : Tree AL V} (h : HA (.node .tS [a]) .term) : HA a .term :=
  h.child ⟨0, by decide⟩

theorem tpl_0A {a b : Tree AL V} (h : HA (.node .tpl [a, b]) .term) : HA a .term :=
  h.child ⟨0, by decide⟩

theorem tpl_1A {a b : Tree AL V} (h : HA (.node .tpl [a, b]) .term) : HA b .term :=
  h.child ⟨1, by decide⟩

theorem tmu_0A {a b : Tree AL V} (h : HA (.node .tmu [a, b]) .term) : HA a .term :=
  h.child ⟨0, by decide⟩

theorem tmu_1A {a b : Tree AL V} (h : HA (.node .tmu [a, b]) .term) : HA b .term :=
  h.child ⟨1, by decide⟩

theorem wn_0A {a : Tree AL V} (h : HA (.node .wn [a]) .wff) : HA a .wff :=
  h.child ⟨0, by decide⟩

theorem wi_0A {a b : Tree AL V} (h : HA (.node .wi [a, b]) .wff) : HA a .wff :=
  h.child ⟨0, by decide⟩

theorem wi_1A {a b : Tree AL V} (h : HA (.node .wi [a, b]) .wff) : HA b .wff :=
  h.child ⟨1, by decide⟩

theorem wb_0A {a b : Tree AL V} (h : HA (.node .wb [a, b]) .wff) : HA a .wff :=
  h.child ⟨0, by decide⟩

theorem wb_1A {a b : Tree AL V} (h : HA (.node .wb [a, b]) .wff) : HA b .wff :=
  h.child ⟨1, by decide⟩

theorem wa_0A {a b : Tree AL V} (h : HA (.node .wa [a, b]) .wff) : HA a .wff :=
  h.child ⟨0, by decide⟩

theorem wa_1A {a b : Tree AL V} (h : HA (.node .wa [a, b]) .wff) : HA b .wff :=
  h.child ⟨1, by decide⟩

theorem wal_0A {a b : Tree AL V} (h : HA (.node .wal [a, b]) .wff) : HA a .wff :=
  h.child ⟨0, by decide⟩

theorem wal_1A {a b : Tree AL V} (h : HA (.node .wal [a, b]) .wff) : HA b .nvar :=
  h.child ⟨1, by decide⟩

theorem wex_0A {a b : Tree AL V} (h : HA (.node .wex [a, b]) .wff) : HA a .wff :=
  h.child ⟨0, by decide⟩

theorem wex_1A {a b : Tree AL V} (h : HA (.node .wex [a, b]) .wff) : HA b .nvar :=
  h.child ⟨1, by decide⟩

theorem weq_0A {a b : Tree AL V} (h : HA (.node .weq [a, b]) .wff) : HA a .term :=
  h.child ⟨0, by decide⟩

theorem weq_1A {a b : Tree AL V} (h : HA (.node .weq [a, b]) .wff) : HA b .term :=
  h.child ⟨1, by decide⟩

theorem wlt_0A {a b : Tree AL V} (h : HA (.node .wlt [a, b]) .wff) : HA a .term :=
  h.child ⟨0, by decide⟩

theorem wlt_1A {a b : Tree AL V} (h : HA (.node .wlt [a, b]) .wff) : HA b .term :=
  h.child ⟨1, by decide⟩

variable (ρ : ∀ q s, ctx q s → (stdModel N).Carrier s)


theorem valA_tvar {a : Tree AL V} (h : HA (.node .tvar [a]) .term) :
    ((stdModel N).value ρ _ h).1 =
      fun e => e ((stdModel N).value ρ a (tvar_0A h)) := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem valA_t0 (h : HA (.node .t0 []) .term) :
    ((stdModel N).value ρ _ h).1 =
      fun _ => 0 := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem valA_tS {a : Tree AL V} (h : HA (.node .tS [a]) .term) :
    ((stdModel N).value ρ _ h).1 =
      fun e => ((stdModel N).value ρ a (tS_0A h)).1 e + 1 := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem valA_tpl {a b : Tree AL V} (h : HA (.node .tpl [a, b]) .term) :
    ((stdModel N).value ρ _ h).1 =
      fun e =>
        ((stdModel N).value ρ a (tpl_0A h)).1 e + ((stdModel N).value ρ b (tpl_1A h)).1 e := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem valA_tmu {a b : Tree AL V} (h : HA (.node .tmu [a, b]) .term) :
    ((stdModel N).value ρ _ h).1 =
      fun e =>
        ((stdModel N).value ρ a (tmu_0A h)).1 e * ((stdModel N).value ρ b (tmu_1A h)).1 e := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem valA_wn {a : Tree AL V} (h : HA (.node .wn [a]) .wff) :
    ((stdModel N).value ρ _ h).1 =
      fun e => ¬ ((stdModel N).value ρ a (wn_0A h)).1 e := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem valA_wi {a b : Tree AL V} (h : HA (.node .wi [a, b]) .wff) :
    ((stdModel N).value ρ _ h).1 =
      fun e => ((stdModel N).value ρ a (wi_0A h)).1 e → ((stdModel N).value ρ b (wi_1A h)).1 e := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem valA_wb {a b : Tree AL V} (h : HA (.node .wb [a, b]) .wff) :
    ((stdModel N).value ρ _ h).1 =
      fun e =>
        (((stdModel N).value ρ a (wb_0A h)).1 e ↔ ((stdModel N).value ρ b (wb_1A h)).1 e) := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem valA_wa {a b : Tree AL V} (h : HA (.node .wa [a, b]) .wff) :
    ((stdModel N).value ρ _ h).1 =
      fun e => ((stdModel N).value ρ a (wa_0A h)).1 e ∧ ((stdModel N).value ρ b (wa_1A h)).1 e := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem valA_wal {a b : Tree AL V} (h : HA (.node .wal [a, b]) .wff) :
    ((stdModel N).value ρ _ h).1 =
      fun e => ∀ m,
        ((stdModel N).value ρ a (wal_0A h)).1 (update e ((stdModel N).value ρ b (wal_1A h)) m) := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem valA_wex {a b : Tree AL V} (h : HA (.node .wex [a, b]) .wff) :
    ((stdModel N).value ρ _ h).1 =
      fun e => ∃ m,
        ((stdModel N).value ρ a (wex_0A h)).1 (update e ((stdModel N).value ρ b (wex_1A h)) m) := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem valA_weq {a b : Tree AL V} (h : HA (.node .weq [a, b]) .wff) :
    ((stdModel N).value ρ _ h).1 =
      fun e =>
        ((stdModel N).value ρ a (weq_0A h)).1 e = ((stdModel N).value ρ b (weq_1A h)).1 e := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem valA_wlt {a b : Tree AL V} (h : HA (.node .wlt [a, b]) .wff) :
    ((stdModel N).value ρ _ h).1 =
      fun e =>
        ((stdModel N).value ρ a (wlt_0A h)).1 e < ((stdModel N).value ρ b (wlt_1A h)).1 e := by
  unfold Model.value
  rw [eval_node]
  rfl

theorem valA_var {q : V} {s : C} (h : HA (.var q) s) :
    (stdModel N).value ρ (.var q) h = ρ q s (HasSort.var_iff.1 h) :=
  Model.value_var _ ρ h

end Values

/-! ## Agreement of ω-models with `ℕ` -/

section Corr

variable {𝒮 : Set (Set ℕ)}

/-- The numbers of an environment. -/
def numPart (e : Sem.Env 𝒮 N) : SetTheory.Env ℕ N := fun x => e (.inl x)

omit [Infinite N] in
theorem numPart_update (e : Sem.Env 𝒮 N) (x : N) (m : ℕ) :
    numPart (update e (.inl x) m) = update (numPart e) x m := by
  funext y
  by_cases hyx : y = x
  · subst hyx
    simp [numPart]
  · simp only [numPart, update_of_ne hyx]
    exact Sem.update_inl_ne e hyx m

omit [Infinite N] in
theorem corr_update {φ : Sem.Env 𝒮 N → Prop} {ψ : SetTheory.Env ℕ N → Prop}
    (h : ∀ e, φ e ↔ ψ (numPart e)) (x : N) (e : Sem.Env 𝒮 N) (m : ℕ) :
    φ (update e (.inl x) m) ↔ ψ (update (numPart e) x m) := by
  rw [h, numPart_update]

variable (N 𝒮) in
/-- A value of the ω-model and a value of the standard model agree when they
are the same name, or the same function of the numbers of an environment. -/
def Corr : (s : C) → (model 𝒮 N).Carrier s → (stdModel N).Carrier s → Prop
  | .nvar, x, y => x = y
  | .term, a, b => ∀ e, a.1 e = b.1 (numPart e)
  | .wff, φ, ψ => ∀ e, φ.1 e ↔ ψ.1 (numPart e)
  | _, _, _ => True

/-- The value of an embedded tree in an ω-model agrees with its value in the
standard model, when the valuations agree. -/
theorem corr {ctx ctx₁ : V → C → Prop} (ρ : (model 𝒮 N).Valuation ctx)
    (ρ₁ : (stdModel N).Valuation ctx₁)
    (hρ : ∀ q s h h₁, Corr N 𝒮 s (ρ q s h) (ρ₁ q s h₁)) (t : Tree AL V) :
    ∀ {s : C} (h₁ : arithGrammar.HasSort (arithGrammar.synCtx ctx₁) t s)
      (h : grammar.HasSort (grammar.synCtx ctx) (embTree t) s),
      Corr N 𝒮 s ((model 𝒮 N).value ρ (embTree t) h) ((stdModel N).value ρ₁ t h₁) := by
  induction t using Tree.induction with
  | var q =>
    intro s h₁ h
    have h' : grammar.HasSort (grammar.synCtx ctx) (.var q) s := h
    have e₁ : (model 𝒮 N).value ρ (embTree (.var q)) h = (model 𝒮 N).value ρ (.var q) h' := rfl
    rw [e₁, val_var, valA_var]
    exact hρ _ _ _ _
  | node l args ih =>
    intro s h₁ h
    obtain ⟨hs, hlen, -⟩ := h₁.node_inv
    cases l with
    | tvar =>
      obtain ⟨a, rfl⟩ : ∃ a, args = [a] := match args, hlen with | [a], _ => ⟨a, rfl⟩
      have hs' : s = .term := hs.symm
      subst hs'
      have h' : grammar.HasSort (grammar.synCtx ctx) (.node .tvar [embTree a]) .term := h
      have e₁ : (model 𝒮 N).value ρ (embTree (.node .tvar [a])) h =
          (model 𝒮 N).value ρ (.node .tvar [embTree a]) h' := rfl
      rw [e₁]
      intro e
      rw [val_tvar ρ h', valA_tvar ρ₁ h₁]
      have ha : _ = _ := ih a (by simp) (tvar_0A h₁) (tvar_0 h')
      simp only [Sem.var, numPart]
      rw [ha]
    | t0 =>
      obtain rfl : args = [] := match args, hlen with | [], _ => rfl
      have hs' : s = .term := hs.symm
      subst hs'
      have h' : grammar.HasSort (grammar.synCtx ctx) (.node .t0 []) .term := h
      have e₁ : (model 𝒮 N).value ρ (embTree (.node .t0 [])) h =
          (model 𝒮 N).value ρ (.node .t0 []) h' := rfl
      rw [e₁]
      intro e
      rw [val_t0 ρ h', valA_t0 ρ₁ h₁]
      rfl
    | tS =>
      obtain ⟨a, rfl⟩ : ∃ a, args = [a] := match args, hlen with | [a], _ => ⟨a, rfl⟩
      have hs' : s = .term := hs.symm
      subst hs'
      have h' : grammar.HasSort (grammar.synCtx ctx) (.node .tS [embTree a]) .term := h
      have e₁ : (model 𝒮 N).value ρ (embTree (.node .tS [a])) h =
          (model 𝒮 N).value ρ (.node .tS [embTree a]) h' := rfl
      rw [e₁]
      intro e
      rw [val_tS ρ h', valA_tS ρ₁ h₁]
      exact congrArg (· + 1) (ih a (by simp) (tS_0A h₁) (tS_0 h') e)
    | tpl =>
      obtain ⟨a, b, rfl⟩ : ∃ a b, args = [a, b] := match args, hlen with
        | [a, b], _ => ⟨a, b, rfl⟩
      have hs' : s = .term := hs.symm
      subst hs'
      have h' : grammar.HasSort (grammar.synCtx ctx) (.node .tpl [embTree a, embTree b]) .term := h
      have e₁ : (model 𝒮 N).value ρ (embTree (.node .tpl [a, b])) h =
          (model 𝒮 N).value ρ (.node .tpl [embTree a, embTree b]) h' := rfl
      rw [e₁]
      intro e
      rw [val_tpl ρ h', valA_tpl ρ₁ h₁]
      exact congrArg₂ (· + ·) (ih a (by simp) (tpl_0A h₁) (tpl_0 h') e)
        (ih b (by simp) (tpl_1A h₁) (tpl_1 h') e)
    | tmu =>
      obtain ⟨a, b, rfl⟩ : ∃ a b, args = [a, b] := match args, hlen with
        | [a, b], _ => ⟨a, b, rfl⟩
      have hs' : s = .term := hs.symm
      subst hs'
      have h' : grammar.HasSort (grammar.synCtx ctx) (.node .tmu [embTree a, embTree b]) .term := h
      have e₁ : (model 𝒮 N).value ρ (embTree (.node .tmu [a, b])) h =
          (model 𝒮 N).value ρ (.node .tmu [embTree a, embTree b]) h' := rfl
      rw [e₁]
      intro e
      rw [val_tmu ρ h', valA_tmu ρ₁ h₁]
      exact congrArg₂ (· * ·) (ih a (by simp) (tmu_0A h₁) (tmu_0 h') e)
        (ih b (by simp) (tmu_1A h₁) (tmu_1 h') e)
    | wn =>
      obtain ⟨a, rfl⟩ : ∃ a, args = [a] := match args, hlen with | [a], _ => ⟨a, rfl⟩
      have hs' : s = .wff := hs.symm
      subst hs'
      have h' : grammar.HasSort (grammar.synCtx ctx) (.node .wn [embTree a]) .wff := h
      have e₁ : (model 𝒮 N).value ρ (embTree (.node .wn [a])) h =
          (model 𝒮 N).value ρ (.node .wn [embTree a]) h' := rfl
      rw [e₁]
      intro e
      rw [val_wn ρ h', valA_wn ρ₁ h₁]
      exact not_congr (ih a (by simp) (wn_0A h₁) (wn_0 h') e)
    | wi =>
      obtain ⟨a, b, rfl⟩ : ∃ a b, args = [a, b] := match args, hlen with
        | [a, b], _ => ⟨a, b, rfl⟩
      have hs' : s = .wff := hs.symm
      subst hs'
      have h' : grammar.HasSort (grammar.synCtx ctx) (.node .wi [embTree a, embTree b]) .wff := h
      have e₁ : (model 𝒮 N).value ρ (embTree (.node .wi [a, b])) h =
          (model 𝒮 N).value ρ (.node .wi [embTree a, embTree b]) h' := rfl
      rw [e₁]
      intro e
      rw [val_wi ρ h', valA_wi ρ₁ h₁]
      exact imp_congr (ih a (by simp) (wi_0A h₁) (wi_0 h') e)
        (ih b (by simp) (wi_1A h₁) (wi_1 h') e)
    | wb =>
      obtain ⟨a, b, rfl⟩ : ∃ a b, args = [a, b] := match args, hlen with
        | [a, b], _ => ⟨a, b, rfl⟩
      have hs' : s = .wff := hs.symm
      subst hs'
      have h' : grammar.HasSort (grammar.synCtx ctx) (.node .wb [embTree a, embTree b]) .wff := h
      have e₁ : (model 𝒮 N).value ρ (embTree (.node .wb [a, b])) h =
          (model 𝒮 N).value ρ (.node .wb [embTree a, embTree b]) h' := rfl
      rw [e₁]
      intro e
      rw [val_wb ρ h', valA_wb ρ₁ h₁]
      exact iff_congr (ih a (by simp) (wb_0A h₁) (wb_0 h') e)
        (ih b (by simp) (wb_1A h₁) (wb_1 h') e)
    | wa =>
      obtain ⟨a, b, rfl⟩ : ∃ a b, args = [a, b] := match args, hlen with
        | [a, b], _ => ⟨a, b, rfl⟩
      have hs' : s = .wff := hs.symm
      subst hs'
      have h' : grammar.HasSort (grammar.synCtx ctx) (.node .wa [embTree a, embTree b]) .wff := h
      have e₁ : (model 𝒮 N).value ρ (embTree (.node .wa [a, b])) h =
          (model 𝒮 N).value ρ (.node .wa [embTree a, embTree b]) h' := rfl
      rw [e₁]
      intro e
      rw [val_wa ρ h', valA_wa ρ₁ h₁]
      exact and_congr (ih a (by simp) (wa_0A h₁) (wa_0 h') e)
        (ih b (by simp) (wa_1A h₁) (wa_1 h') e)
    | wal =>
      obtain ⟨a, b, rfl⟩ : ∃ a b, args = [a, b] := match args, hlen with
        | [a, b], _ => ⟨a, b, rfl⟩
      have hs' : s = .wff := hs.symm
      subst hs'
      have h' : grammar.HasSort (grammar.synCtx ctx) (.node .wal [embTree a, embTree b]) .wff := h
      have e₁ : (model 𝒮 N).value ρ (embTree (.node .wal [a, b])) h =
          (model 𝒮 N).value ρ (.node .wal [embTree a, embTree b]) h' := rfl
      rw [e₁]
      intro e
      rw [val_wal ρ h', valA_wal ρ₁ h₁]
      have hb : ((model 𝒮 N).value ρ (embTree b) (wal_1 h') : N) =
          (stdModel N).value ρ₁ b (wal_1A h₁) := ih b (by simp) (wal_1A h₁) (wal_1 h')
      refine forall_congr' fun m => ?_
      rw [← hb]
      exact corr_update (ih a (by simp) (wal_0A h₁) (wal_0 h')) _ e m
    | wex =>
      obtain ⟨a, b, rfl⟩ : ∃ a b, args = [a, b] := match args, hlen with
        | [a, b], _ => ⟨a, b, rfl⟩
      have hs' : s = .wff := hs.symm
      subst hs'
      have h' : grammar.HasSort (grammar.synCtx ctx) (.node .wex [embTree a, embTree b]) .wff := h
      have e₁ : (model 𝒮 N).value ρ (embTree (.node .wex [a, b])) h =
          (model 𝒮 N).value ρ (.node .wex [embTree a, embTree b]) h' := rfl
      rw [e₁]
      intro e
      rw [val_wex ρ h', valA_wex ρ₁ h₁]
      have hb : ((model 𝒮 N).value ρ (embTree b) (wex_1 h') : N) =
          (stdModel N).value ρ₁ b (wex_1A h₁) := ih b (by simp) (wex_1A h₁) (wex_1 h')
      refine exists_congr fun m => ?_
      rw [← hb]
      exact corr_update (ih a (by simp) (wex_0A h₁) (wex_0 h')) _ e m
    | weq =>
      obtain ⟨a, b, rfl⟩ : ∃ a b, args = [a, b] := match args, hlen with
        | [a, b], _ => ⟨a, b, rfl⟩
      have hs' : s = .wff := hs.symm
      subst hs'
      have h' : grammar.HasSort (grammar.synCtx ctx) (.node .weq [embTree a, embTree b]) .wff := h
      have e₁ : (model 𝒮 N).value ρ (embTree (.node .weq [a, b])) h =
          (model 𝒮 N).value ρ (.node .weq [embTree a, embTree b]) h' := rfl
      rw [e₁]
      intro e
      rw [val_weq ρ h', valA_weq ρ₁ h₁]
      simp only [Sem.eq]
      rw [ih a (by simp) (weq_0A h₁) (weq_0 h') e, ih b (by simp) (weq_1A h₁) (weq_1 h') e]
    | wlt =>
      obtain ⟨a, b, rfl⟩ : ∃ a b, args = [a, b] := match args, hlen with
        | [a, b], _ => ⟨a, b, rfl⟩
      have hs' : s = .wff := hs.symm
      subst hs'
      have h' : grammar.HasSort (grammar.synCtx ctx) (.node .wlt [embTree a, embTree b]) .wff := h
      have e₁ : (model 𝒮 N).value ρ (embTree (.node .wlt [a, b])) h =
          (model 𝒮 N).value ρ (.node .wlt [embTree a, embTree b]) h' := rfl
      rw [e₁]
      intro e
      rw [val_wlt ρ h', valA_wlt ρ₁ h₁]
      simp only [Sem.lt]
      rw [ih a (by simp) (wlt_0A h₁) (wlt_0 h') e, ih b (by simp) (wlt_1A h₁) (wlt_1 h') e]

end Corr

/-! ## Arithmetical soundness -/

/-- An arithmetic sentence has number variables only; its free variables are
read universally. -/
def IsSentence (A : TAssertion AL C V) : Prop := ∀ q s, A.ctx q s → s = .nvar

theorem arithGrammar_prov {c s : C} (h : arithGrammar.prov c = some s) :
    c = .turnstile ∧ s = .wff := by
  cases c <;> cases h
  exact ⟨rfl, rfl⟩

theorem synCtx_of_arith {ctx : V → C → Prop} {q : V} {s : C}
    (h : arithGrammar.synCtx ctx q s) : grammar.synCtx ctx q s :=
  ⟨h.1, by have := h.2; revert this; cases s <;> decide⟩

theorem floats_embAssertion (A : TAssertion AL C V) : (embAssertion A).floats = A.floats := by
  simp only [TAssertion.floats, embAssertion, List.filterMap_map]
  congr 1
  funext h
  cases h <;> rfl

theorem wellTyped_embExpr {ctx : V → C → Prop} {e : TExpr AL C V}
    (h : e.WellTyped arithGrammar ctx) : (embExpr e).WellTyped grammar ctx := by
  obtain ⟨s, hs, ht⟩ := h
  obtain ⟨hc, rfl⟩ := arithGrammar_prov hs
  refine ⟨.wff, ?_, hasSort_embTree ht⟩
  change provOf e.tc = some .wff
  rw [hc]
  rfl

/-- The embedding of a well-formed assertion is well formed. -/
theorem wellFormed_embAssertion {A : TAssertion AL C V} (hA : A.WellFormed arithGrammar) :
    (embAssertion A).WellFormed grammar where
  floats_nodup := by rw [floats_embAssertion]; exact hA.floats_nodup
  float_sort q s h := by
    have := hA.float_sort q s (ctx_embAssertion.1 h)
    revert this
    cases s <;> decide
  ess_wellTyped e he := by
    obtain ⟨e', he', rfl⟩ := mem_essentials_embAssertion.1 he
    exact (wellTyped_embExpr (hA.ess_wellTyped e' he')).mono fun _ _ h => ctx_embAssertion.2 h
  concl_wellTyped :=
    (wellTyped_embExpr hA.concl_wellTyped).mono fun _ _ h => ctx_embAssertion.2 h
  dv_irrefl := hA.dv_irrefl
  dv_float a b h := by
    obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := hA.dv_float a b h
    exact ⟨⟨s, ctx_embAssertion.2 hs⟩, ⟨t, ctx_embAssertion.2 ht⟩⟩

section Agree

variable {𝒮 : Set (Set ℕ)}

/-- The environment assigning the numbers `ν` and the set `A₀` to every set
name. -/
def extendEnv (A₀ : ↥𝒮) (ν : SetTheory.Env ℕ N) : Sem.Env 𝒮 N
  | .inl x => ν x
  | .inr _ => A₀

omit [DecidableEq N] [Infinite N] in
theorem numPart_extendEnv (A₀ : ↥𝒮) (ν : SetTheory.Env ℕ N) :
    numPart (extendEnv A₀ ν) = ν := rfl

omit [Infinite N] in
theorem fresh_of_ne' {a b : N} (h : a ≠ b) :
    Kind.Fresh (𝒮 := 𝒮) .nname .nname a b :=
  ⟨fun n hn m hm => by
    simp only [Kind.nameOf, Option.mem_def, Option.some.injEq] at hn hm
    subst hn hm
    exact fun e => h (Sum.inl_injective e), fun _ _ => trivial, fun _ _ => trivial⟩

theorem isTrue_std {c : C} (hs : arithGrammar.prov c = some .wff)
    (a : (stdModel N).Carrier .wff) : (stdModel N).IsTrue hs a ↔ SetTheory.Valid a.1 := by
  obtain ⟨rfl, -⟩ := arithGrammar_prov hs
  rfl

theorem isTrue_model {c : C} (hc : c = .turnstile) (hs : grammar.prov c = some .wff)
    (a : (model 𝒮 N).Carrier .wff) : (model 𝒮 N).IsTrue hs a ↔ Sem.Valid a.1 := by
  subst hc
  rfl

/-- The embedding of an arithmetic sentence holds in an ω-model with a
nonempty second-order part only if the sentence is true in `ℕ`. -/
theorem satisfies_of_embAssertion (h𝒮 : 𝒮.Nonempty) {A : TAssertion AL C V}
    (hA : A.WellFormed arithGrammar) (hs : IsSentence A)
    (h : (model 𝒮 N).Satisfies (embAssertion A)) : (stdModel N).Satisfies A := by
  obtain ⟨A₀, hA₀⟩ := h𝒮
  intro ρ₁ hdv₁ hess₁
  have hsE : ∀ q s, (embAssertion A).ctx q s → s = .nvar :=
    fun q s h => hs q s (ctx_embAssertion.1 h)
  have hsyn : ∀ q, A.ctx q .nvar → arithGrammar.synCtx A.ctx q .nvar := fun _ h => ⟨h, rfl⟩
  let ρ : (model 𝒮 N).Valuation (embAssertion A).ctx := fun q s hq =>
    cast (congrArg (model 𝒮 N).Carrier (hsE q s hq.1).symm)
      (ρ₁ q .nvar (hsyn q (ctx_embAssertion.1 ((hsE q s hq.1) ▸ hq.1))) : N)
  have hρ : ∀ q s h h₁, Corr N 𝒮 s (ρ q s h) (ρ₁ q s h₁) := by
    intro q s h h₁
    obtain rfl := hsE q s h.1
    exact cast_eq _ _
  have hctx : ∀ q s, arithGrammar.synCtx A.ctx q s → grammar.synCtx (embAssertion A).ctx q s :=
    fun q s h => synCtx_of_arith ⟨ctx_embAssertion.2 h.1, h.2⟩
  have hdv : (model 𝒮 N).DVHolds ρ (embAssertion A).dv := by
    intro a b hab hne s t ha hb
    obtain rfl := hsE a s ha.1
    obtain rfl := hsE b t hb.1
    have := hdv₁ a b hab hne .nvar .nvar (hsyn a (ctx_embAssertion.1 ha.1))
      (hsyn b (ctx_embAssertion.1 hb.1))
    rw [show ρ a .nvar ha = ρ₁ a .nvar _ from cast_eq _ _,
      show ρ b .nvar hb = ρ₁ b .nvar _ from cast_eq _ _]
    exact fresh_of_ne' (Metamath.Env.Kind.fresh_name_name.1 this)
  have hess : ∀ e ∈ (embAssertion A).essentials, (model 𝒮 N).Holds ρ e := by
    intro e he
    obtain ⟨⟨c, t⟩, he₁, rfl⟩ := mem_essentials_embAssertion.1 he
    obtain ⟨s, hs', ht₁, htrue⟩ := hess₁ _ he₁
    obtain ⟨rfl, rfl⟩ := arithGrammar_prov hs'
    have ht : grammar.HasSort (grammar.synCtx (embAssertion A).ctx) (embTree t) .wff :=
      (hasSort_embTree ht₁).mono hctx
    exact ⟨.wff, rfl, ht, fun env => (corr ρ ρ₁ hρ t ht₁ ht env).2 (htrue _)⟩
  obtain ⟨s, hsM, htM, htrueM⟩ := h ρ hdv hess
  obtain ⟨s₁, hs₁, ht₁⟩ := hA.concl_wellTyped
  obtain ⟨hc, rfl⟩ := arithGrammar_prov hs₁
  have hsM' : grammar.prov A.concl.tc = some .wff := by rw [hc]; rfl
  obtain rfl : s = .wff := Option.some.inj (hsM.symm.trans hsM')
  have ht₁' := ht₁.synCtx (G := arithGrammar) rfl
  refine ⟨.wff, hs₁, ht₁', (isTrue_std hs₁ _).2 fun ν => ?_⟩
  have := (corr ρ ρ₁ hρ A.concl.tree ht₁' htM (extendEnv ⟨A₀, hA₀⟩ ν)).1
    ((isTrue_model hc hsM _).1 htrueM _)
  rwa [numPart_extendEnv] at this

end Agree

/-- Arithmetic sentences: well-formed assertions of first-order arithmetic
whose variables are number variables. -/
def ArithSentence : Type := {A : TAssertion AL C V // A.WellFormed arithGrammar ∧ IsSentence A}

/-- The language of first-order arithmetic: its sentences are the arithmetic
sentences, the Σ₁ sentences are given by `sigma1`, and a sentence is true when
the standard model `ℕ` satisfies it. -/
def arithLanguage (sigma1 : TAssertion AL C V → Prop) : ArithLanguage where
  Sentence := ArithSentence
  IsSigma1 A := sigma1 A.1
  TrueInNat A := (stdModel ℕ).Satisfies A.1

/-- A system with an ω-model whose second-order part is nonempty is
arithmetically sound: every arithmetic sentence whose embedding it derives is
true in `ℕ`. -/
theorem arithSound_of_isModel {𝒮 : Set (Set ℕ)} (h𝒮 : 𝒮.Nonempty) {Γ : Set (TAssertion L C V)}
    (hΓ : ∀ B ∈ Γ, B.WellFormed grammar) (hM : (model 𝒮 ℕ).IsModel Γ)
    (sigma1 : TAssertion AL C V → Prop) :
    (arithLanguage sigma1).ArithSound (TDerivable grammar Γ) fun A => embAssertion A.1 :=
  ArithLanguage.arithSound_of_model (model 𝒮 ℕ).Satisfies (fun _ h => (model 𝒮 ℕ).sound hΓ hM h)
    fun A hA => satisfies_of_embAssertion h𝒮 A.2.1 A.2.2 hA

/-- Second-order arithmetic is arithmetically sound: every first-order
arithmetic sentence provable in `Z2` is true in `ℕ`. -/
theorem arithSound_Z2 (sigma1 : TAssertion AL C V → Prop) :
    (arithLanguage sigma1).ArithSound (TDerivable grammar Z2) fun A => embAssertion A.1 :=
  arithSound_of_isModel (𝒮 := Set.univ) ⟨∅, trivial⟩ wellFormed_Z2 isModel_full_Z2 sigma1

theorem arithSound_ACA0 (sigma1 : TAssertion AL C V → Prop) :
    (arithLanguage sigma1).ArithSound (TDerivable grammar ACA0) fun A => embAssertion A.1 :=
  arithSound_of_isModel (𝒮 := Set.univ) ⟨∅, trivial⟩ wellFormed_ACA0 isModel_full_ACA0 sigma1

theorem arithSound_WKL0 (sigma1 : TAssertion AL C V → Prop) :
    (arithLanguage sigma1).ArithSound (TDerivable grammar WKL0) fun A => embAssertion A.1 :=
  arithSound_of_isModel (𝒮 := Set.univ) ⟨∅, trivial⟩ wellFormed_WKL0 isModel_full_WKL0 sigma1

theorem arithSound_RCA0 (sigma1 : TAssertion AL C V → Prop) :
    (arithLanguage sigma1).ArithSound (TDerivable grammar RCA0) fun A => embAssertion A.1 :=
  arithSound_of_isModel (𝒮 := Set.univ) ⟨∅, trivial⟩ wellFormed_RCA0 isModel_full_RCA0 sigma1

/-- In particular `Z2` is Σ₁-sound. -/
theorem sigma1Sound_Z2 (sigma1 : TAssertion AL C V → Prop) :
    (arithLanguage sigma1).Sigma1Sound (TDerivable grammar Z2) fun A => embAssertion A.1 :=
  (arithSound_Z2 sigma1).sigma1Sound

/-- Arithmetical soundness for string derivations: every arithmetic sentence
whose flattened embedding the syntax axioms and the flattened axioms of `Z2`
derive is true in `ℕ`. -/
theorem arithSound_Z2_derivable (sigma1 : TAssertion AL C V → Prop) :
    (arithLanguage sigma1).ArithSound (Derivable (grammar.axioms Z2))
      fun A => (embAssertion A.1).flatten grammar := fun A h =>
  arithSound_Z2 sigma1 A
    ((tderivable_iff_derivable unambiguous wellFormed_Z2 (wellFormed_embAssertion A.2.1)).2 h)

end Silmaril.Logic.Metamath.SecondOrder
