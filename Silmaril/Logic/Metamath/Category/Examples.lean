module

public import Silmaril.Logic.Metamath.Category.Conservative
public import Silmaril.Logic.Metamath.Grammar.Examples

@[expose] public section

/-!
# A definitional extension, end to end

A decidable well-formedness check for tree assertions
(`Grammar.checkWF`, `Grammar.wellFormed_of_checkWF`), and a worked example of
the definitional extension theorem.

`GAxSet.Toy` is a toy implicational calculus with negation: syntax
`wn : wff ::= ¬ φ` and `wi : wff ::= ( φ → ψ )`, provable typecode `⊢`, and
axioms modus ponens, `⊢ ( φ → φ )` and `⊢ ( φ → ( ψ → φ ) )`. Disjunction is
added as a new syntax rule `wo : wff ::= ( φ ∨ ψ )` with the defining axioms
`⊢ ( ( φ ∨ ψ ) → ( ¬ φ → ψ ) )` and `⊢ ( ( ¬ φ → ψ ) → ( φ ∨ ψ ) )`.
Eliminating `∨` by its definiens `( ¬ φ → ψ )` turns both into instances of
`⊢ ( φ → φ )`, so the extension is conservative over the language without `∨`
(`GAxSet.Toy.conservative`, `GAxSet.Toy.definitional_extension`).
-/

namespace Silmaril.Logic.Metamath

open CategoryTheory Grammar

universe u

namespace Grammar

section Check

variable {L C V : Type u} [DecidableEq V] (G : Grammar L C V)

/-- The sort given to `v` by the first floating hypothesis on it. -/
def TAssertion.floatSort (A : TAssertion L C V) (v : V) : Option C :=
  (A.floats.find? fun p => p.2 = v).map Prod.fst

theorem TAssertion.ctx_of_floatSort {A : TAssertion L C V} {v : V} {s : C}
    (h : A.floatSort v = some s) : A.ctx v s := by
  simp only [TAssertion.floatSort, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have hmem := List.mem_of_find?_eq_some hp
  have hv : p.2 = v := by simpa using List.find?_some hp
  rw [← TAssertion.mem_floats, ← hv]
  exact hmem

/-- `e` is at a provable typecode and its tree checks at the corresponding
syntax typecode under the variable sorts `f`. -/
def checkTyped [DecidableEq C] (f : V → Option C) (e : TExpr L C V) : Bool :=
  match G.prov e.tc with
  | some s => G.check f e.tree s
  | none => false

omit [DecidableEq V] in
theorem wellTyped_of_checkTyped [DecidableEq C] {ctx : V → C → Prop} {f : V → Option C}
    (hf : ∀ v s, f v = some s → ctx v s) {e : TExpr L C V} (h : G.checkTyped f e = true) :
    e.WellTyped G ctx := by
  unfold checkTyped at h
  split at h
  · rename_i s hs
    exact ⟨s, hs, ((check_iff _ _).1 h).mono hf⟩
  · cases h

/-- A decidable check of well-formedness, given a decision procedure `isSort`
for the syntax typecodes. -/
def checkWF [DecidableEq C] (isSort : C → Bool) (A : TAssertion L C V) : Bool :=
  decide (A.floats.map Prod.snd).Nodup && A.floats.all (fun p => isSort p.1) &&
    A.essentials.all (G.checkTyped A.floatSort) && G.checkTyped A.floatSort A.concl &&
    A.dv.all fun p => decide (p.1 ≠ p.2) && (A.floatSort p.1).isSome && (A.floatSort p.2).isSome

variable {G} in
theorem wellFormed_of_checkWF [DecidableEq C] {isSort : C → Bool}
    (hs : ∀ c, isSort c = true → c ∈ G.sorts) {A : TAssertion L C V} (h : G.checkWF isSort A = true) : A.WellFormed G := by
  simp only [checkWF, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hnd, hfl⟩, hess⟩, hc⟩, hdv⟩ := h
  have hf : ∀ v s, A.floatSort v = some s → A.ctx v s := fun _ _ => TAssertion.ctx_of_floatSort
  refine ⟨hnd, fun v s hv => hs s (hfl (s, v) (TAssertion.mem_floats.2 hv)),
    fun e he => G.wellTyped_of_checkTyped hf (hess e he), G.wellTyped_of_checkTyped hf hc,
    fun x y hxy => (hdv (x, y) hxy).1.1, fun x y hxy => ?_⟩
  obtain ⟨⟨-, hx⟩, hy⟩ := hdv (x, y) hxy
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 hx
  obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.1 hy
  exact ⟨⟨s, TAssertion.ctx_of_floatSort hs⟩, ⟨s', TAssertion.ctx_of_floatSort hs'⟩⟩

/-- A tree that checks under the floating hypotheses of `A` is well sorted in
its context. -/
theorem hasSort_of_check [DecidableEq C] {A : TAssertion L C V} {t : Tree L V} {s : C}
    (h : G.check A.floatSort t s = true) : G.HasSort A.ctx t s :=
  ((check_iff _ _).1 h).mono fun _ _ => TAssertion.ctx_of_floatSort

end Check

theorem SyntaxRule.mem_args_of_argSort {C V : Type u} [DecidableEq V] {r : SyntaxRule C V}
    {v : V} {s : C} (h : r.argSort v = some s) : (s, v) ∈ r.args := by
  obtain ⟨p, hp, rfl⟩ := lookupArg_eq_some h
  obtain rfl := mem_zip_map_self hp
  exact (List.of_mem_zip hp).2

end Grammar

namespace GAxSet.Toy

open Grammar.Examples

/-- Typecodes and constants. -/
inductive C
  | wff | pf | neg | imp | orr | lp | rp
  deriving DecidableEq, Repr

/-- Rule labels of the base language. -/
inductive L
  | wn | wi
  deriving DecidableEq, Repr

open C in
/-- Negation and implication. -/
def rules : L → SyntaxRule C ℕ
  | .wn => rule wff [(wff, 0)] [.const neg, .var 0]
  | .wi => rule wff [(wff, 0), (wff, 1)] [.const lp, .var 0, .const imp, .var 1, .const rp]

/-- The syntax typecodes. -/
def IsSort : C → Bool
  | .wff => true
  | _ => false

/-- The grammar; `pf` (`⊢`) is read as `wff`. -/
def grammar : Grammar L C ℕ where
  sorts := {c | IsSort c}
  prov := fun
    | .pf => some .wff
    | _ => none
  rule := rules
  rule_tc l := by cases l <;> rfl
  rule_args l := by cases l <;> decide
  prov_sort {c s} h := by cases c <;> cases h; rfl
  prov_not_sort {c s} h := by cases c <;> cases h; decide

/-- The variable `φ`. -/
abbrev φ {L' : Type} : Tree L' ℕ := .var 0

/-- The variable `ψ`. -/
abbrev ψ {L' : Type} : Tree L' ℕ := .var 1

/-- `¬ a`. -/
abbrev neg (a : Tree L ℕ) : Tree L ℕ := .node .wn [a]

/-- `( a → b )`. -/
abbrev imp (a b : Tree L ℕ) : Tree L ℕ := .node .wi [a, b]

/-- The floating hypotheses `wff φ`, `wff ψ`. -/
abbrev floats {L' : Type} : List (THyp L' C ℕ) := [.float .wff 0, .float .wff 1]

/-- Modus ponens. -/
def axMp : TAssertion L C ℕ := ⟨[], floats ++ [.ess ⟨.pf, φ⟩, .ess ⟨.pf, imp φ ψ⟩], ⟨.pf, ψ⟩⟩

/-- `⊢ ( φ → φ )`. -/
def axId : TAssertion L C ℕ := ⟨[], [.float .wff 0], ⟨.pf, imp φ φ⟩⟩

/-- `⊢ ( φ → ( ψ → φ ) )`. -/
def ax1 : TAssertion L C ℕ := ⟨[], floats, ⟨.pf, imp φ (imp ψ φ)⟩⟩

/-- The base axioms. -/
def axioms : Set (TAssertion L C ℕ) := {axMp, axId, ax1}

theorem isSort_mem (c : C) (h : IsSort c = true) : c ∈ grammar.sorts := h

theorem wellFormed_axioms : ∀ A ∈ axioms, A.WellFormed grammar := by
  rintro A (rfl | rfl | rfl) <;> exact wellFormed_of_checkWF isSort_mem (by decide)

/-- The base system. -/
abbrev base : GAxSet.{0} := GAxSet.of grammar axioms wellFormed_axioms

/-- The new syntax rule `wo : wff ::= ( φ ∨ ψ )`. -/
def orRule : SyntaxRule C ℕ :=
  rule .wff [(.wff, 0), (.wff, 1)] [.const .lp, .var 0, .const .orr, .var 1, .const .rp]

theorem orRule_tc : orRule.tc ∈ base.G.sorts := rfl

theorem orRule_args : ∀ p ∈ orRule.args, p.1 ∈ base.G.sorts := by
  intro p hp
  simp only [orRule, Grammar.Examples.rule, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> rfl

/-- The extended grammar, with `wo` labelled `none`. -/
abbrev grammar₁ : Grammar (Option L) C ℕ := base.G.addRule orRule orRule_tc orRule_args

/-- `( a ∨ b )` in the extended language. -/
abbrev or₁ (a b : Tree (Option L) ℕ) : Tree (Option L) ℕ := .node none [a, b]

/-- `¬ a` in the extended language. -/
abbrev neg₁ (a : Tree (Option L) ℕ) : Tree (Option L) ℕ := .node (some .wn) [a]

/-- `( a → b )` in the extended language. -/
abbrev imp₁ (a b : Tree (Option L) ℕ) : Tree (Option L) ℕ := .node (some .wi) [a, b]

/-- `⊢ ( ( φ ∨ ψ ) → ( ¬ φ → ψ ) )`. -/
def dfOr1 : TAssertion (Option L) C ℕ :=
  ⟨[], floats, ⟨.pf, imp₁ (or₁ φ ψ) (imp₁ (neg₁ φ) ψ)⟩⟩

/-- `⊢ ( ( ¬ φ → ψ ) → ( φ ∨ ψ ) )`. -/
def dfOr2 : TAssertion (Option L) C ℕ :=
  ⟨[], floats, ⟨.pf, imp₁ (imp₁ (neg₁ φ) ψ) (or₁ φ ψ)⟩⟩

/-- The defining axioms of `∨`. -/
def defs : Set (TAssertion (Option L) C ℕ) := {dfOr1, dfOr2}

theorem wellFormed_defs : ∀ B ∈ defs, B.WellFormed grammar₁ := by
  rintro B (rfl | rfl) <;> exact wellFormed_of_checkWF (G := grammar₁) isSort_mem (by decide)

/-- The extension of the base system by `∨`. -/
abbrev extended : GAxSet.{0} := base.extend orRule orRule_tc orRule_args defs wellFormed_defs

/-- The definiens `( ¬ φ → ψ )`. -/
def definiens : Tree L ℕ := imp (neg φ) ψ

theorem hasSort_definiens :
    grammar.HasSort (fun w s => (s, w) ∈ orRule.args) definiens orRule.tc :=
  ((check_iff (G := grammar) _ _).1 (by decide : grammar.check orRule.argSort definiens .wff)).mono
    fun _ _ => SyntaxRule.mem_args_of_argSort

/-- Eliminating `∨` by its definiens. -/
abbrev elim : Rewrite grammar₁ grammar :=
  elimRule base.G orRule orRule_tc orRule_args definiens hasSort_definiens

/-- `⊢ ( ( ¬ φ → ψ ) → ( ¬ φ → ψ ) )`, the elimination of both defining axioms. -/
def goal : TAssertion L C ℕ := ⟨[], floats, ⟨.pf, imp definiens definiens⟩⟩

theorem elim_dfOr1 : elim.assertion dfOr1 = goal := rfl

theorem elim_dfOr2 : elim.assertion dfOr2 = goal := rfl

/-- The goal is an instance of `⊢ ( φ → φ )`. -/
theorem tderivable_goal : TDerivable grammar axioms goal := by
  refine ⟨⟨TDummies.none _, ?_⟩⟩
  rw [TAssertion.extend_none]
  refine (TDerivation.app axId (by simp [axioms]) (fun v => if v = 0 then definiens else .var v)
    (fun v s hv => ?_) (fun e he => absurd he (by simp [axId, TAssertion.essentials]))
    (fun x y h => by simp [axId] at h)).cast rfl
  have hv' : s = .wff ∧ v = 0 := by simpa [axId, TAssertion.ctx] using hv
  obtain ⟨rfl, rfl⟩ := hv'
  exact hasSort_of_check grammar (by decide)

/-- Adding `∨` with its defining axioms is conservative over the base language. -/
theorem conservative :
    (base.extendIncl orRule orRule_tc orRule_args defs wellFormed_defs).Conservative :=
  base.extendIncl_conservative orRule orRule_tc orRule_args defs wellFormed_defs definiens
    hasSort_definiens (by
      rintro B (rfl | rfl)
      · rw [elim_dfOr1]; exact tderivable_goal
      · rw [elim_dfOr2]; exact tderivable_goal)

/-- Every well-formed assertion without `∨` that the extension proves is
provable in the base system. -/
theorem definitional_extension {A : TAssertion L C ℕ} (hA : A.WellFormed grammar)
    (h : TDerivable grammar₁ extended.axioms
      ((inclRule base.G orRule orRule_tc orRule_args).assertion A)) :
    TDerivable grammar axioms A :=
  (Hom.conservative_iff _).1 conservative A hA h

end GAxSet.Toy

end Silmaril.Logic.Metamath
