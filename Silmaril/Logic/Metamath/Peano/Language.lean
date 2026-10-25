module

public import Silmaril.Logic.Metamath.Grammar.Examples
public import Silmaril.Logic.Metamath.Model.Check
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
# The language of Peano arithmetic in `peano.mm`

Solovay's `peano.mm` writes first-order arithmetic in Polish notation. Its
syntax typecodes are `wff`, `term` and `var`, together with four typecodes of
operator symbols: `BINOP` (`+`, `*`), `LOGBINOP` (`or`, `and`, `implies`,
`iff`), `BINPRED` (`=`, `<`) and `QUANT` (`forall`, `exists`). Each has a
metavariable, so for instance `binpred s t` is an atomic formula for an
arbitrary binary predicate. The constants and syntax rules are those of
`Grammar.Examples.PeanoMM`; here the variables are all metavariables of
`peano.mm` (`s t u s0 s1 t0 t1`, `v x y z`, `binop logbinop binpred quant`,
`phi psi chi`) together with infinitely many further object variables
`obj n`, as `peano.mm` assumes an infinite supply of variables of type `var`.
The grammar is unambiguous by an LL certificate.

Trees are written with the smart constructors of `Peano.T`, in the order in
which the symbols are read: `T.imp a b` is `implies a b`, whose tree lists the
arguments in the order of the floating hypotheses of `wff_logbinop`.

An arithmetic formula is a formula tree whose variables are object variables
(`IsArith`); its operator symbols are then constants. Such a tree has a truth
value in ℕ under an assignment of numbers to object variables (`evalWff`,
with terms evaluated by `evalTerm`).
-/

namespace Silmaril.Logic.Metamath.Peano

open Silmaril.Logic.Metamath Grammar Function

/-- Typecodes and constants of `peano.mm`. -/
abbrev C := Grammar.Examples.PeanoMM.C

/-- Syntax rule labels of `peano.mm`. -/
abbrev L := Grammar.Examples.PeanoMM.L

/-- The metavariables of `peano.mm`, and further object variables `obj n`. -/
inductive V
  | s | t | u | s0 | s1 | t0 | t1
  | v | x | y | z
  | binop | logbinop | binpred | quant
  | phi | psi | chi
  | obj (n : ℕ)
  deriving DecidableEq, Repr

instance : Infinite V := Infinite.of_injective V.obj fun _ _ h => V.obj.inj h

open Grammar.Examples in
/-- The syntax rules of `peano.mm`, with floating hypotheses in database order. -/
def rules : L → SyntaxRule C V
  | .binopPlus => rule .binop [] [.const .plus] .nil .nil
  | .binopTimes => rule .binop [] [.const .times] .nil .nil
  | .tvar => rule .term [(.var, .v)] [.var .v]
  | .tzero => rule .term [] [.const .zero] .nil .nil
  | .tsucc => rule .term [(.term, .s)] [.const .succ, .var .s]
  | .tbinop => rule .term [(.term, .s), (.term, .t), (.binop, .binop)]
      [.var .binop, .var .s, .var .t]
  | .logbinopOr => rule .logbinop [] [.const .or] .nil .nil
  | .logbinopAnd => rule .logbinop [] [.const .and] .nil .nil
  | .logbinopImplies => rule .logbinop [] [.const .implies] .nil .nil
  | .logbinopIff => rule .logbinop [] [.const .iff] .nil .nil
  | .binpredEquals => rule .binpred [] [.const .eq] .nil .nil
  | .binpredLessThan => rule .binpred [] [.const .lt] .nil .nil
  | .quantAll => rule .quant [] [.const .all] .nil .nil
  | .quantEx => rule .quant [] [.const .ex] .nil .nil
  | .wffAtom => rule .wff [(.term, .s), (.term, .t), (.binpred, .binpred)]
      [.var .binpred, .var .s, .var .t]
  | .wffNot => rule .wff [(.wff, .psi)] [.const .not, .var .psi]
  | .wffLogbinop => rule .wff [(.logbinop, .logbinop), (.wff, .phi), (.wff, .psi)]
      [.var .logbinop, .var .psi, .var .phi]
  | .wffQuant => rule .wff [(.var, .v), (.quant, .quant), (.wff, .phi)]
      [.var .quant, .var .v, .var .phi]

/-- The grammar of `peano.mm`; `|-` is read as `wff`. -/
def grammar : Grammar L C V where
  sorts := {c | Grammar.Examples.PeanoMM.IsSort c}
  prov := fun
    | .turnstile => some .wff
    | _ => none
  rule := rules
  rule_tc l := by cases l <;> rfl
  rule_args l := by cases l <;> decide
  prov_sort {c s} h := by cases c <;> cases h; rfl
  prov_not_sort {c s} h := by cases c <;> cases h; decide

instance : DecidablePred (· ∈ grammar.sorts) :=
  fun c => inferInstanceAs (Decidable (Grammar.Examples.PeanoMM.IsSort c))

theorem llCert : LLCert grammar Grammar.Examples.PeanoMM.first := by decide

theorem unambiguous : grammar.Unambiguous := llCert.unambiguous

/-! ## Tree notation -/

namespace T

/-- The term `v` for an object variable. -/
abbrev tv (a : V) : Tree L V := .node .tvar [.var a]
/-- `0`. -/
abbrev zero : Tree L V := .node .tzero []
/-- `S t`. -/
abbrev succ (t : Tree L V) : Tree L V := .node .tsucc [t]
/-- `b s t` for a binary operation `b`. -/
abbrev bin (b s t : Tree L V) : Tree L V := .node .tbinop [s, t, b]
/-- `+ s t`. -/
abbrev plus (s t : Tree L V) : Tree L V := bin (.node .binopPlus []) s t
/-- `* s t`. -/
abbrev times (s t : Tree L V) : Tree L V := bin (.node .binopTimes []) s t
/-- `p s t` for a binary predicate `p`. -/
abbrev atom (p s t : Tree L V) : Tree L V := .node .wffAtom [s, t, p]
/-- `= s t`. -/
abbrev eq (s t : Tree L V) : Tree L V := atom (.node .binpredEquals []) s t
/-- `< s t`. -/
abbrev lt (s t : Tree L V) : Tree L V := atom (.node .binpredLessThan []) s t
/-- `not a`. -/
abbrev not (a : Tree L V) : Tree L V := .node .wffNot [a]
/-- `l a b` for a binary connective `l`. -/
abbrev lop (l a b : Tree L V) : Tree L V := .node .wffLogbinop [l, b, a]
/-- `implies a b`. -/
abbrev imp (a b : Tree L V) : Tree L V := lop (.node .logbinopImplies []) a b
/-- `or a b`. -/
abbrev or (a b : Tree L V) : Tree L V := lop (.node .logbinopOr []) a b
/-- `and a b`. -/
abbrev and (a b : Tree L V) : Tree L V := lop (.node .logbinopAnd []) a b
/-- `iff a b`. -/
abbrev iff (a b : Tree L V) : Tree L V := lop (.node .logbinopIff []) a b
/-- `q b a` for a quantifier `q`. -/
abbrev qnt (q : Tree L V) (b : V) (a : Tree L V) : Tree L V := .node .wffQuant [.var b, q, a]
/-- `forall b a`. -/
abbrev all (b : V) (a : Tree L V) : Tree L V := qnt (.node .quantAll []) b a
/-- `exists b a`. -/
abbrev ex (b : V) (a : Tree L V) : Tree L V := qnt (.node .quantEx []) b a
/-- A metavariable. -/
abbrev mv (a : V) : Tree L V := .var a
/-- `|- a`. -/
abbrev pf (a : Tree L V) : TExpr L C V := ⟨.turnstile, a⟩

end T

/-! ## Arithmetic formulas and their truth in ℕ -/

/-- The context in which every variable is an object variable. -/
def objCtx (_ : V) (c : C) : Prop := c = .var

/-- An arithmetic term: a term tree whose variables are object variables. -/
def IsArithTerm (t : Tree L V) : Prop := grammar.HasSort objCtx t .term

/-- An arithmetic formula: a formula tree whose variables are object variables. -/
def IsArith (t : Tree L V) : Prop := grammar.HasSort objCtx t .wff

instance (t : Tree L V) (c : C) : Decidable (grammar.HasSort objCtx t c) :=
  decidable_of_iff (grammar.HasSort (fun w s => (fun _ => some (.var : C)) w = some s) t c)
    (by simp only [Option.some.injEq, eq_comm]; rfl)

/-- The value of an arithmetic term in ℕ, under an assignment of numbers to
object variables. -/
def evalTerm (e : V → ℕ) : Tree L V → ℕ
  | .node .tvar [.var a] => e a
  | .node .tsucc [a] => evalTerm e a + 1
  | .node .tbinop [a, b, .node .binopPlus []] => evalTerm e a + evalTerm e b
  | .node .tbinop [a, b, .node .binopTimes []] => evalTerm e a * evalTerm e b
  | _ => 0

/-- The truth value of an arithmetic formula in ℕ, under an assignment of
numbers to object variables. -/
def evalWff (e : V → ℕ) : Tree L V → Prop
  | .node .wffAtom [a, b, .node .binpredEquals []] => evalTerm e a = evalTerm e b
  | .node .wffAtom [a, b, .node .binpredLessThan []] => evalTerm e a < evalTerm e b
  | .node .wffNot [a] => ¬ evalWff e a
  | .node .wffLogbinop [.node .logbinopImplies [], b, a] => evalWff e a → evalWff e b
  | .node .wffLogbinop [.node .logbinopOr [], b, a] => evalWff e a ∨ evalWff e b
  | .node .wffLogbinop [.node .logbinopAnd [], b, a] => evalWff e a ∧ evalWff e b
  | .node .wffLogbinop [.node .logbinopIff [], b, a] => evalWff e a ↔ evalWff e b
  | .node .wffQuant [.var w, .node .quantAll [], a] => ∀ n, evalWff (update e w n) a
  | .node .wffQuant [.var w, .node .quantEx [], a] => ∃ n, evalWff (update e w n) a
  | _ => False

section Eval

variable (e : V → ℕ)

@[simp] theorem evalTerm_tv (a : V) : evalTerm e (T.tv a) = e a := rfl
@[simp] theorem evalTerm_zero : evalTerm e T.zero = 0 := rfl
@[simp] theorem evalTerm_succ (a : Tree L V) : evalTerm e (T.succ a) = evalTerm e a + 1 := rfl
@[simp] theorem evalTerm_plus (a b : Tree L V) :
    evalTerm e (T.plus a b) = evalTerm e a + evalTerm e b := rfl
@[simp] theorem evalTerm_times (a b : Tree L V) :
    evalTerm e (T.times a b) = evalTerm e a * evalTerm e b := rfl

@[simp] theorem evalWff_eq (a b : Tree L V) :
    evalWff e (T.eq a b) ↔ evalTerm e a = evalTerm e b := Iff.rfl
@[simp] theorem evalWff_lt (a b : Tree L V) :
    evalWff e (T.lt a b) ↔ evalTerm e a < evalTerm e b := Iff.rfl
@[simp] theorem evalWff_not (a : Tree L V) : evalWff e (T.not a) ↔ ¬ evalWff e a := Iff.rfl
@[simp] theorem evalWff_imp (a b : Tree L V) :
    evalWff e (T.imp a b) ↔ (evalWff e a → evalWff e b) := Iff.rfl
@[simp] theorem evalWff_or (a b : Tree L V) :
    evalWff e (T.or a b) ↔ evalWff e a ∨ evalWff e b := Iff.rfl
@[simp] theorem evalWff_and (a b : Tree L V) :
    evalWff e (T.and a b) ↔ evalWff e a ∧ evalWff e b := Iff.rfl
@[simp] theorem evalWff_iff (a b : Tree L V) :
    evalWff e (T.iff a b) ↔ (evalWff e a ↔ evalWff e b) := Iff.rfl
@[simp] theorem evalWff_all (w : V) (a : Tree L V) :
    evalWff e (T.all w a) ↔ ∀ n, evalWff (update e w n) a := Iff.rfl
@[simp] theorem evalWff_ex (w : V) (a : Tree L V) :
    evalWff e (T.ex w a) ↔ ∃ n, evalWff (update e w n) a := Iff.rfl

end Eval

/-- The value of a term only depends on its variables. -/
theorem evalTerm_congr {e e' : V → ℕ} (t : Tree L V) (h : ∀ a ∈ t.vars, e a = e' a) :
    evalTerm e t = evalTerm e' t := by
  fun_induction evalTerm e t <;> simp_all [evalTerm]

theorem update_congr {e e' : V → ℕ} {w : V} {a : Tree L V}
    (h : ∀ b, b = w ∨ b ∈ a.vars → e b = e' b) (n : ℕ) :
    ∀ b ∈ a.vars, update e w n b = update e' w n b := by
  intro b hb
  by_cases hbw : b = w
  · subst hbw; simp
  · simp [update_of_ne hbw, h b (.inr hb)]

/-- The truth value of a formula only depends on its variables. -/
theorem evalWff_congr {e e' : V → ℕ} (t : Tree L V) (h : ∀ a ∈ t.vars, e a = e' a) :
    evalWff e t ↔ evalWff e' t := by
  fun_induction evalWff e t generalizing e' <;> simp only [evalWff] <;>
    simp only [Tree.vars_node, List.flatMap_cons, List.flatMap_nil, List.mem_append,
      Tree.vars_var, List.mem_singleton, List.append_nil, List.not_mem_nil, false_or] at h
  all_goals first
    | rfl
    | (rename_i a b
       rw [evalTerm_congr a fun w hw => h w (.inl hw), evalTerm_congr b fun w hw => h w (.inr hw)])
    | (rename_i ih; exact not_congr (ih h))
    | (rename_i ih₁ ih₂
       exact imp_congr (ih₁ fun w hw => h w (.inr hw)) (ih₂ fun w hw => h w (.inl hw)))
    | (rename_i ih₁ ih₂
       exact or_congr (ih₁ fun w hw => h w (.inr hw)) (ih₂ fun w hw => h w (.inl hw)))
    | (rename_i ih₁ ih₂
       exact and_congr (ih₁ fun w hw => h w (.inr hw)) (ih₂ fun w hw => h w (.inl hw)))
    | (rename_i ih₁ ih₂
       exact iff_congr (ih₁ fun w hw => h w (.inr hw)) (ih₂ fun w hw => h w (.inl hw)))
    | (rename_i ih; exact forall_congr' fun n => ih n (update_congr h n))
    | (rename_i ih; exact exists_congr fun n => ih n (update_congr h n))

end Silmaril.Logic.Metamath.Peano
