module

public import Silmaril.Logic.Metamath.Grammar.Unambiguous
public import Mathlib.Data.Fintype.Basic

@[expose] public section

/-!
# Example grammars

Concrete grammars written as Lean data, each with an LL certificate
(`Grammar.LLCert`) checked by `decide`, hence unambiguous.

* `SetMM`: the primitive grammar of set.mm (`wn`, `wi`, `wal`, `cv`, `wceq`,
  `wcel`) with `wb`, `wa`, `wo`, `wex` and class abstraction `cab`. These are
  also the primitive syntax axioms of iset.mm, where `wb`, `wa`, `wo` and `wex`
  are primitive connectives.
* `HolMM`: the grammar of hol.mm.
* `PeanoMM`: the grammar of peano.mm's language of arithmetic, in Polish
  notation.
-/

namespace Silmaril.Logic.Metamath.Grammar.Examples

open Silmaril.Logic.Metamath Grammar

/-- A syntax rule whose side conditions are checked by `decide`. -/
abbrev rule {C V : Type} [DecidableEq V] (tc : C) (args : List (C × V)) (body : Str C V)
    (hnd : (args.map Prod.snd).Nodup := by decide)
    (hp : (Str.vars body).Perm (args.map Prod.snd) := by decide) : SyntaxRule C V :=
  ⟨tc, args, body, hnd, hp⟩

namespace SetMM

/-- Typecodes and constants. -/
inductive C
  | wff | setvar | «class» | turnstile
  | not | lp | rp | imp | bi | and | or | all | ex | eq | el | lb | bar | rb
  deriving DecidableEq, Repr

/-- Variables. -/
inductive V
  | ph | ps | x | A | B
  deriving DecidableEq, Repr

/-- Rule labels. -/
inductive L
  | wn | wi | wb | wa | wo | wal | wex | cv | wceq | wcel | cab
  deriving DecidableEq, Repr

instance : Fintype C :=
  .ofList [.wff, .setvar, .«class», .turnstile, .not, .lp, .rp, .imp, .bi, .and, .or, .all, .ex,
    .eq, .el, .lb, .bar, .rb] (by intro c; cases c <;> simp)

instance : Fintype L :=
  .ofList [.wn, .wi, .wb, .wa, .wo, .wal, .wex, .cv, .wceq, .wcel, .cab]
    (by intro l; cases l <;> simp)

open C V in
/-- The syntax rules, with floating hypotheses in database order. -/
def rules : L → SyntaxRule C V
  | .wn => rule wff [(wff, ph)] [.const not, .var ph]
  | .wi => rule wff [(wff, ph), (wff, ps)]
      [.const lp, .var ph, .const imp, .var ps, .const rp]
  | .wb => rule wff [(wff, ph), (wff, ps)]
      [.const lp, .var ph, .const bi, .var ps, .const rp]
  | .wa => rule wff [(wff, ph), (wff, ps)]
      [.const lp, .var ph, .const and, .var ps, .const rp]
  | .wo => rule wff [(wff, ph), (wff, ps)]
      [.const lp, .var ph, .const or, .var ps, .const rp]
  | .wal => rule wff [(wff, ph), (setvar, x)] [.const all, .var x, .var ph]
  | .wex => rule wff [(wff, ph), (setvar, x)] [.const ex, .var x, .var ph]
  | .cv => rule «class» [(setvar, x)] [.var x]
  | .wceq => rule wff [(«class», A), («class», B)] [.var A, .const eq, .var B]
  | .wcel => rule wff [(«class», A), («class», B)] [.var A, .const el, .var B]
  | .cab => rule «class» [(wff, ph), (setvar, x)]
      [.const lb, .var x, .const bar, .var ph, .const rb]

/-- The syntax typecodes. -/
def IsSort : C → Bool
  | .wff | .setvar | .«class» => true
  | _ => false

/-- The grammar; `|-` is read as `wff`. -/
def grammar : Grammar L C V where
  sorts := {c | IsSort c}
  prov := fun
    | .turnstile => some .wff
    | _ => none
  rule := rules
  rule_tc l := by cases l <;> rfl
  rule_args l := by cases l <;> decide
  prov_sort {c s} h := by cases c <;> cases h; rfl
  prov_not_sort {c s} h := by cases c <;> cases h; decide

open C in
/-- The first-symbol classes of each sort. -/
def first : C → List (C ⊕ C)
  | .wff => [.inr .wff, .inl not, .inl lp, .inl all, .inl ex,
      .inr .«class», .inr setvar, .inl lb]
  | .«class» => [.inr .«class», .inr setvar, .inl lb]
  | c => [.inr c]

theorem llCert : LLCert grammar first := by decide

theorem unambiguous : grammar.Unambiguous := llCert.unambiguous

/-- The sorts of the variables. -/
def varSort : V → Option C
  | .ph | .ps => some .wff
  | .x => some .setvar
  | .A | .B => some .«class»

open C V in
/-- `( ph -> -. ps )` is the flattening of `wi ph (wn ps)`. -/
example : grammar.flatten (.node .wi [.var ph, .node .wn [.var ps]]) =
    [.const lp, .var ph, .const imp, .const not, .var ps, .const rp] := by decide

open C V in
/-- `A. x x e. { x | ph }` is a formula. -/
example : grammar.HasSort (fun v s => varSort v = some s)
    (.node .wal [.node .wcel [.node .cv [.var x], .node .cab [.var ph, .var x]], .var x])
    wff := by decide

open C V in
/-- The set variable `x` is not a formula. -/
example : ¬ grammar.HasSort (fun v s => varSort v = some s) (.var x) wff := by decide

end SetMM

namespace HolMM

/-- Typecodes and constants. -/
inductive C
  | wff | var | type | term | turnstile
  | colon | dot | models | bool | ind | arrow | lp | rp | comma | lam | eq | tru | lbr | rbr
  | fal | and | neg | imp | all | ex | or | eu | typedef | oneOne | onto | indef
  deriving DecidableEq, Repr

/-- Variables. -/
inductive V
  | al | be | x | A | B | C | F | T
  deriving DecidableEq, Repr

/-- Rule labels. -/
inductive L
  | tv | ht | hb | hi | kc | kl | ke | kt | kbr | kct | wffMMJ2 | wffMMJ2t
  | tfal | tan | tne | tim | tal | tex | tor | teu | wffMMJ2d | tf11 | tfo | tat
  deriving DecidableEq, Repr

instance : Fintype C :=
  .ofList [.wff, .var, .type, .term, .turnstile, .colon, .dot, .models, .bool, .ind, .arrow, .lp,
    .rp, .comma, .lam, .eq, .tru, .lbr, .rbr, .fal, .and, .neg, .imp, .all, .ex, .or, .eu,
    .typedef, .oneOne, .onto, .indef] (by intro c; cases c <;> simp)

instance : Fintype L :=
  .ofList [.tv, .ht, .hb, .hi, .kc, .kl, .ke, .kt, .kbr, .kct, .wffMMJ2, .wffMMJ2t, .tfal, .tan,
    .tne, .tim, .tal, .tex, .tor, .teu, .wffMMJ2d, .tf11, .tfo, .tat]
    (by intro l; cases l <;> simp)

/-- A term constant. -/
abbrev const (c : C) : SyntaxRule C V := rule .term [] [.const c] .nil .nil

open C V in
/-- The syntax rules, with floating hypotheses in database order. -/
def rules : L → SyntaxRule C V
  | .tv => rule term [(type, al), (var, x)] [.var x, .const colon, .var al]
  | .ht => rule type [(type, al), (type, be)]
      [.const lp, .var al, .const arrow, .var be, .const rp]
  | .hb => rule type [] [.const bool]
  | .hi => rule type [] [.const ind]
  | .kc => rule term [(term, F), (term, T)] [.const lp, .var F, .var T, .const rp]
  | .kl => rule term [(type, al), (var, x), (term, T)]
      [.const lam, .var x, .const colon, .var al, .const dot, .var T]
  | .ke => const eq
  | .kt => const tru
  | .kbr => rule term [(term, A), (term, B), (term, F)]
      [.const lbr, .var A, .var F, .var B, .const rbr]
  | .kct => rule term [(term, A), (term, B)]
      [.const lp, .var A, .const comma, .var B, .const rp]
  | .wffMMJ2 => rule wff [(term, A), (term, B)] [.var A, .const models, .var B]
  | .wffMMJ2t => rule wff [(type, al), (term, A)] [.var A, .const colon, .var al]
  | .tfal => const fal
  | .tan => const and
  | .tne => const neg
  | .tim => const imp
  | .tal => const all
  | .tex => const ex
  | .tor => const or
  | .teu => const eu
  | .wffMMJ2d => rule wff [(type, al), (term, A), (term, B), (term, V.C)]
      [.const typedef, .var al, .const lp, .var A, .const comma, .var B, .const rp, .var V.C]
  | .tf11 => const oneOne
  | .tfo => const onto
  | .tat => const indef

/-- The syntax typecodes. -/
def IsSort : C → Bool
  | .wff | .var | .type | .term => true
  | _ => false

/-- The grammar; `|-` is read as `wff`. -/
def grammar : Grammar L C V where
  sorts := {c | IsSort c}
  prov := fun
    | .turnstile => some .wff
    | _ => none
  rule := rules
  rule_tc l := by cases l <;> rfl
  rule_args l := by cases l <;> decide
  prov_sort {c s} h := by cases c <;> cases h; rfl
  prov_not_sort {c s} h := by cases c <;> cases h; decide

open C in
/-- The first-symbol classes of each sort. -/
def first : C → List (C ⊕ C)
  | .type => [.inr type, .inl lp, .inl bool, .inl ind]
  | .term => [.inr term, .inr var, .inl lp, .inl lam, .inl eq, .inl tru, .inl lbr, .inl fal,
      .inl and, .inl neg, .inl imp, .inl all, .inl ex, .inl or, .inl eu, .inl oneOne,
      .inl onto, .inl indef]
  | .wff => [.inr wff, .inl typedef, .inr term, .inr var, .inl lp, .inl lam, .inl eq, .inl tru,
      .inl lbr, .inl fal, .inl and, .inl neg, .inl imp, .inl all, .inl ex, .inl or, .inl eu,
      .inl oneOne, .inl onto, .inl indef]
  | c => [.inr c]

theorem llCert : LLCert grammar first := by decide

theorem unambiguous : grammar.Unambiguous := llCert.unambiguous

end HolMM

namespace PeanoMM

/-- Typecodes and constants. -/
inductive C
  | turnstile | wff | term | var | binop | logbinop | binpred | quant
  | zero | succ | plus | times | not | or | and | implies | iff | eq | lt | all | ex
  deriving DecidableEq, Repr

/-- Variables. -/
inductive V
  | s | t | v | binop | logbinop | binpred | quant | phi | psi
  deriving DecidableEq, Repr

/-- Rule labels. -/
inductive L
  | binopPlus | binopTimes | tvar | tzero | tsucc | tbinop
  | logbinopOr | logbinopAnd | logbinopImplies | logbinopIff
  | binpredEquals | binpredLessThan | quantAll | quantEx
  | wffAtom | wffNot | wffLogbinop | wffQuant
  deriving DecidableEq, Repr

instance : Fintype C :=
  .ofList [.turnstile, .wff, .term, .var, .binop, .logbinop, .binpred, .quant, .zero, .succ,
    .plus, .times, .not, .or, .and, .implies, .iff, .eq, .lt, .all, .ex]
    (by intro c; cases c <;> simp)

instance : Fintype L :=
  .ofList [.binopPlus, .binopTimes, .tvar, .tzero, .tsucc, .tbinop, .logbinopOr, .logbinopAnd,
    .logbinopImplies, .logbinopIff, .binpredEquals, .binpredLessThan, .quantAll, .quantEx,
    .wffAtom, .wffNot, .wffLogbinop, .wffQuant] (by intro l; cases l <;> simp)

/-- A rule whose body is a single constant. -/
abbrev const (tc c : C) : SyntaxRule C V := rule tc [] [.const c] .nil .nil

/-- The syntax rules, with floating hypotheses in database order. -/
def rules : L → SyntaxRule C V
  | .binopPlus => const .binop .plus
  | .binopTimes => const .binop .times
  | .tvar => rule .term [(.var, .v)] [.var .v]
  | .tzero => const .term .zero
  | .tsucc => rule .term [(.term, .s)] [.const .succ, .var .s]
  | .tbinop => rule .term [(.term, .s), (.term, .t), (.binop, .binop)]
      [.var .binop, .var .s, .var .t]
  | .logbinopOr => const .logbinop .or
  | .logbinopAnd => const .logbinop .and
  | .logbinopImplies => const .logbinop .implies
  | .logbinopIff => const .logbinop .iff
  | .binpredEquals => const .binpred .eq
  | .binpredLessThan => const .binpred .lt
  | .quantAll => const .quant .all
  | .quantEx => const .quant .ex
  | .wffAtom => rule .wff [(.term, .s), (.term, .t), (.binpred, .binpred)]
      [.var .binpred, .var .s, .var .t]
  | .wffNot => rule .wff [(.wff, .psi)] [.const .not, .var .psi]
  | .wffLogbinop => rule .wff [(.logbinop, .logbinop), (.wff, .phi), (.wff, .psi)]
      [.var .logbinop, .var .psi, .var .phi]
  | .wffQuant => rule .wff [(.var, .v), (.quant, .quant), (.wff, .phi)]
      [.var .quant, .var .v, .var .phi]

/-- The syntax typecodes. -/
def IsSort : C → Bool
  | .wff | .term | .var | .binop | .logbinop | .binpred | .quant => true
  | _ => false

/-- The grammar; `|-` is read as `wff`. -/
def grammar : Grammar L C V where
  sorts := {c | IsSort c}
  prov := fun
    | .turnstile => some .wff
    | _ => none
  rule := rules
  rule_tc l := by cases l <;> rfl
  rule_args l := by cases l <;> decide
  prov_sort {c s} h := by cases c <;> cases h; rfl
  prov_not_sort {c s} h := by cases c <;> cases h; decide

/-- The first-symbol classes of each sort. -/
def first : C → List (C ⊕ C)
  | .term => [.inr .term, .inr .var, .inl .zero, .inl .succ, .inr .binop, .inl .plus,
      .inl .times]
  | .binop => [.inr .binop, .inl .plus, .inl .times]
  | .logbinop => [.inr .logbinop, .inl .or, .inl .and, .inl .implies, .inl .iff]
  | .binpred => [.inr .binpred, .inl .eq, .inl .lt]
  | .quant => [.inr .quant, .inl .all, .inl .ex]
  | .wff => [.inr .wff, .inl .not, .inr .logbinop, .inl .or, .inl .and, .inl .implies,
      .inl .iff, .inr .binpred, .inl .eq, .inl .lt, .inr .quant, .inl .all, .inl .ex]
  | c => [.inr c]

theorem llCert : LLCert grammar first := by decide

theorem unambiguous : grammar.Unambiguous := llCert.unambiguous

end PeanoMM

end Silmaril.Logic.Metamath.Grammar.Examples
