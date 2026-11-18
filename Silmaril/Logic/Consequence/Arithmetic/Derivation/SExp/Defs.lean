module

public import Silmaril.Logic.Consequence.Arithmetic.Derivation.Defs
public import Silmaril.Logic.Consequence.Derivation.SExp.Defs
public import Silmaril.Logic.Arithmetic.SExp.Defs

/-!
# PA and Q proofs as S-expressions

**Judgments** (`readSeq`, `encodeSeq`; presentation `silmaril.arithmetic.sequent`, v1):

```
J ::= (seq n (formula*) formula)
```

`n` is the canonical decimal number of variables in scope; the hypotheses and the conclusion are
formulas of `silmaril.arithmetic.formula` with `n` variables in scope.

**Raw rules** (`elabRule`): a rule name, or `(name arg*)`. The elaborator reads each node's
conclusion and premise conclusions to fill in the rule instance; it is untrusted, since the
result is checked.

| raw rule | arguments | rule instance |
|---|---|---|
| `hyp` | | `hyp` |
| `(ax NAME)` | `succ-nonzero`, `succ-injective`, `add-zero`, `add-succ`, `mul-zero`, `mul-succ`, `predecessor` (Q), `induction` (PA) | `ax` |
| `weaken`, `imp-intro`, `imp-elim`, `bot-elim`, `classical` | | as named |
| `and-intro`, `and-left`, `and-right`, `or-left`, `or-right`, `or-elim` | | as named |
| `all-intro`, `ex-elim`, `eq-refl` | | as named |
| `(all-elim t)`, `(ex-intro t)` | the term `t` | as named |
| `(eq-elim φ)` | the motive `φ`, with one more variable | as named |

**Checking** (`checkTree`, `checkLines`): decode, elaborate, check; the result is the checked
conclusion, or an error saying which stage failed.
-/

@[expose] public section

namespace Silmaril.Consequence.Arithmetic.ND

open Silmaril.Logic.Arithmetic Silmaril.Logic.Arithmetic.SExp
open Silmaril.Logic.Smt (SE)
open Silmaril.Logic.Concrete (SExpCodec)
open Silmaril.Logic.Concrete.SExp (num num?)

/-- The concrete form of a judgment. -/
def encodeSeq (s : Seq) : SE :=
  .list [.atom "seq", num s.n, .list (s.ctx.map encodeFormula), encodeFormula s.goal]

/-- Read formulas with `n` variables in scope. -/
def readFormulas (n : ℕ) : List SE → Option (Context n)
  | [] => some []
  | e :: es =>
    match decodeFormula n e, readFormulas n es with
    | some φ, some Γ => some (φ :: Γ)
    | _, _ => none

/-- Read a judgment. -/
def readSeq : SE → Option Seq
  | .list [.atom "seq", k, .list hs, g] =>
    match num? k with
    | some n =>
      match readFormulas n hs, decodeFormula n g with
      | some Γ, some φ => some ⟨n, Γ, φ⟩
      | _, _ => none
    | none => none
  | _ => none

/-- Reindex a judgment to `n` variables, when it has `n`. -/
def castSeq (n : ℕ) (s : Seq) : Option (Context n × Formula n) :=
  if h : s.n = n then some (h ▸ s.ctx, h ▸ s.goal) else none

/-- A raw rule's name and arguments. -/
def ruleName : SE → Option (String × List SE)
  | .atom s => some (s, [])
  | .list (.atom s :: args) => some (s, args)
  | _ => none

/-- Recognise an axiom instance by name and shape. -/
def axiomCode? {n : ℕ} (name : String) (φ : Formula n) : Option (AxiomCode n) :=
  match name, φ with
  | "succ-nonzero", .imp (.equal (.succ t) .zero) .bot => some (.succNonzero t)
  | "succ-injective", .imp (.equal (.succ s) (.succ t)) _ => some (.succInjective s t)
  | "add-zero", .equal (.add t .zero) _ => some (.addZero t)
  | "add-succ", .equal (.add s (.succ t)) _ => some (.addSucc s t)
  | "mul-zero", .equal (.mul t .zero) _ => some (.mulZero t)
  | "mul-succ", .equal (.mul s (.succ t)) _ => some (.mulSucc s t)
  | "predecessor", .imp (.imp (.equal t .zero) .bot) _ => some (.pred t)
  | "induction", .imp _ (.all ψ) => some (.induction ψ)
  | _, _ => none

/-! ## Reading rule arguments (untrusted, so kernel-reducible rather than canonical) -/

/-- Decimal digits. -/
def digits? : List Char → Option ℕ
  | [] => none
  | [c] => if c.isDigit then some (c.toNat - '0'.toNat) else none
  | c :: cs =>
    if c.isDigit then (digits? cs).map fun k => (c.toNat - '0'.toNat) * 10 ^ cs.length + k
    else none

/-- A term argument with `n` variables in scope. -/
def termArg? (n : ℕ) : SE → Option (Term n)
  | .list [.atom "var", .atom i] =>
    (digits? i.toList).bind fun k => if h : k < n then some (.var ⟨k, h⟩) else none
  | .atom "zero" => some .zero
  | .list [.atom "succ", t] => (termArg? n t).map .succ
  | .list [.atom "+", s, t] =>
    match termArg? n s, termArg? n t with
    | some s, some t => some (.add s t)
    | _, _ => none
  | .list [.atom "*", s, t] =>
    match termArg? n s, termArg? n t with
    | some s, some t => some (.mul s t)
    | _, _ => none
  | _ => none

/-- A formula argument with `n` variables in scope. -/
def formulaArg? : (n : ℕ) → SE → Option (Formula n)
  | _, .atom "false" => some .bot
  | n, .list [.atom "=", s, t] =>
    match termArg? n s, termArg? n t with
    | some s, some t => some (.equal s t)
    | _, _ => none
  | n, .list [.atom "->", φ, ψ] =>
    match formulaArg? n φ, formulaArg? n ψ with
    | some φ, some ψ => some (.imp φ ψ)
    | _, _ => none
  | n, .list [.atom "and", φ, ψ] =>
    match formulaArg? n φ, formulaArg? n ψ with
    | some φ, some ψ => some (.conj φ ψ)
    | _, _ => none
  | n, .list [.atom "or", φ, ψ] =>
    match formulaArg? n φ, formulaArg? n ψ with
    | some φ, some ψ => some (.disj φ ψ)
    | _, _ => none
  | n, .list [.atom "forall", φ] => (formulaArg? (n + 1) φ).map .all
  | n, .list [.atom "exists", φ] => (formulaArg? (n + 1) φ).map .ex
  | _, _ => none

/-- **The elaborator**: a raw rule, the premise conclusions and the conclusion give a rule
instance. Untrusted. -/
def elabRule (r : SE) (ps : List Seq) (c : Seq) : Option (Σ n, Rule n) :=
  let n := c.n
  let Γ := c.ctx
  let φ := c.goal
  match ruleName r, ps with
  | some ("hyp", []), [] => some ⟨n, .hyp Γ φ⟩
  | some ("ax", [.atom a]), [] => (axiomCode? a φ).map fun a => ⟨n, .ax Γ a⟩
  | some ("weaken", []), [p] => (castSeq n p).map fun q => ⟨n, .weaken q.1 Γ φ⟩
  | some ("imp-intro", []), [_] =>
    match φ with
    | .imp a b => some ⟨n, .impIntro Γ a b⟩
    | _ => none
  | some ("imp-elim", []), [_, p] => (castSeq n p).map fun q => ⟨n, .impElim Γ q.2 φ⟩
  | some ("bot-elim", []), [_] => some ⟨n, .botElim Γ φ⟩
  | some ("classical", []), [_] => some ⟨n, .classical Γ φ⟩
  | some ("and-intro", []), [_, _] =>
    match φ with
    | .conj a b => some ⟨n, .conjIntro Γ a b⟩
    | _ => none
  | some ("and-left", []), [p] =>
    match castSeq n p with
    | some (_, .conj a b) => some ⟨n, .conjLeft Γ a b⟩
    | _ => none
  | some ("and-right", []), [p] =>
    match castSeq n p with
    | some (_, .conj a b) => some ⟨n, .conjRight Γ a b⟩
    | _ => none
  | some ("or-left", []), [_] =>
    match φ with
    | .disj a b => some ⟨n, .disjLeft Γ a b⟩
    | _ => none
  | some ("or-right", []), [_] =>
    match φ with
    | .disj a b => some ⟨n, .disjRight Γ a b⟩
    | _ => none
  | some ("or-elim", []), [p, _, _] =>
    match castSeq n p with
    | some (_, .disj a b) => some ⟨n, .disjElim Γ a b φ⟩
    | _ => none
  | some ("all-intro", []), [_] =>
    match φ with
    | .all a => some ⟨n, .allIntro Γ a⟩
    | _ => none
  | some ("all-elim", [t]), [p] =>
    match castSeq n p, termArg? n t with
    | some (_, .all a), some t => some ⟨n, .allElim Γ a t⟩
    | _, _ => none
  | some ("ex-intro", [t]), [_] =>
    match φ, termArg? n t with
    | .ex a, some t => some ⟨n, .exIntro Γ a t⟩
    | _, _ => none
  | some ("ex-elim", []), [p, _] =>
    match castSeq n p with
    | some (_, .ex a) => some ⟨n, .exElim Γ a φ⟩
    | _ => none
  | some ("eq-refl", []), [] =>
    match φ with
    | .equal t _ => some ⟨n, .eqRefl Γ t⟩
    | _ => none
  | some ("eq-elim", [m]), [p, _] =>
    match castSeq n p, formulaArg? (n + 1) m with
    | some (_, .equal s t), some m => some ⟨n, .eqElim Γ m s t⟩
    | _, _ => none
  | _, _ => none

/-- Why a concrete proof was rejected. -/
inductive Rejection where
  /-- Not a canonical form of the proof format (including its judgments). -/
  | syntax
  /-- Some raw rule is unknown, has the wrong arguments or premises, or does not fit. -/
  | elaboration
  /-- Some step is not an instance of its rule, or a side condition fails. -/
  | check
  /-- The lines format has no lines. -/
  | empty
  deriving DecidableEq, Repr

end Silmaril.Consequence.Arithmetic.ND
