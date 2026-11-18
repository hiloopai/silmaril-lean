module

public import Silmaril.Logic.Consequence.FirstOrder.Derivation.Defs
public import Silmaril.Logic.Consequence.Derivation.SExp.Defs
public import Silmaril.Logic.Institution.Examples.Unsorted.SExp.Defs

/-!
# First-order proofs as S-expressions, over a named signature

**Judgments** (`encodeSeq`, `readSeq`; presentation `silmaril.fol.sequent`, v1):

```
J ::= (seq k (formula*) formula)
```

with formulas of `silmaril.fol.formula` over the named signature (`named opArity relArity`) and
`k` variables in scope.

**Raw rules** (`elabRule`): a rule name, or `(name arg*)`. The elaborator reads each node's
conclusion and premise conclusions to fill in the rule instance; it is untrusted, since the result
is checked.

| raw rule | arguments | rule instance |
|---|---|---|
| `hyp`, `weaken`, `true-intro`, `dne` | | as named |
| `not-intro`, `not-elim` | | `notIntro` (ψ from the first premise), `notElim` |
| `and-intro`, `and-left`, `and-right` | | as named |
| `all-intro`, `eq-refl` | | as named |
| `(all-elim t)` | the term `t` | `allElim` |
| `(eq-elim φ)` | the motive `φ`, with one more variable | `eqElim` |
-/

@[expose] public section

namespace Silmaril.Consequence.FirstOrder.ND

open Silmaril.Logic.Institution.Examples.UFOL Silmaril.Logic.Institution.Examples.UFOL.SExp
open Silmaril.Logic.Smt (SE)
open Silmaril.Logic.Concrete.SExp (num num?)

variable {opArity relArity : String → Option ℕ}

/-- The concrete form of a judgment. -/
def encodeSeq (s : Seq (named opArity relArity)) : SE :=
  .list [.atom "seq", num s.k, .list (s.ctx.map encodeFormula), encodeFormula s.goal]

variable (opArity relArity) in
/-- Read formulas with `k` variables in scope. -/
def readFormulas (k : ℕ) : List SE → Option (List (Formula (named opArity relArity) k))
  | [] => some []
  | e :: es =>
    match decodeFormula opArity relArity k e, readFormulas k es with
    | some φ, some Γ => some (φ :: Γ)
    | _, _ => none

variable (opArity relArity) in
/-- Read a judgment. -/
def readSeq : SE → Option (Seq (named opArity relArity))
  | .list [.atom "seq", n, .list hs, g] =>
    match num? n with
    | some k =>
      match readFormulas opArity relArity k hs, decodeFormula opArity relArity k g with
      | some Γ, some φ => some ⟨k, Γ, φ⟩
      | _, _ => none
    | none => none
  | _ => none

/-! ## Reading rule arguments (untrusted, so kernel-reducible rather than canonical) -/

/-- Decimal digits. -/
def digits? : List Char → Option ℕ
  | [] => none
  | [c] => if c.isDigit then some (c.toNat - '0'.toNat) else none
  | c :: cs =>
    if c.isDigit then (digits? cs).map fun m => (c.toNat - '0'.toNat) * 10 ^ cs.length + m
    else none

variable (opArity relArity) in
mutual

/-- A term argument with `k` variables in scope. -/
def termArg? (k : ℕ) : SE → Option (Term (named opArity relArity) k)
  | .list [.atom "var", .atom i] =>
    (digits? i.toList).bind fun m => if h : m < k then some (.var ⟨m, h⟩) else none
  | .list (.atom "app" :: .atom f :: args) =>
    match h : opArity f with
    | some n =>
      (termArgs? k args).bind fun ts =>
        if hl : ts.length = n then some (.app (n := n) ⟨f, h⟩ fun j => ts.get ⟨j, hl ▸ j.isLt⟩)
        else none
    | none => none
  | _ => none

/-- A list of term arguments. -/
def termArgs? (k : ℕ) : List SE → Option (List (Term (named opArity relArity) k))
  | [] => some []
  | e :: es =>
    match termArg? k e, termArgs? k es with
    | some t, some ts => some (t :: ts)
    | _, _ => none

end

variable (opArity relArity) in
/-- A formula argument with `k` variables in scope. -/
def formulaArg? : (k : ℕ) → SE → Option (Formula (named opArity relArity) k)
  | k, .list [.atom "=", t, u] =>
    match termArg? opArity relArity k t, termArg? opArity relArity k u with
    | some t, some u => some (.eq t u)
    | _, _ => none
  | k, .list (.atom "rel" :: .atom r :: args) =>
    match h : relArity r with
    | some n =>
      (termArgs? opArity relArity k args).bind fun ts =>
        if hl : ts.length = n then some (.rel (n := n) ⟨r, h⟩ fun j => ts.get ⟨j, hl ▸ j.isLt⟩)
        else none
    | none => none
  | _, .atom "true" => some .tt
  | k, .list [.atom "not", φ] => (formulaArg? k φ).map .not
  | k, .list [.atom "and", φ, ψ] =>
    match formulaArg? k φ, formulaArg? k ψ with
    | some φ, some ψ => some (.and φ ψ)
    | _, _ => none
  | k, .list [.atom "forall", φ] => (formulaArg? (k + 1) φ).map .all
  | _, _ => none

/-- Reindex a judgment to `k` variables, when it has `k`. -/
def castSeq {Sg : Signature} (k : ℕ) (s : Seq Sg) : Option (List (Formula Sg k) × Formula Sg k) :=
  if h : s.k = k then some (h ▸ s.ctx, h ▸ s.goal) else none

/-- A raw rule's name and arguments. -/
def ruleName : SE → Option (String × List SE)
  | .atom s => some (s, [])
  | .list (.atom s :: args) => some (s, args)
  | _ => none

variable (opArity relArity) in
/-- **The elaborator**: a raw rule, the premise conclusions and the conclusion give a rule
instance. Untrusted. -/
def elabRule (r : SE) (ps : List (Seq (named opArity relArity))) (c : Seq (named opArity relArity)) :
    Option (Σ k, Rule (named opArity relArity) k) :=
  let k := c.k
  let Γ := c.ctx
  let φ := c.goal
  match ruleName r, ps with
  | some ("hyp", []), [] => some ⟨k, .hyp Γ φ⟩
  | some ("weaken", []), [p] => (castSeq k p).map fun q => ⟨k, .weaken q.1 Γ φ⟩
  | some ("true-intro", []), [] => some ⟨k, .ttIntro Γ⟩
  | some ("not-intro", []), [p, _] =>
    match φ, castSeq k p with
    | .not a, some (_, ψ) => some ⟨k, .notIntro Γ a ψ⟩
    | _, _ => none
  | some ("not-elim", []), [p, _] => (castSeq k p).map fun q => ⟨k, .notElim Γ q.2 φ⟩
  | some ("dne", []), [_] => some ⟨k, .dne Γ φ⟩
  | some ("and-intro", []), [_, _] =>
    match φ with
    | .and a b => some ⟨k, .andIntro Γ a b⟩
    | _ => none
  | some ("and-left", []), [p] =>
    match castSeq k p with
    | some (_, .and a b) => some ⟨k, .andLeft Γ a b⟩
    | _ => none
  | some ("and-right", []), [p] =>
    match castSeq k p with
    | some (_, .and a b) => some ⟨k, .andRight Γ a b⟩
    | _ => none
  | some ("all-intro", []), [_] =>
    match φ with
    | .all a => some ⟨k, .allIntro Γ a⟩
    | _ => none
  | some ("all-elim", [t]), [p] =>
    match castSeq k p, termArg? opArity relArity k t with
    | some (_, .all a), some t => some ⟨k, .allElim Γ a t⟩
    | _, _ => none
  | some ("eq-refl", []), [] =>
    match φ with
    | .eq t _ => some ⟨k, .eqRefl Γ t⟩
    | _ => none
  | some ("eq-elim", [m]), [p, _] =>
    match castSeq k p, formulaArg? opArity relArity (k + 1) m with
    | some (_, .eq s t), some m => some ⟨k, .eqElim Γ m s t⟩
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

variable (opArity relArity) in
/-- Elaborate and check a raw proof tree. -/
def checkRawTree (raw : ProofTree SE (Seq (named opArity relArity))) :
    Except Rejection (Seq (named opArity relArity)) :=
  match raw.elaborate (elabRule opArity relArity) with
  | none => .error .elaboration
  | some t => if (system (named opArity relArity)).check [] t then .ok t.concl else .error .check

variable (opArity relArity) in
/-- Elaborate and check raw indexed lines; the conclusion is the last line's. -/
def checkRawLines (raw : List (Line SE (Seq (named opArity relArity)))) :
    Except Rejection (Seq (named opArity relArity)) :=
  match raw.getLast? with
  | none => .error .empty
  | some last =>
    match Line.elaborate (elabRule opArity relArity) [] raw with
    | none => .error .elaboration
    | some ls =>
      if (system (named opArity relArity)).checkLines [] [] ls then .ok last.concl else .error .check

end Silmaril.Consequence.FirstOrder.ND
