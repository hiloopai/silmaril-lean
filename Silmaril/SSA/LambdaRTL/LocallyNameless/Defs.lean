module

public import Silmaril.SSA.LambdaRTL.Nameless.Defs

/-!
# Locally nameless presentation of acyclic λSSA

The middle layer between the named regions `Region V L F` and the fully nameless
`DB.Region L F`: **bound** variables are de Bruijn indices, **free** variables keep their names
(`LN.Val.fvar x`). Binders are as in `DB.Region` (`let1` binds index `0`, `let2` binds `1, 0`
with the second component innermost, `case` binds the payload in each branch, `join` binds the
handler parameter).

* `Region.toLN B r` — named → locally nameless, with `B` the names bound by enclosing binders
  (innermost first); a variable in `B` becomes a bound index, any other stays free.
* `LN.Region.close Γ k d` — locally nameless → nameless: free name `x` becomes index
  `k + idx x Γ`, where `k` is the binder depth and `Γ` the context of free names.
* `LN.Region.ofLN S A B d` — locally nameless → named, opening each binder with a name from the
  supply `S` fresh for the avoid set `A` (which must contain the free names) and the names
  already bound.

Checked results in `Silmaril.SSA.LambdaRTL.LocallyNameless.Thms`: the triangle
`close Γ |B| ∘ toLN B = toDB (B ++ Γ)`, adequacy of both semantics, and the round trip
`toLN B ∘ ofLN S A B = id` on well-scoped terms.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL

universe v w

namespace LN

/-- Locally nameless values: named free variables, indexed bound variables. -/
inductive Val (V : Type w) : Type w
  | fvar (x : V)
  | bvar (i : ℕ)
  | unit
  | pair (a b : Val V)
  deriving DecidableEq

/-- Locally nameless operands. -/
inductive Op (V : Type w) (F : Type v) : Type (max v w)
  | val (a : Val V)
  | app (f : F) (a : Val V)
  | inl (a : Val V)
  | inr (a : Val V)
  | abort (a : Val V)

/-- Locally nameless acyclic regions (binders as in `DB.Region`). -/
inductive Region (V : Type w) (L : Type w) (F : Type v) : Type (max v w)
  | br (ℓ : L) (a : Val V)
  | let1 (o : Op V F) (r : Region V L F)
  | let2 (o : Op V F) (r : Region V L F)
  | case (o : Op V F) (r s : Region V L F)
  | join (r : Region V L F) (ℓ : L) (t : Region V L F)

section Syntax

variable {V L : Type w} {F : Type v}

/-- Bound indices are `< n` (local closure at depth `n`). -/
def Val.WS (n : ℕ) : Val V → Prop
  | .fvar _ => True
  | .bvar i => i < n
  | .unit => True
  | .pair a b => a.WS n ∧ b.WS n

/-- The value an operand reads. -/
def Op.arg : Op V F → Val V
  | .val a | .app _ a | .inl a | .inr a | .abort a => a

/-- Well-scoped operands. -/
def Op.WS (n : ℕ) (o : Op V F) : Prop := o.arg.WS n

/-- Well-scoped regions: bound indices in range at every depth. -/
def Region.WS : ℕ → Region V L F → Prop
  | n, .br _ a => a.WS n
  | n, .let1 o r => o.WS n ∧ r.WS (n + 1)
  | n, .let2 o r => o.WS n ∧ r.WS (n + 2)
  | n, .case o r s => o.WS n ∧ r.WS (n + 1) ∧ s.WS (n + 1)
  | n, .join r _ t => r.WS n ∧ t.WS (n + 1)

variable [DecidableEq V]

/-- Free names of a value. -/
def Val.fv : Val V → Finset V
  | .fvar x => {x}
  | .bvar _ => ∅
  | .unit => ∅
  | .pair a b => a.fv ∪ b.fv

/-- Free names of an operand. -/
def Op.fv (o : Op V F) : Finset V := o.arg.fv

/-- Free names of a region (no erasure: binders bind indices, not names). -/
def Region.fv : Region V L F → Finset V
  | .br _ a => a.fv
  | .let1 o r => o.fv ∪ r.fv
  | .let2 o r => o.fv ∪ r.fv
  | .case o r s => o.fv ∪ r.fv ∪ s.fv
  | .join r _ t => r.fv ∪ t.fv

end Syntax

section Semantics

variable {V L : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}

/-- Evaluation of a value: free names read `ρ`, bound indices read `η`. -/
def Val.eval (m : Model F M α) (ρ : V → α) (η : ℕ → α) : Val V → α
  | .fvar x => ρ x
  | .bvar i => η i
  | .unit => m.unit
  | .pair a b => m.pair (a.eval m ρ η) (b.eval m ρ η)

variable [Monad M]

/-- Evaluation of an operand. -/
def Op.eval (m : Model F M α) (ρ : V → α) (η : ℕ → α) : Op V F → M α
  | .val a => pure (a.eval m ρ η)
  | .app f a => m.app f (a.eval m ρ η)
  | .inl a => pure (m.inl (a.eval m ρ η))
  | .inr a => pure (m.inr (a.eval m ρ η))
  | .abort a => m.abort (a.eval m ρ η)

variable [DecidableEq L]

/-- Lexical semantics of locally nameless regions. -/
def Region.eval (m : Model F M α) (ρ : V → α) : Region V L F → (ℕ → α) → M (L × α)
  | .br ℓ a, η => pure (ℓ, a.eval m ρ η)
  | .let1 o r, η => o.eval m ρ η >>= fun a => r.eval m ρ (DB.cons a η)
  | .let2 o r, η => o.eval m ρ η >>= m.unpair >>= fun p =>
      r.eval m ρ (DB.cons p.2 (DB.cons p.1 η))
  | .case o r s, η => o.eval m ρ η >>= m.split >>= fun
      | .inl a => r.eval m ρ (DB.cons a η)
      | .inr b => s.eval m ρ (DB.cons b η)
  | .join r ℓ t, η => r.eval m ρ η >>= fun e =>
      if e.1 = ℓ then t.eval m ρ (DB.cons e.2 η) else pure e

end Semantics

/-! ## Locally nameless → nameless -/

section Close

variable {V L : Type w} {F : Type v} [DecidableEq V]

/-- Close a value at depth `k` against the free-name context `Γ`. -/
def Val.close (Γ : List V) (k : ℕ) : Val V → DB.Val
  | .fvar x => .var (k + idx x Γ)
  | .bvar i => .var i
  | .unit => .unit
  | .pair a b => .pair (a.close Γ k) (b.close Γ k)

/-- Close an operand. -/
def Op.close (Γ : List V) (k : ℕ) : Op V F → DB.Op F
  | .val a => .val (a.close Γ k)
  | .app f a => .app f (a.close Γ k)
  | .inl a => .inl (a.close Γ k)
  | .inr a => .inr (a.close Γ k)
  | .abort a => .abort (a.close Γ k)

/-- Close a region: free names become indices beyond the current binder depth. -/
def Region.close (Γ : List V) : ℕ → Region V L F → DB.Region L F
  | k, .br ℓ a => .br ℓ (a.close Γ k)
  | k, .let1 o r => .let1 (o.close Γ k) (r.close Γ (k + 1))
  | k, .let2 o r => .let2 (o.close Γ k) (r.close Γ (k + 2))
  | k, .case o r s => .case (o.close Γ k) (r.close Γ (k + 1)) (s.close Γ (k + 1))
  | k, .join r ℓ t => .join (r.close Γ k) ℓ (t.close Γ (k + 1))

end Close

/-! ## Locally nameless → named -/

section Open

variable {V L : Type w} {F : Type v} [DecidableEq V]

/-- Open a value: index `i` reads the `i`-th bound name of `B`; free names stay. -/
def Val.ofLN (d : V) (B : List V) : Val V → LambdaRTL.Val V
  | .fvar x => .var x
  | .bvar i => .var (B.getD i d)
  | .unit => .unit
  | .pair a b => .pair (a.ofLN d B) (b.ofLN d B)

/-- Open an operand. -/
def Op.ofLN (d : V) (B : List V) : Op V F → LambdaRTL.Op V F
  | .val a => .val (a.ofLN d B)
  | .app f a => .app f (a.ofLN d B)
  | .inl a => .inl (a.ofLN d B)
  | .inr a => .inr (a.ofLN d B)
  | .abort a => .abort (a.ofLN d B)

/-- Open a region, naming each binder with a name fresh for `A ∪ B`. -/
def Region.ofLN (S : Supply V) (A : Finset V) : List V → Region V L F → LambdaRTL.Region V L F
  | B, .br ℓ a => .br ℓ (a.ofLN (S.fresh ∅) B)
  | B, .let1 o r =>
      let x := S.fresh (A ∪ B.toFinset)
      .let1 x (o.ofLN (S.fresh ∅) B) (r.ofLN S A (x :: B))
  | B, .let2 o r =>
      let x := S.fresh (A ∪ B.toFinset)
      let y := S.fresh (insert x (A ∪ B.toFinset))
      .let2 x y (o.ofLN (S.fresh ∅) B) (r.ofLN S A (y :: x :: B))
  | B, .case o r s =>
      let x := S.fresh (A ∪ B.toFinset)
      .case (o.ofLN (S.fresh ∅) B) x (r.ofLN S A (x :: B)) x (s.ofLN S A (x :: B))
  | B, .join r ℓ t =>
      let x := S.fresh (A ∪ B.toFinset)
      .join (r.ofLN S A B) ℓ x (t.ofLN S A (x :: B))

end Open

end LN

/-! ## Named → locally nameless -/

section ToLN

variable {V L : Type w} {F : Type v} [DecidableEq V]

/-- A value to locally nameless form, with bound names `B`. -/
def Val.toLN (B : List V) : Val V → LN.Val V
  | .var x => if x ∈ B then .bvar (idx x B) else .fvar x
  | .unit => .unit
  | .pair a b => .pair (a.toLN B) (b.toLN B)

/-- An operand to locally nameless form. -/
def Op.toLN (B : List V) : Op V F → LN.Op V F
  | .val a => .val (a.toLN B)
  | .app f a => .app f (a.toLN B)
  | .inl a => .inl (a.toLN B)
  | .inr a => .inr (a.toLN B)
  | .abort a => .abort (a.toLN B)

/-- A region to locally nameless form, with bound names `B` (innermost first). -/
def Region.toLN : List V → Region V L F → LN.Region V L F
  | B, .br ℓ a => .br ℓ (a.toLN B)
  | B, .let1 x o r => .let1 (o.toLN B) (r.toLN (x :: B))
  | B, .let2 x y o r => .let2 (o.toLN B) (r.toLN (y :: x :: B))
  | B, .case o x r y s => .case (o.toLN B) (r.toLN (x :: B)) (s.toLN (y :: B))
  | B, .join r ℓ x t => .join (r.toLN B) ℓ (t.toLN (x :: B))

end ToLN

end Silmaril.SSA.LambdaRTL
