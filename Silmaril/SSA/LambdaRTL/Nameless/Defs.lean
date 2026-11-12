module

public import Silmaril.SSA.LambdaRTL.Defs
public import Mathlib.Data.Fintype.EquivFin

/-!
# Nameless (de Bruijn) presentation of acyclic λSSA regions

`Region V L F` (`Silmaril.SSA.LambdaRTL.Defs`) is the *named* presentation: variables range over an
arbitrary type `V` with decidable equality and the lexical semantics `Region.evalSSA` runs over
environments `V → α`. This file gives:

* `DB.Region L F`: the fully nameless presentation. **Variables are de Bruijn indices; labels stay
  named.** Labels are kept named on purpose: in this acyclic calculus a label is observable (the
  result of `evalSSA` is an exit `(ℓ, a) : L × α`), so a de Bruijn presentation of labels would
  change the observable type and is a different (later) design decision. Variable binding is the
  only binding this file makes nameless. `DB.Region.eval` is the lexical semantics over
  environments `ℕ → α`, extended on the left by `DB.cons`.
* `Region.toDB Γ r`: translation to de Bruijn form in a context `Γ : List V` (names in scope,
  innermost first). A variable `x` becomes the index of its *first* occurrence in `Γ`
  (`idx x Γ`), so shadowing is resolved lexically; a name not in `Γ` becomes `Γ.length`.
* `Region.rename`: renaming of variable names `V → W` (binders included).
* `DB.Region.rename`: de Bruijn renamings `ℕ → ℕ` (lifted under binders), and `DB.Region.wk`.
* `DB.Region.WS n`: well-scopedness (all free indices `< n`).
* `Supply V`: a fresh-name supply `fresh : Finset V → V` with `fresh s ∉ s`. A supply exists iff
  `V` is infinite (`Supply.ofInfinite`); **this is the only place infinitude enters**, and only
  the back translation `DB.Region.ofDB` uses it (to name binders apart from the context).
* `Region.AlphaEq Γ r r'`: α-equivalence in context `Γ`, *defined* as equality of de Bruijn images.

Theorems are in `Silmaril.SSA.LambdaRTL.Nameless.Thms`.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL

universe u v w

namespace DB

/-- de Bruijn values `v ::= #i | () | (v, v')`. -/
inductive Val : Type
  | var (i : ℕ)
  | unit
  | pair (a b : Val)
  deriving DecidableEq

/-- de Bruijn operands. -/
inductive Op (F : Type v) : Type v
  | val (a : Val)
  | app (f : F) (a : Val)
  | inl (a : Val)
  | inr (a : Val)
  | abort (a : Val)

/-- Nameless acyclic regions. Binders bind index `0` in their body:

* `let1 o r` binds one variable in `r`;
* `let2 o r` binds two: in `r`, `#0` is the *second* component and `#1` the first (matching the
  named `let2 x y`, in which `y` is innermost);
* `case o r s` binds the payload in each branch;
* `join r ℓ t` binds the parameter of label `ℓ` in `t` (labels stay named). -/
inductive Region (L : Type w) (F : Type v) : Type (max v w)
  | br (ℓ : L) (a : Val)
  | let1 (o : Op F) (r : Region L F)
  | let2 (o : Op F) (r : Region L F)
  | case (o : Op F) (r s : Region L F)
  | join (r : Region L F) (ℓ : L) (t : Region L F)

/-- Extend a de Bruijn environment: `cons a η 0 = a`, `cons a η (n+1) = η n`. -/
def cons {α : Sort u} (a : α) (η : ℕ → α) : ℕ → α
  | 0 => a
  | n + 1 => η n

/-- Lift a de Bruijn renaming under one binder. -/
def lift (ξ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => ξ n + 1

section Syntax

variable {L : Type w} {F F' : Type v}

/-- Well-scoped values: every index is `< n`. -/
def Val.WS (n : ℕ) : Val → Prop
  | .var i => i < n
  | .unit => True
  | .pair a b => a.WS n ∧ b.WS n

/-- The value an operand reads. -/
def Op.arg : Op F → Val
  | .val a | .app _ a | .inl a | .inr a | .abort a => a

/-- Well-scoped operands. -/
def Op.WS (n : ℕ) (o : Op F) : Prop := o.arg.WS n

/-- Well-scoped regions: every free index is `< n`. -/
def Region.WS : ℕ → Region L F → Prop
  | n, .br _ a => a.WS n
  | n, .let1 o r => o.WS n ∧ r.WS (n + 1)
  | n, .let2 o r => o.WS n ∧ r.WS (n + 2)
  | n, .case o r s => o.WS n ∧ r.WS (n + 1) ∧ s.WS (n + 1)
  | n, .join r _ t => r.WS n ∧ t.WS (n + 1)

/-- de Bruijn renaming of a value. -/
def Val.rename (ξ : ℕ → ℕ) : Val → Val
  | .var i => .var (ξ i)
  | .unit => .unit
  | .pair a b => .pair (a.rename ξ) (b.rename ξ)

/-- de Bruijn renaming of an operand. -/
def Op.rename (ξ : ℕ → ℕ) : Op F → Op F
  | .val a => .val (a.rename ξ)
  | .app f a => .app f (a.rename ξ)
  | .inl a => .inl (a.rename ξ)
  | .inr a => .inr (a.rename ξ)
  | .abort a => .abort (a.rename ξ)

/-- de Bruijn renaming of a region (lifted under binders). -/
def Region.rename : (ℕ → ℕ) → Region L F → Region L F
  | ξ, .br ℓ a => .br ℓ (a.rename ξ)
  | ξ, .let1 o r => .let1 (o.rename ξ) (r.rename (lift ξ))
  | ξ, .let2 o r => .let2 (o.rename ξ) (r.rename (lift (lift ξ)))
  | ξ, .case o r s => .case (o.rename ξ) (r.rename (lift ξ)) (s.rename (lift ξ))
  | ξ, .join r ℓ t => .join (r.rename ξ) ℓ (t.rename (lift ξ))

/-- Weakening: shift every free index by one. -/
def Region.wk (r : Region L F) : Region L F := r.rename Nat.succ

/-- Renaming of instruction symbols in an operand. -/
def Op.mapOp (h : F → F') : Op F → Op F'
  | .val a => .val a
  | .app f a => .app (h f) a
  | .inl a => .inl a
  | .inr a => .inr a
  | .abort a => .abort a

/-- Renaming of instruction symbols in a region. -/
def Region.mapOp (h : F → F') : Region L F → Region L F'
  | .br ℓ a => .br ℓ a
  | .let1 o r => .let1 (o.mapOp h) (r.mapOp h)
  | .let2 o r => .let2 (o.mapOp h) (r.mapOp h)
  | .case o r s => .case (o.mapOp h) (r.mapOp h) (s.mapOp h)
  | .join r ℓ t => .join (r.mapOp h) ℓ (t.mapOp h)

end Syntax

section Semantics

variable {L : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}

/-- Evaluation of a de Bruijn value. -/
def Val.eval (m : Model F M α) (η : ℕ → α) : Val → α
  | .var i => η i
  | .unit => m.unit
  | .pair a b => m.pair (a.eval m η) (b.eval m η)

variable [Monad M]

/-- Evaluation of a de Bruijn operand. -/
def Op.eval (m : Model F M α) (η : ℕ → α) : Op F → M α
  | .val a => pure (a.eval m η)
  | .app f a => m.app f (a.eval m η)
  | .inl a => pure (m.inl (a.eval m η))
  | .inr a => pure (m.inr (a.eval m η))
  | .abort a => m.abort (a.eval m η)

variable [DecidableEq L]

/-- Lexical semantics of nameless regions (the de Bruijn reading of `Region.evalSSA`). -/
def Region.eval (m : Model F M α) : Region L F → (ℕ → α) → M (L × α)
  | .br ℓ a, η => pure (ℓ, a.eval m η)
  | .let1 o r, η => o.eval m η >>= fun a => r.eval m (cons a η)
  | .let2 o r, η => o.eval m η >>= m.unpair >>= fun p => r.eval m (cons p.2 (cons p.1 η))
  | .case o r s, η => o.eval m η >>= m.split >>= fun
      | .inl a => r.eval m (cons a η)
      | .inr b => s.eval m (cons b η)
  | .join r ℓ t, η => r.eval m η >>= fun e =>
      if e.1 = ℓ then t.eval m (cons e.2 η) else pure e

end Semantics

end DB

/-! ## Named → nameless -/

section ToDB

variable {V W L : Type w} {F : Type v}

/-- Position of the first occurrence of `x` in `Γ` (innermost first); `Γ.length` if absent. -/
def idx [DecidableEq V] (x : V) : List V → ℕ
  | [] => 0
  | y :: Γ => if x = y then 0 else idx x Γ + 1

/-- The de Bruijn environment of a named context: index `i` reads the `i`-th name of `Γ`;
indices out of range read the default `d`. -/
def env {α : Type w} (Γ : List V) (ρ : V → α) (d : α) (i : ℕ) : α :=
  match Γ[i]? with
  | some x => ρ x
  | none => d

/-- A de Bruijn environment `η` represents a named environment `ρ` along `Γ`. -/
def Agree {α : Type w} [DecidableEq V] (Γ : List V) (η : ℕ → α) (ρ : V → α) : Prop :=
  ∀ x ∈ Γ, η (idx x Γ) = ρ x

/-- Value to de Bruijn form. -/
def Val.toDB [DecidableEq V] (Γ : List V) : Val V → DB.Val
  | .var x => .var (idx x Γ)
  | .unit => .unit
  | .pair a b => .pair (a.toDB Γ) (b.toDB Γ)

/-- Operand to de Bruijn form. -/
def Op.toDB [DecidableEq V] (Γ : List V) : Op V F → DB.Op F
  | .val a => .val (a.toDB Γ)
  | .app f a => .app f (a.toDB Γ)
  | .inl a => .inl (a.toDB Γ)
  | .inr a => .inr (a.toDB Γ)
  | .abort a => .abort (a.toDB Γ)

/-- Region to de Bruijn form, in context `Γ` (innermost name first). -/
def Region.toDB [DecidableEq V] : List V → Region V L F → DB.Region L F
  | Γ, .br ℓ a => .br ℓ (a.toDB Γ)
  | Γ, .let1 x o r => .let1 (o.toDB Γ) (r.toDB (x :: Γ))
  | Γ, .let2 x y o r => .let2 (o.toDB Γ) (r.toDB (y :: x :: Γ))
  | Γ, .case o x r y s => .case (o.toDB Γ) (r.toDB (x :: Γ)) (s.toDB (y :: Γ))
  | Γ, .join r ℓ x t => .join (r.toDB Γ) ℓ (t.toDB (x :: Γ))

/-- **α-equivalence in context `Γ`**: equal de Bruijn images. -/
def Region.AlphaEq [DecidableEq V] (Γ : List V) (r r' : Region V L F) : Prop :=
  r.toDB Γ = r'.toDB Γ

/-- Every variable name occurring in a region (binders and uses). -/
def Region.vars [DecidableEq V] : Region V L F → Finset V
  | .br _ a => a.fv
  | .let1 x o r => insert x (o.fv ∪ r.vars)
  | .let2 x y o r => insert x (insert y (o.fv ∪ r.vars))
  | .case o x r y s => insert x (insert y (o.fv ∪ r.vars ∪ s.vars))
  | .join r _ x t => insert x (r.vars ∪ t.vars)

/-- Renaming of variable names in a value. -/
def Val.rename (f : V → W) : Val V → Val W
  | .var x => .var (f x)
  | .unit => .unit
  | .pair a b => .pair (a.rename f) (b.rename f)

/-- Renaming of variable names in an operand. -/
def Op.rename (f : V → W) : Op V F → Op W F
  | .val a => .val (a.rename f)
  | .app g a => .app g (a.rename f)
  | .inl a => .inl (a.rename f)
  | .inr a => .inr (a.rename f)
  | .abort a => .abort (a.rename f)

/-- Renaming of all variable names (binders and uses) in a region. -/
def Region.rename (f : V → W) : Region V L F → Region W L F
  | .br ℓ a => .br ℓ (a.rename f)
  | .let1 x o r => .let1 (f x) (o.rename f) (r.rename f)
  | .let2 x y o r => .let2 (f x) (f y) (o.rename f) (r.rename f)
  | .case o x r y s => .case (o.rename f) (f x) (r.rename f) (f y) (s.rename f)
  | .join r ℓ x t => .join (r.rename f) ℓ (f x) (t.rename f)

end ToDB

/-! ## Nameless → named -/

/-- A fresh-name supply. Such a supply exists exactly when `V` is infinite. -/
structure Supply (V : Type w) where
  fresh : Finset V → V
  fresh_not_mem : ∀ s, fresh s ∉ s

/-- The supply induced by `[Infinite V]` (noncomputable choice). -/
noncomputable def Supply.ofInfinite (V : Type w) [Infinite V] : Supply V where
  fresh s := Classical.choose (Infinite.exists_notMem_finset s)
  fresh_not_mem s := Classical.choose_spec (Infinite.exists_notMem_finset s)

section OfDB

variable {V L : Type w} {F : Type v} [DecidableEq V]

/-- A canonical context of `n` pairwise distinct names (innermost first). -/
def Supply.ctx (S : Supply V) : ℕ → List V
  | 0 => []
  | n + 1 => S.fresh (S.ctx n).toFinset :: S.ctx n

/-- de Bruijn value to named form in context `Γ`; out-of-range indices (absent on well-scoped
input) read the default name `d`. -/
def DB.Val.ofDB (d : V) (Γ : List V) : DB.Val → LambdaRTL.Val V
  | .var i => .var (Γ.getD i d)
  | .unit => .unit
  | .pair a b => .pair (a.ofDB d Γ) (b.ofDB d Γ)

/-- de Bruijn operand to named form. -/
def DB.Op.ofDB (d : V) (Γ : List V) : DB.Op F → LambdaRTL.Op V F
  | .val a => .val (a.ofDB d Γ)
  | .app f a => .app f (a.ofDB d Γ)
  | .inl a => .inl (a.ofDB d Γ)
  | .inr a => .inr (a.ofDB d Γ)
  | .abort a => .abort (a.ofDB d Γ)

/-- de Bruijn region to named form in context `Γ`: each binder gets a name fresh for the names
currently in scope (so sibling scopes may reuse names, as in dominator-tree SSA). -/
def DB.Region.ofDB (S : Supply V) : List V → DB.Region L F → LambdaRTL.Region V L F
  | Γ, .br ℓ a => .br ℓ (a.ofDB (S.fresh ∅) Γ)
  | Γ, .let1 o r =>
      let x := S.fresh Γ.toFinset
      .let1 x (o.ofDB (S.fresh ∅) Γ) (r.ofDB S (x :: Γ))
  | Γ, .let2 o r =>
      let x := S.fresh Γ.toFinset
      let y := S.fresh (insert x Γ.toFinset)
      .let2 x y (o.ofDB (S.fresh ∅) Γ) (r.ofDB S (y :: x :: Γ))
  | Γ, .case o r s =>
      let x := S.fresh Γ.toFinset
      .case (o.ofDB (S.fresh ∅) Γ) x (r.ofDB S (x :: Γ)) x (s.ofDB S (x :: Γ))
  | Γ, .join r ℓ t =>
      let x := S.fresh Γ.toFinset
      .join (r.ofDB S Γ) ℓ x (t.ofDB S (x :: Γ))

end OfDB

end Silmaril.SSA.LambdaRTL
