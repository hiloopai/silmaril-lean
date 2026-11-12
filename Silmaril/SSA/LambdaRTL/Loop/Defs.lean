module

public import Silmaril.SSA.LambdaRTL.Defs
public import Silmaril.Semantics.Elgot.Defs

/-!
# λRTL with loops: a self-recursive `where`, read lexically and by store passing

`Loop.Region V L F` extends the acyclic `LambdaRTL.Region V L F` with one recursive constructor:

* `loop r ℓ x t` is `r where { ℓ(x) => t }` with `ℓ` **in scope in `t`**: both the body `r` and
  the handler `t` may jump to `ℓ`. Exits of `t` to `ℓ` re-enter the handler; every other exit
  leaves the `where`-block.

All acyclic constructors (including the non-recursive `join`) are kept unchanged, so the acyclic
API in `Silmaril.SSA.LambdaRTL` stays intact; `Region.ofAcyclic` embeds it and both semantics
commute with the embedding (`Silmaril.SSA.LambdaRTL.Loop.Thms`).

Both semantics interpret the loop by the iteration operator `Silmaril.Elgot.iter` of the monad
(convention: `Sum.inl` returns, `Sum.inr` continues):

* `Region.evalSSA` (lexical): the loop state is the argument `a : α` of `ℓ`; each iteration runs
  `t` in the **definition-site** environment `ρ[x ↦ a]`.
* `Region.evalRTL` (λRTL): the loop state is `(a, σ)`, the argument and the **jump-site store**;
  each iteration runs `t` in `σ[x ↦ a]` and passes on the store it ends with.

`Region.NoClobber` additionally requires that no live-in of a loop handler (other than its
parameter) is assigned in `r` or in `t` itself.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.Loop

open Silmaril.Elgot

universe v w

/-- Regions with acyclic joins and self-recursive loops.

* `br`, `let1`, `let2`, `case`, `join` are as in `Silmaril.SSA.LambdaRTL.Region`;
* `loop r ℓ x t` is the recursive `r where { ℓ(x) => t }`: `r` and `t` may both jump to `ℓ`. -/
inductive Region (V : Type w) (L : Type w) (F : Type v) : Type (max v w)
  | br (ℓ : L) (a : Val V)
  | let1 (x : V) (o : Op V F) (r : Region V L F)
  | let2 (x y : V) (o : Op V F) (r : Region V L F)
  | case (o : Op V F) (x : V) (r : Region V L F) (y : V) (s : Region V L F)
  | join (r : Region V L F) (ℓ : L) (x : V) (t : Region V L F)
  | loop (r : Region V L F) (ℓ : L) (x : V) (t : Region V L F)

section Syntax

variable {V L : Type w} {F F' : Type v}

/-- The acyclic fragment, embedded constructor by constructor. -/
def Region.ofAcyclic : LambdaRTL.Region V L F → Region V L F
  | .br ℓ a => .br ℓ a
  | .let1 x o r => .let1 x o (Region.ofAcyclic r)
  | .let2 x y o r => .let2 x y o (Region.ofAcyclic r)
  | .case o x r y s => .case o x (Region.ofAcyclic r) y (Region.ofAcyclic s)
  | .join r ℓ x t => .join (Region.ofAcyclic r) ℓ x (Region.ofAcyclic t)

/-- Renaming of instruction symbols in a region. -/
def Region.mapOp (h : F → F') : Region V L F → Region V L F'
  | .br ℓ a => .br ℓ a
  | .let1 x o r => .let1 x (o.mapOp h) (r.mapOp h)
  | .let2 x y o r => .let2 x y (o.mapOp h) (r.mapOp h)
  | .case o x r y s => .case (o.mapOp h) x (r.mapOp h) y (s.mapOp h)
  | .join r ℓ x t => .join (r.mapOp h) ℓ x (t.mapOp h)
  | .loop r ℓ x t => .loop (r.mapOp h) ℓ x (t.mapOp h)

variable [DecidableEq V]

/-- Lexically free variables of a region. -/
def Region.fv : Region V L F → Finset V
  | .br _ a => a.fv
  | .let1 x o r => o.fv ∪ r.fv.erase x
  | .let2 x y o r => o.fv ∪ (r.fv.erase y).erase x
  | .case o x r y s => o.fv ∪ r.fv.erase x ∪ s.fv.erase y
  | .join r _ x t => r.fv ∪ t.fv.erase x
  | .loop r _ x t => r.fv ∪ t.fv.erase x

/-- Every variable bound (SSA) or assigned (RTL) anywhere in a region. -/
def Region.bound : Region V L F → Finset V
  | .br _ _ => ∅
  | .let1 x _ r => insert x r.bound
  | .let2 x y _ r => insert x (insert y r.bound)
  | .case _ x r y s => insert x (insert y (r.bound ∪ s.bound))
  | .join r _ x t => r.bound ∪ insert x t.bound
  | .loop r _ x t => r.bound ∪ insert x t.bound

/-- **No clobbering**: at every join point no live-in of the handler (other than its
parameter) is assigned in the body `r`; at every loop, no live-in of the handler is assigned in
`r` **or in the handler `t` itself** (a later iteration reads it again). -/
def Region.NoClobber : Region V L F → Prop
  | .br _ _ => True
  | .let1 _ _ r => r.NoClobber
  | .let2 _ _ _ r => r.NoClobber
  | .case _ _ r _ s => r.NoClobber ∧ s.NoClobber
  | .join r _ x t => r.NoClobber ∧ t.NoClobber ∧ Disjoint (t.fv.erase x) r.bound
  | .loop r _ x t => r.NoClobber ∧ t.NoClobber ∧ Disjoint (t.fv.erase x) (r.bound ∪ t.bound)

/-- **Dominance-scoped SSA** in context `Γ`, as in the acyclic stage; the handler of a loop is
scoped like the handler of a join (its own binders are re-bound on every iteration, which is
lexical shadowing of the *previous iteration's* scope, not of an enclosing one). -/
def Region.IsSSA : Finset V → Region V L F → Prop
  | Γ, .br _ a => a.fv ⊆ Γ
  | Γ, .let1 x o r => o.fv ⊆ Γ ∧ x ∉ Γ ∧ r.IsSSA (insert x Γ)
  | Γ, .let2 x y o r => o.fv ⊆ Γ ∧ x ∉ Γ ∧ y ∉ Γ ∧ x ≠ y ∧ r.IsSSA (insert y (insert x Γ))
  | Γ, .case o x r y s => o.fv ⊆ Γ ∧ x ∉ Γ ∧ y ∉ Γ ∧ r.IsSSA (insert x Γ) ∧ s.IsSSA (insert y Γ)
  | Γ, .join r _ x t => r.IsSSA Γ ∧ x ∉ Γ ∧ t.IsSSA (insert x Γ)
  | Γ, .loop r _ x t => r.IsSSA Γ ∧ x ∉ Γ ∧ t.IsSSA (insert x Γ)

end Syntax

section Semantics

variable {V L : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}

variable [DecidableEq L]

/-- Route a lexical exit of a loop handler: a jump to `ℓ` continues with its argument. -/
def routeSSA (ℓ : L) (e : L × α) : (L × α) ⊕ α :=
  if e.1 = ℓ then .inr e.2 else .inl e

/-- Route a λRTL exit of a loop handler: a jump to `ℓ` continues with its argument and the
jump-site store. -/
def routeRTL (ℓ : L) (e : L × α × (V → α)) : (L × α × (V → α)) ⊕ (α × (V → α)) :=
  if e.1 = ℓ then .inr e.2 else .inl e

variable [Monad M] [Iterate M] [DecidableEq V]

/-- Lexical (named lambda-SSA) semantics with loops: exits are `(label, argument)`. -/
def Region.evalSSA (m : Model F M α) : Region V L F → (V → α) → M (L × α)
  | .br ℓ a, ρ => pure (ℓ, a.eval m ρ)
  | .let1 x o r, ρ => o.eval m ρ >>= fun a => r.evalSSA m (upd ρ x a)
  | .let2 x y o r, ρ => o.eval m ρ >>= m.unpair >>= fun p =>
      r.evalSSA m (upd (upd ρ x p.1) y p.2)
  | .case o x r y s, ρ => o.eval m ρ >>= m.split >>= fun
      | .inl a => r.evalSSA m (upd ρ x a)
      | .inr b => s.evalSSA m (upd ρ y b)
  | .join r ℓ x t, ρ => r.evalSSA m ρ >>= fun e =>
      if e.1 = ℓ then t.evalSSA m (upd ρ x e.2) else pure e
  | .loop r ℓ x t, ρ => r.evalSSA m ρ >>= fun e =>
      if e.1 = ℓ then iter (fun a => routeSSA ℓ <$> t.evalSSA m (upd ρ x a)) e.2 else pure e

/-- Store (λRTL) semantics with loops: binders overwrite registers, jumps carry the current
store, and a loop iterates on `(argument, store)`. -/
def Region.evalRTL (m : Model F M α) : Region V L F → (V → α) → M (L × α × (V → α))
  | .br ℓ a, σ => pure (ℓ, a.eval m σ, σ)
  | .let1 x o r, σ => o.eval m σ >>= fun a => r.evalRTL m (upd σ x a)
  | .let2 x y o r, σ => o.eval m σ >>= m.unpair >>= fun p =>
      r.evalRTL m (upd (upd σ x p.1) y p.2)
  | .case o x r y s, σ => o.eval m σ >>= m.split >>= fun
      | .inl a => r.evalRTL m (upd σ x a)
      | .inr b => s.evalRTL m (upd σ y b)
  | .join r ℓ x t, σ => r.evalRTL m σ >>= fun e =>
      if e.1 = ℓ then t.evalRTL m (upd e.2.2 x e.2.1) else pure e
  | .loop r ℓ x t, σ => r.evalRTL m σ >>= fun e =>
      if e.1 = ℓ then iter (fun p => routeRTL ℓ <$> t.evalRTL m (upd p.2 x p.1)) e.2 else pure e

/-- Observational λRTL semantics (final store is dead). -/
def Region.evalObs (m : Model F M α) (r : Region V L F) (σ : V → α) : M (L × α) :=
  obs <$> r.evalRTL m σ

end Semantics

end Silmaril.SSA.LambdaRTL.Loop
