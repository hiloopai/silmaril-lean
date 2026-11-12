module

public import Mathlib.Data.Finset.Basic

/-!
# λRTL: lambda-SSA's dominator-tree syntax with overwritable variables (acyclic stage)

`Region V L F` is the region syntax of named lambda-SSA (Ghalayini–Krishnaswami, *The Denotational
Semantics of SSA*, §3, Fig. "Rules for typing regions") restricted, at this stage, to the acyclic
fragment: a `where`-block has exactly one non-recursive label (`join r ℓ x t` is
`r where { ℓ(x) => t }` with `t` unable to jump to `ℓ`). Values and operands follow the
three-address grammar of §2.1 (`v ::= x | (v, v') | ()`, `o ::= v | f v | ιₗ v | ιᵣ v | abort v`).

The same tree is read in two ways:

* `Region.evalSSA` is the **lexical** reading of named lambda-SSA: a label body `t` runs in the
  environment of its *definition site*, extended with its parameter. Shadowing is lexical.
* `Region.evalRTL` is the **λRTL** reading: a binder `x = o` *overwrites* register `x` of a global
  store, and a jump carries the *current store*; `t` runs in the store at the *jump site*. The
  result keeps the final store.

The two readings agree exactly when no binder on the way to a jump clobbers a live-in of the
target label (`Region.NoClobber`), in particular on dominance-scoped SSA (`Region.IsSSA`); see
`Silmaril.SSA.LambdaRTL.Thms`. They do *not* agree in general (`Thms.clobber_counterexample`).

Name and label index types `V`, `L` are arbitrary types with decidable equality; no infinitude is
needed at this stage (infinite name supplies only enter when translating λRTL *into* SSA by
versioning, which is not part of this stage).

Semantics are monadic and untyped: a `Model F M α` interprets values in `α` and instructions as
Kleisli arrows of a monad `M`; ill-typed eliminations are delegated to the model's
`unpair`/`split`. Typing and categorical (Freyd/Elgot) models are later stages,
see `docs/projects/ssa.md`.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL

universe v w

/-- Values `v ::= x | () | (v, v')` (paper §2.1, three-address grammar). -/
inductive Val (V : Type w) : Type w
  | var (x : V)
  | unit
  | pair (a b : Val V)
  deriving DecidableEq

/-- Operands `o ::= v | f v | ιₗ v | ιᵣ v | abort v` (paper §2.1). -/
inductive Op (V : Type w) (F : Type v) : Type (max v w)
  | val (a : Val V)
  | app (f : F) (a : Val V)
  | inl (a : Val V)
  | inr (a : Val V)
  | abort (a : Val V)

/-- Acyclic regions in dominator-tree form.

* `br ℓ v` jumps to label `ℓ` with argument `v`;
* `let1 x o r` binds (SSA) or assigns (RTL) `x := o`, then continues with `r`;
* `let2 x y o r` destructures a pair;
* `case o x r y s` branches on a sum, binding the payload to `x` resp. `y`;
* `join r ℓ x t` is `r where { ℓ(x) => t }`: `r` may jump to `ℓ`; `t` is not recursive. -/
inductive Region (V : Type w) (L : Type w) (F : Type v) : Type (max v w)
  | br (ℓ : L) (a : Val V)
  | let1 (x : V) (o : Op V F) (r : Region V L F)
  | let2 (x y : V) (o : Op V F) (r : Region V L F)
  | case (o : Op V F) (x : V) (r : Region V L F) (y : V) (s : Region V L F)
  | join (r : Region V L F) (ℓ : L) (x : V) (t : Region V L F)

/-- A monadic, untyped model: value constructors and destructors in a carrier `α`, and
instructions as Kleisli arrows of `M`. -/
structure Model (F : Type v) (M : Type w → Type w) (α : Type w) where
  unit : α
  pair : α → α → α
  inl : α → α
  inr : α → α
  unpair : α → M (α × α)
  split : α → M (α ⊕ α)
  app : F → α → M α
  abort : α → M α

/-- Reduct of a model along a renaming of instruction symbols (precomposition). -/
def Model.reduct {F F' : Type v} {M : Type w → Type w} {α : Type w} (h : F → F')
    (m : Model F' M α) : Model F M α :=
  { m with app := fun f => m.app (h f) }

/-- Point update of an environment or store. -/
def upd {V : Type w} {α : Type w} [DecidableEq V] (σ : V → α) (x : V) (a : α) : V → α :=
  fun y => if y = x then a else σ y

section Syntax

variable {V L : Type w} {F F' : Type v}

/-- Free variables of a value. -/
def Val.fv [DecidableEq V] : Val V → Finset V
  | .var x => {x}
  | .unit => ∅
  | .pair a b => a.fv ∪ b.fv

/-- Free variables of an operand. -/
def Op.fv [DecidableEq V] : Op V F → Finset V
  | .val a | .app _ a | .inl a | .inr a | .abort a => a.fv

/-- Renaming of instruction symbols in an operand. -/
def Op.mapOp (h : F → F') : Op V F → Op V F'
  | .val a => .val a
  | .app f a => .app (h f) a
  | .inl a => .inl a
  | .inr a => .inr a
  | .abort a => .abort a

/-- Renaming of instruction symbols in a region. -/
def Region.mapOp (h : F → F') : Region V L F → Region V L F'
  | .br ℓ a => .br ℓ a
  | .let1 x o r => .let1 x (o.mapOp h) (r.mapOp h)
  | .let2 x y o r => .let2 x y (o.mapOp h) (r.mapOp h)
  | .case o x r y s => .case (o.mapOp h) x (r.mapOp h) y (s.mapOp h)
  | .join r ℓ x t => .join (r.mapOp h) ℓ x (t.mapOp h)

/-- Lexically free variables of a region. -/
def Region.fv [DecidableEq V] : Region V L F → Finset V
  | .br _ a => a.fv
  | .let1 x o r => o.fv ∪ r.fv.erase x
  | .let2 x y o r => o.fv ∪ (r.fv.erase y).erase x
  | .case o x r y s => o.fv ∪ r.fv.erase x ∪ s.fv.erase y
  | .join r _ x t => r.fv ∪ t.fv.erase x

/-- Every variable bound (SSA) or assigned (RTL) anywhere in a region. -/
def Region.bound [DecidableEq V] : Region V L F → Finset V
  | .br _ _ => ∅
  | .let1 x _ r => insert x r.bound
  | .let2 x y _ r => insert x (insert y r.bound)
  | .case _ x r y s => insert x (insert y (r.bound ∪ s.bound))
  | .join r _ x t => r.bound ∪ insert x t.bound

/-- **No clobbering**: at every join point `r where { ℓ(x) => t }`, no variable read by `t`
(other than its parameter) is (re)assigned anywhere in `r`. This is the exact side condition
used by the agreement theorem; it is path-insensitive and therefore conservative. -/
def Region.NoClobber [DecidableEq V] : Region V L F → Prop
  | .br _ _ => True
  | .let1 _ _ r => r.NoClobber
  | .let2 _ _ _ r => r.NoClobber
  | .case _ _ r _ s => r.NoClobber ∧ s.NoClobber
  | .join r _ x t => r.NoClobber ∧ t.NoClobber ∧ Disjoint (t.fv.erase x) r.bound

/-- **Dominance-scoped SSA** in context `Γ`: every use is in scope, and no binder rebinds a
variable that is already in scope. Sibling scopes (the two branches of a `case`, or the body
`r` and the handler `t` of a join) may reuse names, as in lexical/dominator-tree SSA. -/
def Region.IsSSA [DecidableEq V] : Finset V → Region V L F → Prop
  | Γ, .br _ a => a.fv ⊆ Γ
  | Γ, .let1 x o r => o.fv ⊆ Γ ∧ x ∉ Γ ∧ r.IsSSA (insert x Γ)
  | Γ, .let2 x y o r => o.fv ⊆ Γ ∧ x ∉ Γ ∧ y ∉ Γ ∧ x ≠ y ∧ r.IsSSA (insert y (insert x Γ))
  | Γ, .case o x r y s => o.fv ⊆ Γ ∧ x ∉ Γ ∧ y ∉ Γ ∧ r.IsSSA (insert x Γ) ∧ s.IsSSA (insert y Γ)
  | Γ, .join r _ x t => r.IsSSA Γ ∧ x ∉ Γ ∧ t.IsSSA (insert x Γ)

end Syntax

section Semantics

variable {V L : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}

/-- Evaluation of a value. -/
def Val.eval (m : Model F M α) (σ : V → α) : Val V → α
  | .var x => σ x
  | .unit => m.unit
  | .pair a b => m.pair (a.eval m σ) (b.eval m σ)

variable [Monad M]

/-- Evaluation of an operand. -/
def Op.eval (m : Model F M α) (σ : V → α) : Op V F → M α
  | .val a => pure (a.eval m σ)
  | .app f a => m.app f (a.eval m σ)
  | .inl a => pure (m.inl (a.eval m σ))
  | .inr a => pure (m.inr (a.eval m σ))
  | .abort a => m.abort (a.eval m σ)

variable [DecidableEq V] [DecidableEq L]

/-- Lexical (named lambda-SSA) semantics: exits are `(label, argument)`. -/
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

/-- Store (λRTL) semantics: binders overwrite registers and jumps carry the current store.
Exits are `(label, argument, final store)`. -/
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

/-- Observable outcome of a λRTL run: forget the final store. -/
def obs (e : L × α × (V → α)) : L × α := (e.1, e.2.1)

/-- Observational λRTL semantics (final store is dead). -/
def Region.evalObs (m : Model F M α) (r : Region V L F) (σ : V → α) : M (L × α) :=
  obs <$> r.evalRTL m σ

end Semantics

end Silmaril.SSA.LambdaRTL
