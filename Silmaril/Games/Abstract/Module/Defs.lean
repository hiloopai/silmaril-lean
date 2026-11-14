module

public import Silmaril.Games.Abstract.Function.Defs
public import Mathlib.Order.FixedPoints

/-!
# Abstract modules: internal shape, internal calls, closing

A module's **internal shape** (`Shape`) is everything inside it:

* `E`: its imports;
* `S`: its internal state (memories, globals, tables, consolidated into one
  state space);
* `F`: its functions, internal and exported, with argument types `A f` and
  result types `B f`.

Its **public interface** (`Iface`) is separate: the names `X` it exports and
the function each name denotes. Two modules can share an interface and differ
in shape, and the other way round.

An **open** abstract module gives each function an abstract function
(`Silmaril.Games.Abstract.Function`) that may call the imports and the
module's own functions. An internal call `⟨g, (a, s)⟩` passes the argument
and the current state and is answered with a result and the state the callee
left (`Shape.self`). A **closed** module has only import calls.

`close m` resolves the internal calls. It is the least fixpoint of `resolve m`,
which replaces each internal call by a behaviour of the callee
(`Subst`). A callee that traps or diverges makes the caller trap or diverge.
The least fixpoint keeps only finite derivations, so an unbounded recursion
gets no behaviour, not a divergence. `closeD` adds divergence along infinite
internal-call chains that make finitely many import calls.
Open and closed modules of a fixed shape are complete lattices, pointwise. Closing is
monotone, but it does not commute with joins
(`Silmaril.Games.Abstract.Module.Thms`): a pointwise join of open modules can
create behaviours (one module provides a callee that the other's function
needs) that no closed module of either has.

Concrete projections: a module whose functions make no internal calls
(`lift`) closes to itself. Core 3.0 modules project this way
(`Silmaril.Wasm.Abstract.Module`), because their internal calls are already
resolved by the store semantics.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

open Silmaril.Games

universe u

/-- The internal shape of a module. -/
structure Shape : Type (u + 1) where
  /-- Imports. -/
  E : Sig.{u}
  /-- Internal state. -/
  S : Type u
  /-- Functions, internal and exported. -/
  F : Type u
  /-- Argument types. -/
  A : F → Type u
  /-- Result types. -/
  B : F → Type u

/-- A public interface over a shape: exported names and the functions they
denote. -/
structure Iface (sh : Shape.{u}) : Type (u + 1) where
  /-- Exported names. -/
  X : Type u
  /-- The function each name denotes. -/
  fn : X → sh.F

namespace Shape

variable (sh : Shape.{u})

/-- Internal calls: a function, its argument and the current state, answered
with a result and the new state. -/
def self : Sig.{u} := ⟨Σ f : sh.F, sh.A f × sh.S, fun c => sh.B c.1 × sh.S⟩

/-- An open module: functions may call imports (`inl`) and the module's own
functions (`inr`). -/
abbrev OpenMod : Type u := (f : sh.F) → AFun (sh.E ⊕ₛ sh.self) sh.S (sh.A f) (sh.B f)

/-- A closed module: functions call imports only. -/
abbrev ClosedMod : Type u := (f : sh.F) → AFun sh.E sh.S (sh.A f) (sh.B f)

variable {sh}

/-- Resolve the internal calls of an open call behaviour against a closed
module `c`: `Subst c x y` says `y` is `x` with every internal call replaced
by a behaviour of the callee. -/
inductive Subst (c : sh.ClosedMod) {R : Type u} :
    List (Call (sh.E ⊕ₛ sh.self)) → End sh.S R → CallBeh sh.E sh.S R → Prop
  /-- No call left. -/
  | nil (e : End sh.S R) : Subst c [] e ([], e)
  /-- An import call stays. -/
  | ext {m : sh.E.Op} {n : sh.E.Ar m} {rest : List (Call (sh.E ⊕ₛ sh.self))}
      {e : End sh.S R} {y : CallBeh sh.E sh.S R} :
      Subst c rest e y → Subst c (⟨.inl m, n⟩ :: rest) e (⟨m, n⟩ :: y.1, y.2)
  /-- An internal call answered by a returning behaviour of the callee. -/
  | int {g : sh.F} {a : sh.A g} {s : sh.S} {b : sh.B g} {s' : sh.S}
      {rest : List (Call (sh.E ⊕ₛ sh.self))} {e : End sh.S R} {c₁ : List (Call sh.E)}
      {y : CallBeh sh.E sh.S R} :
      (c₁, .ret b s') ∈ c g s a → Subst c rest e y →
      Subst c (⟨.inr ⟨g, (a, s)⟩, (b, s')⟩ :: rest) e (c₁ ++ y.1, y.2)
  /-- An internal call whose callee traps. -/
  | intTrap {g : sh.F} {a : sh.A g} {s : sh.S} {ans : sh.B g × sh.S}
      {rest : List (Call (sh.E ⊕ₛ sh.self))} {e : End sh.S R} {c₁ : List (Call sh.E)} :
      (c₁, .trap) ∈ c g s a → Subst c (⟨.inr ⟨g, (a, s)⟩, ans⟩ :: rest) e (c₁, .trap)
  /-- An internal call whose callee diverges. -/
  | intDiv {g : sh.F} {a : sh.A g} {s : sh.S} {ans : sh.B g × sh.S}
      {rest : List (Call (sh.E ⊕ₛ sh.self))} {e : End sh.S R} {c₁ : List (Call sh.E)} :
      (c₁, .div) ∈ c g s a → Subst c (⟨.inr ⟨g, (a, s)⟩, ans⟩ :: rest) e (c₁, .div)

theorem Subst.mono {c c' : sh.ClosedMod} (h : c ≤ c') {R : Type u}
    {x : List (Call (sh.E ⊕ₛ sh.self))} {e : End sh.S R} {y : CallBeh sh.E sh.S R}
    (hs : Subst c x e y) : Subst c' x e y := by
  induction hs with
  | nil e => exact .nil e
  | ext _ ih => exact .ext ih
  | int hc _ ih => exact .int (h _ _ _ hc) ih
  | intTrap hc => exact .intTrap (h _ _ _ hc)
  | intDiv hc => exact .intDiv (h _ _ _ hc)

/-- One round of resolution: the closed module whose behaviours are those of
`m` with internal calls answered by `c`. -/
def resolve (m : sh.OpenMod) : sh.ClosedMod →o sh.ClosedMod where
  toFun c f s a := {y | ∃ x ∈ m f s a, Subst c x.1 x.2 y}
  monotone' _ _ h _ _ _ _ := fun ⟨x, hx, hs⟩ => ⟨x, hx, hs.mono h⟩

/-- Close a module: the least fixpoint of resolution. Its behaviours are the
*finite derivations*: every internal call is answered by a finished behaviour
of the callee. A callee's `div` propagates to the caller (`Subst.intDiv`),
but a recursion that never bottoms out yields **no behaviour at all**, not a
`div`: `f` calling itself closes to the empty set
(`Silmaril.Games.Abstract.Shape.exists_close_omits_div`). Use `closeD` when
divergence through unbounded internal recursion must be observed. -/
def close (m : sh.OpenMod) : sh.ClosedMod := (resolve m).lfp

/-- Resolve the internal calls of a *prefix* of an open behaviour: every
internal call in it returned. -/
inductive SubstPre (c : sh.ClosedMod) : List (Call (sh.E ⊕ₛ sh.self)) → List (Call sh.E) → Prop
  | nil : SubstPre c [] []
  | ext {m : sh.E.Op} {n : sh.E.Ar m} {rest : List (Call (sh.E ⊕ₛ sh.self))}
      {q : List (Call sh.E)} : SubstPre c rest q → SubstPre c (⟨.inl m, n⟩ :: rest) (⟨m, n⟩ :: q)
  | int {g : sh.F} {a : sh.A g} {s : sh.S} {b : sh.B g} {s' : sh.S}
      {rest : List (Call (sh.E ⊕ₛ sh.self))} {c₁ q : List (Call sh.E)} :
      (c₁, .ret b s') ∈ c g s a → SubstPre c rest q →
      SubstPre c (⟨.inr ⟨g, (a, s)⟩, (b, s')⟩ :: rest) (c₁ ++ q)

/-- One descent: a call `x` of the module, running in `m`, performs the import
calls `q` (its internal calls returning through `c`) and then makes the
internal call `y`. -/
def Descends (m : sh.OpenMod) (c : sh.ClosedMod) (x : sh.self.Op) (q : List (Call sh.E))
    (y : sh.self.Op) : Prop :=
  ∃ z ∈ m x.1 x.2.2 x.2.1, ∃ u ans rest, z.1 = u ++ ⟨.inr y, ans⟩ :: rest ∧ SubstPre c u q

/-- An infinite chain of internal calls from `x`, making only finitely many
import calls `qs` in total: divergence through unbounded internal recursion,
observed after `qs`. -/
def DivChain (m : sh.OpenMod) (c : sh.ClosedMod) (x : sh.self.Op) (qs : List (Call sh.E)) :
    Prop :=
  ∃ (g : Nat → sh.self.Op) (q : Nat → List (Call sh.E)) (N : Nat), g 0 = x ∧
    (∀ n, Descends m c (g n) (q n) (g (n + 1))) ∧ (∀ n, N ≤ n → q n = []) ∧
    qs = (List.range N).flatMap q

/-- Closing with divergence: the finite derivations of `close`, plus `div`
after the import calls of every infinite internal-call chain.

**Scope.** An infinite chain with infinitely many import calls is an infinite
productive run, which `AFun` does not represent; it is omitted. No theorem
here states that `closeD` agrees with an operational semantics with recursion,
or that it is a congruence for the outcome-sensitive equivalences; those are
open. -/
def closeD (m : sh.OpenMod) : sh.ClosedMod := fun f s a =>
  close m f s a ∪ {y | y.2 = .div ∧ DivChain m (close m) ⟨f, (a, s)⟩ y.1}

/-- A closed module as an open one that makes no internal call. -/
def lift (c : sh.ClosedMod) : sh.OpenMod := fun f s a =>
  (fun y => (y.1.map fun x => (⟨.inl x.1, x.2⟩ : Call (sh.E ⊕ₛ sh.self)), y.2)) '' c f s a

/-- The public view of a closed module through an interface. -/
def view (I : Iface sh) (c : sh.ClosedMod) : (x : I.X) → AFun sh.E sh.S (sh.A (I.fn x)) (sh.B (I.fn x)) :=
  fun x => c (I.fn x)

end Shape

end Silmaril.Games.Abstract
