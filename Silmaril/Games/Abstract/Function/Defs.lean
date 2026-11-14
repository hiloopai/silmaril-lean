module

public import Silmaril.Games.Sig.Defs
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Data.Set.Lattice.Order
public import Mathlib.Data.Set.Lattice.Image

/-!
# Abstract functions under a module state and an environment

An abstract function `f : AFun E S A B` is called with an argument `a : A` in
a module state `s : S`. It may call the environment's functions `E` (imports)
and receive their answers, and it ends in one of three ways:

* `ret b s'`: it returns `b` and leaves the module in state `s'`;
* `trap`;
* `div`: after its last import call it runs forever without another call
  (silent divergence).

`f.beh s a` is the set of possible *call behaviours*: the import calls with
their answers, then the end. It is an arbitrary set, possibly noncomputable,
and nothing forces it to be realisable by code. Concrete functions (Wasm code)
map into this type by a projection (`Silmaril.Wasm.Abstract.Function`), and
quotients of behaviours are taken through observations. An infinite sequence
of import calls is not represented; such runs are out of scope for this layer.

Import answers come from the environment: they are inputs. Statements about a
fixed environment use a `Host`, which answers each call.

## Observations and equivalence

An observation `κ` maps a call behaviour to whatever an observer sees.
`ObsEquiv κ f g` says `f` and `g` have the same observations at every state
and argument. This is an equivalence defined by the observation; whether it
is a congruence or agrees with a contextual equivalence is proved separately.

* `obsId`: everything;
* `obsCollapse`: trap and divergence merged (trap ≈ divergence);
* `obsForgetState`: the final state forgotten (results and calls only);
* `obsIO`: import calls forgotten.

## Function problems

All quantifiers are explicit: over module states `s`, arguments `a`, and
(through `beh`) all environment answers, unless a `Host` is fixed.

* Determinism: `Det f` (the next call or the end is a function of the history,
  including import answers). It is relative to inputs: different answers may
  lead to different behaviours.
* Statefulness, as several distinct notions, not one Boolean:
  * `StatePreserving f`: every return leaves the state unchanged;
  * `StateIndependent f`: the observations with final state forgotten do not
    depend on the initial state;
  * `StateIndependentOn R f`: the same, for initial states in `R` only
    (reachable states, say);
  * `Pure f`: state-preserving, state-independent, and making no import call.
* May and must: `MayTrap`, `MustTrap`, `MayDiv`, `MustDiv`, `MayAbort`,
  `MustReturn`, each at a given state and argument, either over all
  environment answers or under a host (`…Under`).
* Shape of behaviour: `Callees` (imports possibly called), `CallsOn N` (inputs
  that may call `N`), `IO` (the input/output relation of returns), `outputs`,
  `trapInputs`, `divInputs`, `detInputs`, and `UniquePreimage` (outputs with
  exactly one input producing them).
-/

@[expose] public section

namespace Silmaril.Games.Abstract

open Silmaril.Games

universe u

/-- An import call with its answer. -/
abbrev Call (E : Sig.{u}) : Type u := Σ m : E.Op, E.Ar m

/-- How a call ends. -/
inductive End (S B : Type u) : Type u
  /-- Return `b`, leaving state `s`. -/
  | ret (b : B) (s : S)
  /-- Trap. -/
  | trap
  /-- Silent divergence. -/
  | div

/-- A call behaviour: import calls with answers, then the end. -/
abbrev CallBeh (E : Sig.{u}) (S B : Type u) : Type u := List (Call E) × End S B

/-- An abstract function: its possible call behaviours at each state and
argument. Ordered pointwise by inclusion: `f ≤ g` means every behaviour of `f`
is allowed by `g`. -/
abbrev AFun (E : Sig.{u}) (S A B : Type u) : Type u := S → A → Set (CallBeh E S B)

/-- An environment that answers each import call. -/
abbrev Host (E : Sig.{u}) : Type u := (m : E.Op) → E.Ar m

/-- Ends with trap and divergence merged. -/
inductive CEnd (S B : Type u) : Type u
  | ret (b : B) (s : S)
  | abort

/-- Ends with the final state forgotten. -/
inductive REnd (B : Type u) : Type u
  | ret (b : B)
  | trap
  | div

namespace End

variable {S B : Type u}

/-- Merge trap and divergence. -/
def collapse : End S B → CEnd S B
  | .ret b s => .ret b s
  | .trap => .abort
  | .div => .abort

/-- Forget the final state. -/
def forgetState : End S B → REnd B
  | .ret b _ => .ret b
  | .trap => .trap
  | .div => .div

/-- A trap or a divergence. -/
def IsAbort : End S B → Prop
  | .ret _ _ => False
  | _ => True

end End

namespace AFun

variable {E : Sig.{u}} {S A B C : Type u}

/-! ## Observations -/

/-- Equal observations through `κ` at every state and argument. -/
def ObsEquiv {O : Type u} (κ : CallBeh E S B → O) (f g : AFun E S A B) : Prop :=
  ∀ s a, κ '' f s a = κ '' g s a

/-- Observe everything. -/
def obsId : CallBeh E S B → CallBeh E S B := id

/-- Observe with trap and divergence merged. -/
def obsCollapse : CallBeh E S B → List (Call E) × CEnd S B := fun x => (x.1, x.2.collapse)

/-- Observe with the final state forgotten. -/
def obsForgetState : CallBeh E S B → List (Call E) × REnd B := fun x => (x.1, x.2.forgetState)

/-- Observe the end only, forgetting import calls. -/
def obsIO : CallBeh E S B → End S B := fun x => x.2

/-! ## Sequencing -/

/-- Run `f`, then, if it returned, run `g` on its result in the state it left. -/
def seq (f : AFun E S A B) (g : AFun E S B C) : AFun E S A C := fun s a =>
  {x | (∃ c, (c, End.trap) ∈ f s a ∧ x = (c, End.trap)) ∨
       (∃ c, (c, End.div) ∈ f s a ∧ x = (c, End.div)) ∨
       ∃ c₁ b s₁ c₂ e, (c₁, End.ret b s₁) ∈ f s a ∧ (c₂, e) ∈ g s₁ b ∧ x = (c₁ ++ c₂, e)}

/-! ## Determinism -/

/-- Two behaviours agree as long as the import answers agree: same calls,
and, while the answers are equal, the same continuation and end. -/
def Agree : List (Call E) → End S B → List (Call E) → End S B → Prop
  | [], e₁, [], e₂ => e₁ = e₂
  | ⟨m₁, n₁⟩ :: c₁, e₁, ⟨m₂, n₂⟩ :: c₂, e₂ => m₁ = m₂ ∧ (HEq n₁ n₂ → Agree c₁ e₁ c₂ e₂)
  | _, _, _, _ => False

/-- Determinism given the history: any two behaviours at the same state and
argument agree until the environment answers differently. -/
def Det (f : AFun E S A B) : Prop :=
  ∀ s a x y, x ∈ f s a → y ∈ f s a → Agree x.1 x.2 y.1 y.2

/-- A call list consistent with a host. -/
def Consistent (h : Host E) (c : List (Call E)) : Prop := ∀ x ∈ c, x.2 = h x.1

/-- The behaviours under a fixed host. -/
def under (h : Host E) (f : AFun E S A B) : AFun E S A B := fun s a =>
  {x | x ∈ f s a ∧ Consistent h x.1}

/-! ## Statefulness -/

/-- Every return leaves the state unchanged. -/
def StatePreserving (f : AFun E S A B) : Prop :=
  ∀ s a c b s', (c, End.ret b s') ∈ f s a → s' = s

/-- The behaviour with final state forgotten does not depend on the initial
state, for initial states in `R`. -/
def StateIndependentOn (R : Set S) (f : AFun E S A B) : Prop :=
  ∀ s ∈ R, ∀ s' ∈ R, ∀ a, obsForgetState '' f s a = obsForgetState '' f s' a

/-- `StateIndependentOn` every state. -/
def StateIndependent (f : AFun E S A B) : Prop := StateIndependentOn Set.univ f

/-- No import call, state-preserving and state-independent. -/
def Pure (f : AFun E S A B) : Prop :=
  StatePreserving f ∧ StateIndependent f ∧ ∀ s a x, x ∈ f s a → x.1 = []

/-! ## May and must -/

/-- Some behaviour traps. -/
def MayTrap (f : AFun E S A B) (s : S) (a : A) : Prop := ∃ c, (c, End.trap) ∈ f s a
/-- Some behaviour diverges. -/
def MayDiv (f : AFun E S A B) (s : S) (a : A) : Prop := ∃ c, (c, End.div) ∈ f s a
/-- Some behaviour traps or diverges. -/
def MayAbort (f : AFun E S A B) (s : S) (a : A) : Prop := ∃ x ∈ f s a, x.2.IsAbort
/-- There is a behaviour, and every behaviour traps. -/
def MustTrap (f : AFun E S A B) (s : S) (a : A) : Prop :=
  (f s a).Nonempty ∧ ∀ x ∈ f s a, x.2 = .trap
/-- There is a behaviour, and every behaviour diverges. -/
def MustDiv (f : AFun E S A B) (s : S) (a : A) : Prop :=
  (f s a).Nonempty ∧ ∀ x ∈ f s a, x.2 = .div
/-- There is a behaviour, and every behaviour returns. -/
def MustReturn (f : AFun E S A B) (s : S) (a : A) : Prop :=
  (f s a).Nonempty ∧ ∀ x ∈ f s a, ¬ x.2.IsAbort

/-! ## Shape of behaviour -/

/-- The imports possibly called. -/
def Callees (f : AFun E S A B) : Set E.Op := {m | ∃ s a x, x ∈ f s a ∧ ∃ y ∈ x.1, y.1 = m}

/-- The inputs that may call some import of `N`. -/
def CallsOn (N : Set E.Op) (f : AFun E S A B) : Set (S × A) :=
  {p | ∃ x ∈ f p.1 p.2, ∃ y ∈ x.1, y.1 ∈ N}

/-- The input/output relation of returns: from state and argument to result
and final state. -/
def IO (f : AFun E S A B) (i : S × A) (o : B × S) : Prop :=
  ∃ c, (c, End.ret o.1 o.2) ∈ f i.1 i.2

/-- The possible results and final states. -/
def outputs (f : AFun E S A B) : Set (B × S) := {o | ∃ i, IO f i o}

/-- The inputs that may trap. -/
def trapInputs (f : AFun E S A B) : Set (S × A) := {i | MayTrap f i.1 i.2}

/-- The inputs that may diverge. -/
def divInputs (f : AFun E S A B) : Set (S × A) := {i | MayDiv f i.1 i.2}

/-- The inputs on which `f` is deterministic given the history. -/
def detInputs (f : AFun E S A B) : Set (S × A) :=
  {i | ∀ x y, x ∈ f i.1 i.2 → y ∈ f i.1 i.2 → Agree x.1 x.2 y.1 y.2}

/-- An output produced by exactly one input. -/
def UniquePreimage (f : AFun E S A B) (o : B × S) : Prop := ∃! i, IO f i o

end AFun

end Silmaril.Games.Abstract
