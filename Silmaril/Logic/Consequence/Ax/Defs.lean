module

public import Silmaril.Logic.Consequence.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Basic

/-!
# Context shapes for consequence systems

`System Ax C` leaves the context type `Ax` free. Common choices, each a plain specialization:

| shape | `Ax` | what a context records |
|---|---|---|
| `SingleSystem C` | `C` | one premise |
| `ListSystem C` | `List C` | premises in order, with repetitions |
| `NamedSystem N C` | `N → Option C` | premises under names from `N`, possibly infinitely many |
| `NatNamedSystem C` | `ℕ → Option C` | premises under numeric names (positions) |
| `FinsetSystem C` | `Finset C` | a finite set of premises |
| `SetSystem C` | `Set C` | any set of premises (the shape of `Room.Entails`) |

The maps between shapes, and exactly what each forgets (proved in `Thms`):

* `ctxSingle : C → List C` (`[c]`): forgets nothing (injective).
* `ctxNamed : List C → (ℕ → Option C)` (`fun n => l[n]?`): forgets nothing (injective); a
  list becomes the assignment of its positions.
* `ctxFinset : List C → Finset C` (`List.toFinset`): forgets order and multiplicity
  (`ctxFinset_perm`, `ctxFinset_dup`, and it is not injective).
* `ctxSet : Finset C → Set C` (coercion): forgets only finiteness (injective).
* `ctxRange : (N → Option C) → Set C` (the premises named somewhere): forgets names,
  order and multiplicity (not injective).

Pulling a system back along one of these maps (`System.pullback`) moves it to the finer
shape; the result cannot distinguish contexts the map identifies (`pullback_ctxFinset_perm`).

Weakening orders, for `System.MonoWrt`: `List.Subset` (premises included as sets),
`List.Sublist` (premises included in order), `⊆` on `Finset`/`Set`, and `NamedLE` on named
contexts (every named premise kept under its name). These are passed explicitly; `List`'s
`≤` instance is lexicographic and is not a weakening order.
-/

@[expose] public section

namespace Silmaril.Consequence

universe u v

variable (N : Type v) (C : Type u)

/-- Systems with a single premise. -/
abbrev SingleSystem := System C C
/-- Systems over ordered lists of premises. -/
abbrev ListSystem := System (List C) C
/-- Systems over premises named by `N`. -/
abbrev NamedSystem := System (N → Option C) C
/-- Systems over premises named by natural numbers (positions). -/
abbrev NatNamedSystem := NamedSystem ℕ C
/-- Systems over finite sets of premises. -/
abbrev FinsetSystem := System (Finset C) C
/-- Systems over arbitrary sets of premises. -/
abbrev SetSystem := System (Set C) C

variable {N C}

/-- One premise as a list. -/
def ctxSingle (c : C) : List C := [c]

/-- A list as named premises: position `n` names the `n`-th premise. -/
def ctxNamed (l : List C) : ℕ → Option C := fun n => l[n]?

/-- A list as a finite set of premises. -/
def ctxFinset [DecidableEq C] (l : List C) : Finset C := l.toFinset

/-- A finite set of premises as a set. -/
def ctxSet (s : Finset C) : Set C := ↑s

/-- The premises named somewhere in a named context. -/
def ctxRange (Γ : N → Option C) : Set C := {c | ∃ n, Γ n = some c}

/-- Weakening of named contexts: every premise of `Γ` is kept, under the same name. -/
def NamedLE (Γ Δ : N → Option C) : Prop := ∀ n c, Γ n = some c → Δ n = some c

end Silmaril.Consequence
