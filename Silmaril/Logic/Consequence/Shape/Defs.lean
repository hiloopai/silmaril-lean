module

public import Silmaril.Logic.Consequence.Accept.Defs
public import Mathlib.Order.Hom.Basic

/-!
# Shapes of consequence systems

Semantic descriptors for the explorer's shape filters. A shape is a property of a raw
`System Ax C` or of a checker predicate. No rule is assumed anywhere.

**Degenerate coordinates.**
* `System Unit C`: acceptors. A language `L : Set C` is the system in which the unique context
  proves exactly the members of `L` (`acceptorEquiv`, an order isomorphism).
* `System Ax Unit`: by convention, **rejectors**. `a ⊢ ()` reads "`a` derives the unique
  (bottom) conclusion", the `liftAxFF` reading of a refuted context (`rejectorEquiv`). That `()`
  is a bottom is a convention of the reading, not a reject signal produced by anything.

**Slices of a general system.**
* `ttSlice S tt`: the conclusions proved by the selected context `tt`.
* `ffSlice S ff`: the contexts proving the selected conclusion `ff`.
* `SupportedAx S tt`: only `tt` proves anything. `SupportedC S ff`: only `ff` is ever proved.
* `ContextFree S`: what is proved does not depend on the context. `ConclusionFree S`: each
  context proves everything or nothing.

These are exactly the conditions under which the four acceptor lifts recover the whole system
from a slice (`Thms`). Without them a slice does not determine the system.

**Checker predicates on list contexts** (`ListPred`), for a predicate `P : List C → Prop` such
as a refutation (UNSAT) checker:
* `PermInv`: invariant under permutation.
* `SetInv`: depends only on the members.
* `UpClosed`: closed under membership weakening.
* `AppendExtensive`: `P l → P (l ++ l')`.
* `AppendClosed`: `P l → P l' → P (l ++ l')`. This is a different property: it is not
  extensive.
* `finExt P`: the explicit finitary extension of a predicate to sets. It agrees with `P` on the
  member sets of lists and is false on infinite sets. Other extensions exist; this one is not
  canonical.
-/

@[expose] public section

namespace Silmaril.Consequence

universe u v w

variable {Ax : Type u} {C : Type v}

/-- The selected-context slice: what `tt` proves. -/
def ttSlice (S : System Ax C) (tt : Ax) : Set C := {c | S tt c}

/-- The selected-conclusion slice: the contexts proving `ff`. -/
def ffSlice (S : System Ax C) (ff : C) : Set Ax := {a | S a ff}

/-- Only the context `tt` proves anything. -/
def SupportedAx (S : System Ax C) (tt : Ax) : Prop := ∀ a c, S a c → a = tt

/-- Only the conclusion `ff` is ever proved. -/
def SupportedC (S : System Ax C) (ff : C) : Prop := ∀ a c, S a c → c = ff

/-- What is proved does not depend on the context. -/
def ContextFree (S : System Ax C) : Prop := ∀ a a' c, S a c → S a' c

/-- Each context proves everything or nothing. -/
def ConclusionFree (S : System Ax C) : Prop := ∀ a c c', S a c → S a c'

/-- Acceptors: systems with a single context are languages of conclusions. -/
def acceptorEquiv : System Unit C ≃o Set C where
  toFun S := {c | S () c}
  invFun L := fun _ c => c ∈ L
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := ⟨fun h u c => by cases u; exact @h c, fun h c => h () c⟩

/-- Rejectors (by convention): systems with a single conclusion are languages of contexts, the
contexts deriving it. -/
def rejectorEquiv : System Ax Unit ≃o Set Ax where
  toFun S := {a | S a ()}
  invFun L := fun a _ => a ∈ L
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := ⟨fun h a u => by cases u; exact @h a, fun h a => h a ()⟩

namespace ListPred

variable (P : List C → Prop)

/-- Invariant under permutation. -/
def PermInv : Prop := ∀ l l', l.Perm l' → (P l ↔ P l')

/-- Depends only on the members. -/
def SetInv : Prop := ∀ l l', (∀ x, x ∈ l ↔ x ∈ l') → (P l ↔ P l')

/-- Closed under membership weakening. -/
def UpClosed : Prop := ∀ l l', l ⊆ l' → P l → P l'

/-- Closed under appending anything. -/
def AppendExtensive : Prop := ∀ l l', P l → P (l ++ l')

/-- Closed under concatenation of two accepted lists (not extensive in general). -/
def AppendClosed : Prop := ∀ l l', P l → P l' → P (l ++ l')

/-- The finitary extension to sets: holds of a set enumerated by some accepted list. -/
def finExt (s : Set C) : Prop := ∃ l, (∀ x, x ∈ l ↔ x ∈ s) ∧ P l

end ListPred

end Silmaril.Consequence
