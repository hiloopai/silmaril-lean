module

public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Consequence systems: definitions

A *consequence system* between a type `Ax` of contexts ("axioms", premises) and a type `C` of
conclusions is a relation `S : Ax → C → Prop`; `S a c` reads "`a ⊢ c`". Nothing else is
assumed: `Ax` need not be a collection of `C`s, and **no structural rule** (reflexivity,
weakening, cut, contraction, exchange) is built in. Structural properties are separate,
explicitly named hypotheses (`MonoWrt`, `AxMono` below; closures live in other modules).

* `System Ax C`: an `abbrev` for `Ax → C → Prop`, so the order and lattice structure are
  Mathlib's pointwise `Pi`/`Prop` instances (a `CompleteBooleanAlgebra`: `≤`, `⊥`, `⊤`, `⊔`,
  `⊓`, `\`, `sSup`, `sInf`). `S ≤ T` is inclusion: every `S`-judgement is a `T`-judgement.
* `WSystem Ax C`: proof-relevant systems `Ax → C → Type w`, a type of *witnesses* (derivations,
  certificates) per judgement; `WSystem.erase` forgets witnesses through `Nonempty`.
* `Sound S T` (`S ≤ T`) and `Complete S T` (`T ≤ S`): `S` against a reference system `T`.
* `pullback f g T`: reindex `T` along `f : Ax' → Ax` and `g : C' → C`.

## Four different "everything follows" notions

These are kept apart because they differ, especially on empty domains:

* `Universal S`: every context proves every conclusion (`S = ⊤`). Global.
* `ProvesAll S a`: the fixed context `a` proves every conclusion (context *inconsistency* or
  triviality). If `C` is empty, every context proves everything vacuously.
* `ContextConsistent S a`: `¬ ProvesAll S a`; it needs a conclusion `a` does not prove, so it
  never holds when `C` is empty.
* `ProvesFalse S ff a` (`S a ff`) and `ConsistentWrt S ff a` (`¬ S a ff`): consistency relative
  to a chosen bottom conclusion `ff`. They agree with `ProvesAll`/`ContextConsistent` only under
  an explosion hypothesis `Explosive S ff` (`Silmaril.Logic.Consequence.Thms`).
-/

@[expose] public section

namespace Silmaril.Consequence

universe u v w u' v'

/-- A consequence system from contexts `Ax` to conclusions `C`: `S a c` is "`a ⊢ c`". No
structural rule is assumed. The order and lattice operations are Mathlib's pointwise ones. -/
abbrev System (Ax : Type u) (C : Type v) : Type (max u v) := Ax → C → Prop

/-- A proof-relevant consequence system: `W a c` is the type of witnesses (derivations,
certificates) of `a ⊢ c`. -/
abbrev WSystem (Ax : Type u) (C : Type v) : Type (max u v (w + 1)) := Ax → C → Type w

namespace WSystem

variable {Ax : Type u} {C : Type v}

/-- Forget witnesses: `a ⊢ c` holds when some witness exists. -/
def erase (W : WSystem.{u, v, w} Ax C) : System Ax C := fun a c => Nonempty (W a c)

end WSystem

namespace System

variable {Ax : Type u} {C : Type v} {Ax' : Type u'} {C' : Type v'}

/-- `S` is sound with respect to the reference system `T`: whatever `S` proves, `T` proves. -/
def Sound (S T : System Ax C) : Prop := S ≤ T

/-- `S` is complete with respect to the reference system `T`: whatever `T` proves, `S` proves. -/
def Complete (S T : System Ax C) : Prop := T ≤ S

/-- Reindex `T` along a map of contexts and a map of conclusions:
`(pullback f g T) a c ↔ T (f a) (g c)`. -/
def pullback (f : Ax' → Ax) (g : C' → C) (T : System Ax C) : System Ax' C' :=
  fun a c => T (f a) (g c)

/-- Every context proves every conclusion (`S = ⊤`, `Thms`). -/
def Universal (S : System Ax C) : Prop := ∀ a c, S a c

/-- The context `a` proves every conclusion: `a` is inconsistent (trivial) in `S`. -/
def ProvesAll (S : System Ax C) (a : Ax) : Prop := ∀ c, S a c

/-- The context `a` is consistent (nontrivial) in `S`: some conclusion does not follow. -/
def ContextConsistent (S : System Ax C) (a : Ax) : Prop := ¬ S.ProvesAll a

/-- The context `a` proves the chosen bottom conclusion `ff`. -/
def ProvesFalse (S : System Ax C) (ff : C) (a : Ax) : Prop := S a ff

/-- The context `a` is consistent relative to the chosen bottom conclusion `ff`. -/
def ConsistentWrt (S : System Ax C) (ff : C) (a : Ax) : Prop := ¬ S a ff

/-- `ff` is explosive in `S`: a context proving `ff` proves everything (ex falso). -/
def Explosive (S : System Ax C) (ff : C) : Prop := ∀ a, S a ff → S.ProvesAll a

/-- Monotonicity in contexts along an arbitrary relation `r` on `Ax` (weakening, when `r a b`
reads "`b` has at least the premises of `a`"). An explicit hypothesis, never assumed. The
relation is explicit because context types often carry an unrelated order (`List` has the
lexicographic one). -/
def MonoWrt (r : Ax → Ax → Prop) (S : System Ax C) : Prop :=
  ∀ ⦃a b⦄, r a b → ∀ ⦃c⦄, S a c → S b c

/-- Monotonicity in contexts for the preorder instance on `Ax`: `MonoWrt (· ≤ ·)`. -/
def AxMono [Preorder Ax] (S : System Ax C) : Prop := S.MonoWrt (· ≤ ·)

end System

end Silmaril.Consequence
