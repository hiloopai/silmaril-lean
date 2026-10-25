module

public import Mathlib.Order.Basic

@[expose] public section

/-! # Pass API: semantic contracts

A **contract** fixes what "a sound pass" means for an IR whose programs live in `X`:

* `Rel x y`: `y` is an acceptable replacement for `x` (a preorder: `refl`, `trans`);
* `Inv x`: the invariant a pass may assume and must preserve (profile, typing).

The contract is deliberately **abstract**: nothing here mentions Binaryen, `ExportRefines`
or `SessionRel`, so the same API serves any IR. The Binaryen instances
(`PassAPI/Instances.lean`) build a contract by pulling a preorder on lowered Core modules
back along `BModule.lower` (`Contract.pullback`); their reflexivity and transitivity come
from `Binaryen/Contracts.lean`.

Contracts are preordered by **inclusion** (`Contract.Le`): the same invariant, and every
`C`-step from an invariant-satisfying program is a `D`-step. A pass for a stronger
contract is a pass for a weaker one (`Pass.weaken`, a monoid hom: `PassAPI/Pass.lean`).

Design: composable pass API (comment "a composable pass API").
-/

namespace Silmaril.Wasm.Binaryen.PassAPI

universe u v

/-- A semantic contract on programs of type `X`: a preorder of acceptable replacements
and an invariant. -/
structure Contract (X : Type u) where
  /-- `Rel x y`: `y` may replace `x`. -/
  Rel : X → X → Prop
  refl : ∀ x, Rel x x
  trans : ∀ {a b c : X}, Rel a b → Rel b c → Rel a c
  /-- The invariant passes assume and preserve. -/
  Inv : X → Prop

namespace Contract

variable {X : Type u}

/-- Pull a preorder on a semantic carrier `S` back along a denotation (for Binaryen:
`BModule.lower`), with an invariant on programs. -/
def pullback {S : Type v} (R : S → S → Prop) (hrefl : ∀ s, R s s)
    (htrans : ∀ {a b c : S}, R a b → R b c → R a c) (den : X → S) (Inv : X → Prop) :
    Contract X where
  Rel x y := R (den x) (den y)
  refl x := hrefl (den x)
  trans h₁ h₂ := htrans h₁ h₂
  Inv := Inv

@[simp] theorem pullback_rel {S : Type v} (R : S → S → Prop) (hrefl : ∀ s, R s s)
    (htrans : ∀ {a b c : S}, R a b → R b c → R a c) (den : X → S) (Inv : X → Prop)
    (x y : X) : (pullback R hrefl htrans den Inv).Rel x y = R (den x) (den y) := rfl

/-- **Contract inclusion.** `C ≤ D`: the same invariant, and every `C`-replacement of an
invariant-satisfying program is a `D`-replacement. (For Binaryen: `ExportEquiv Eq` is
included in `ExportRefines Eq`, which is included in `ExportRefines TrapsUB`.) -/
structure Le (C D : Contract X) : Prop where
  inv_iff : ∀ x, C.Inv x ↔ D.Inv x
  rel : ∀ x y, C.Inv x → C.Rel x y → D.Rel x y

theorem le_refl' (C : Contract X) : Le C C := ⟨fun _ => Iff.rfl, fun _ _ _ h => h⟩

theorem le_trans' {C D E : Contract X} (h₁ : Le C D) (h₂ : Le D E) : Le C E :=
  ⟨fun x => (h₁.inv_iff x).trans (h₂.inv_iff x),
   fun x y hx h => h₂.rel x y ((h₁.inv_iff x).mp hx) (h₁.rel x y hx h)⟩

/-- Contracts on `X` form a preorder under inclusion. -/
instance : Preorder (Contract X) where
  le := Le
  le_refl := le_refl'
  le_trans _ _ _ := le_trans'

end Contract

end Silmaril.Wasm.Binaryen.PassAPI
