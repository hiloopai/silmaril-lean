module

public import Silmaril.Wasm.Component.Semantics.Thms
public import Silmaril.Compile.PassAPI.Category

/-!
# Contracts for component passes

The semantic domain of components (`compDomain`) is the triple of the import
count, the export count and the strategy over `sigU`; a replacement is
acceptable when it has the same interface sizes and its strategy *refines* the
original one (`≤`, inclusion of plays). Every result below is stated for an
arbitrary core semantics `C`.

* `nestedIR C`, `linkedIR C`, `programIR C`: the nested IR, the flat IR and
  programs (components with observed exports), as `Silmaril.Compile.PassAPI`
  IRs over `compDomain`. Their contracts (`IR.contract`) are
  `Contract.pullback` of the refinement preorder along the denotation.
* `refines_den`: refinement in the contract implies refinement of the typed
  denotations `Comp.den` at any interface sizes.

The invariant is `True`: the semantics is dynamically typed (ill-typed calls
trap), so no pass needs a typing invariant.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Games
open Silmaril.Compile.PassAPI

variable {M : Type} [CoreModule M]

/-- Denotations with their interface sizes. -/
abbrev DenT : Type := Nat × Nat × Strategy sigU sigU

/-- Acceptable replacement: same interface sizes, refined strategy. -/
def DenT.Rel (x y : DenT) : Prop := y.1 = x.1 ∧ y.2.1 = x.2.1 ∧ y.2.2 ≤ x.2.2

theorem DenT.rel_refl (x : DenT) : DenT.Rel x x := ⟨rfl, rfl, le_rfl⟩

theorem DenT.rel_trans {x y z : DenT} (h₁ : DenT.Rel x y) (h₂ : DenT.Rel y z) :
    DenT.Rel x z :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

/-- An equality of strategies at equal sizes is an acceptable replacement. -/
theorem DenT.rel_of_eq {a b : Nat} {σ τ : Strategy sigU sigU} (h : τ = σ) :
    DenT.Rel (a, b, σ) (a, b, τ) := ⟨rfl, rfl, h.le⟩

/-- The semantic domain of components. -/
def compDomain : Domain DenT := ⟨DenT.Rel, DenT.rel_refl, DenT.rel_trans⟩

/-- The denotation of a component with its interface sizes. -/
def Comp.denT (C : CoreSem M) (c : Comp M) : DenT :=
  (c.imports.length, c.exports.length, c.denU C)

/-- The denotation of a flat component with its interface sizes. -/
def Linked.denT (C : CoreSem M) (l : Linked M) : DenT :=
  (l.imports.length, l.exports.length, l.denU C)

/-- The number of observed exports of a program. -/
def Program.width (p : Program M) : Nat :=
  match p.observe with
  | none => p.comp.exports.length
  | some obs => obs.length

/-- The denotation of a program with its interface sizes. -/
def Program.denT (C : CoreSem M) (p : Program M) : DenT :=
  (p.comp.imports.length, p.width, p.denU C)

/-- The nested IR. -/
def nestedIR (C : CoreSem M) : IR compDomain := ⟨Comp M, Comp.denT C, fun _ => True⟩

/-- The flat IR. -/
def linkedIR (C : CoreSem M) : IR compDomain := ⟨Linked M, Linked.denT C, fun _ => True⟩

/-- Programs: components with observed exports. -/
def programIR (C : CoreSem M) : IR compDomain := ⟨Program M, Program.denT C, fun _ => True⟩

/-- The contract of component passes: refinement pulled back along the
denotation. -/
abbrev contract (C : CoreSem M) : Contract (Comp M) := (nestedIR C).contract

theorem contract_rel (C : CoreSem M) (c c' : Comp M) :
    (contract C).Rel c c' ↔ c'.imports.length = c.imports.length ∧
      c'.exports.length = c.exports.length ∧ c'.denU C ≤ c.denU C := Iff.rfl

/-- **Meaning of the contract**: an acceptable replacement refines the typed
denotation at any interface sizes (in particular at the common sizes of the
two components). -/
theorem refines_den (C : CoreSem M) {c c' : Comp M} (h : (contract C).Rel c c') (n k : Nat) :
    atSizes n k (c'.denU C) ≤ atSizes n k (c.denU C) :=
  Strategy.comp_mono (Strategy.comp_mono le_rfl h.2.2) le_rfl

/-- The typed denotation is `denU` at the interface sizes. -/
theorem den_eq_atSizes (C : CoreSem M) (c : Comp M) :
    c.den C = atSizes c.imports.length c.exports.length (c.denU C) := rfl

end Silmaril.Wasm.Component
