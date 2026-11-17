module

public import Silmaril.Logic.Consequence.Soundness.Defs
public import Silmaril.Logic.Institution.Examples.Unsorted.SExp.Defs

/-!
# First-order logic as consequence systems: semantics over structures

Unsorted first-order logic (`Silmaril.Logic.Institution.Examples.UFOL`, registered in the logic
graph as `logic.institution.examples.ufol.inst`) over a signature `Sg`:

* `consequence Sg`: the institution's semantic consequence, every structure satisfying the premises
  satisfies the conclusion (`roomSeq (room Sg)`; structures have nonempty carriers);
* `inStructure M`: the interpretation in **one specified structure** `M`, and `truthIn M` its
  consequence.

**No derivation system** for this logic is defined yet; consistency here is model existence and
nontriviality of semantic consequence, never derivability.

**A specified signature and structure** for the concrete row: `orderSig` (`zero`, `succ` and `<`,
named) and `natStructure`, ℕ with `0`, successor and `<`. `orderTheory` is a concrete theory:
irreflexivity of `<` and `x < succ x`.
-/

@[expose] public section

namespace Silmaril.Consequence.FirstOrder

open Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples.UFOL

/-- **Semantic consequence of first-order logic** over `Sg`: truth in every structure. -/
def consequence (Sg : Signature) : System (List (Sentence Sg)) (Sentence Sg) := roomSeq (room Sg)

/-- **The interpretation in one specified structure.** -/
def inStructure {Sg : Signature} (M : Structure Sg) :
    Satisfaction.{0, 0, 0} (List (Sentence Sg)) (Sentence Sg) where
  Model := Unit
  satAx _ Γ := ∀ φ ∈ Γ, Sentence.Holds M φ
  satC _ φ := Sentence.Holds M φ

/-- Consequence in the structure `M`. -/
def truthIn {Sg : Signature} (M : Structure Sg) : System (List (Sentence Sg)) (Sentence Sg) :=
  (inStructure M).entails

/-- Operation arities of `orderSig`: `zero` (0) and `succ` (1). -/
def orderOps : String → Option ℕ
  | "zero" => some 0
  | "succ" => some 1
  | _ => none

/-- Relation arities of `orderSig`: `<` (2). -/
def orderRels : String → Option ℕ
  | "<" => some 2
  | _ => none

/-- **The specified signature**: `zero`, `succ`, `<`. -/
abbrev orderSig : Signature := named orderOps orderRels

/-- **The specified structure**: ℕ, with `zero` as `0`, `succ` as `+ 1` and `<` as `<`. -/
def natStructure : Structure orderSig where
  carrier := ℕ
  nonempty := ⟨0⟩
  op {n} o args :=
    if h : o.1 = "succ" then
      args ⟨0, by have := o.2; rw [h] at this; simp [orderOps] at this; omega⟩ + 1
    else 0
  rel {n} r args :=
    if h : r.1 = "<" then
      args ⟨0, by have := r.2; rw [h] at this; simp [orderRels] at this; omega⟩ <
        args ⟨1, by have := r.2; rw [h] at this; simp [orderRels] at this; omega⟩
    else False

end Silmaril.Consequence.FirstOrder
