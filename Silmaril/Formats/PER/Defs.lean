module
public import Silmaril.Formats.Binary.Defs
public import Silmaril.Encoding.Per
public import Mathlib.Data.List.Forall2

/-! Partial equivalences describe valid representations modulo semantic equality.
No reflexivity is imposed on invalid inputs. Canonicality is a transversal
condition, stronger than merely restricting a decoder's accepted inputs. -/
@[expose] public section
namespace Silmaril.Formats

/-- A partial equivalence relation, using Silmaril's shared PER laws. -/
structure PER (α : Type) where
  rel : α → α → Prop
  laws : Silmaril.IsPartialEquivalence rel

namespace PER
variable {α β γ : Type}

def Dom (R : PER α) (x : α) : Prop := R.rel x x

def pull (R : PER β) (f : α → β) : PER α :=
  ⟨fun x y => R.rel (f x) (f y), ⟨by intro x y h; exact R.laws.symm h, by intro x y z h k; exact R.laws.trans h k⟩⟩

def equality (α : Type) : PER α := ⟨Eq, ⟨by intro x y h; exact h.symm, by intro x y z h k; exact h.trans k⟩⟩

def kernel (f : α → β) : PER α := (equality β).pull f

/-- Same successful decoding. Failure is outside the PER domain. -/
def ofDecoder (decode : α → Option β) : PER α where
  rel x y := ∃ value, decode x = some value ∧ decode y = some value
  laws.symm := by rintro x y ⟨v, hx, hy⟩; exact ⟨v, hy, hx⟩
  laws.trans := by
    rintro x y z ⟨v, hx, hy⟩ ⟨w, hy', hz⟩
    have hw : v = w := Option.some.inj (hy.symm.trans hy')
    exact ⟨w, hw ▸ hx, hz⟩

/-- Pull an AST PER through a partial decoder, permitting semantic quotients
such as unordered maps rather than only literal AST equality. -/
def decodePull (R : PER β) (decode : α → Option β) : PER α where
  rel x y := ∃ a b, decode x = some a ∧ decode y = some b ∧ R.rel a b
  laws := Silmaril.EncRel.Lift.isPartialEquivalence
    (Silmaril.EncRel.ofDecoder_functional decode) R.laws

/-- Ambiguous relations require transitive closure: sharing one AST alone
need not be transitive. -/
def ofRelation (E : Silmaril.EncRel α β) : PER α :=
  ⟨E.per, Silmaril.EncRel.per_isPartialEquivalence⟩

/-- Restrict the supported elements without changing their equivalences. -/
def restrict (R : PER α) (selected : α → Prop) : PER α where
  rel x y := selected x ∧ selected y ∧ R.rel x y
  laws.symm := by rintro x y ⟨hx, hy, h⟩; exact ⟨hy, hx, R.laws.symm h⟩
  laws.trans := by rintro x y z ⟨hx, _, h⟩ ⟨_, hz, k⟩; exact ⟨hx, hz, R.laws.trans h k⟩

/-- Equality of projections on a specified valid domain, suitable for CSTs
whose type alone does not certify grammatical validity. -/
def kernelOn (valid : α → Prop) (project : α → β) : PER α :=
  (kernel project).restrict valid

/-- Pointwise inclusion of partial equivalences. -/
def Sub (R S : PER α) : Prop := ∀ ⦃x y⦄, R.rel x y → S.rel x y

/-- The everywhere-defined indiscrete PER. -/
def universal (α : Type) : PER α :=
  ⟨fun _ _ => True, ⟨by intros; trivial, by intros; trivial⟩⟩

/-- The empty format has no supported values. -/
def empty (α : Type) : PER α :=
  ⟨fun _ _ => False, ⟨by intros; contradiction, by intros; contradiction⟩⟩

/-- Intersection preserves partial equivalence. Union generally does not. -/
def intersection (R S : PER α) : PER α where
  rel x y := R.rel x y ∧ S.rel x y
  laws.symm := by intro x y h; exact ⟨R.laws.symm h.1, S.laws.symm h.2⟩
  laws.trans := by intro x y z h k; exact ⟨R.laws.trans h.1 k.1, S.laws.trans h.2 k.2⟩

def iInf {ι : Sort*} (family : ι → PER α) : PER α where
  rel x y := ∀ i, (family i).rel x y
  laws.symm := by intro x y h i; exact (family i).laws.symm (h i)
  laws.trans := by intro x y z h k i; exact (family i).laws.trans (h i) (k i)

/-- A canonical subformat selects exactly one supported representative of
every original equivalence class. This does not assume an executable selector. -/
structure Canonical (R : PER α) where
  selected : α → Prop
  supported : ∀ x, selected x → R.Dom x
  representative : ∀ x, R.Dom x → ∃! y, selected y ∧ R.rel x y

def Canonical.per {R : PER α} (C : Canonical R) : PER α := R.restrict C.selected

/-- A PER denotes its supported elements modulo the PER. -/
def supportSetoid (R : PER α) : Setoid {x // R.Dom x} where
  r x y := R.rel x.val y.val
  iseqv := ⟨fun x => x.property, fun h => R.laws.symm h, fun h k => R.laws.trans h k⟩

abbrev Quotient (R : PER α) := _root_.Quotient R.supportSetoid

/-- A total map of supported representations respecting equivalence. -/
structure Map (R : PER α) (S : PER β) where
  fn : {x // R.Dom x} → {y // S.Dom y}
  respects : ∀ x y, R.rel x.val y.val → S.rel (fn x).val (fn y).val

def Map.quotient {R : PER α} {S : PER β} (f : Map R S) : R.Quotient → S.Quotient :=
  _root_.Quotient.map f.fn f.respects

/-- Pointwise extension to finite record sequences. Lengths must agree. -/
def list (R : PER α) : PER (List α) where
  rel := List.Forall₂ R.rel
  laws.symm := by intro x y h; exact h.flip.imp (fun _ _ h => R.laws.symm h)
  laws.trans := by
    intro x y z h k
    induction h generalizing z with
    | nil => cases k; exact .nil
    | cons h hs ih => cases k with
      | cons k ks => exact .cons (R.laws.trans h k) (ih ks)
end PER
end Silmaril.Formats
