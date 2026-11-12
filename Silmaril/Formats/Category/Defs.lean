module
public import Silmaril.Formats.PER.Defs
public import Silmaril.Encoding.Category
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Category.KleisliCat

/-! Relations as objects use covariant relation-preserving squares, as in
Silmaril's encoding categories. They are not Chu transforms (whose second
map is contravariant). Fixed-carrier categories are fibers, not full
subcategories of the varying-carrier category. -/
@[expose] public section
namespace Silmaril.Formats
open CategoryTheory

abbrev RelationCat := Silmaril.EncCat₂
abbrev ByteRelationCat := Silmaril.EncCat Bytes

def unambiguous : ObjectProperty RelationCat := fun X => X.rel.Functional
abbrev UnambiguousRelationCat := unambiguous.FullSubcategory

def byteUnambiguous : ObjectProperty ByteRelationCat := fun X => X.rel.Functional
abbrev ByteUnambiguousRelationCat := byteUnambiguous.FullSubcategory

/-- Types and partial functions, the Kleisli category of the option monad.
The preceding categories instead have (possibly partial) functions as
*objects*, with commuting/preserving squares as morphisms. -/
abbrev PartialMapCat := KleisliCat Option

/-- A PER presentation; morphisms below are arbitrary functions between its
supported quotients. No computability or realizability tracking is imposed. -/
structure PerObject where
  carrier : Type
  per : PER carrier

def PerObject.denotation (X : PerObject) : Type := X.per.Quotient

/-- The extensional category of PER presentations and maps of represented sets.
This is deliberately distinct from the tracked PER category of realizability. -/
abbrev PerCat := InducedCategory (Type) PerObject.denotation

def perDenotation : PerCat ⥤ Type := inducedFunctor PerObject.denotation

def perDenotationFullyFaithful : perDenotation.FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance : perDenotation.Full := perDenotationFullyFaithful.full
instance : perDenotation.Faithful := perDenotationFullyFaithful.faithful

/-- PERs on bytes, with all maps of their supported quotient sets. -/
abbrev BytePerCat := InducedCategory PerCat (fun R : PER Bytes =>
  (⟨Bytes, R⟩ : PerObject))

def bytePerInclusion : BytePerCat ⥤ PerCat := inducedFunctor _

/-- Fullness includes arbitrary extensional maps of byte equivalence classes. -/
def bytePerFullyFaithful : bytePerInclusion.FullyFaithful := fullyFaithfulInducedFunctor _

instance : bytePerInclusion.Full := bytePerFullyFaithful.full
instance : bytePerInclusion.Faithful := bytePerFullyFaithful.faithful

/-- A proof-relevant parsing relation presented as a span
`Bytes ← Derivation → Ast`. Distinct derivations may have the same projections. -/
structure Format where
  Ast : Type
  Derivation : Type
  bytes : Derivation → Bytes
  ast : Derivation → Ast

namespace Format

def rel (F : Format) : Silmaril.EncRel Bytes F.Ast :=
  fun bytes ast => ∃ d, F.bytes d = bytes ∧ F.ast d = ast

def Unambiguous (F : Format) : Prop := F.rel.Functional

@[ext] structure Hom (F G : Format) where
  onAst : F.Ast → G.Ast
  onDerivation : F.Derivation → G.Derivation
  bytes_commute : ∀ d, G.bytes (onDerivation d) = F.bytes d
  ast_commute : ∀ d, G.ast (onDerivation d) = onAst (F.ast d)

instance : Category Format where
  Hom := Hom
  id _ := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
  comp f g := ⟨g.onAst ∘ f.onAst, g.onDerivation ∘ f.onDerivation,
    fun d => (g.bytes_commute _).trans (f.bytes_commute d),
    fun d => (g.ast_commute _).trans (congrArg g.onAst (f.ast_commute d))⟩

/-- The relation presented by a span, forgetting proof-relevant derivations. -/
def toRelation : Format ⥤ ByteRelationCat where
  obj F := ⟨F.Ast, F.rel⟩
  map f := ⟨f.onAst, by
    rintro bytes ast ⟨d, rfl, rfl⟩
    exact ⟨f.onDerivation d, f.bytes_commute d, f.ast_commute d⟩⟩

/-- The graph presentation of an executable parser. -/
def ofDecoder {A : Type} (decode : Bytes → Option A) : Format where
  Ast := A
  Derivation := {pair : Bytes × A // decode pair.1 = some pair.2}
  bytes d := d.val.1
  ast d := d.val.2

/-- An arbitrary relation has its tautological proof-relevant presentation. -/
def ofRelation {A : Type} (E : Silmaril.EncRel Bytes A) : Format where
  Ast := A
  Derivation := {pair : Bytes × A // E pair.1 pair.2}
  bytes d := d.val.1
  ast d := d.val.2

/-- Restrict byte/AST pairs, retaining their original derivations. -/
def restrict (F : Format) (accept : Bytes → F.Ast → Prop) : Format where
  Ast := F.Ast
  Derivation := {d : F.Derivation // accept (F.bytes d) (F.ast d)}
  bytes d := F.bytes d.val
  ast d := F.ast d.val

/-- Parse a list of records according to an explicit framing function.
Different CSV/TSV/JSONL framing policies are separate arguments. -/
def records (F : Format) (frame : List Bytes → Bytes) : Format where
  Ast := List F.Ast
  Derivation := List F.Derivation
  bytes ds := frame (ds.map F.bytes)
  ast ds := ds.map F.ast

/-- CSTs/derivations are equivalent exactly when their abstract projections agree. -/
def derivationPER (F : Format) : PER F.Derivation := PER.kernel F.ast

def bytePER (F : Format) : PER Bytes := PER.ofRelation F.rel
end Format
end Silmaril.Formats
