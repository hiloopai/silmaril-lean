module
public import Silmaril.Formats.Category.Defs
public import Silmaril.Formats.PER.Thms

@[expose] public section
namespace Silmaril.Formats
open CategoryTheory

/-- The byte-PER inclusion also embeds objects, so it presents a genuine full
subcategory rather than duplicating presentations under an induced category. -/
theorem bytePerInclusion_injective : Function.Injective bytePerInclusion.obj := by
  intro R S h
  change (⟨Bytes, R⟩ : PerObject) = ⟨Bytes, S⟩ at h
  simp only [PerObject.mk.injEq, true_and] at h
  exact eq_of_heq h

namespace Format
@[simp] theorem ofDecoder_rel {A : Type} (decode : Bytes → Option A) (bytes : Bytes) (ast : A) :
    (ofDecoder decode).rel bytes ast ↔ decode bytes = some ast := by
  constructor
  · rintro ⟨⟨⟨b, a⟩, h⟩, rfl, rfl⟩; exact h
  · intro h; exact ⟨⟨(bytes, ast), h⟩, rfl, rfl⟩

@[simp] theorem ofRelation_rel {A : Type} (E : Silmaril.EncRel Bytes A) (bytes : Bytes) (ast : A) :
    (ofRelation E).rel bytes ast ↔ E bytes ast := by
  constructor
  · rintro ⟨⟨⟨b, a⟩, h⟩, rfl, rfl⟩; exact h
  · intro h; exact ⟨⟨(bytes, ast), h⟩, rfl, rfl⟩

theorem ofDecoder_unambiguous {A : Type} (decode : Bytes → Option A) :
    (ofDecoder decode).Unambiguous := by
  intro bytes a b ha hb
  exact Option.some.inj ((ofDecoder_rel decode bytes a).mp ha |>.symm.trans
    ((ofDecoder_rel decode bytes b).mp hb))

/-- A profile restriction includes into the unrestricted derivation span. -/
def restrictInclusion (F : Format) (accept : Bytes → F.Ast → Prop) :
    F.restrict accept ⟶ F := ⟨id, Subtype.val, fun _ => rfl, fun _ => rfl⟩

/-- Record sequencing transports format morphisms pointwise. The framing
policy is fixed for the functor and need not be injective. -/
def recordsFunctor (frame : List Bytes → Bytes) : Format ⥤ Format where
  obj F := F.records frame
  map {X Y} f :=
    { onAst := List.map f.onAst
      onDerivation := List.map f.onDerivation
      bytes_commute ds := by
        change List X.Derivation at ds
        change frame ((ds.map f.onDerivation).map _) = frame (ds.map _)
        simp only [List.map_map, Function.comp_def, f.bytes_commute]
      ast_commute ds := by
        change List X.Derivation at ds
        change (ds.map f.onDerivation).map _ = (ds.map _).map f.onAst
        simp only [List.map_map, Function.comp_def, f.ast_commute] }
  map_id F := by
    apply Hom.ext
    · funext xs; exact List.map_id xs
    · funext xs; exact List.map_id xs
  map_comp f g := by
    apply Hom.ext
    · funext xs
      change xs.map (g.onAst ∘ f.onAst) = (xs.map f.onAst).map g.onAst
      exact List.map_map.symm
    · funext xs
      change xs.map (g.onDerivation ∘ f.onDerivation) = (xs.map f.onDerivation).map g.onDerivation
      exact List.map_map.symm

/-- For unambiguous formats, closure is unnecessary: equivalent bytes have a
common AST. This implication is false for arbitrary ambiguous relations. -/
theorem bytePER_iff (F : Format) (unambiguous : F.Unambiguous) (left right : Bytes) :
    F.bytePER.rel left right ↔ ∃ ast, F.rel left ast ∧ F.rel right ast := by
  change F.rel.per left right ↔ F.rel.same left right
  rw [unambiguous.per_eq_same]
end Format

/-- Every deterministic parser gives an object of the fixed-byte functional
relation category, regardless of what independent grammar it implements. -/
def parserRelation {A : Type} (decode : Bytes → Option A) : ByteUnambiguousRelationCat :=
  ⟨⟨A, Silmaril.EncRel.ofDecoder decode⟩, Silmaril.EncRel.ofDecoder_functional decode⟩

/-- Functional relations are partial functions classically; no decidability or
executable recognition is inferred from the relational specification. -/
noncomputable def decoderOfFunctional {A B : Type} (E : Silmaril.EncRel A B) : A → Option B := by
  classical
  exact fun a => if h : ∃ b, E a b then some h.choose else none

theorem decoderOfFunctional_graph {A B : Type} (E : Silmaril.EncRel A B)
    (functional : E.Functional) (a : A) (b : B) :
    decoderOfFunctional E a = some b ↔ E a b := by
  classical
  simp only [decoderOfFunctional]
  split_ifs with h
  · constructor
    · intro eq; cases Option.some.inj eq; exact h.choose_spec
    · intro hb; exact congrArg some (functional h.choose_spec hb)
  · simp only [false_iff]
    exact fun hb => h ⟨b, hb⟩

/-- Relation-preserving squares induce extensional maps between PER quotients,
including the transitive-closure PER in the ambiguous case. -/
def relationsToPER : RelationCat ⥤ PerCat where
  obj X := ⟨X.carrier, PER.ofRelation X.rel⟩
  map f := InducedCategory.homMk (TypeCat.ofHom
    (PER.Map.quotient ⟨fun x => ⟨f.onCarrier x.val, f.per x.property⟩,
      fun _ _ h => f.per h⟩))
  map_id X := by
    apply InducedCategory.hom_ext
    ext q
    induction q using Quotient.inductionOn with
    | _ x => rfl
  map_comp f g := by
    apply InducedCategory.hom_ext
    ext q
    induction q using Quotient.inductionOn with
    | _ x => rfl

/-- Fixed-byte relations map into the full category of byte PERs. The source
restricts byte functions to identity; the target allows every extensional map. -/
def byteRelationsToPER : ByteRelationCat ⥤ BytePerCat where
  obj X := PER.ofRelation X.rel
  map f := InducedCategory.homMk (InducedCategory.homMk (TypeCat.ofHom
    (PER.Map.quotient ⟨fun x => ⟨x.val, f.per x.property⟩,
      fun _ _ h => f.per h⟩)))
  map_id X := by
    apply InducedCategory.hom_ext
    apply InducedCategory.hom_ext
    ext q
    induction q using Quotient.inductionOn with
    | _ x => rfl
  map_comp f g := by
    apply InducedCategory.hom_ext
    apply InducedCategory.hom_ext
    ext q
    induction q using Quotient.inductionOn with
    | _ x => rfl

def formatsToPER : Format ⥤ BytePerCat := Format.toRelation ⋙ byteRelationsToPER
end Silmaril.Formats
