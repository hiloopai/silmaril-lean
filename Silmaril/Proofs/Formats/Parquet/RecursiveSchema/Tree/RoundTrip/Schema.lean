module

public import Silmaril.Formats.Parquet.RecursiveSchema.Tree.Rows.Projection.Defs

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.RoundTrip

open Silmaril.Formats
open Parquet
open Parquet.RecursiveSchema (Kind Entry)
open Parquet.RecursiveSchema.Repeated (Field FieldWire FieldsWire Wrapper wrapperAt)
open Parquet.RecursiveSchema.Tree

private theorem not_struct (kind : Kind) : kind.arrow ≠ .struct := by
  cases kind <;> decide

private theorem not_list (kind : Kind) : kind.arrow ≠ .list := by
  cases kind <;> decide

private theorem signed_kind {first second : Kind} (same : first.arrow = second.arrow) : first = second := by
  cases first <;> cases second <;> simp_all [Kind.arrow]

private theorem site_eq {ctx : RecursiveSchema.Repeated.Context} {ordinal : Nat} {a b : String} {p q : Bool}
    (name : (ctx.site ordinal a p).name = (ctx.site ordinal b q).name)
    (nullable : (ctx.site ordinal a p).nullable = (ctx.site ordinal b q).nullable) :
    ctx.site ordinal a p = ctx.site ordinal b q := by
  change a = b at name
  change p = q at nullable
  rw [name, nullable]

mutual

private theorem field_eq {lr rr : ThriftCompact.Traversal.Reader} {ls rs : Array Entry}
    {ld rd start stopL stopR : Nat} {ctx : RecursiveSchema.Repeated.Context} {left right : Field}
    (first : FieldWire lr ls ld ctx start left stopL)
    (second : FieldWire rr rs rd ctx start right stopR) (arrow : left.arrow = right.arrow) :
    left = right ∧ stopL = stopR := by
  cases first with
  | leaf _ _ _ _ _ _ =>
    cases second <;> simp [Field.arrow, not_struct, not_list] at arrow
    obtain ⟨name, nullable, kind⟩ := arrow
    rw [site_eq name nullable, signed_kind kind]
    exact ⟨rfl, rfl⟩
  | group =>
    rename_i children
    cases second <;> simp [Field.arrow, Ne.symm (not_struct _)] at arrow
    rename_i rightChildren
    obtain ⟨name, nullable, fields⟩ := arrow
    rw [site_eq name nullable] at children ⊢
    obtain ⟨equal, stopped⟩ := fields_eq children rightChildren fields
    exact ⟨by rw [equal], stopped⟩
  | list _ _ _ _ _ _ wrapper children =>
    cases second <;> simp [Field.arrow, Ne.symm (not_list _)] at arrow
    rename_i rightWrapper _ _ _ rightChild
    obtain ⟨name, nullable, element⟩ := arrow
    simp only [wrapperAt, wrapper.1, site_eq name nullable] at children ⊢
    simp only [wrapperAt, rightWrapper.1] at rightChild ⊢
    obtain ⟨equal, stopped⟩ := field_eq children rightChild element
    exact ⟨by rw [equal], stopped⟩
termination_by (ld, 0)

private theorem fields_eq {lr rr : ThriftCompact.Traversal.Reader} {ls rs : Array Entry}
    {ld rd countL countR start stopL stopR : Nat} {ctx : RecursiveSchema.Repeated.Context} {left right : List Field}
    (first : FieldsWire lr ls ld ctx countL start left stopL)
    (second : FieldsWire rr rs rd ctx countR start right stopR)
    (arrow : left.map Field.arrow = right.map Field.arrow) : left = right ∧ stopL = stopR := by
  cases first with
  | nil => cases second <;> simp_all
  | cons first rest =>
    cases second with
    | nil => simp at arrow
    | cons head tail =>
      obtain ⟨arrowHead, arrowTail⟩ := List.cons.inj arrow
      obtain ⟨h, c⟩ := field_eq first head arrowHead
      cases h
      cases c
      obtain ⟨eq, final⟩ := fields_eq rest tail arrowTail
      exact ⟨congrArg (List.cons _) eq, final⟩
termination_by (ld, countL + 1)

end

/-- The recursive Arrow declaration determines the canonical physical
schema tree, including its preorder locations and LIST wrappers. -/
public theorem compiled_fields {ll rl : Snapshot.Limits} {ls rs : Snapshot.Checked}
    {left : Compiled ll ls} {right : Compiled rl rs} (arrow : left.arrow = right.arrow) :
    left.schema.fields = right.schema.fields := by
  obtain ⟨_, _, _, first⟩ := left.schema.grammar.children
  obtain ⟨_, _, _, second⟩ := right.schema.grammar.children
  exact (fields_eq first second (congrArg Arrow.RecursiveSchema.Schema.fields arrow)).1

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Tree.RoundTrip
