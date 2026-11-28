module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Rows.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Rows.Split

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Rows

open Silmaril.Formats
open Parquet.RecursiveSchema.ListPath
open Parquet.RecursiveSchema.ListPath.Rows
open Arrow.RecursiveSchema.Batch.Rows (Cell CellFits Row RowFits)

private theorem bind_some {α β : Type} {first : Option α} {next : α → Option β} {result : β}
    (accepted : (first >>= next) = some result) :
    ∃ value, first = some value ∧ next value = some result := by
  cases first with
  | none => contradiction
  | some value => exact ⟨value, rfl, accepted⟩

private theorem foldDemand {α : Type} (measure : α → Nat) (values : List α) (total : Nat) :
    values.foldl (fun accumulated value => accumulated + measure value) total =
      total + (values.map measure).sum := by
  induction values generalizing total with
  | nil => simp
  | cons first rest ih => simp [ih, Nat.add_assoc]

private theorem sumDemand_cons {α : Type} (measure : α → Nat) (first : α) (rest : List α) :
    sumDemand measure (first :: rest) = measure first + sumDemand measure rest := by
  simp [sumDemand, foldDemand]

private structure CellWire (shape : Shape) (depth rep base : Nat) (value : Cell) (part : Segment) : Prop where
  starts : part.first.repetition = rep
  continues : ∀ atom ∈ part.rest, depth < atom.repetition
  definition : base ≤ part.first.definition
  typed : CellFits shape.arrow value
  words : part.atoms.filterMap Atom.word = words shape value
  demand : part.atoms.length = demand shape value
  inverse : assemble shape depth base part.atoms = some value

private structure PartsWire (shape : Shape) (depth rep base : Nat)
    (values : List Cell) (parts : List Segment) : Prop where
  starts : ∀ part ∈ parts, part.first.repetition = rep
  continues : ∀ part ∈ parts, ∀ atom ∈ part.rest, depth < atom.repetition
  typed : RowFits (List.replicate values.length shape.arrow) values
  words : (parts.flatMap Segment.atoms).filterMap Atom.word = values.flatMap (words shape)
  demand : (parts.flatMap Segment.atoms).length = sumDemand (demand shape) values
  inverse : (parts.map Segment.atoms).mapM (assemble shape depth base) = some values

private theorem parts_wire {shape : Shape} {depth rep base : Nat} {values : List Cell} {parts : List Segment}
    (emit : ∀ value part, Projection.cell shape depth rep base value = some part →
      CellWire shape depth rep base value part)
    (accepted : values.mapM (Projection.cell shape depth rep base) = some parts) :
    PartsWire shape depth rep base values parts := by
  induction values generalizing parts with
  | nil =>
    cases Option.some.inj accepted
    exact ⟨by simp, by simp, .nil, rfl, rfl, rfl⟩
  | cons value values ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, firstRead, accepted⟩ := bind_some accepted
    obtain ⟨rest, restRead, done⟩ := bind_some accepted
    cases Option.some.inj done
    have head := emit value first firstRead
    have tail := ih restRead
    refine ⟨?_, ?_, .cons head.typed tail.typed, ?_, ?_, ?_⟩
    · intro part member
      rcases List.mem_cons.mp member with rfl | found
      · exact head.starts
      · exact tail.starts part found
    · intro part member
      rcases List.mem_cons.mp member with rfl | found
      · exact head.continues
      · exact tail.continues part found
    · simp [head.words, tail.words]
    · simp [head.demand, tail.demand, sumDemand_cons]
    · simp [List.mapM_cons, head.inverse, tail.inverse]

private theorem signed_wire (site : Parquet.RecursiveSchema.Site) (kind : Parquet.RecursiveSchema.Kind)
    (depth rep base : Nat) (value : Cell) (part : Segment)
    (accepted : Projection.cell (.signed site kind) depth rep base value = some part) :
    CellWire (.signed site kind) depth rep base value part := by
  cases value with
  | none =>
    cases optional : site.nullable with
    | false => simp [Projection.cell, optional] at accepted
    | true =>
      have same : Projection.marker rep base = part := by simpa [Projection.cell, optional] using accepted
      subst part
      refine ⟨rfl, by simp [Projection.marker], Nat.le_refl _, ?_, by cases kind <;> rfl, rfl, ?_⟩
      · rw [Shape.arrow, optional]
        exact .null
      · simp [assemble, Segment.atoms, Projection.marker, optional]
  | some value =>
    cases kind <;> cases value <;> simp [Projection.cell, signedWord] at accepted <;> subst part
    · refine ⟨rfl, by simp, Nat.le_add_right .., .int32, rfl, rfl, ?_⟩
      cases h : site.nullable <;> simp [assemble, Segment.atoms, signedCell, h]
    · refine ⟨rfl, by simp, Nat.le_add_right .., .int64, rfl, rfl, ?_⟩
      cases h : site.nullable <;> simp [assemble, Segment.atoms, signedCell, h]

private theorem list_many (node : Parquet.RecursiveSchema.TwoList.ListSite) (child : Shape)
    (depth rep base : Nat) (below : rep ≤ depth)
    (first : Cell) (rest : List Cell) (part : Segment)
    (emit : ∀ depth rep base value part, rep ≤ depth →
      Projection.cell child depth rep base value = some part → CellWire child depth rep base value part)
    (accepted : Projection.cell (.list node child) depth rep base (some (.list (first :: rest))) = some part) :
    CellWire (.list node child) depth rep base (some (.list (first :: rest))) part := by
  let empty := base + node.site.nullable.toNat
  simp only [Projection.cell] at accepted
  obtain ⟨head, headRead, accepted⟩ := bind_some accepted
  obtain ⟨tail, tailRead, done⟩ := bind_some accepted
  cases Option.some.inj done
  have headWire := emit (depth + 1) rep (empty + 1) first head (by omega) headRead
  have tailWire := parts_wire (fun value segment => emit (depth + 1) (depth + 1) (empty + 1)
    value segment (Nat.le_refl _)) tailRead
  have separated : split (depth + 1) ((head :: tail).flatMap Segment.atoms) =
      (head :: tail).map Segment.atoms := by
    apply split_segments
    · intro segment member
      rcases List.mem_cons.mp member with rfl | later
      · rw [headWire.starts]
        omega
      · rw [tailWire.starts segment later]
    · intro segment member
      rcases List.mem_cons.mp member with rfl | later
      · exact headWire.continues
      · exact tailWire.continues segment later
  have decoded : ((head :: tail).map Segment.atoms).mapM (assemble child (depth + 1) (empty + 1)) =
      some (first :: rest) := by
    simp [List.mapM_cons, headWire.inverse, tailWire.inverse]
  have after : empty < head.first.definition := headWire.definition
  have notNull : (node.site.nullable && head.first.definition == base) = false := by
    have : head.first.definition ≠ base := by dsimp [empty] at after; omega
    simp [this]
  have notEmpty : head.first.definition ≠ empty := Nat.ne_of_gt after
  refine ⟨headWire.starts, ?_, ?_, .list (.cons headWire.typed tailWire.typed), ?_, ?_, ?_⟩
  · intro atom member
    rcases List.mem_append.mp member with inherited | later
    · have := headWire.continues atom inherited
      omega
    · obtain ⟨p, existsPart, inPart⟩ := List.mem_flatMap.mp later
      rcases List.mem_cons.mp inPart with rfl | inside
      · rw [tailWire.starts p existsPart]
        omega
      · have := tailWire.continues p existsPart atom inside
        omega
  · change base ≤ head.first.definition
    dsimp [empty] at after
    omega
  · change ((head :: tail).flatMap Segment.atoms).filterMap Atom.word = _
    simp [words, headWire.words, tailWire.words]
  · change ((head :: tail).flatMap Segment.atoms).length = _
    simp [demand, headWire.demand, tailWire.demand]
  · change assemble (.list node child) depth base ((head :: tail).flatMap Segment.atoms) = _
    rw [show (head :: tail).flatMap Segment.atoms = head.first :: (head.rest ++ tail.flatMap Segment.atoms)
      from rfl]
    simp only [assemble, notNull, Bool.false_eq_true, ↓reduceIte]
    rw [show base + node.site.nullable.toNat = empty from rfl, ite_eq_right notEmpty, ite_eq_left after]
    rw [← show (head :: tail).flatMap Segment.atoms = head.first :: (head.rest ++ tail.flatMap Segment.atoms)
      from rfl, separated, decoded]
    rfl

private theorem cell_wire (shape : Shape) (depth rep base : Nat) (value : Cell) (part : Segment)
    (below : rep ≤ depth) (accepted : Projection.cell shape depth rep base value = some part) :
    CellWire shape depth rep base value part := by
  induction shape generalizing depth rep base value part with
  | signed site kind => exact signed_wire site kind depth rep base value part accepted
  | list node child ih =>
    cases value with
    | none =>
      cases optional : node.site.nullable with
      | false => simp [Projection.cell, optional] at accepted
      | true =>
        have same : Projection.marker rep base = part := by simpa [Projection.cell, optional] using accepted
        subst part
        refine ⟨rfl, by simp [Projection.marker], Nat.le_refl _, ?_, rfl, rfl, ?_⟩
        · rw [Shape.arrow, optional]
          exact .null
        · simp [assemble, Segment.atoms, Projection.marker, optional]
    | some value =>
      cases value with
      | struct fields => contradiction
      | int32 word => contradiction
      | int64 word => contradiction
      | list cells =>
        cases cells with
        | nil =>
          have same := Option.some.inj accepted
          subst part
          refine ⟨rfl, by simp [Projection.marker], Nat.le_add_right .., .list .nil, rfl, rfl, ?_⟩
          cases h : node.site.nullable <;> simp [assemble, Segment.atoms, Projection.marker, h]
        | cons first rest => exact list_many node child depth rep base below first rest part ih accepted

/-- Each part comes from one logical row, with its original starts,
ordered leaves, and a constructive inverse for its full segment. -/
structure RowsWire (plan : Plan) (rows : List Row) (parts : List Segment) : Prop where
  count : parts.length = rows.length
  starts : ∀ part ∈ parts, part.first.repetition = 0
  continues : ∀ part ∈ parts, ∀ atom ∈ part.rest, 0 < atom.repetition
  typed : ∀ row ∈ rows, RowFits plan.arrow.fields row
  words : (parts.flatMap Segment.atoms).filterMap Atom.word = rows.flatMap (rowWords plan)
  demand : (parts.flatMap Segment.atoms).length = slotDemand plan rows
  inverse : (parts.map Segment.atoms).mapM (fun segment => (assemble plan.shape 0 0 segment).map (· :: [])) =
    some rows

theorem rows_wire {plan : Plan} {rows : List Row} {parts : List Segment}
    (accepted : rows.mapM (Projection.row plan) = some parts) : RowsWire plan rows parts := by
  induction rows generalizing parts with
  | nil =>
    cases Option.some.inj accepted
    exact ⟨rfl, by simp, by simp, by simp, rfl, rfl, rfl⟩
  | cons row rows ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, firstRead, accepted⟩ := bind_some accepted
    obtain ⟨rest, restRead, done⟩ := bind_some accepted
    cases Option.some.inj done
    match row with
    | [] | _ :: _ :: _ => contradiction
    | [value] =>
      have head := cell_wire plan.shape 0 0 0 value first (Nat.le_refl _) firstRead
      have tail := ih restRead
      refine ⟨by simp [tail.count], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro part member
        rcases List.mem_cons.mp member with rfl | later
        · exact head.starts
        · exact tail.starts part later
      · intro part member
        rcases List.mem_cons.mp member with rfl | later
        · exact head.continues
        · exact tail.continues part later
      · intro row member
        rcases List.mem_cons.mp member with rfl | later
        · exact .cons head.typed .nil
        · exact tail.typed row later
      · simp [rowWords, head.words, tail.words]
      · simp only [List.flatMap_cons, List.length_append, head.demand, tail.demand, slotDemand,
          sumDemand_cons, rowDemand]
      · simp [List.mapM_cons, head.inverse, tail.inverse]

private theorem trace_parts {plan : Plan} {input : List Atom} {rows : List Row}
    (relation : Relation plan input rows) :
    ∃ parts, rows.mapM (Projection.row plan) = some parts ∧ parts.flatMap Segment.atoms = input := by
  unfold Relation Projection.trace at relation
  cases decoded : rows.mapM (Projection.row plan) with
  | none => simp [decoded] at relation
  | some parts => exact ⟨parts, rfl, by simpa [decoded] using relation⟩

public theorem relation_sound {plan : Plan} {input : List Atom} {rows : List Row}
    (relation : Relation plan input rows) :
    (∀ row ∈ rows, RowFits plan.arrow.fields row) ∧
      rows.flatMap (rowWords plan) = input.filterMap Atom.word := by
  obtain ⟨parts, projected, rfl⟩ := trace_parts relation
  have wire := rows_wire projected
  exact ⟨wire.typed, wire.words.symm⟩

public theorem relation_demand {plan : Plan} {input : List Atom} {rows : List Row}
    (relation : Relation plan input rows) : slotDemand plan rows = input.length := by
  obtain ⟨parts, projected, rfl⟩ := trace_parts relation
  exact (rows_wire projected).demand.symm

public theorem relation_segments {plan : Plan} {input : List Atom} {rows : List Row}
    (relation : Relation plan input rows) :
    (split 0 input).length = rows.length ∧
    (split 0 input).mapM (fun segment => (assemble plan.shape 0 0 segment).map (· :: [])) = some rows := by
  obtain ⟨parts, projected, rfl⟩ := trace_parts relation
  have wire := rows_wire projected
  rw [split_segments 0 parts (fun part found => Nat.le_of_eq (wire.starts part found)) wire.continues]
  exact ⟨by simp [wire.count], wire.inverse⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Rows
