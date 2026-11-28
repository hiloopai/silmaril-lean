module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows.Defs
import Mathlib.Data.List.Forall2

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows

open Silmaril.Formats.Parquet.RecursiveSchema
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct (Plan Side)
open Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Rows (Cell Row)

public theorem addressed_atoms (address : RecursiveSchema.Chunk.Address)
    (observed : RecursiveSchema.ListPath.Chunk.Observation) :
    (addressed address observed).map Addressed.atom = observed.atoms := by
  unfold addressed RecursiveSchema.ListPath.Chunk.Observation.atoms
  rw [List.map_flatMap]
  simp only [List.map_map]
  change ((observed.pages.zipIdx observed.dictionary.isSome.toNat).flatMap fun page =>
    (page.1.decoded.atoms.zipIdx page.1.start.slots).map Prod.fst) = _
  simp only [List.zipIdx_map_fst]
  calc
    _ = ((observed.pages.zipIdx observed.dictionary.isSome.toNat).map Prod.fst).flatMap
        (fun page => page.decoded.atoms) := by
      rw [List.flatMap_map]
    _ = _ := by rw [List.zipIdx_map_fst]

public theorem addressed_slot {address : RecursiveSchema.Chunk.Address}
    {observed : RecursiveSchema.ListPath.Chunk.Observation} {slot : Addressed}
    (member : slot ∈ addressed address observed) :
    ∃ page ordinal indexInPage,
      observed.pages[ordinal]? = some page ∧ page.decoded.atoms[indexInPage]? = some slot.atom ∧
      slot.point = ⟨address, observed.dictionary.isSome.toNat + ordinal, page.frame.header.start,
        page.start.slots + indexInPage⟩ := by
  obtain ⟨⟨page, ordinal⟩, pageMember, atomMember⟩ := List.mem_flatMap.mp member
  obtain ⟨⟨atom, index⟩, found, rfl⟩ := List.mem_map.mp atomMember
  obtain ⟨low, atomAt⟩ := List.mk_mem_zipIdx_iff_le_and_getElem?_sub.mp found
  obtain ⟨first, pageAt⟩ := List.mk_mem_zipIdx_iff_le_and_getElem?_sub.mp pageMember
  exact ⟨page, ordinal - observed.dictionary.isSome.toNat, index - page.start.slots, pageAt,
    atomAt, by simp [Nat.add_sub_of_le first, Nat.add_sub_of_le low]⟩

public theorem topology_wire {ceiling start : Nat} {left right : RecursiveSchema.Chunk.Address}
    {lhs rhs : List Addressed} (read : checkTopology ceiling left right lhs rhs start = .ok ()) :
    TopologyWire ceiling lhs rhs := by
  induction lhs generalizing rhs start with
  | nil =>
    cases rhs with
    | nil => exact .nil
    | cons => contradiction
  | cons first rest ih =>
    cases rhs with
    | nil => contradiction
    | cons other tail =>
      simp only [checkTopology] at read
      split at read
      · rename_i same
        exact .cons same (ih read)
      · contradiction

public theorem topology_failure {ceiling start : Nat} {left right : RecursiveSchema.Chunk.Address}
    {lhs rhs : List Addressed} {cause : TopologyError}
    (read : checkTopology ceiling left right lhs rhs start = .error cause) :
    TopologyFailure ceiling left right lhs rhs start cause := by
  induction lhs generalizing rhs start with
  | nil =>
    cases rhs with
    | nil => contradiction
    | cons =>
      cases Except.error.inj read
      exact .missingLeft
  | cons first rest ih =>
    cases rhs with
    | nil =>
      cases Except.error.inj read
      exact .missingRight
    | cons other tail =>
      simp only [checkTopology] at read
      split at read
      · rename_i same
        exact .next same (ih read)
      · rename_i different
        cases Except.error.inj read
        exact .conflict different

private theorem bind_some {α β : Type} {input : Option α} {next : α → Option β} {out : β}
    (read : (input >>= next) = some out) :
    ∃ value, input = some value ∧ next value = some out := by
  cases input with
  | none => contradiction
  | some value => exact ⟨value, rfl, read⟩

private theorem map_some {α β : Type} {input : Option α} {f : α → β} {out : β}
    (read : input.map f = some out) : ∃ value, input = some value ∧ out = f value := by
  cases input with
  | none => contradiction
  | some value => exact ⟨value, rfl, (Option.some.inj read).symm⟩

private theorem pairMap_projection {α β : Type} {merge : α → α → Option β}
    {project : β → Option α} {side : Side}
    (each : ∀ {a b value}, merge a b = some value → project value = some (side.select a b))
    {lhs rhs : List α} {out : List β} (read : pairMap merge lhs rhs = some out) :
    out.mapM project = some (side.select lhs rhs) := by
  induction lhs generalizing rhs out with
  | nil =>
    cases rhs with
    | cons => simp [pairMap] at read
    | nil =>
      cases Option.some.inj read
      cases side <;> rfl
  | cons first rest ih =>
    cases rhs with
    | nil => simp [pairMap] at read
    | cons other tail =>
      unfold pairMap at read
      split at read
      · rename_i same
        rw [List.zipWithM_cons_cons] at read
        obtain ⟨cell, cellRead, more⟩ := bind_some read
        obtain ⟨cells, projected, done⟩ := bind_some more
        cases Option.some.inj done
        have tailEqual : rest.length = tail.length := Nat.succ.inj same
        have pairedTail : pairMap merge rest tail = some cells := by
          simpa [pairMap, tailEqual] using projected
        have firstRead := each cellRead
        have tailRead := ih pairedTail
        cases side <;> simp [List.mapM_cons, firstRead, tailRead, Side.select]
      · contradiction

private theorem projectElement_merge (side : Side) {optional : Bool} {lhs rhs out : Cell}
    (read : mergeElement optional lhs rhs = some out) :
    projectElement side optional out = some (side.select lhs rhs) := by
  cases optional with
  | false =>
    cases Option.some.inj read
    rfl
  | true =>
    simp only [mergeElement, ↓reduceIte] at read
    split at read
    · cases Option.some.inj read; cases side <;> rfl
    · cases Option.some.inj read; cases side <;> rfl
    · contradiction

private theorem projectCell_merge (side : Side) {depth : Nat} {optional : Bool} {lhs rhs out : Cell}
    (read : mergeCell optional depth lhs rhs = some out) :
    projectCell side optional depth out = some (side.select lhs rhs) := by
  induction depth generalizing lhs rhs out with
  | zero => exact projectElement_merge side read
  | succ depth ih =>
    cases lhs with
    | none =>
      cases rhs with
      | none => cases Option.some.inj read; cases side <;> rfl
      | some => contradiction
    | some first =>
      cases rhs with
      | none => cases first <;> contradiction
      | some other =>
        cases first <;> cases other <;> try contradiction
        rename_i left right
        obtain ⟨elements, paired, rfl⟩ := map_some read
        have checked := pairMap_projection (fun accepted => ih accepted) paired
        cases side <;> simp [projectCell, checked, Side.select]

private theorem projectRow_merge (side : Side) {optional : Bool} {lhs rhs out : Row}
    (read : mergeRow optional lhs rhs = some out) :
    projectRow side optional out = some (side.select lhs rhs) := by
  cases lhs with
  | nil => contradiction
  | cons first rest =>
    cases rest with
    | cons => contradiction
    | nil =>
      cases rhs with
      | nil => contradiction
      | cons other rest =>
        cases rest with
        | cons => contradiction
        | nil =>
          obtain ⟨value, merged, rfl⟩ := map_some read
          have projected := projectCell_merge side merged
          cases side <;> simp [projectRow, projected, Side.select]

public theorem mergeRows_wire {optional : Bool} {lhs rhs out : List Row}
    (read : mergeRows lhs rhs optional = some out) :
    ∀ side, projectRows side out optional = some (side.select lhs rhs) :=
  fun side => pairMap_projection (projectRow_merge side) read

public theorem projectRows_count {side : Side} {optional : Bool} {rows out : List Row}
    (read : projectRows side rows optional = some out) : out.length = rows.length := by
  induction rows generalizing out with
  | nil => cases Option.some.inj read; rfl
  | cons first rest ih =>
    unfold projectRows at read
    rw [List.mapM_cons] at read
    obtain ⟨head, _, next⟩ := bind_some read
    obtain ⟨tail, tailRead, done⟩ := bind_some next
    cases Option.some.inj done
    simp [ih tailRead]

private theorem sumDemand_mapM {α β : Type} {project : α → Option β} {before : α → Nat} {after : β → Nat}
    (each : ∀ {value projected}, project value = some projected → after projected = before value)
    {values : List α} {projected : List β} (read : values.mapM project = some projected) :
    ListPath.Rows.sumDemand after projected = ListPath.Rows.sumDemand before values := by
  unfold ListPath.Rows.sumDemand
  suffices ∀ total, projected.foldl (fun acc value => acc + after value) total =
      values.foldl (fun acc value => acc + before value) total from this 0
  induction values generalizing projected with
  | nil => cases Option.some.inj read; intro; rfl
  | cons first rest ih =>
    rw [List.mapM_cons] at read
    obtain ⟨head, headRead, next⟩ := bind_some read
    obtain ⟨tail, tailRead, done⟩ := bind_some next
    cases Option.some.inj done
    intro total
    simp only [List.foldl_cons, each headRead]
    exact ih tailRead _

private def nest : List TwoList.ListSite → ListPath.Shape → ListPath.Shape
  | [], suffix => suffix
  | node :: rest, suffix => .list node (nest rest suffix)

private theorem projectCell_demand {layers : List TwoList.ListSite} {suffix : ListPath.Shape}
    {side : Side} {optional : Bool} {value projected : Cell}
    (unit : ∀ cell, ListPath.Rows.demand suffix cell = 1)
    (read : projectCell side optional layers.length value = some projected) :
    ListPath.Rows.demand (nest layers suffix) projected = cellDemand layers.length value := by
  induction layers generalizing value projected with
  | nil => exact unit projected
  | cons node layers ih =>
    match value with
    | none =>
      cases Option.some.inj read
      rfl
    | some (.list []) =>
      cases Option.some.inj read
      rfl
    | some (.list (first :: rest)) =>
      simp only [List.length_cons, projectCell, List.mapM_cons] at read
      obtain ⟨elements, mapped, rfl⟩ := map_some read
      obtain ⟨head, headRead, next⟩ := bind_some mapped
      obtain ⟨tail, tailRead, done⟩ := bind_some next
      cases Option.some.inj done
      simp only [nest, ListPath.Rows.demand, cellDemand, List.length_cons, ih headRead,
        sumDemand_mapM (fun accepted => ih accepted) tailRead]
    | some (.int32 _) | some (.int64 _) | some (.struct _) => contradiction

private theorem projectRow_demand {plan : Plan} {side : Side} {row projected : Row}
    (read : projectRow side plan.element.nullable row = some projected) :
    ListPath.Rows.rowDemand (plan.path side) projected = rowDemand row := by
  match row with
  | [value] =>
    obtain ⟨cell, decoded, rfl⟩ := map_some read
    let child := plan.child side
    let leaf := ListPath.Shape.signed child.1 child.2
    let suffix := if plan.element.nullable then ListPath.Shape.struct plan.element leaf else leaf
    have unit : ∀ cell, ListPath.Rows.demand suffix cell = 1 := by
      intro cell
      cases optional : plan.element.nullable with
      | false => simp [suffix, leaf, optional, ListPath.Rows.demand]
      | true =>
        simp only [suffix, optional, ↓reduceIte]
        match cell with
        | none | some (.int32 _) | some (.int64 _) | some (.list _) |
            some (.struct []) | some (.struct [_]) | some (.struct (_ :: _ :: _)) => rfl
    exact projectCell_demand (layers := [plan.outer, plan.inner]) (suffix := suffix) unit decoded
  | [] | _ :: _ :: _ => contradiction

public theorem projectRows_demand {plan : Plan} {side : Side} {rows projected : List Row}
    (read : projectRows side rows plan.element.nullable = some projected) :
    ListPath.Rows.slotDemand (plan.path side) projected = slotDemand rows :=
  sumDemand_mapM (project := projectRow side plan.element.nullable)
    (fun accepted => projectRow_demand (plan := plan) accepted) read

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Rows
