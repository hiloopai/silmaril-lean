module

public import Silmaril.Formats.Parquet.NestedPoint.Multi.ToIpc.Defs
import all Silmaril.Formats.Parquet.NestedPoint.Multi.ToIpc.Defs
import Silmaril.Formats.Parquet.Snapshot.Thms
import Silmaril.Formats.Parquet.NestedPoint.Multi.Thms
import Silmaril.Formats.Parquet.NestedPresence.Thms
import Silmaril.Formats.Parquet.Footer.NestedLeaf.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.NestedPoint.Multi.ToIpc

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.NestedPoint.Multi.ToIpc
open Silmaril.Formats.Parquet.NestedPoint.Multi (Kind Decoded FrameWire ColumnWire parentMask)
open NestedPresence (Presence)
open Arrow.StructInt32 (Field)

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

private theorem selectLeaf_wire {limits : Footer.Limits} {snapshot : Snapshot.Checked} {kind : Kind}
    {leaf : Footer.NestedLeaf.Selection snapshot} (selected : selectLeaf limits snapshot kind = .ok leaf) :
    LeafWire limits snapshot kind leaf := by
  unfold selectLeaf at selected
  obtain ⟨selection, source, selected⟩ := bind_ok selected
  split at selected
  · rename_i shape
    split at selected
    · contradiction
    · rename_i annotated
      cases Except.ok.inj selected
      refine ⟨Footer.NestedLeaf.select_wire (mapError_ok source), shape.2, shape.1, ?_⟩
      intro item member
      have clean := List.any_eq_false.mp (Bool.eq_false_iff.mpr annotated) item member
      simpa using clean
  · contradiction

private theorem parent_optional {limits : Footer.Limits} {snapshot : Snapshot.Checked}
    {kind : Kind} {leaf : Footer.NestedLeaf.Selection snapshot} (wire : LeafWire limits snapshot kind leaf) :
    leaf.parent.repetition = some .optional := by
  obtain ⟨shape, admitted, schema⟩ := wire.original.shape
  have parent : shape.parent = leaf.parent := by
    simpa [schema] using wire.original.parentAt
  exact parent ▸ admitted.2.2.2.1

theorem openFile_wire {limits : SourceLimits} {bytes : Bytes} {checked : Checked}
    (opened : openFile limits bytes = .ok checked) : OpenWire limits bytes checked := by
  unfold openFile at opened
  obtain ⟨snapshot, snapshotRead, opened⟩ := bind_ok opened
  obtain ⟨left, leftRead, opened⟩ := bind_ok opened
  obtain ⟨right, rightRead, opened⟩ := bind_ok opened
  cases Except.ok.inj opened
  have original := mapError_ok snapshotRead
  have signed := selectLeaf_wire leftRead
  have wide := selectLeaf_wire rightRead
  exact ⟨original, Snapshot.check_bytes original, left, right, signed, wide, rfl,
    Option.some.inj (signed.original.parentAt.symm.trans wide.original.parentAt),
    parent_optional signed, signed.repetition, wide.repetition⟩

private theorem frame_value_mask {kind : Kind} {limits : NestedPresence.Limits} {bytes : Bytes}
    {frame : Page.Frame} {page : Decoded kind.Value} (wire : FrameWire kind limits bytes frame page) :
    page.slots.map Option.isSome = page.states.map Presence.valuePresent := by
  obtain ⟨_, decoded, _, _, _, states, _, mask, _⟩ := wire.wire
  simpa [states, NestedPoint.valueMask] using mask

/-- Required-child states only contain the original level-zero and level-one
cases. Its value mask is therefore exactly the shared parent mask. -/
private theorem frame_required_mask {limits : NestedPresence.Limits} {bytes : Bytes}
    {frame : Page.Frame} {page : Decoded Int32} (wire : FrameWire .signed limits bytes frame page) :
    page.slots.map Option.isSome = parentMask page.states := by
  rw [frame_value_mask wire, parentMask]
  obtain ⟨_, decoded, _, _, frameWire, states, _, _, _⟩ := wire.wire
  obtain ⟨_, _, _, _, _, levelWire⟩ := frameWire.page
  obtain ⟨_, _, levels, _, _, _, _, _, bounded, classified⟩ := levelWire.definitions
  rw [states, classified]
  apply List.map_congr_left
  intro state member
  obtain ⟨level, belongs, rfl⟩ := List.mem_map.mp member
  have admissible := NestedPresence.classify_contract (child := .required) (bounded level belongs)
  change (NestedPresence.classify .required level).valuePresent =
    (NestedPresence.classify .required level != .parentAbsent)
  cases presence : NestedPresence.classify .required level
  · rfl
  · have impossible := (admissible.2.1.mp presence).1
    contradiction
  · rfl

private theorem flatten_mask {kind : Kind} {limits : NestedPresence.Limits} {bytes : Bytes}
    {predicate : Presence → Bool} {frames : List Page.Frame} {pages : List (Decoded kind.Value)}
    (checked : List.Forall₂ (FrameWire kind limits bytes) frames pages)
    (mask : ∀ {frame page}, FrameWire kind limits bytes frame page →
      page.slots.map Option.isSome = page.states.map predicate) :
    (pages.flatMap Decoded.slots).map Option.isSome = (pages.flatMap Decoded.states).map predicate := by
  induction checked with
  | nil => rfl
  | cons first _ tail => simp [List.flatMap_cons, List.map_append, mask first, tail]

private theorem column_mask {kind : Kind} {limits : NestedPoint.Multi.Limits}
    {snapshot : Snapshot.Checked} {ordinal : Nat} {column : Decoded kind.Value} {predicate : Presence → Bool}
    (wire : ColumnWire kind limits snapshot ordinal column)
    (mask : ∀ {frame page}, FrameWire kind limits.leaf.presence snapshot.bytes frame page →
      page.slots.map Option.isSome = page.states.map predicate) :
    column.slots.map Option.isSome = column.states.map predicate := by
  obtain ⟨_, _, _, _, _, pages, _, _, _, _, _, _, _, _, _, _, _, _, frames, same, _, _⟩ := wire.source
  subst column
  exact flatten_mask frames mask

private theorem paired_slots (states : List Presence) (lhs : List (Option Int32)) (rhs : List (Option Int64))
    (left : lhs.map Option.isSome = parentMask states) (right : rhs.map Option.isSome = states.map Presence.valuePresent) :
    List.Forall₂ (fun (state, a, b) slot => SlotWire state a b slot)
      (states.zip (lhs.zip rhs)) ((NestedPoint.pairSlots lhs rhs).map nativeRow) := by
  induction states generalizing lhs rhs with
  | nil => cases lhs <;> cases rhs <;> simp_all [parentMask, NestedPoint.pairSlots]
  | cons state rest ih =>
    cases lhs with
    | nil => simp [parentMask] at left
    | cons a leftSlots =>
      cases rhs with
      | nil => simp at right
      | cons b rightSlots =>
        have leftSplit : a.isSome = (state != .parentAbsent) ∧
            leftSlots.map Option.isSome = parentMask rest := by simpa [parentMask] using left
        have rightSplit : b.isSome = state.valuePresent ∧
            rightSlots.map Option.isSome = rest.map Presence.valuePresent := by simpa using right
        refine .cons ?_ (ih leftSlots rightSlots leftSplit.2 rightSplit.2)
        cases state <;> cases a <;> cases b <;>
          simp_all [Presence.valuePresent, nativeRow] <;> constructor

theorem readGroup_wire {limits : NestedPoint.Multi.Limits} {snapshot : Snapshot.Checked}
    {ordinal : Nat} {rows : List NestedPoint.Row}
    (decoded : NestedPoint.Multi.read limits snapshot ordinal = .ok rows) : GroupWire limits snapshot ordinal rows := by
  have wire := NestedPoint.Multi.read_wire decoded
  obtain ⟨lhs, rhs, left, right, parent, pair⟩ := wire.aligned
  have lhsMask : lhs.slots.map Option.isSome = parentMask lhs.states :=
    column_mask left frame_required_mask
  have rhsMask := column_mask right frame_value_mask
  exact ⟨wire.count, lhs, rhs, left, right, parent, pair,
    pair ▸ paired_slots rhs.states lhs.slots rhs.slots (lhsMask.trans parent) rhsMask⟩

end Silmaril.Proofs.Formats.Parquet.NestedPoint.Multi.ToIpc
