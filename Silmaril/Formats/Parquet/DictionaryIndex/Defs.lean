module

public import Silmaril.Formats.Parquet.ScalarPage.Defs

/-! Parquet dictionary data pages over a checked, typed dictionary in wire order. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.DictionaryIndex

inductive Error where
  | unsupportedEncoding (id : Int)
  | page (error : ScalarPage.Error)
  | indexByteLimit
  | missingBitWidth
  | hybrid (error : Hybrid.Error)
  | outOfBounds (index : Nat)
  | slots (error : FlatPage.Error)
  deriving DecidableEq, Repr

/-- Check the byte budget including the width octet. Hybrid checks the width,
expected count, exact consumption, and final packed padding of the suffix. -/
def readIndices (limits : Hybrid.Limits) (expected : Nat) (source : Bytes) :
    Except Error (List Nat) :=
  if limits.bytes < source.length then .error .indexByteLimit
  else
    match source.toList with
    | [] => .error .missingBitWidth
    | width :: runs =>
      (Hybrid.decode width.toNat expected limits (Bytes.ofList runs)).mapError Error.hybrid

/-- Resolve each index in wire order. The typed dictionary uses its original
zero-based entry order. -/
def select {α : Type} (dictionary : Array α) (indices : List Nat) : Except Error (List α) :=
  indices.mapM fun index =>
    match dictionary[index]? with
    | some value => .ok value
    | none => .error (.outOfBounds index)

/-- Resolve an entire width-prefixed index suffix against the local dictionary. -/
def readValues {α : Type} (limits : Hybrid.Limits) (dictionary : Array α)
    (expected : Nat) (source : Bytes) : Except Error (List α) := do
  let indices ← readIndices limits expected source
  select dictionary indices

def ValuesWire {α : Type} (limits : Hybrid.Limits) (dictionary : Array α)
    (expected : Nat) (source : Bytes) (values : List α) : Prop :=
  ∃ (width : UInt8) (runs : List UInt8) (indices : List Nat),
    source.toList = width :: runs ∧ width.toNat ≤ 32 ∧ source.length ≤ limits.bytes ∧
    expected ≤ limits.values ∧ expected < Hybrid.runLimit ∧
    Hybrid.Wire width.toNat expected runs indices ∧
    (∀ index ∈ indices, index < dictionary.size) ∧
    indices.map (fun index => dictionary[index]?) = values.map some

/-- Decode an exact flat V1 or V2 body with a caller-supplied typed dictionary.
Both dictionary data-page tags use the width-prefixed Hybrid index stream. -/
def decode {α : Type} (dictionary : Array α) (params : ScalarPage.Parameters)
    (pageLimits : ScalarPage.Limits) (indexLimits : Hybrid.Limits) (source : Bytes) :
    Except Error (List (Option α)) := do
  if params.encoding = 8 ∨ params.encoding = 2 then
    let page ← (ScalarPage.prepareFor params.encoding params pageLimits source).mapError Error.page
    let indices ← readIndices indexLimits (page.mask.count true) page.scalars
    let values ← select dictionary indices
    (FlatPage.reconstruct page.mask values).mapError Error.slots
  else throw (.unsupportedEncoding params.encoding)

end Silmaril.Formats.Parquet.DictionaryIndex
