module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Defs

/-! Strict codec-0 TIMESTAMP with one PLAIN dictionary and only V2 references. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2

/-- Retain the original codec-0 V2 header and require the RLE_DICTIONARY tag. -/
def planData (bound : Bound) (frame : Parquet.Page.Frame) : Except DictionaryPageError DataPage := do
  if let .dictionary _ := frame.value.kind then throw .misplacedDictionary
  let .dataV2 header := frame.value.kind | throw (.parameters .unsupportedPage)
  if header.encoding ≠ 8 then throw (.encoding header.encoding)
  let params ← (Timestamp.Page.parameters bound.binding.leaf bound.levels
    Payload.Codec.uncompressed.id frame.value).mapError .parameters
  return ⟨frame, params⟩

/-- Specialize the shared CRC-checked PLAIN dictionary reader to a literal body. -/
def readEntries := Snappy.readEntriesWithCodec .uncompressed .plain

def checkGroup (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error CheckedChunk :=
  Dictionary.checkGroupUsing .dictionary limits leafLimits bound index
    (planData bound) (fun _ => .ok ()) (readEntries limits leafLimits bound)

/-- The shared body decoder takes its codec from the admitted original parameters. -/
def readGroup (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except Leaf.Error (Slots bound) :=
  Snappy.readGroupUsing limits leafLimits bound (checkGroup limits leafLimits bound index)

def readBound (limits : Dictionary.Limits) (leafLimits : Leaf.Limits) (bound : Bound) : Events.ToIpc.Source :=
  Events.readBoundWith bound (readGroup limits leafLimits bound)

/-- Emit one native Arrow batch per original footer group for the selected modern leaf. -/
def convert (limits : Dictionary.Limits) (inputLimits : Events.ToIpc.Limits)
    (outputLimits : Arrow.ObservationLimits) (input : Bytes) (ordinal : Nat) :
    Except Events.ToIpc.Error KBytes :=
  Events.ToIpc.convertGroups .modernOnly inputLimits outputLimits input ordinal
    (readGroup limits inputLimits.leaf)

end Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Uncompressed.V2
