module

public import Silmaril.Parse.ByteParse.Defs
public import Silmaril.Parse.DecodeGraph.Defs
public import Silmaril.Prelude.Bytes.Defs

/-! # Optional ByteParse adapter for cursor reads on KBytes -/

@[expose] public section

namespace Silmaril.Parse.DecodeGraph

def ByteView.kbytes : ByteView KBytes := ⟨KBytes.toList, fun bytes => bytes.wf = true⟩

/-- The single-byte parser on a rope. It uses direct cursor access and does not
compute the reference byte list or copy an unconsumed suffix. -/
@[inline] def kbyte (bytes : KBytes) (stop pos : Nat) : ByteParse.Res UInt8 :=
  if pos < stop then
    match bytes.get? pos with
    | some value => .ok value (pos + 1)
    | none => .err ⟨pos, .eof⟩
  else .err ⟨pos, .eof⟩

end Silmaril.Parse.DecodeGraph
