module

public import Silmaril.Machine.DecodeGraph.Decoder.Defs
public import Silmaril.Machine.DecodeGraph.Thms
import Silmaril.Proofs.Machine.DecodeGraph.Decoder

public section

namespace Silmaril.Machine.DecodeGraph

open Silmaril.Parse.DecodeGraph

variable {Context Source : Type*}

theorem ofDecoder_deterministic (decoder : Decoder Source) :
    Deterministic (ofDecoder (Context := Context) decoder) := Proofs.ofDecoder_deterministic decoder

theorem ofDecoder_positive (decoder : Decoder Source) : Positive (ofDecoder (Context := Context) decoder) := by
  rintro input instr _ ⟨_, width, decoded, rfl⟩
  exact Nat.lt_add_of_pos_right (decoder.decode_length_pos decoded)

/-- On a valid reference window the unchanged decoder succeeds exactly for
segments it consumes in full. The list conversion stays in this adapter. -/
theorem ofDecoder_exact (decoder : Decoder Source) : ofDecoder (Context := Context) decoder =
    ofGrammar (fun _ span value => decoder.decode (span.map UInt8.toBitVec) = some (value, span.length)) :=
  Proofs.ofDecoder_exact decoder

/-- Each factored block refines sequential decoding on its claimed prefix;
the converse need not hold, because sequential decoding can lack a terminator. -/
theorem blocks_subset_sequentialPrefixes (decoder : Decoder Source) (ends : Context → Nat → Source → Prop)
    (fuel : Nat) : blocks (ofDecoder decoder) ends fuel ⊆ sequentialPrefixes decoder fuel :=
  Proofs.blocks_subset_sequentialPrefixes decoder ends fuel

end Silmaril.Machine.DecodeGraph
