module

public import Silmaril.Wasm.Binary.Extensions.Structured.DecodeDelimited
public import Silmaril.Wasm.Binary.Extensions.Structured.DecodeSound

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.Structured.Decode

open Core Core.Decode

theorem readSeqUntil_sound {Leaf : Type} {G : Bytes → Leaf → Prop}
    (reader : Nat → DecodeM Leaf)
    (hreader : ∀ op : UInt8, Sound (fun pre i => G ([op] ++ pre) i) (reader op.toNat))
    (stops : List UInt8) (fuel : Nat) :
    Sound (fun pre (r : List (Wasm.Extensions.Structured.Instr Leaf) × UInt8) =>
      r.2 ∈ stops ∧ ∃ b, pre = b ++ [r.2] ∧ Instrs Forms.all G b r.1) (readSeqUntil reader stops fuel) := by
  induction fuel with
  | zero => intro c a c' h; exact (decodeError_ok h).elim
  | succ fuel ih =>
    intro c a c' h
    simp only [readSeqUntil] at h
    obtain ⟨b, cm, hb, h⟩ := run_bind_ok h
    obtain ⟨hbb, hrb⟩ := readByte_ok hb
    split at h
    · next hstop =>
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      exact ⟨hbb, [b], hrb, hstop, [], rfl, .nil⟩
    · obtain ⟨i, ci, hi, h⟩ := run_bind_ok h
      obtain ⟨⟨is, term⟩, ce, hs, h⟩ := run_bind_ok h
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      obtain ⟨hbi, bi, hri, hgi⟩ := (readInstr_readSeq_sound reader hreader fuel).1 b hi
      obtain ⟨hbs, bs, hrs, hterm, bodyBytes, rfl, hgbody⟩ := ih hs
      refine ⟨hbs.trans (hbi.trans hbb), [b] ++ bi ++ (bodyBytes ++ [term]), ?_,
        hterm, [b] ++ bi ++ bodyBytes, ?_, .cons hgi hgbody⟩
      · simp [hrb, hri, hrs, List.append_assoc]
      · simp [List.append_assoc]

end Silmaril.Wasm.Binary.Extensions.Structured.Decode
