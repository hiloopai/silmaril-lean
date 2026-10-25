module

public import Silmaril.Wasm.Binary.Extensions.LegacyExceptions.DecodeInstructions
public import Silmaril.Wasm.Binary.Extensions.BinaryenMemory.DecodeInstructionsSound
public import Silmaril.Wasm.Binary.Extensions.Structured.DecodeDelimitedSound

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.LegacyExceptions.Decode

open Core Core.Decode

theorem readHandlers_sound
    (reader : Nat → DecodeM Wasm.Extensions.LegacyExceptions.Leaf)
    (hreader : ∀ op : UInt8, Sound (fun pre i => Leaf Forms.all ([op] ++ pre) i) (reader op.toNat))
    (fuel : Nat) (term : UInt8) :
    Sound (fun pre r => Handlers Forms.all ([term] ++ pre) r) (readHandlers reader fuel term) := by
  induction fuel generalizing term with
  | zero => intro c a c' h; exact (decodeError_ok h).elim
  | succ fuel ih =>
    intro c a c' h
    simp only [readHandlers] at h
    split at h
    · next ht =>
      have ht : term = 0x0b := by simpa using ht
      subst term
      obtain ⟨rfl, rfl⟩ := run_pure_ok h
      exact ⟨rfl, [], by simp, .end_⟩
    · split at h
      · next ht =>
        have ht : term = 0x07 := by simpa using ht
        subst term
        obtain ⟨tag, ct, ht, h⟩ := run_bind_ok h
        obtain ⟨hbt, bt, hrt, hgt⟩ := readIdx_sound ht
        obtain ⟨⟨body, next⟩, cb, hb, h⟩ := run_bind_ok h
        obtain ⟨hbb, bb, hrb, _, bodyBytes, rfl, hgb⟩ :=
          Structured.Decode.readSeqUntil_sound reader hreader [0x07, 0x19, 0x0b] fuel hb
        obtain ⟨⟨catches, all⟩, cr, hr, h⟩ := run_bind_ok h
        obtain ⟨hbr, rest, hrr, hgr⟩ := ih next hr
        obtain ⟨rfl, rfl⟩ := run_pure_ok h
        refine ⟨hbr.trans (hbb.trans hbt), bt ++ bodyBytes ++ [next] ++ rest, ?_, ?_⟩
        · simp [hrt, hrb, hrr, List.append_assoc]
        · simpa only [List.append_assoc] using Handlers.catch_ hgt hgb hgr
      · split at h
        · next ht =>
          have ht : term = 0x19 := by simpa using ht
          subst term
          obtain ⟨⟨body, next⟩, cb, hb, h⟩ := run_bind_ok h
          obtain ⟨hbb, bb, hrb, hnext, bodyBytes, rfl, hgb⟩ :=
            Structured.Decode.readSeqUntil_sound reader hreader [0x0b] fuel hb
          have hnext : next = 0x0b := by simpa using hnext
          subst next
          obtain ⟨rfl, rfl⟩ := run_pure_ok h
          exact ⟨hbb, bodyBytes ++ [0x0b], hrb, by
            simpa only [List.append_assoc] using Handlers.catchAll hgb⟩
        · exact (decodeError_ok h).elim

theorem readLeaf_sound (fuel : Nat) (op : UInt8) :
    Sound (fun pre i => Leaf Forms.all ([op] ++ pre) i) (readLeaf fuel op.toNat) := by
  induction fuel generalizing op with
  | zero => intro c a c' h; exact (decodeError_ok h).elim
  | succ fuel ih =>
    intro c a c' h
    simp only [readLeaf] at h
    split at h
    · next hop =>
      have hop : op = 0x06 := UInt8.toNat_inj.mp (by simpa using hop)
      subst op
      obtain ⟨type, ct, ht, h⟩ := run_bind_ok h
      obtain ⟨hbt, bt, hrt, hgt⟩ := readBlockType_sound ht
      obtain ⟨⟨body, term⟩, cb, hb, h⟩ := run_bind_ok h
      obtain ⟨hbb, bb, hrb, _, bodyBytes, rfl, hgb⟩ :=
        Structured.Decode.readSeqUntil_sound (readLeaf fuel) ih [0x07, 0x19, 0x18, 0x0b] fuel hb
      dsimp only at h
      split at h
      · next he =>
        have he : term = 0x18 := by simpa using he
        subst term
        obtain ⟨label, cl, hl, h⟩ := run_bind_ok h
        obtain ⟨hbl, bl, hrl, hgl⟩ := readIdx_sound hl
        obtain ⟨rfl, rfl⟩ := run_pure_ok h
        refine ⟨hbl.trans (hbb.trans hbt), bt ++ bodyBytes ++ [0x18] ++ bl, ?_, ?_⟩
        · simp [hrt, hrb, hrl, List.append_assoc]
        · simpa only [List.append_assoc] using Leaf.delegate hgt hgb hgl
      · obtain ⟨⟨catches, all⟩, cr, hr, h⟩ := run_bind_ok h
        obtain ⟨hbr, rest, hrr, hgr⟩ := readHandlers_sound (readLeaf fuel) ih fuel term hr
        obtain ⟨rfl, rfl⟩ := run_pure_ok h
        refine ⟨hbr.trans (hbb.trans hbt), bt ++ bodyBytes ++ [term] ++ rest, ?_, ?_⟩
        · simp [hrt, hrb, hrr, List.append_assoc]
        · simpa only [List.append_assoc] using Leaf.try_ hgt hgb hgr
    · split at h
      · next hop =>
        have hop : op = 0x09 := UInt8.toNat_inj.mp (by simpa using hop)
        subst op
        exact sound_map readIdx_sound Wasm.Extensions.LegacyExceptions.Leaf.rethrow
          (fun _ _ hg => .rethrow hg) h
      · exact sound_map (BinaryenMemory.Decode.readLeaf_sound op) Wasm.Extensions.LegacyExceptions.Leaf.base
          (fun _ _ hg => .base hg) h

theorem readExpr_sound : Sound (Expr Forms.all) readExpr := by
  intro c a c' h
  unfold readExpr at h
  obtain ⟨n, cn, hn, h⟩ := run_bind_ok h
  have hc : cn = c := by
    change Except.ok (_, c) = Except.ok (n, cn) at hn
    exact (Prod.mk.inj (Except.ok.inj hn)).2.symm
  subst cn
  exact Structured.Decode.readExpr_sound (readLeaf (n + 1)) (readLeaf_sound (n + 1)) h

end Silmaril.Wasm.Binary.Extensions.LegacyExceptions.Decode
