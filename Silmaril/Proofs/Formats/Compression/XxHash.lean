module

public import Silmaril.Formats.Compression.XxHash.Defs

/-! Proofs for `Silmaril.Formats.Compression.XxHash.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.XxHash

open Silmaril.Formats.Compression Silmaril.Formats.Compression.XxHash

variable {σ : Type} {width : Nat} {step : σ → List UInt8 → σ}

theorem stripes_nil (hw : 0 < width) (fuel : Nat) (acc : σ) :
    stripes width step fuel acc [] = (acc, []) := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [stripes, show ¬ width ≤ 0 by omega]

/-- Appending one byte to the input of `stripes` either extends the partial
stripe or completes it. -/
theorem stripes_concat (hw : 0 < width) (b : UInt8) :
    ∀ (fuel : Nat) (acc : σ) (bytes : List UInt8), bytes.length ≤ fuel →
      stripes width step (fuel + 1) acc (bytes ++ [b]) =
        let r := stripes width step fuel acc bytes
        if width ≤ (r.2 ++ [b]).length then (step r.1 (r.2 ++ [b]), []) else (r.1, r.2 ++ [b])
  | 0, acc, bytes, h => by
    obtain rfl : bytes = [] := List.eq_nil_of_length_eq_zero (by omega)
    by_cases hw1 : width ≤ 1
    · simp [stripes, show width = 1 by omega]
    · simp [stripes, hw1]
  | fuel + 1, acc, bytes, h => by
    by_cases hb : width ≤ bytes.length
    · have hlen : (bytes.drop width).length ≤ fuel := by simp; omega
      have := stripes_concat hw b fuel (step acc (bytes.take width)) (bytes.drop width) hlen
      rw [stripes, ite_eq_left (by simp; omega), List.take_append_of_le_length hb,
        List.drop_append_of_le_length hb, this]
      simp only [stripes, ite_eq_left hb]
    · have h0 : stripes width step (fuel + 1) acc bytes = (acc, bytes) := by
        simp only [stripes, ite_eq_right hb]
      rw [h0, stripes]
      simp only [List.length_append, List.length_singleton]
      by_cases hb' : width ≤ bytes.length + 1
      · have he : (bytes ++ [b]).length = width := by simp; omega
        rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega), stripes_nil hw]
      · simp [hb']

/-- Pushing bytes one at a time computes `stripes` over the whole input. -/
theorem foldl_push (hw : 0 < width) (lanes : σ) (bytes : List UInt8) :
    bytes.foldl (Stream.push width step) (Stream.start lanes) =
      let r := stripes width step bytes.length lanes bytes
      ⟨r.1, r.2, bytes.length⟩ := by
  rw [← List.reverse_reverse bytes]
  induction bytes.reverse with
  | nil => rfl
  | cons b bytes ih =>
    rw [List.reverse_cons, List.foldl_append, ih, List.length_append, List.length_singleton,
      stripes_concat hw b _ lanes _ (Nat.le_refl _)]
    simp only [List.foldl, Stream.push]
    split <;> rfl

theorem xxh32_digest (seed : UInt32) (bytes : List UInt8) :
    (Checksum.xxh32 seed).digest bytes = xxh32 seed bytes := by
  simp only [Checksum.digest, Checksum.xxh32, foldl_push (by decide : 0 < 16), xxh32]

theorem xxh64_stream (seed : UInt64) (bytes : List UInt8) :
    let s := bytes.foldl (Stream.push 32 XXH64.stripe) (Stream.start (XXH64.init seed))
    XXH64.finish seed s.lanes s.length s.buffer = xxh64 seed bytes := by
  simp only [foldl_push (by decide : 0 < 32), xxh64]

theorem xxh64Low32_digest (seed : UInt64) (bytes : List UInt8) :
    (Checksum.xxh64Low32 seed).digest bytes = (xxh64 seed bytes).toUInt32 := by
  simp only [Checksum.digest, Checksum.xxh64Low32, foldl_push (by decide : 0 < 32), xxh64]

end Silmaril.Proofs.Formats.Compression.XxHash
