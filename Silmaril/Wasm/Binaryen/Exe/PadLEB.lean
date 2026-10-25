module

public import Silmaril.Wasm.Binaryen.Exe.EncodeBaseSound

@[expose] public section

/-! # Padded LEB128

Linkers write relocatable immediates (call indices, `i32.const` addresses, memory
offsets) as LEB128 padded to their maximal width: `80 80 84 80 00` for `65536`, whose
minimal encoding is `80 80 04`. The binary grammar allows these encodings (`UN`/`SN`
admit up to `⌈N/7⌉` bytes), so the padded encoder of `EncodePadded.lean` may emit them.

`padU n w`/`padS i w` write `n`/`i` in at least `w` bytes (exactly `w` when the minimal
encoding fits). `padU_sound`/`padS_sound` prove them against `UN N`/`SN N` for every
width up to `⌈N/7⌉`; the padded emitters cap the requested width there, so the width
is untrusted (it is read from the input being matched).
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core

/-- Unsigned LEB128 of `n` in at least `w` bytes. -/
def padU (n w : Nat) : List UInt8 :=
  if n < 0x80 ∧ w ≤ 1 then [UInt8.ofNat n]
  else UInt8.ofNat (n % 0x80 + 0x80) :: padU (n / 0x80) (w - 1)
termination_by n + w
decreasing_by omega

/-- Signed LEB128 of `i` in at least `w` bytes. -/
def padS (i : Int) (w : Nat) : List UInt8 :=
  if -64 ≤ i ∧ i < 64 ∧ w ≤ 1 then [UInt8.ofNat (i % 128).toNat]
  else UInt8.ofNat (i % 128 + 128).toNat :: padS (i / 128) (w - 1)
termination_by i.natAbs + w
decreasing_by omega

/-- The length of the LEB128 at `pos` of `b` (at most 10 bytes; `0` past the end). -/
def lebLen (b : ByteArray) (pos : Nat) : Nat :=
  go 0
where
  go (k : Nat) : Nat :=
    if k < 10 ∧ pos + k < b.size then
      if b[pos + k]! < 0x80 then k + 1 else go (k + 1)
    else k
  termination_by 10 - k

/-- A `u32` in the width of the LEB128 at `pos` of `hint` (capped at 5 bytes). -/
def padU32 (hint : ByteArray) (pos n : Nat) : List UInt8 := padU n (min (lebLen hint pos) 5)

/-- An index in the width of the LEB128 at `pos` of `hint`. -/
def padIdx {k : IndexKind} (hint : ByteArray) (pos : Nat) (x : Idx k) : List UInt8 :=
  padU32 hint pos x.toNat

/-- An `iN` constant (`N` = 32 or 64) in the width of the LEB128 at `pos` of `hint`. -/
def padIN (hint : ByteArray) (pos N : Nat) (i : Int) : List UInt8 :=
  padS i (min (lebLen hint pos) ((N + 6) / 7))

private theorem u8_toNat {k : Nat} (hk : k < 256) : (UInt8.ofNat k).toNat = k :=
  UInt8.toNat_ofNat_of_lt' hk

theorem padU_sound {N n w : Nat} (h : n < 2 ^ N) (hw : 7 * (w - 1) < N) :
    UN N (padU n w) n := by
  rw [padU]
  split
  · next hs =>
    have e : (UInt8.ofNat n).toNat = n := u8_toNat (by omega)
    have := UN.byte (N := N) (UInt8.ofNat n) (by rw [e]; simp only [Nat.reducePow]; omega)
      (by rw [e]; exact h)
    rwa [e] at this
  · next hs =>
    have hN7 : 7 < N := by
      by_cases hn : n < 0x80
      · omega
      · apply Nat.lt_of_not_le
        intro hc
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) hc
        simp only [Nat.reducePow] at this
        omega
    have e2 : 2 ^ N = 2 ^ (N - 7) * 2 ^ 7 := by
      rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
    have hb : UN (N - 7) (padU (n / 0x80) (w - 1)) (n / 0x80) :=
      padU_sound (by rw [e2] at h; simp only [Nat.reducePow] at h; omega) (by omega)
    have e : (UInt8.ofNat (n % 0x80 + 0x80)).toNat = n % 0x80 + 0x80 := u8_toNat (by omega)
    have := UN.cont (UInt8.ofNat (n % 0x80 + 0x80)) (by rw [e]; simp only [Nat.reducePow]; omega)
      hN7 hb
    have hv : 2 ^ 7 * (n / 0x80) + ((UInt8.ofNat (n % 0x80 + 0x80)).toNat - 2 ^ 7) = n := by
      rw [e]; simp only [Nat.reducePow]; omega
    rwa [hv] at this
termination_by n + w
decreasing_by omega

theorem padS_sound {N : Nat} {i : Int} {w : Nat} (hlo : -(2 ^ (N - 1) : Int) ≤ i)
    (hhi : i < 2 ^ (N - 1)) (hN : 0 < N) (hw : 7 * (w - 1) < N) : SN N (padS i w) i := by
  have hP : ((2 ^ (N - 1) : Nat) : Int) = (2 : Int) ^ (N - 1) := by simp
  rw [padS]
  split
  · next hs =>
    have h1 : (((i % 128).toNat : Nat) : Int) = i % 128 :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
    have e : (UInt8.ofNat (i % 128).toNat).toNat = (i % 128).toNat := u8_toNat (by omega)
    by_cases hi : 0 ≤ i
    · have := SN.pos (N := N) (UInt8.ofNat (i % 128).toNat)
        (by rw [e]; simp only [Nat.reducePow]; omega) (by rw [e]; omega)
      have hv : (((UInt8.ofNat (i % 128).toNat).toNat : Nat) : Int) = i := by rw [e]; omega
      rwa [hv] at this
    · have := SN.neg (N := N) (UInt8.ofNat (i % 128).toNat)
        (by rw [e]; simp only [Nat.reducePow]; omega) (by rw [e]; simp only [Nat.reducePow]; omega)
        (by rw [e]; simp only [Int.reducePow]; omega)
      have hv : (((UInt8.ofNat (i % 128).toNat).toNat : Nat) : Int) - 2 ^ 7 = i := by
        rw [e]; simp only [Int.reducePow]; omega
      rwa [hv] at this
  · next hs =>
    have hN7 : 7 < N := by
      by_cases hr : -64 ≤ i ∧ i < 64
      · omega
      · apply Nat.lt_of_not_le
        intro hc
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show N - 1 ≤ 6 by omega)
        simp only [Nat.reducePow] at this
        omega
    have e2 : (2 : Int) ^ (N - 1) = 2 ^ 7 * 2 ^ (N - 7 - 1) := by
      rw [← Int.pow_add]
      congr 1
      omega
    have hb : SN (N - 7) (padS (i / 128) (w - 1)) (i / 128) :=
      padS_sound (by rw [e2] at hlo; simp only [Int.reducePow] at hlo; omega)
        (by rw [e2] at hhi; simp only [Int.reducePow] at hhi; omega) (by omega) (by omega)
    have h1 : (((i % 128 + 128).toNat : Nat) : Int) = i % 128 + 128 :=
      Int.toNat_of_nonneg (by omega)
    have e : (UInt8.ofNat (i % 128 + 128).toNat).toNat = (i % 128 + 128).toNat :=
      u8_toNat (by omega)
    have := SN.cont (UInt8.ofNat (i % 128 + 128).toNat)
      (by rw [e]; simp only [Nat.reducePow]; omega) hN7 hb
    have hv : (2 : Int) ^ 7 * (i / 128) +
        ((((UInt8.ofNat (i % 128 + 128).toNat).toNat : Nat) : Int) - 2 ^ 7) = i := by
      rw [e]; simp only [Int.reducePow]; omega
    rwa [hv] at this
termination_by i.natAbs + w
decreasing_by omega

theorem padU32_sound (hint : ByteArray) (pos : Nat) {n : Nat} (h : n < 2 ^ 32) :
    U32 (padU32 hint pos n) n :=
  padU_sound h (by omega)

theorem padIdx_sound {k : IndexKind} (hint : ByteArray) (pos : Nat) (x : Idx k) :
    Index (padIdx hint pos x) x :=
  padU32_sound hint pos x.value.isLt

/-- A padded `iN` constant: signed LEB128 of the two's-complement value. -/
theorem padIN_sound (hint : ByteArray) (pos : Nat) {w : Nat} (hw : 0 < w) (b : BitVec w) :
    IN w (padIN hint pos w b.toInt) b := by
  have := IN.mk (padS_sound (N := w) (w := min (lebLen hint pos) ((w + 6) / 7))
    (BitVec.le_toInt b) BitVec.toInt_lt hw (by omega))
  rwa [BitVec.ofInt_toInt] at this

end Silmaril.Wasm.Binaryen.Exe
