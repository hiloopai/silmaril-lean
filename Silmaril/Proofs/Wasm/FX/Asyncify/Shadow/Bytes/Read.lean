module

public import Silmaril.Wasm.FX.Asyncify.Shadow.Bytes.Defs

/-!
# Reading records back from the byte layout

`readRec_layout`: when the cells `pre ++ enc q ++ post` have a byte layout, the record read
backwards from the address where `enc q` ends is `q`, and it starts where `pre` ends.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Shadow.Bytes

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.Models.FXAsyncPC Silmaril.Wasm.FX.Asyncify.Shadow

variable {V : Type} (C : Codec V)

theorem pad_len {k : Nat} {l : List UInt8} (h : l.length ≤ k) : (pad k l).length = k := by
  simp only [pad, List.length_append, List.length_replicate]
  omega

theorem le32_len (n : Nat) : (le32 n).length = 4 := rfl

theorem cellBytes_len {c : Cell V} {b : List UInt8} (h : cellBytes C c = some b) :
    b.length = cellWidth C c := by
  match c, h with
  | .num n, h =>
    have hb : le32 n = b := by
      by_cases hn : n < 2 ^ 32
      · simpa [cellBytes, hn] using h
      · simp [cellBytes, hn] at h
    rw [← hb]; rfl
  | .sv (.val v), h =>
    have hb : 0 :: pad (max C.w 4) (C.enc v) = b := by simpa [cellBytes] using h
    rw [← hb, List.length_cons, pad_len (by rw [C.enc_len]; omega)]
    simp only [cellWidth, Codec.sw]
    omega
  | .sv (.cont k), h =>
    have hb : 1 :: pad (max C.w 4) (le32 k) = b := by
      by_cases hk : k < 2 ^ 32
      · simpa [cellBytes, hk] using h
      · simp [cellBytes, hk] at h
    rw [← hb, List.length_cons, pad_len (by rw [le32_len]; omega)]
    simp only [cellWidth, Codec.sw]
    omega

theorem layout_cons {c : Cell V} {cs : List (Cell V)} {bs : List UInt8}
    (h : layout C (c :: cs) = some bs) :
    ∃ b r, cellBytes C c = some b ∧ layout C cs = some r ∧ bs = b ++ r := by
  unfold layout at h
  split at h
  · exact ⟨_, _, by assumption, by assumption, (Option.some.inj h).symm⟩
  · cases h

theorem layout_len : ∀ {cs : List (Cell V)} {bs : List UInt8}, layout C cs = some bs →
    bs.length = addrOf C cs
  | [], bs, h => by cases h; rfl
  | c :: cs, bs, h => by
    obtain ⟨b, r, hb, hr, rfl⟩ := layout_cons C h
    rw [List.length_append, cellBytes_len C hb, layout_len hr]
    simp [addrOf]

theorem layout_append : ∀ {a b : List (Cell V)} {bs : List UInt8}, layout C (a ++ b) = some bs →
    ∃ ba bb, layout C a = some ba ∧ layout C b = some bb ∧ bs = ba ++ bb
  | [], b, bs, h => ⟨[], bs, rfl, h, rfl⟩
  | c :: a, b, bs, h => by
    obtain ⟨x, r, hx, hr, rfl⟩ := layout_cons C h
    obtain ⟨ba, bb, ha, hb, rfl⟩ := layout_append hr
    have hl : layout C (c :: a) = some (x ++ ba) := by simp [layout, hx, ha]
    exact ⟨x ++ ba, bb, hl, hb, (List.append_assoc _ _ _).symm⟩

theorem drop_pre (pre l : List UInt8) (k : Nat) : (pre ++ l).drop (pre.length + k) = l.drop k := by
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
  congr 1
  omega

theorem rd32_at {pre post : List UInt8} {n : Nat} (hn : n < 2 ^ 32) :
    rd32 (pre ++ le32 n ++ post) pre.length = n := by
  have h := drop_pre pre (le32 n ++ post) 0
  rw [Nat.add_zero, List.drop_zero] at h
  unfold rd32
  rw [List.append_assoc, h, List.take_append_of_le_length (by simp [le32_len]),
    List.take_of_length_le (by simp [le32_len]), unle32_le32 hn]

theorem layout_sv {ops : List (SV V)} {ob : List UInt8} (h : layout C (ops.map .sv) = some ob) :
    ob.length = C.sw * ops.length := by
  rw [layout_len C h]
  simp [addrOf, cellWidth, Function.comp_def, List.map_const', Nat.mul_comm]

theorem cellBytes_num {n : Nat} {b : List UInt8} (h : cellBytes C (.num n : Cell V) = some b) :
    n < 2 ^ 32 ∧ b = le32 n := by
  by_cases hn : n < 2 ^ 32
  · exact ⟨hn, by simpa [cellBytes, hn, eq_comm] using h⟩
  · simp [cellBytes, hn] at h

theorem getElem?_pre (pre l : List UInt8) (x : UInt8) :
    (pre ++ x :: l)[pre.length]? = some x := by
  simp

theorem take_pad {k : Nat} (l post : List UInt8) :
    ((pad k l) ++ post).take l.length = l := by
  simp [pad, List.append_assoc]

theorem rdSV_val {v : V} (pre post : List UInt8) :
    rdSV C (pre ++ (0 :: pad (max C.w 4) (C.enc v)) ++ post) pre.length = some (.val v) := by
  have h0 : (pre ++ (0 :: pad (max C.w 4) (C.enc v)) ++ post)[pre.length]? = some 0 := by simp
  have hd : (pre ++ (0 :: pad (max C.w 4) (C.enc v)) ++ post).drop (pre.length + 1) =
      pad (max C.w 4) (C.enc v) ++ post := by
    rw [List.append_assoc, drop_pre]
    rfl
  have ht : (pad (max C.w 4) (C.enc v) ++ post).take C.w = C.enc v := by
    have := take_pad (k := max C.w 4) (C.enc v) post
    rwa [C.enc_len] at this
  unfold rdSV
  rw [h0, hd, ht, C.dec_enc]
  rfl

theorem rdSV_cont {k : Nat} (hk : k < 2 ^ 32) (pre post : List UInt8) :
    rdSV C (pre ++ (1 :: pad (max C.w 4) (le32 k)) ++ post) pre.length = some (.cont k) := by
  have h1 : (pre ++ (1 :: pad (max C.w 4) (le32 k)) ++ post)[pre.length]? = some 1 := by simp
  have he : pre ++ (1 :: pad (max C.w 4) (le32 k)) ++ post =
      (pre ++ [1]) ++ le32 k ++ (List.replicate (max C.w 4 - (le32 k).length) 0 ++ post) := by
    simp [pad]
  have hr : rd32 (pre ++ (1 :: pad (max C.w 4) (le32 k)) ++ post) (pre.length + 1) = k := by
    rw [he, show pre.length + 1 = (pre ++ [1]).length by simp]
    exact rd32_at hk
  unfold rdSV
  rw [h1, hr]
  rfl

/-- The slot of a stored value reads back as that value. -/
theorem rdSV_at {x : SV V} {b : List UInt8} (h : cellBytes C (.sv x) = some b)
    (pre post : List UInt8) : rdSV C (pre ++ b ++ post) pre.length = some x := by
  cases x with
  | val v =>
    have hb : 0 :: pad (max C.w 4) (C.enc v) = b := by simpa [cellBytes] using h
    exact hb ▸ rdSV_val C pre post
  | cont k =>
    have hk : k < 2 ^ 32 := by
      by_cases hn : k < 2 ^ 32
      · exact hn
      · simp [cellBytes, hn] at h
    have hb : 1 :: pad (max C.w 4) (le32 k) = b := by simpa [cellBytes, hk] using h
    exact hb ▸ rdSV_cont C hk pre post

/-- The slots of stored values read back as those values. -/
theorem rdVals_at : ∀ {ops : List (SV V)} {ob : List UInt8} (pre post : List UInt8),
    layout C (ops.map .sv) = some ob → rdVals C (pre ++ ob ++ post) pre.length ops.length = some ops
  | [], ob, pre, post, h => by cases h; rfl
  | x :: xs, ob, pre, post, h => by
    obtain ⟨b, r, hb, hr, rfl⟩ := layout_cons C h
    have hx : rdSV C (pre ++ (b ++ r) ++ post) pre.length = some x := by
      have := rdSV_at C hb pre (r ++ post)
      simpa [List.append_assoc] using this
    have hlen : (pre ++ b).length = pre.length + C.sw := by
      rw [List.length_append, cellBytes_len C hb]
      rfl
    have hxs : rdVals C (pre ++ (b ++ r) ++ post) (pre.length + C.sw) xs.length = some xs := by
      have := rdVals_at (pre ++ b) post hr
      rw [hlen] at this
      simpa [List.append_assoc] using this
    simp only [List.length_cons, rdVals, hx, hxs]

end Silmaril.Proofs.Wasm.FX.Asyncify.Shadow.Bytes
