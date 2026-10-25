module

public import Silmaril.Wasm.Binaryen.Exe.EncodeBase
public import Silmaril.Wasm.Binaryen.Exe.ExceptSound
public import Silmaril.Wasm.Binary.Core.Modules

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core

/-! ## `Except` plumbing -/

theorem throw_ne_ok {ε α : Type} {e : ε} {b : α} : (throw e : Except ε α) ≠ .ok b := by
  intro h
  cases h

private theorem u8_toNat {k : Nat} (hk : k < 256) : (UInt8.ofNat k).toNat = k :=
  UInt8.toNat_ofNat_of_lt' hk

/-! ## LEB128 -/

theorem encU_sound {N n : Nat} (h : n < 2 ^ N) : UN N (encU n) n := by
  rw [encU]
  split
  · next hs =>
    have e : (UInt8.ofNat n).toNat = n := u8_toNat (by omega)
    have := UN.byte (N := N) (UInt8.ofNat n) (by rw [e]; simp only [Nat.reducePow]; omega)
      (by rw [e]; exact h)
    rwa [e] at this
  · next hs =>
    have hN7 : 7 < N := by
      apply Nat.lt_of_not_le
      intro hc
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) hc
      simp only [Nat.reducePow] at this
      omega
    have e2 : 2 ^ N = 2 ^ (N - 7) * 2 ^ 7 := by
      rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
    have hb : UN (N - 7) (encU (n / 0x80)) (n / 0x80) :=
      encU_sound (by rw [e2] at h; simp only [Nat.reducePow] at h; omega)
    have e : (UInt8.ofNat (n % 0x80 + 0x80)).toNat = n % 0x80 + 0x80 := u8_toNat (by omega)
    have := UN.cont (UInt8.ofNat (n % 0x80 + 0x80)) (by rw [e]; simp only [Nat.reducePow]; omega)
      hN7 hb
    have hv : 2 ^ 7 * (n / 0x80) + ((UInt8.ofNat (n % 0x80 + 0x80)).toNat - 2 ^ 7) = n := by
      rw [e]; simp only [Nat.reducePow]; omega
    rwa [hv] at this
termination_by n
decreasing_by omega

theorem encS_sound {N : Nat} {i : Int} (hlo : -(2 ^ (N - 1) : Int) ≤ i)
    (hhi : i < 2 ^ (N - 1)) (hN : 0 < N) : SN N (encS i) i := by
  have hP : ((2 ^ (N - 1) : Nat) : Int) = (2 : Int) ^ (N - 1) := by simp
  rw [encS]
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
      apply Nat.lt_of_not_le
      intro hc
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show N - 1 ≤ 6 by omega)
      simp only [Nat.reducePow] at this
      omega
    have e2 : (2 : Int) ^ (N - 1) = 2 ^ 7 * 2 ^ (N - 7 - 1) := by
      rw [← Int.pow_add]
      congr 1
      omega
    have hb : SN (N - 7) (encS (i / 128)) (i / 128) :=
      encS_sound (by rw [e2] at hlo; simp only [Int.reducePow] at hlo; omega)
        (by rw [e2] at hhi; simp only [Int.reducePow] at hhi; omega) (by omega)
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
termination_by i.natAbs
decreasing_by omega

theorem encU32_sound {n : Nat} {b : List UInt8} (h : encU32 n = .ok b) : U32 b n := by
  unfold encU32 at h
  split at h
  · next hn =>
    cases Except.ok.inj h
    exact encU_sound hn
  · exact absurd h throw_ne_ok

theorem encIdx_sound {k : IndexKind} (x : Idx k) : Index (encIdx x) x :=
  encU_sound x.value.isLt

/-- An `iN` constant: signed LEB128 of the two's-complement value. -/
theorem in_toInt {w : Nat} (hw : 0 < w) (b : BitVec w) : IN w (encS b.toInt) b := by
  have := IN.mk (encS_sound (N := w) (BitVec.le_toInt b) BitVec.toInt_lt hw)
  rwa [BitVec.ofInt_toInt] at this

/-! ## Vectors, sections, names -/

theorem encList_sound {α β : Type} {f : α → Except String (List UInt8)}
    {G : Bytes → β → Prop} {g : α → β} :
    ∀ {xs : List α} {bs : List UInt8}, (∀ x ∈ xs, ∀ b, f x = .ok b → G b (g x)) →
      encList f xs = .ok bs → Seq G bs (xs.map g)
  | [], bs, _, h => by
    simp only [encList] at h
    cases Except.ok.inj h
    exact Seq.nil
  | x :: xs, bs, hf, h => by
    simp only [encList] at h
    obtain ⟨a, ha, h⟩ := bind_ok h
    obtain ⟨b, hb, h⟩ := bind_ok h
    cases Except.ok.inj h
    exact Seq.cons (hf x List.mem_cons_self a ha)
      (encList_sound (fun y hy => hf y (List.mem_cons_of_mem _ hy)) hb)

theorem encVec_sound {α β : Type} {f : α → Except String (List UInt8)}
    {G : Bytes → β → Prop} {g : α → β} {xs : List α} {bs : List UInt8}
    (hf : ∀ x ∈ xs, ∀ b, f x = .ok b → G b (g x)) (h : encVec f xs = .ok bs) :
    Vec G bs (xs.map g) := by
  unfold encVec at h
  obtain ⟨a, ha, h⟩ := bind_ok h
  obtain ⟨b, hb, h⟩ := bind_ok h
  cases Except.ok.inj h
  exact Vec.mk (by rw [List.length_map]; exact encU32_sound ha) (encList_sound hf hb)

theorem encVec_sound_id {α : Type} {f : α → Except String (List UInt8)}
    {G : Bytes → α → Prop} {xs : List α} {bs : List UInt8}
    (hf : ∀ x ∈ xs, ∀ b, f x = .ok b → G b x) (h : encVec f xs = .ok bs) : Vec G bs xs := by
  have := encVec_sound (g := id) hf h
  rwa [List.map_id] at this

theorem encSection_sound {α : Type} {G : Bytes → List α → Prop} {n : UInt8} {count : Nat}
    {body bs : List UInt8} {xs : List α} (hG : count ≠ 0 → G body xs)
    (hc : count = 0 → xs = []) (h : encSection n count body = .ok bs) : Section n G bs xs := by
  unfold encSection at h
  split at h
  · next h0 =>
    cases Except.ok.inj h
    rw [hc h0]
    exact Section.empty
  · next h0 =>
    obtain ⟨a, ha, h⟩ := bind_ok h
    cases Except.ok.inj h
    exact Section.mk (encU32_sound ha) rfl (hG h0)

theorem seq_byte : ∀ bs : List UInt8, Seq Byte bs bs
  | [] => Seq.nil
  | b :: bs => Seq.cons (Byte.mk b) (seq_byte bs)

theorem encName_sound {s : String} {bs : List UInt8} (h : encName s = .ok bs) : Name bs s := by
  unfold encName at h
  obtain ⟨a, ha, h⟩ := bind_ok h
  cases Except.ok.inj h
  exact Name.mk (Vec.mk (encU32_sound ha) (seq_byte _)) (Utf8.toUTF8 s)

end Silmaril.Wasm.Binaryen.Exe
