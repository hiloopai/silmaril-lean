module

public import Silmaril.Net.Wire.Defs

/-!
# Network byte order: theorems

PROVED (standard axioms):

* `rd16_be16`, `be16_rd16`: `be16` and `rd16` are mutually inverse; `rd32_be32`, `be32_rd32`
  the same for 32 bits. So a 16- or 32-bit field and its octets determine each other.
* `be16_length`, `be32_length`, `zeros_length`, `be16_inj`, `be32_inj`.
-/

@[expose] public section

namespace Silmaril.Net.Wire

theorem u8_toNat_ofNat (n : Nat) : (UInt8.ofNat n).toNat = n % 256 := by
  simp

theorem u16_toNat_ofNat (n : Nat) : (UInt16.ofNat n).toNat = n % 65536 := by
  simp

theorem u32_toNat_ofNat (n : Nat) : (UInt32.ofNat n).toNat = n % 4294967296 := by
  simp

@[simp] theorem be16_length (x : UInt16) : (be16 x).length = 2 := rfl

@[simp] theorem be32_length (x : UInt32) : (be32 x).length = 4 := rfl

@[simp] theorem zeros_length (n : Nat) : (zeros n).length = n := by simp [zeros]

theorem rd16_toNat (a b : UInt8) : (rd16 a b).toNat = a.toNat * 256 + b.toNat := by
  have ha : a.toNat < 256 := a.toNat_lt
  have hb : b.toNat < 256 := b.toNat_lt
  rw [rd16, u16_toNat_ofNat]
  omega

/-- Reading the octets of `x` gives `x` back. -/
@[simp] theorem rd16_be16 (x : UInt16) :
    rd16 (UInt8.ofNat (x.toNat / 256)) (UInt8.ofNat (x.toNat % 256)) = x := by
  have hx : x.toNat < 65536 := x.toNat_lt
  apply UInt16.toNat_inj.mp
  rw [rd16_toNat, u8_toNat_ofNat, u8_toNat_ofNat]
  omega

/-- The octets of a field read from `a`, `b` are `a`, `b`. -/
theorem be16_rd16 (a b : UInt8) : be16 (rd16 a b) = [a, b] := by
  have ha : a.toNat < 256 := a.toNat_lt
  have hb : b.toNat < 256 := b.toNat_lt
  have h1 : UInt8.ofNat ((rd16 a b).toNat / 256) = a := by
    apply UInt8.toNat_inj.mp
    rw [u8_toNat_ofNat, rd16_toNat]
    omega
  have h2 : UInt8.ofNat ((rd16 a b).toNat % 256) = b := by
    apply UInt8.toNat_inj.mp
    rw [u8_toNat_ofNat, rd16_toNat]
    omega
  rw [be16, h1, h2]

theorem rd32_toNat (a b c d : UInt8) :
    (rd32 a b c d).toNat = a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat := by
  have ha : a.toNat < 256 := a.toNat_lt
  have hb : b.toNat < 256 := b.toNat_lt
  have hc : c.toNat < 256 := c.toNat_lt
  have hd : d.toNat < 256 := d.toNat_lt
  rw [rd32, u32_toNat_ofNat]
  omega

/-- Reading the octets of `x` gives `x` back. -/
@[simp] theorem rd32_be32 (x : UInt32) :
    rd32 (UInt8.ofNat (x.toNat / 16777216)) (UInt8.ofNat (x.toNat / 65536 % 256))
      (UInt8.ofNat (x.toNat / 256 % 256)) (UInt8.ofNat (x.toNat % 256)) = x := by
  have hx : x.toNat < 4294967296 := x.toNat_lt
  apply UInt32.toNat_inj.mp
  rw [rd32_toNat, u8_toNat_ofNat, u8_toNat_ofNat, u8_toNat_ofNat, u8_toNat_ofNat]
  omega

/-- The octets of a field read from `a b c d` are `a b c d`. -/
theorem be32_rd32 (a b c d : UInt8) : be32 (rd32 a b c d) = [a, b, c, d] := by
  have ha : a.toNat < 256 := a.toNat_lt
  have hb : b.toNat < 256 := b.toNat_lt
  have hc : c.toNat < 256 := c.toNat_lt
  have hd : d.toNat < 256 := d.toNat_lt
  have hv : (rd32 a b c d).toNat = a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat :=
    rd32_toNat a b c d
  have h1 : UInt8.ofNat ((rd32 a b c d).toNat / 16777216) = a := by
    apply UInt8.toNat_inj.mp; rw [u8_toNat_ofNat, hv]; omega
  have h2 : UInt8.ofNat ((rd32 a b c d).toNat / 65536 % 256) = b := by
    apply UInt8.toNat_inj.mp; rw [u8_toNat_ofNat, hv]; omega
  have h3 : UInt8.ofNat ((rd32 a b c d).toNat / 256 % 256) = c := by
    apply UInt8.toNat_inj.mp; rw [u8_toNat_ofNat, hv]; omega
  have h4 : UInt8.ofNat ((rd32 a b c d).toNat % 256) = d := by
    apply UInt8.toNat_inj.mp; rw [u8_toNat_ofNat, hv]; omega
  rw [be32, h1, h2, h3, h4]

theorem be16_inj {x y : UInt16} (h : be16 x = be16 y) : x = y := by
  have hx : rd16 (UInt8.ofNat (x.toNat / 256)) (UInt8.ofNat (x.toNat % 256)) = x := rd16_be16 x
  have hy : rd16 (UInt8.ofNat (y.toNat / 256)) (UInt8.ofNat (y.toNat % 256)) = y := rd16_be16 y
  simp only [be16, List.cons.injEq, and_true] at h
  rw [← hx, ← hy, h.1, h.2]

theorem be32_inj {x y : UInt32} (h : be32 x = be32 y) : x = y := by
  have hx := rd32_be32 x
  have hy := rd32_be32 y
  simp only [be32, List.cons.injEq, and_true] at h
  rw [← hx, ← hy, h.1, h.2.1, h.2.2.1, h.2.2.2]

/-- The value of a 16-bit field from its octets. -/
theorem be16_toNat (x : UInt16) :
    (UInt8.ofNat (x.toNat / 256)).toNat * 256 + (UInt8.ofNat (x.toNat % 256)).toNat = x.toNat := by
  have hx : x.toNat < 65536 := x.toNat_lt
  rw [u8_toNat_ofNat, u8_toNat_ofNat]
  omega

end Silmaril.Net.Wire
