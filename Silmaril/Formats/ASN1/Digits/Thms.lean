module

public import Silmaril.Formats.ASN1.Digits.Defs
import Silmaril.Proofs.Formats.ASN1.Digits

/-!
# ASN.1: big-endian digit strings, laws

* `ofDigitsBE_digitsBE`, `digitsBE_ofDigitsBE`: minimal digits and their value
  are mutually inverse on digit lists without a leading zero;
* `beNat_beBytes`, `beBytes_beNat`: the same for base-256 octets;
* `base128Octets_iff`: the transcription of X.690 §8.1.2.4.2/§8.19.2 has
  exactly one spelling of each number, `base128 n`;
* `readBase128_eq_some`: the reader accepts exactly `base128 n` followed by
  anything.
-/

@[expose] public section

namespace Silmaril.Formats.ASN1

/-! ## Generic digits -/

theorem ofDigitsBE_append_singleton (b : Nat) (l : List Nat) (d : Nat) :
    ofDigitsBE b (l ++ [d]) = ofDigitsBE b l * b + d :=
  Proofs.Formats.ASN1.ofDigitsBE_append_singleton b l d

theorem digitsBE_eq_nil_iff {b n : Nat} (hb : 1 < b) : digitsBE b n = [] ↔ n = 0 :=
  Proofs.Formats.ASN1.digitsBE_eq_nil_iff hb

theorem ofDigitsBE_digitsBE {b : Nat} (hb : 1 < b) (n : Nat) :
    ofDigitsBE b (digitsBE b n) = n :=
  Proofs.Formats.ASN1.ofDigitsBE_digitsBE hb n

theorem lt_of_mem_digitsBE {b n d : Nat} (hb : 1 < b) (h : d ∈ digitsBE b n) : d < b :=
  Proofs.Formats.ASN1.lt_of_mem_digitsBE hb h

theorem head?_digitsBE_ne_zero {b : Nat} (hb : 1 < b) (n : Nat) :
    (digitsBE b n).head? ≠ some 0 :=
  Proofs.Formats.ASN1.head?_digitsBE_ne_zero hb n

theorem digitsBE_ofDigitsBE {b : Nat} (hb : 1 < b) {l : List Nat}
    (hl : ∀ d ∈ l, d < b) (h0 : l.head? ≠ some 0) : digitsBE b (ofDigitsBE b l) = l :=
  Proofs.Formats.ASN1.digitsBE_ofDigitsBE hb hl h0

/-! ## Base 256 -/

@[simp] theorem beNat_beBytes (n : Nat) : beNat (beBytes n) = n :=
  Proofs.Formats.ASN1.beNat_beBytes n

theorem beBytes_beNat {l : List UInt8} (h0 : l.head? ≠ some 0) : beBytes (beNat l) = l :=
  Proofs.Formats.ASN1.beBytes_beNat h0

theorem head?_beBytes_ne_zero (n : Nat) : (beBytes n).head? ≠ some 0 :=
  Proofs.Formats.ASN1.head?_beBytes_ne_zero n

theorem beBytes_eq_nil_iff (n : Nat) : beBytes n = [] ↔ n = 0 :=
  Proofs.Formats.ASN1.beBytes_eq_nil_iff n

/-! ## Base 128 -/

theorem base128_ne_nil (n : Nat) : base128 n ≠ [] :=
  Proofs.Formats.ASN1.base128_ne_nil n

/-- X.690 §8.1.2.4.2 / §8.19.2 determine the octets: `base128 n` is the only
spelling of `n`. -/
theorem base128Octets_iff (n : Nat) (ds : List UInt8) : Base128Octets n ds ↔ ds = base128 n :=
  Proofs.Formats.ASN1.base128Octets_iff n ds

/-- The reader is sound and complete for `base128`, whatever follows. -/
theorem readBase128_eq_some {n : Nat} {s r : List UInt8} :
    readBase128 s = some (n, r) ↔ s = base128 n ++ r :=
  Proofs.Formats.ASN1.readBase128_eq_some

end Silmaril.Formats.ASN1
