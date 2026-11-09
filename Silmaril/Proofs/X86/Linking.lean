module

public import Silmaril.X86.Linking.Defs

/-! # Proofs: byte encoding and patch success of the x86-64 relocation profile -/

@[expose] public section

namespace Silmaril.Proofs.X86.Linking

open Silmaril.Formats.ELF Silmaril.Formats.ELF.Link Silmaril.X86.Linking.Relocation

@[simp] theorem encodeLE_length (n v : Nat) : (encodeLE n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [encodeLE, ih]

/-- Byte encoding is exact for every in-range unsigned value, not just fixtures. -/
theorem decodeLE_encodeLE (n v : Nat) (fits : v < 256 ^ n) :
    decodeLE (encodeLE n v) = v := by
  induction n generalizing v with
  | zero =>
    have : v = 0 := by simpa using fits
    subst v
    rfl
  | succ n ih =>
    have quotient : v / 256 < 256 ^ n := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).2
      simpa [Nat.pow_succ, Nat.mul_comm] using fits
    simp only [encodeLE, decodeLE, BitVec.toNat_ofNat]
    rw [ih _ quotient]
    exact Nat.mod_add_div v 256

/-- The actual emitted bytes decode to the specified two's-complement residue. -/
theorem decodeLE_encoded (kind : Nat) (v : Int) :
    decodeLE (encoded kind v).toList = (v % (256 ^ width kind)).toNat := by
  simp only [encoded, List.toList_toArray]
  apply decodeLE_encodeLE
  apply (Int.toNat_lt' (Nat.pow_pos (by decide : 0 < 256))).2
  simpa using Int.emod_lt_of_pos v (Int.pow_pos (by decide : (0 : Int) < 256) :
    (0 : Int) < 256 ^ width kind)

@[simp] theorem encoded_size (kind : Nat) (v : Int) :
    (encoded kind v).size = width kind := by simp [encoded]

/-- Successful patches have the prescribed offset, width, exact arithmetic
encoding, supported kind and signedness range, and stay within their section. -/
theorem patch_spec {r : ResolvedRelocation} {bytes : Bytes} {p : Patch}
    (success : patch r bytes = .ok p) :
    supported r.kind ∧ Fits r.kind (value r) ∧
      p.offset = r.offset ∧ p.bytes = encoded r.kind (value r) ∧
      p.bytes.size = width r.kind ∧ p.offset + p.bytes.size ≤ bytes.size := by
  unfold patch at success
  split at success <;> simp_all
  split at success <;> simp_all
  split at success <;> simp_all
  split at success <;> simp_all
  subst p
  simp_all

/-- The shared linker's Option callback cannot hide a diagnostic failure. -/
theorem relocate_success {all : List ResolvedRelocation} {r : ResolvedRelocation}
    {bytes : Bytes} {p : Patch} (success : relocate all r bytes = some p) :
    patch r bytes = .ok p := by
  cases actual : patch r bytes with
  | error error => simp [relocate, actual, Except.toOption] at success
  | ok candidate =>
    have equal : candidate = p := by simpa [relocate, actual, Except.toOption] using success
    simp [equal]

end Silmaril.Proofs.X86.Linking
