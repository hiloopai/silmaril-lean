module

public import Silmaril.Prelude.Bytes.Digits.Defs
import Silmaril.Proofs.Prelude.Bytes.Digits

/-! # Base-256 digits: theorems

Proofs are in `Silmaril.Proofs.Prelude.Bytes.Digits`.
-/

@[expose] public section

namespace Silmaril.KBytes

open Silmaril.Proofs.Prelude.Bytes

theorem length_unpack (k v : Nat) : (unpack k v).length = k :=
  Proofs.Prelude.Bytes.length_unpack k v

theorem leVal_unpack (k v : Nat) : leVal (unpack k v) = v % 256 ^ k :=
  Proofs.Prelude.Bytes.leVal_unpack k v

theorem unpack_leVal (bs : List UInt8) : unpack bs.length (leVal bs) = bs :=
  Proofs.Prelude.Bytes.unpack_leVal bs

theorem leVal_append (xs ys : List UInt8) :
    leVal (xs ++ ys) = leVal xs + 256 ^ xs.length * leVal ys :=
  Proofs.Prelude.Bytes.leVal_append xs ys

/-- Compiled code decodes leaves by divide and conquer. -/
@[csimp] theorem unpack_eq_unpackFast : @unpack = @unpackFast := by
  funext k v
  exact (unpackFast_eq k v).symm

end Silmaril.KBytes
