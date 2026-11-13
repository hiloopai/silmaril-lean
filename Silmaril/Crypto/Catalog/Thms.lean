module

public import Silmaril.Crypto.Catalog.Defs

@[expose] public section

/-!
# The algorithm catalogue: theorems

* `implemented_iff`: a hash is at least `implemented` exactly when `hashImpl` has a function
  for it, so the level cannot claim an implementation that does not exist;
* `proved_iff`: only SHA-256 is at level `proved`;
* `vectors_ok`: every catalogued vector is reproduced by `hashImpl` (checked by the kernel);
* `hashImpl_length`: the implementations return digests of the catalogued length.
-/

namespace Silmaril.Crypto.Catalog

theorem implemented_iff (h : HashAlg) :
    ((Algorithm.hash h).level = .implemented ∨ (Algorithm.hash h).level = .proved) ↔
      (hashImpl h).isSome = true := by
  cases h <;> simp [Algorithm.level, hasFunctionalProof, hashImpl]

theorem proved_iff (a : Algorithm) : a.level = .proved ↔ a = .hash .sha256 := by
  cases a with
  | hash h => cases h <;> simp [Algorithm.level, hasFunctionalProof, hashImpl]
  | _ => simp [Algorithm.level]

theorem hashImpl_length {h : HashAlg} {f : List UInt8 → List UInt8} (hf : hashImpl h = some f)
    (msg : List UInt8) : some (f msg).length = h.digestLen := by
  cases h <;> simp [hashImpl] at hf <;> subst hf <;> rfl

theorem vectors_ok : ∀ v ∈ vectors, (hashImpl v.alg).map (· v.input) = some v.digest := by
  decide +kernel

end Silmaril.Crypto.Catalog
