module

public import Silmaril.Crypto.Catalog.Defs

@[expose] public section

/-!
# The algorithm catalogue: theorems

* `implemented_iff`: an algorithm is `implemented` exactly when it is a hash for which `hashImpl`
  has a function, so the catalogue cannot claim an implementation that does not exist;
* `refinement_iff`: only SHA-256 has a machine-code refinement;
* `refinement_implies_implemented`: refinement evidence is only recorded for implemented
  algorithms (but not conversely, and neither implies security);
* `vectors_ok`: every catalogued vector is reproduced by `hashImpl` (checked by the kernel);
* `hashImpl_length`: the implementations return digests of the catalogued length.
-/

namespace Silmaril.Crypto.Catalog

theorem implemented_iff (a : Algorithm) :
    a.evidence.implemented = true ↔ ∃ h, a = .hash h ∧ (hashImpl h).isSome = true := by
  cases a <;> simp [Algorithm.evidence]

theorem refinement_iff (a : Algorithm) : a.evidence.refinement = true ↔ a = .hash .sha256 := by
  cases a with
  | hash h => cases h <;> simp [Algorithm.evidence, hasRefinement]
  | _ => simp [Algorithm.evidence]

theorem refinement_implies_implemented (a : Algorithm) (h : a.evidence.refinement = true) :
    a.evidence.implemented = true := by
  rw [refinement_iff] at h; subst h; rfl

theorem hashImpl_length {h : HashAlg} {f : List UInt8 → List UInt8} (hf : hashImpl h = some f)
    (msg : List UInt8) : some (f msg).length = h.digestLen := by
  cases h <;> simp [hashImpl] at hf <;> subst hf <;> rfl

theorem vectors_ok : ∀ v ∈ vectors, (hashImpl v.alg).map (· v.input) = some v.digest := by
  decide +kernel

end Silmaril.Crypto.Catalog
