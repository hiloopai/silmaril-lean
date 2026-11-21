module

public import Silmaril.Crypto.Blake3.Range.Extension.Thms
import Silmaril.Proofs.Crypto.Blake3.Range.ExtensionCounterexample

public section

namespace Silmaril.Crypto.Blake3

open Silmaril.Semantics.Naming.ByteRange (Fact)

/-- The checker accepts a nonempty range and EOF, but the opaque CV already
has a preimage with the wrong role. No collision-free extension can name a
whole at that digest, even without assuming the extension is canonical. -/
theorem blocked_opaque_cv : ∃ run digest,
    let base := Compression.graph run
    base.Canonical ∧ ¬ base.Collision ∧ Checked base 1025 digest 1024 [1] ∧ CheckedEOF base 1025 digest ∧
    ∀ extension, base.Extends extension → (¬ extension.Collision) → ∀ bytes, ¬ Named extension digest bytes :=
  Proofs.Crypto.Blake3.Range.ExtensionCounterexample.blocked

/-- The same abstract checker can accept different bytes at the same offset
when the canonical paths for the two claims diverge. -/
theorem conflicting_cross_extent : ∃ run digest,
    let base := Compression.graph run
    base.Canonical ∧ ¬ base.Collision ∧ Checked base 1025 digest 1024 [1] ∧ Checked base 2049 digest 1024 [0] ∧
    ¬ ∃ bytes, (Fact.range 1024 [1]).Holds bytes ∧ (Fact.range 1024 [0]).Holds bytes :=
  Proofs.Crypto.Blake3.Range.ExtensionCounterexample.overlap

end Silmaril.Crypto.Blake3
