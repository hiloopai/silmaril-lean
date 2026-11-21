module

public import Silmaril.Semantics.Naming.ByteRange.Extension.Defs
public import Silmaril.Semantics.Naming.ByteRange.Thms
import Silmaril.Proofs.Semantics.Naming.ByteRange.Extension

public section

namespace Silmaril.Semantics.Naming.ByteRange

theorem Fact.range_iff {whole fragment : Bytes} {offset : Nat} :
    (Fact.range offset fragment).Holds whole ↔ Slice whole offset fragment :=
  Proofs.Semantics.Naming.ByteRange.Extension.range_iff

theorem Fact.whole_iff {expected bytes : Bytes} :
    (Fact.whole expected).Holds bytes ↔ bytes = expected := Proofs.Semantics.Naming.ByteRange.Extension.whole_iff

theorem Fact.eof_iff {length : Nat} {bytes : Bytes} :
    (Fact.eof length).Holds bytes ↔ bytes.length = length := Proofs.Semantics.Naming.ByteRange.Extension.eof_iff

namespace Observations

variable {Name : Type} {seen : Observations Name} {base rel : Relation Name Bytes} {name : Name}

/-- At any admissible length, uncovered offsets can take any supplied bytes. -/
theorem fits_filling (length : Nat) (gap : Nat → UInt8) (agrees : seen.Agrees name)
    (bound : ∀ fact, seen name fact → fact.bound ≤ length)
    (ending : ∀ fact actual, seen name fact → fact.end? = some actual → length = actual) :
    ∃ bytes, bytes.length = length ∧ seen.Fits name bytes ∧
      ∀ pos, pos < length → (¬ ∃ byte, seen.ByteAt name pos byte) → bytes[pos]? = some (gap pos) :=
  Proofs.Semantics.Naming.ByteRange.Extension.fits_filling length gap agrees bound ending

theorem exists_fits_iff : (∃ bytes, seen.Fits name bytes) ↔ seen.Compatible name :=
  Proofs.Semantics.Naming.ByteRange.Extension.exists_fits_iff

theorem Model.preservesFiber {bytes : Bytes} (model : seen.Model base rel) (old : base name bytes) :
    ∀ payload, rel name payload ↔ base name payload := Proofs.Semantics.Naming.ByteRange.Extension.model_preserves_fiber model old

/-- Exact joint extension criterion for arbitrary sets of closed observations. -/
theorem exists_model_iff : (∃ rel, seen.Model base rel) ↔ Binding base ∧
    (∀ ⦃name bytes⦄, base name bytes → seen.Fits name bytes) ∧
    (∀ name, seen.Queried name → seen.Compatible name) := Proofs.Semantics.Naming.ByteRange.Extension.exists_model_iff

theorem exists_unique_model_iff : (∃ rel, seen.Model base rel ∧ UniqueNames rel) ↔
    Binding base ∧ UniqueNames base ∧ (∀ ⦃name bytes⦄, base name bytes → seen.Fits name bytes) ∧
    ∃ pick, seen.FreshAssignment base pick := Proofs.Semantics.Naming.ByteRange.Extension.exists_unique_model_iff

end Observations
end Silmaril.Semantics.Naming.ByteRange
