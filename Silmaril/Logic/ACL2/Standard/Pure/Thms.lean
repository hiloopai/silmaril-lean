module

public import Silmaril.Logic.ACL2.Standard.Pure.Source
public import Silmaril.Logic.ACL2.Standard.Objects.Thms

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.Pure

theorem eql_native (x y : Object) : x.eql y = eqlBody x y := rfl

theorem logicalNot_native (x : Object) : x.logicalNot = notBody x := by
  by_cases h : x = .nil <;> simp [Object.logicalNot, Object.equal, Object.ofBool, notBody, h]

theorem atom_native (x : Object) : atomBody x = Object.ofBool (!x.consp) := by
  cases x <;> rfl

/-- The exported recursive call is interpreted by the total, structural MV-NTH. -/
theorem mvNth_native (index values : Object) :
    index.mvNth values = mvNthBody Object.mvNth index values := by
  cases values <;> rfl

/-- At an atomic remainder the index is irrelevant, including on dotted lists. -/
theorem mvNth_atom (index values : Object) (h : values.consp = false) :
    index.mvNth values = .nil := by
  cases values <;> first | rfl | contradiction

/-- Negative integers and nonintegers use the same projection as zero. -/
theorem mvNth_of_not_positive (index values : Object)
    (h : ¬ ∃ n : Int, 0 < n ∧ index = .integer n) : index.mvNth values = values.car := by
  have hz : index.zp ≠ .nil := fun hn => h ((Object.zp_eq_nil_iff index).mp hn)
  cases values <;> simp [Object.mvNth, Object.car, hz]

end Silmaril.Logic.ACL2.Standard.Pure
