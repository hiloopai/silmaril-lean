module

public import Silmaril.Cerberus.Core.Outcome.Defs

/-! Kernel checks for the live-allocation branch of memory requests and the
format fragment. Linked-program agreement is checked by the census. -/

@[expose] public section
namespace Silmaril.Cerberus.Core.Dynamics
open Mem.Concrete

def memopInt : Ctype := .mk [] (.basic (.integer (.signed .int)))
def memopState : Mem.Concrete.State :=
  {allocations := Map.ofList [(7, {base := 100, size := 12})]}

theorem shift_one_past : shiftPointer ∅ memopState (.allocated 7 100) memopInt 3 =
    .ok (.allocated 7 112) := by rfl

theorem shift_outside : shiftPointer ∅ memopState (.allocated 7 100) memopInt 4 =
    .error (.ub .UB046_array_pointer_outside) := by rfl

theorem difference_negative : difference ∅ memopState memopInt (.allocated 7 100) (.allocated 7 112) =
    .ok (-3) := by rfl

theorem difference_distinct : difference ∅ memopState memopInt (.allocated 7 100) (.allocated 8 100) =
    .error (.ub .UB048_disjoint_array_pointers_subtraction) := by rfl

/-- Extra arguments do not change a literal format. -/
theorem literal_format (tags : Tags) (args : PrintArgs) (s : Mem.Concrete.State) :
    printFormat tags 2 ['a'] args s = .ok ("a", s) := by rfl

private theorem signed_format : printIntegerType "" true memopInt = true := by rfl
private theorem unsigned_format_rejects_signed : printIntegerType "" false memopInt = false := by rfl

/-- The pin compares pointer type constructors without inspecting referents. -/
theorem atomic_pointer_constructor_equal (qa qb : Qualifiers) (a b : Ctype) :
    atomicTypeEqual (.mk [] (.atomic (.mk [] (.pointer qa a))))
      (.mk [] (.atomic (.mk [] (.pointer qb b)))) = some true := by rfl

theorem exposed_address : addressPointer (Map.ofList [(7, {base := 100, size := 12, exposed := true})])
    [] memopInt 104 = .ok (.allocated 7 104) := by
  have keys : (show Finset Int from
      (Map.ofList [((7 : Int), ({base := 100, size := 12, exposed := true} : Allocation))]).keys) = {7} := by
    ext x
    simp [Finmap.mem_keys, Map.ofList, Map.insert, MapKey.key, Finmap.notMem_empty]
  simp only [addressPointer, keys, Finset.sort_singleton]
  rfl

theorem ambiguous_exposure : addressPointer
    (Map.ofList [(7, {base := 100, size := 4, exposed := true}),
     (8, {base := 104, size := 4, exposed := true})]) [] memopInt 104 =
    .error (.unsupported "PNVI-ae-udi symbolic provenance from ambiguous exposure") := by
  have keys : (show Finset Int from
      (Map.ofList [((7 : Int), ({base := 100, size := 4, exposed := true} : Allocation)),
        (8, {base := 104, size := 4, exposed := true})]).keys) = {7, 8} := by
    ext x
    simp [Finmap.mem_keys, Map.ofList, Map.insert, MapKey.key, Finmap.notMem_empty, or_comm]
  have sorted : ({7, 8} : Finset Int).sort (· ≤ ·) = [7, 8] := by
    rw [Finset.sort_insert (· ≤ ·) (by simp) (by decide)]
    simp
  simp only [addressPointer, keys, sorted]
  rfl

end Silmaril.Cerberus.Core.Dynamics
