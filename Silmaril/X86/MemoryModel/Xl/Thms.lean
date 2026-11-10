module

public import Silmaril.X86.MemoryModel.Xl.Defs
public import Silmaril.X86.MemoryModel.Axiomatic.Thms
import Silmaril.Proofs.X86.MemoryModel.Xl.Inclusion

/-!
# The loose x86 concurrency model XL: theorems

PROVED (standard axioms only; proofs in `Silmaril.Proofs.X86.MemoryModel.Xl.Inclusion`), for
**every** candidate execution, with no well-formedness hypothesis:

* `Exec.xl_of_tso`: x86-TSO-consistent implies XL-consistent;
* `Exec.xl_of_sc`: SC-consistent implies XL-consistent (with `Exec.tso_of_sc`);
* `Exec.thinAir_of_tso`: x86-TSO implies no-thin-air (`acyclic po | rf`);
* `Exec.xl_iff_tso_of_tame`: when every memory unit is write-back and not tearable, XL and
  x86-TSO coincide;
* `Decidable` instances for `Exec.Xl` and `Exec.Tame`.

Sanity candidates (checked by `decide`): store buffering (`sb`: TSO and XL, not SC),
SB+mfences (`sbMfence`: not XL), the interleaved SB outcome (`sbInterleaved`: SC), two
non-atomic `lock inc`s (`lockInc`: not XL), message passing with a non-temporal data store (`mpNt`:
XL, not TSO), the same with an `sfence` (`mpNtSfence`: not XL), and a torn misaligned
two-byte store (`torn`: XL, not TSO).
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Axiomatic

namespace Exec
variable (x : Exec)

instance : Decidable x.Xl := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
instance : Decidable x.Tame := inferInstanceAs (Decidable (∀ _, _))

/-- x86-TSO implies no-thin-air. -/
theorem thinAir_of_tso (h : x.Tso) : BRel.Acyclic x.thinAir := Proofs.Xl.thinAir_of_tso x h

/-- x86-TSO implies XL, for every candidate execution. -/
theorem xl_of_tso (h : x.Tso) : x.Xl := Proofs.Xl.tso_xl x h

/-- SC implies XL, for every candidate execution. -/
theorem xl_of_sc (h : x.Sc) : x.Xl := x.xl_of_tso (x.tso_of_sc h)

/-- On tame executions XL is exactly x86-TSO. -/
theorem xl_iff_tso_of_tame (ht : x.Tame) : x.Xl ↔ x.Tso :=
  ⟨Proofs.Xl.tso_of_xl_of_tame x ht, x.xl_of_tso⟩

end Exec

/-! ## Sanity candidates -/

namespace Sanity

/-- SB, both loads reading the initial zero: `x := 1; r0 := y ∥ y := 1; r1 := x`. -/
def sb : Exec where
  evs := [{ tid := 0, pos := 0, act := .write, addr := 0, size := 1, data := [1] },
          { tid := 0, pos := 1, act := .read, addr := 1, size := 1 },
          { tid := 1, pos := 0, act := .write, addr := 1, size := 1, data := [1] },
          { tid := 1, pos := 1, act := .read, addr := 0, size := 1 }]
  co := fun y => if y = 0 then [0] else if y = 1 then [2] else []

theorem sb_verdict : sb.Wf = true ∧ ¬ sb.Sc ∧ sb.Tso ∧ sb.Xl := by decide

/-- SB with an `mfence` after each store, both loads reading zero. -/
def sbMfence : Exec where
  evs := [{ tid := 0, pos := 0, act := .write, addr := 0, size := 1, data := [1] },
          { tid := 0, pos := 1, act := .fence .mfence },
          { tid := 0, pos := 2, act := .read, addr := 1, size := 1 },
          { tid := 1, pos := 0, act := .write, addr := 1, size := 1, data := [1] },
          { tid := 1, pos := 1, act := .fence .mfence },
          { tid := 1, pos := 2, act := .read, addr := 0, size := 1 }]
  co := fun y => if y = 0 then [0] else if y = 1 then [3] else []

theorem sbMfence_verdict : sbMfence.Wf = true ∧ ¬ sbMfence.Tso ∧ ¬ sbMfence.Xl := by decide

/-- MP whose data store is non-temporal: `movnti x, 1; y := 1 ∥ r0 := y (= 1); r1 := x (= 0)`. -/
def mpNt : Exec where
  evs := [{ tid := 0, pos := 0, act := .write, addr := 0, size := 1, ann := .nt, data := [1] },
          { tid := 0, pos := 1, act := .write, addr := 1, size := 1, data := [1] },
          { tid := 1, pos := 0, act := .read, addr := 1, size := 1 },
          { tid := 1, pos := 1, act := .read, addr := 0, size := 1 }]
  rf := fun r y => if r = 2 ∧ y = 1 then some 1 else none
  co := fun y => if y = 0 then [0] else if y = 1 then [1] else []

theorem mpNt_verdict : mpNt.Wf = true ∧ ¬ mpNt.Tso ∧ mpNt.Xl := by decide

/-- `mpNt` with an `sfence` between the two stores. -/
def mpNtSfence : Exec where
  evs := [{ tid := 0, pos := 0, act := .write, addr := 0, size := 1, ann := .nt, data := [1] },
          { tid := 0, pos := 1, act := .fence .sfence },
          { tid := 0, pos := 2, act := .write, addr := 1, size := 1, data := [1] },
          { tid := 1, pos := 0, act := .read, addr := 1, size := 1 },
          { tid := 1, pos := 1, act := .read, addr := 0, size := 1 }]
  rf := fun r y => if r = 3 ∧ y = 1 then some 2 else none
  co := fun y => if y = 0 then [0] else if y = 1 then [2] else []

theorem mpNtSfence_verdict : mpNtSfence.Wf = true ∧ ¬ mpNtSfence.Tso ∧ ¬ mpNtSfence.Xl := by
  decide

/-- A misaligned two-byte store at address 1, split into bytes, read by a misaligned
two-byte load (also split) that sees the new byte 1 and the old byte 2. -/
def torn : Exec where
  evs := [{ tid := 0, pos := 0, act := .write, addr := 1, size := 1, accAddr := 1, accSize := 2,
            data := [1] },
          { tid := 0, pos := 0, act := .write, addr := 2, size := 1, accAddr := 1, accSize := 2,
            data := [1] },
          { tid := 1, pos := 0, act := .read, addr := 1, size := 1, accAddr := 1, accSize := 2 },
          { tid := 1, pos := 0, act := .read, addr := 2, size := 1, accAddr := 1, accSize := 2 }]
  rf := fun r y => if r = 2 ∧ y = 1 then some 0 else none
  co := fun y => if y = 1 then [0] else if y = 2 then [1] else []

theorem torn_verdict : torn.Wf = true ∧ ¬ torn.Sc ∧ ¬ torn.Tso ∧ torn.Xl ∧ ¬ torn.Tame := by
  decide

/-- The same bytes as an aligned two-byte access at address 0: tame, so XL forbids the tear. -/
def tornAligned : Exec where
  evs := [{ tid := 0, pos := 0, act := .write, addr := 0, size := 1, accAddr := 0, accSize := 2,
            data := [1] },
          { tid := 0, pos := 0, act := .write, addr := 1, size := 1, accAddr := 0, accSize := 2,
            data := [1] },
          { tid := 1, pos := 0, act := .read, addr := 0, size := 1, accAddr := 0, accSize := 2 },
          { tid := 1, pos := 0, act := .read, addr := 1, size := 1, accAddr := 0, accSize := 2 }]
  rf := fun r y => if r = 2 ∧ y = 0 then some 0 else none
  co := fun y => if y = 0 then [0] else if y = 1 then [1] else []

theorem tornAligned_verdict : tornAligned.Wf = true ∧ tornAligned.Tame ∧ ¬ tornAligned.Xl := by
  decide

/-- SB with the interleaved outcome `r0 = 0, r1 = 1`: consistent under all three models. -/
def sbInterleaved : Exec := { sb with rf := fun r y => if r = 3 ∧ y = 0 then some 0 else none }

theorem sbInterleaved_verdict :
    sbInterleaved.Wf = true ∧ sbInterleaved.Sc ∧ sbInterleaved.Tso ∧ sbInterleaved.Xl := by
  decide

/-- Two `lock inc [x]`, both reading the initial value: the RMWs are not atomic. -/
def lockInc : Exec where
  evs := [{ tid := 0, pos := 0, act := .read, addr := 0, size := 1, locked := true },
          { tid := 0, pos := 1, act := .write, addr := 0, size := 1, locked := true, data := [1] },
          { tid := 1, pos := 0, act := .read, addr := 0, size := 1, locked := true },
          { tid := 1, pos := 1, act := .write, addr := 0, size := 1, locked := true, data := [1] }]
  co := fun y => if y = 0 then [1, 3] else []
  rmw := [(0, 1), (2, 3)]

theorem lockInc_verdict : lockInc.Wf = true ∧ lockInc.atomicB = false ∧ ¬ lockInc.Xl := by
  decide

end Sanity

end Silmaril.X86.MemoryModel.Axiomatic
