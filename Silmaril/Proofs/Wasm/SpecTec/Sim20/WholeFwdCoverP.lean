module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdCover
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholePlainTail

/-!
# The pure cover without its administrative-tail cases

`pureStep_cover` (pass 2) splits every V2 `PureStep` into `PureFrag20`, `PureFrag20B` and
`PureRest20`. Four of `PureRest20`'s cases are `br`, `return` (frame and label) and `trap-vals`
with administrative code after the redex. Under the plain-tail invariant (`Tail20`, which holds at
the inner code of every context of a run from plain code, `WholePlainTail`) the code after the
redex is plain, so those cases do not occur:

* `PureRest20N`: `PureRest20` without the tail cases (a vector operator, an integer unary operator
  invalid at its type, a conversion `toShared` does not define);
* **`pureStep_cover_tail`**: every V2 pure step from `Tail20` code is in `PureFrag20`, in
  `PureFrag20B`, or in `PureRest20N`;
* `pureStep_cover_plain`: the same from `Plain20` code.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **The pure steps neither fragment covers, from plain-tail code.** -/
inductive PureRest20N : List Admin → Prop where
  | vec {is : List Admin} {i : V2.Instr} (hm : .plain i ∈ is) (hv : vecOp20 i = true) :
      PureRest20N is
  | unOpInvalid {t : IntType} {op : IntUnOp} {x : BitVec t.width} (h : ¬ op.valid t) :
      PureRest20N [.plain (.intConst t x), .plain (.intUnOp t op)]
  | cvtUndefined {target source : NumType} {op : V2.CvtOp} {x : BitVec source.width}
      (h : V2.CvtOp.toShared target source op = none) :
      PureRest20N [(Val.num ⟨source, x⟩).toAdmin, .plain (.cvtOp target source op)]

theorem not_pendOp_br (l : LabelIdx) : ¬ PendOp (.plain (.br l)) := by
  rintro (⟨_, h⟩ | h) <;> simp [store8] at h

theorem not_pendOp_return : ¬ PendOp (.plain .return_) := by
  rintro (⟨_, h⟩ | h) <;> simp [store8] at h

theorem not_pendOp_trap : ¬ PendOp .trap := by
  rintro (⟨_, h⟩ | h) <;> cases h

/-- The code after a redex `y` in a plain-tail body is plain. -/
theorem plainTail_of_body {s : Store H} {f : Frame} {us : List Val} {y : Admin} {rest : List Admin}
    (h : Plain20 s f (vals us ++ [y] ++ rest)) (hy : y.isVal = false) (hp : ¬ PendOp y) :
    PlainTail rest :=
  Tail20.plain_after (a := us) (y := y) (by simpa using h.tail) hy hp

/-- **A `PureRest20` step from `Tail20` code is a `PureRest20N` step**: the tail cases do not
occur. -/
theorem pureRest20N_of_tail {s : Store H} {f : Frame} {is : List Admin} (h : PureRest20 is)
    (ht : Tail20 s f is) : PureRest20N is := by
  cases h with
  | vec hm hv => exact .vec hm hv
  | unOpInvalid h => exact .unOpInvalid h
  | cvtUndefined h => exact .cvtUndefined h
  | brTail h => exact absurd (plainTail_of_body (tail20_label ht) rfl (not_pendOp_br _)) h
  | returnFrameTail h =>
    exact absurd (plainTail_of_body (tail20_frame ht) rfl not_pendOp_return) h
  | returnLabelTail h =>
    exact absurd (plainTail_of_body (tail20_label ht) rfl not_pendOp_return) h
  | trapTail h =>
    exact absurd (Tail20.plain_after (y := .trap) (by simpa using ht) rfl not_pendOp_trap) h

/-- **Every V2 pure step from plain-tail code is covered** by the two forward fragments or by
`PureRest20N`. -/
theorem pureStep_cover_tail {P : Profile} {s : Store H} {f : Frame} {is is' : List Admin}
    (h : PureStep P is is') (ht : Tail20 s f is) :
    PureFrag20 P is is' ∨ PureFrag20B P is is' ∨ PureRest20N is := by
  rcases pureStep_cover h with h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (pureRest20N_of_tail h ht))

/-- The same from `Plain20` code. -/
theorem pureStep_cover_plain {P : Profile} {s : Store H} {f : Frame} {is is' : List Admin}
    (h : PureStep P is is') (hp : Plain20 s f is) :
    PureFrag20 P is is' ∨ PureFrag20B P is is' ∨ PureRest20N is :=
  pureStep_cover_tail h hp.tail

end Silmaril.Wasm.SpecTec.Sim20.Whole
