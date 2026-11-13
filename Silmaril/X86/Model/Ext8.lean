module

public import Silmaril.X86.Model.Basic
public import Silmaril.X86.Ext8.Basic

/-!
# `X86.Ext8` in the model order

`X86.Ext8` (the 8-bit ALU and legacy high-byte variant) runs on the integer
state `X86.MState` and tries `X86.Ext`'s decoder first. Its agreement lemma
`Ext8.step_eq_of_ne_undecodable` says that every outcome of `Ext.step` other
than `undecodable` is `Ext8`'s outcome, so the identity is a map
`Model.ext ⟶ Model.ext8` (`Hom.extToExt8`), and `Model.ext ≤ Model.ext8`.

A new byte form that faults on data is `halted`; one that depends on an
undefined flag is `unsettled`.

`Ext8` is not (yet) an `Extension` of the feature machine: that needs
prefix-code laws for `Ext8.decodeNew`, and its forms overlap `Wire`'s (for
example `3A /r` with register operands), so a joint configuration would also
need an agreement proof on the overlap.
-/

@[expose] public section

namespace Silmaril.X86

open Silmaril.X86.Model (Sem Step)

namespace Model

/-- An `Ext8` outcome as a refinement step. -/
def ofExt8Outcome : Ext8.Outcome → Step X86.MState
  | .ext o => ofExtOutcome o
  | .retired next => .retired next
  | .newFault (.ok _ _) => .unsettled
  | .newFault .dataFault => .halted
  | .newFault .divideError => .halted
  | .newFault .trap => .halted
  | .newFault (.undefinedCondition _) => .unsettled

/-- The 8-bit ALU variant `X86.Ext8`. -/
abbrev ext8 : Model where
  name := "X86.Ext8"
  State := X86.MState
  sem := ⟨fun exit m => ofExt8Outcome (Ext8.step exit m)⟩

/-- **`Ext ≤ Ext8`**, from `Ext8.step_eq_of_ne_undecodable`. -/
def Hom.extToExt8 : ext ⟶ ext8 :=
  Sem.Hom.ofAgree fun exit m hs => by
    change ofExtOutcome (Ext.step exit m) ≠ .unsettled at hs
    change ofExt8Outcome (Ext8.step exit m) = ofExtOutcome (Ext.step exit m)
    have hu : Ext.step exit m ≠ .undecodable := by
      intro e; rw [e] at hs; exact hs rfl
    rw [Ext8.step_eq_of_ne_undecodable hu]
    rfl

theorem ext_le_ext8 : ext ≤ ext8 := Hom.extToExt8.le

theorem ext8_stepOpt (exit : Word) (m : X86.MState) : ext8.sem.stepOpt exit m = Ext8.stepOpt exit m := by
  cases h : Ext8.step exit m with
  | ext o => cases o <;> simp [Sem.stepOpt, Ext8.stepOpt, ofExt8Outcome, ofExtOutcome, h]
  | retired next => simp [Sem.stepOpt, Ext8.stepOpt, ofExt8Outcome, h]
  | newFault r => cases r <;> simp [Sem.stepOpt, Ext8.stepOpt, ofExt8Outcome, h]

theorem ext8_run (exit : Word) (n : Nat) (m : X86.MState) :
    ext8.sem.run exit n m = Machine.Execution.run (Ext8.stepOpt exit) n m := by
  unfold Sem.run
  congr 1
  funext m
  exact ext8_stepOpt exit m

/-- `Model.ext8`'s returns are `Ext8.Returns`. -/
theorem ext8_returns_iff {exit : Word} {initial final : X86.MState} :
    ext8.sem.Returns exit initial final ↔ Ext8.Returns exit initial final := by
  unfold Sem.Returns Ext8.Returns
  constructor
  · rintro ⟨n, mid, hr, hs⟩
    refine ⟨n, mid, by rw [← ext8_run]; exact hr, ?_⟩
    change ofExt8Outcome (Ext8.step exit mid) = _ at hs
    cases h : Ext8.step exit mid with
    | ext o => rw [h] at hs; cases o <;> cases hs; rfl
    | retired => rw [h] at hs; cases hs
    | newFault r => rw [h] at hs; cases r <;> cases hs
  · rintro ⟨n, mid, hr, hs⟩
    exact ⟨n, mid, by rw [ext8_run]; exact hr, by change ofExt8Outcome _ = _; rw [hs]; rfl⟩

/-- `Ext8.returns_of_ext`, recovered from the map. -/
example {exit : Word} {initial final : X86.MState} (h : Ext.Returns exit initial final) :
    Ext8.Returns exit initial final :=
  ext8_returns_iff.mp (Hom.extToExt8.returns (ext_returns_iff.mpr h))

end Model

end Silmaril.X86
