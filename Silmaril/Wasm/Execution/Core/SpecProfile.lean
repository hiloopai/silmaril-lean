module

public import Silmaril.Wasm.Execution.Core.Properties

@[expose] public section

/-! # Admitting deterministic executions with `$ND = true`

The relaxed numerics library identifies every `$ND = false` operator with
`$ND = true` at the all-zero choice (`RelaxedChoice.det`). This file lifts that
identification to complete Core executions, including control, allocation and
host interactions. The same global choice is used throughout the execution;
this does not assert inclusion for arbitrary nonzero relaxed choices.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Numerics

variable {H : Type} {host : HostSemantics H}

theorem NumericStep.spec_false_to_true {r : RelaxedChoice} {is is' : List Admin}
    (h : NumericStep (Profile.spec false r) is is') :
    NumericStep (Profile.spec true {}) is is' := by
  cases h <;> constructor <;> assumption

theorem VectorStep.spec_false_to_true {r : RelaxedChoice} {is is' : List Admin}
    (h : VectorStep (Profile.spec false r) is is') :
    VectorStep (Profile.spec true {}) is is' := by
  cases h with
  | vecUnOp op a => exact .vecUnOp op a
  | vecBinOp op a b => exact .vecBinOp op a b
  | vecTernOp op a b c => exact .vecTernOp op a b c
  | vecTestOp op a => exact .vecTestOp op a
  | vecIntUnOp sh op a => exact .vecIntUnOp sh op a
  | vecFloatUnOp h => exact .vecFloatUnOp h
  | vecFloatUnOpTrap h => exact .vecFloatUnOpTrap h
  | vecIntBinOp sh op a b => exact .vecIntBinOp sh op a b
  | vecFloatBinOp h => exact .vecFloatBinOp h
  | vecFloatBinOpTrap h => exact .vecFloatBinOpTrap h
  | vecIntTernOp sh op a b c => exact .vecIntTernOp sh op a b c
  | vecFloatTernOp h => exact .vecFloatTernOp h
  | vecFloatTernOpTrap h => exact .vecFloatTernOpTrap h
  | vecAllTrue sh a => exact .vecAllTrue sh a
  | vecIntRelOp sh op a b => exact .vecIntRelOp sh op a b
  | vecFloatRelOp sh op a b => exact .vecFloatRelOp sh op a b
  | vecShiftOp sh op a n => exact .vecShiftOp sh op a n
  | vecBitmask sh a => exact .vecBitmask sh a
  | vecSwizzle a s => exact .vecSwizzle a s
  | vecRelaxedSwizzle a s => exact .vecRelaxedSwizzle a s
  | vecShuffle idx a b hidx => exact .vecShuffle idx a b hidx
  | vecSplat sh x => exact .vecSplat sh x
  | vecExtractLane sh sx i a hi => exact .vecExtractLane sh sx i a hi
  | vecReplaceLane sh i a x hi => exact .vecReplaceLane sh i a x hi
  | vecExtUnOp h => exact .vecExtUnOp h
  | vecExtBinOp h => exact .vecExtBinOp h
  | vecExtTernOp h => exact .vecExtTernOp h
  | vecNarrow h => exact .vecNarrow h
  | vecConvert h =>
    rename_i src tgt op a result
    refine .vecConvert ?_
    cases op with
    | relaxedTrunc sx z =>
      cases src with
      | int _ => exact h.elim
      | float fs =>
        exact ⟨h.1, by
          change vrelaxedTruncRel true .det sx fs a result
          rw [← vrelaxedTruncRel_false r]
          exact h.2⟩
    | _ => exact h

theorem MemoryStep.spec_false_to_true {r : RelaxedChoice} {c c' : Config H}
    (h : MemoryStep (Profile.spec false r) c c') :
    MemoryStep (Profile.spec true {}) c c' := by
  cases h <;> constructor <;> assumption

theorem TableStep.spec_false_to_true {r : RelaxedChoice} {c c' : Config H}
    (h : TableStep (Profile.spec false r) c c') :
    TableStep (Profile.spec true {}) c c' := by
  cases h <;> constructor <;> assumption

/-- The `$ND = false` specification embeds in the `$ND = true` specification
with one global all-zero relaxed choice, shared by every step. -/
theorem Step.spec_false_to_true {r : RelaxedChoice} {a b : Config H}
    (h : Step (Profile.spec false r) host a b) : Step (Profile.spec true {}) host a b := by
  induction h with
  | parametric h => exact .parametric h
  | numeric h => exact .numeric h.spec_false_to_true
  | vector h => exact .vector h.spec_false_to_true
  | «variable» h => exact .«variable» h
  | table h => exact .table h.spec_false_to_true
  | memory h => exact .memory h.spec_false_to_true
  | reference h => exact .reference h
  | aggregate h => exact .aggregate h
  | ctxtInstrs _ hne ih => exact .ctxtInstrs ih hne
  | ctxtLabel _ ih => exact .ctxtLabel ih
  | ctxtHandler _ ih => exact .ctxtHandler ih
  | ctxtFrame _ ih => exact .ctxtFrame ih
  | block hbt hm => exact .block hbt hm
  | loop hbt hm => exact .loop hbt hm
  | ifTrue hc => exact .ifTrue hc
  | ifFalse => exact .ifFalse
  | labelVals => exact .labelVals
  | brLabelZero hl hn => exact .brLabelZero hl hn
  | brLabelSucc hl => exact .brLabelSucc hl
  | brHandler => exact .brHandler
  | brIfTrue hc => exact .brIfTrue hc
  | brIfFalse => exact .brIfFalse
  | brTableLt hi => exact .brTableLt hi
  | brTableGe hi => exact .brTableGe hi
  | brOnNullNull => exact .brOnNullNull
  | brOnNullAddr hv => exact .brOnNullAddr hv
  | brOnNonNullNull => exact .brOnNonNullNull
  | brOnNonNullAddr hv => exact .brOnNonNullAddr hv
  | brOnCastSucceed h => exact .brOnCastSucceed h
  | brOnCastFail h => exact .brOnCastFail h
  | brOnCastFailSucceed h => exact .brOnCastFailSucceed h
  | brOnCastFailFail h => exact .brOnCastFailFail h
  | call hx hf => exact .call hx hf
  | callRefNull hc => exact .callRefNull hc
  | callRefFunc hc hf he hn hcode => exact .callRefFunc hc hf he hn hcode
  | callRefHost hc hf he hn hcode hhost => exact .callRefHost hc hf he hn hcode hhost
  | callRefHostDiv hc hf he hn hcode hhost => exact .callRefHostDiv hc hf he hn hcode hhost
  | returnCall hx hf => exact .returnCall hx hf
  | returnCallRefLabel hc => exact .returnCallRefLabel hc
  | returnCallRefHandler hc => exact .returnCallRefHandler hc
  | returnCallRefFrameNull hc => exact .returnCallRefFrameNull hc
  | returnCallRefFrameAddr hc hf he hn => exact .returnCallRefFrameAddr hc hf he hn
  | callIndirect => exact .callIndirect
  | returnCallIndirect => exact .returnCallIndirect
  | frameVals hn => exact .frameVals hn
  | returnFrame hn => exact .returnFrame hn
  | returnLabel => exact .returnLabel
  | returnHandler => exact .returnHandler
  | throw ht he hn => exact .throw ht he hn
  | throwRefNull => exact .throwRefNull
  | throwRefInstrs hne => exact .throwRefInstrs hne
  | throwRefLabel => exact .throwRefLabel
  | throwRefFrame => exact .throwRefFrame
  | throwRefHandlerEmpty => exact .throwRefHandlerEmpty
  | throwRefHandlerCatch he ht => exact .throwRefHandlerCatch he ht
  | throwRefHandlerCatchRef he ht => exact .throwRefHandlerCatchRef he ht
  | throwRefHandlerCatchAll => exact .throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef => exact .throwRefHandlerCatchAllRef
  | throwRefHandlerNext h => exact .throwRefHandlerNext h
  | tryTable hbt hm => exact .tryTable hbt hm
  | handlerVals => exact .handlerVals
  | trapInstrs hne => exact .trapInstrs hne
  | trapLabel => exact .trapLabel
  | trapHandler => exact .trapHandler
  | trapFrame => exact .trapFrame

/-- Every chosen deterministic step is admitted with either value of `$ND`,
using default relaxed choices and the specification's NaN/growth policies. -/
theorem Step.deterministic_refines_spec (nd : Bool)
    {o : GrowKind → Nat → Nat → Nat → Bool} {a b : Config H}
    (h : Step (Profile.deterministic o) host a b) :
    Step (Profile.spec nd {}) host a b := by
  cases nd with
  | false => exact h.deterministic_refines
  | true => exact h.deterministic_refines.spec_false_to_true

/-- A whole finite run is admitted using a single global relaxed choice. -/
theorem Steps.deterministic_refines_spec (nd : Bool)
    {o : GrowKind → Nat → Nat → Nat → Bool} {a b : Config H}
    (h : Steps (Profile.deterministic o) host a b) :
    Steps (Profile.spec nd {}) host a b :=
  Relation.ReflTransGen.mono (fun _ _ step => step.deterministic_refines_spec nd) _ _ h

end Silmaril.Wasm.Execution.Core
