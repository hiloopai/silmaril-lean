module

public import Silmaril.Proofs.Wasm.Det.NoMem.Basic

/-!
# The memory-free, float-free subset: profile transfer of one step

`step_transfer`: on code of the subset (`Seq`), a Core step at a profile `P` is a step at every
profile `P'` (same host). Only the numeric, vector, table and memory rules of `Step` mention the
profile. Of those, the subset admits the integer numeric rules, the float comparisons (which have
no profile premise) and the integer conversions `wrap`/`extend` (whose profile relation is the
function `convert` under both NaN policies), and the table rules other than `table.grow`; the
vector and memory rules, the float operators and the other conversions are excluded
syntactically.

Adapted from `Silmaril.Proofs.Wasm.Interp.Profile.step_profile` (native-profile code); the subset is
larger (references, GC, exceptions, tail and indirect calls, tables). New proof.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.NoMem

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Det.NoMem

variable {H : Type} {q : Nat → Bool} {ind : Bool}

/-- The integer conversions are profile-independent. -/
theorem convertP_int {P P' : Profile} {op : ConvertOp} (hop : flatOk (.convert op) = true)
    {x : NumValue op.source} {r : Except FloatTrap (NumValue op.target)}
    (h : convertP P op x r) : convertP P' op x r := by
  have hr : r = convert op x := by
    cases op <;> simp only [flatOk, Bool.false_eq_true] at hop <;>
      (unfold convertP at h; split at h <;> exact h)
  subst hr
  unfold convertP
  split <;> first | rfl | (cases op <;> simp only [flatOk, Bool.false_eq_true] at hop <;>
    simp only [convertRel])

/-- The plain instruction at the end of subset code satisfies `instrB` (or is a constant). -/
theorem plainOk_of_seq_last {fs : List Nat} {p : Prop} {l : List Admin} {i : Instr}
    (h : Seq q ind fs p (l ++ [.plain i])) : PlainOk q ind fs i := by
  rw [seq_append] at h
  exact h.2.2.1

/-- Unpack a `PlainOk` of a non-constant instruction. -/
theorem instrB_of_plainOk {fs : List Nat} {i : Instr} (h : PlainOk q ind fs i)
    (hf : ∀ t b, i ≠ .floatConst t b) (hv : ∀ b, i ≠ .vecConst b) : instrB q ind fs i = true := by
  rcases h with h | ⟨t, b, rfl⟩ | ⟨b, rfl⟩
  · exact h
  · exact absurd rfl (hf t b)
  · exact absurd rfl (hv b)

/-- The table rules other than `table.grow` do not depend on the profile. -/
theorem tableStep_transfer {P P' : Profile} {c c' : Config H} (h : TableStep P c c')
    (hg : ∀ s f x rest, c ≠ ⟨s, f, rest ++ [.plain (.tableGrow x)]⟩) : TableStep P' c c' := by
  cases h with
  | getOob ht h => exact .getOob ht h
  | getVal ht h => exact .getVal ht h
  | setOob ht h => exact .setOob ht h
  | setVal ht h => exact .setVal ht h
  | size ht => exact .size ht
  | growSucceed => exact absurd rfl (hg _ _ _ [_, _])
  | growFail => exact absurd rfl (hg _ _ _ [_, _])
  | fillOob ht h => exact .fillOob ht h
  | fillZero ht h => exact .fillZero ht h
  | fillSucc ht h hn => exact .fillSucc ht h hn
  | copyOob h₁ h₂ h => exact .copyOob h₁ h₂ h
  | copyZero h₁ h₂ h => exact .copyZero h₁ h₂ h
  | copyLe h₁ h₂ h hn hle => exact .copyLe h₁ h₂ h hn hle
  | copyGt h₁ h₂ h hn hgt => exact .copyGt h₁ h₂ h hn hgt
  | initOob ht he h => exact .initOob ht he h
  | initZero ht he h => exact .initZero ht he h
  | initSucc ht he h hn hr => exact .initSucc ht he h hn hr
  | elemDrop he => exact .elemDrop he

/-- `table.grow` is not in the subset. -/
theorem not_seq_tableGrow {fs : List Nat} {p : Prop} {rest : List Admin} {x : TableIdx} :
    ¬ Seq q ind fs p (rest ++ [.plain (.tableGrow x)]) := by
  intro h
  have h' := plainOk_of_seq_last h
  rcases h' with h' | ⟨_, _, h'⟩ | ⟨_, h'⟩
  · simp [instrB, flatOk] at h'
  · cases h'
  · cases h'

/-- A conversion in subset code is an integer conversion. -/
theorem flatOk_convert {fs : List Nat} {p : Prop} {v : Admin} {op : ConvertOp}
    (h : Seq q ind fs p [v, .plain (.convert op)]) : flatOk (.convert op) = true := by
  have hop : instrB q ind fs (.convert op) = true := instrB_of_plainOk
    (plainOk_of_seq_last (l := [v]) h) (fun _ _ h => by cases h) (fun _ h => by cases h)
  simpa [instrB] using hop

/-- The numeric rules of subset code do not depend on the profile. -/
theorem numericStep_transfer {P P' : Profile} {fs : List Nat} {p : Prop} {is is' : List Admin}
    (h : NumericStep P is is') (hN : Seq q ind fs p is) : NumericStep P' is is' := by
  cases h with
  | intUnOp => exact .intUnOp
  | intBinOp hz => exact .intBinOp hz
  | intBinOpTrap he => exact .intBinOpTrap he
  | intTestOp => exact .intTestOp
  | intRelOp => exact .intRelOp
  | floatRelOp => exact .floatRelOp
  | floatUnOp => exact absurd hN (by simp [PlainOk, instrB, flatOk])
  | floatBinOp => exact absurd hN (by simp [PlainOk, instrB, flatOk])
  | convert hz => exact .convert (convertP_int (flatOk_convert hN) hz)
  | convertTrap hz => exact .convertTrap (convertP_int (flatOk_convert hN) hz)

/-- **Profile transfer of one step**: on code of the subset, a Core step at profile `P` is a
step at every profile `P'` (same host). -/
theorem step_transfer {P P' : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') {p : Prop} (hN : Seq q ind c.frame.module.funcs p c.code) :
    Step P' host c c' := by
  induction h generalizing p with
  | parametric h => exact .parametric h
  | numeric h => exact .numeric (numericStep_transfer h hN)
  | vector h => cases h <;> exact absurd hN (by simp [PlainOk, instrB, flatOk])
  | «variable» h => exact .«variable» h
  | table h =>
    exact .table (tableStep_transfer h fun _ _ _ _ he => not_seq_tableGrow (he ▸ hN))
  | memory h => cases h <;> exact absurd hN (by simp [PlainOk, instrB, flatOk, aconst])
  | reference h => exact .reference h
  | aggregate h => exact .aggregate h
  | ctxtInstrs _ hne ih => exact .ctxtInstrs (ih ((seq_append3 _ _ _).mp hN).2.1) hne
  | ctxtLabel _ ih => exact .ctxtLabel (ih (aOk_label.mp (seq_cons.mp hN).2.1).2)
  | ctxtHandler _ ih => exact .ctxtHandler (ih (aOk_handler.mp (seq_cons.mp hN).2.1))
  | ctxtFrame _ ih => exact .ctxtFrame (ih (aOk_frame.mp (seq_cons.mp hN).2.1))
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

end Silmaril.Proofs.Wasm.Det.NoMem
