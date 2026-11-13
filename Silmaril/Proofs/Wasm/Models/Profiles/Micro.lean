module

public import Silmaril.Wasm.Models.Runtime.Thms
public import Silmaril.Wasm.Models.Features.Thms
public import Silmaril.Wasm.Behaviour.Semantics.V3

/-!
# Micro Wasm: profile independence of one step

`step_transfer`: on runtime code of a feature set without floats (hence without SIMD and
saturating truncation), a Core step at profile `P` is a step at every profile `P'` with the same
grow policy. Of the profile-dependent rules, the float operators and conversions and every
vector rule are excluded by the code; the integer conversions `wrap`/`extend` are the function
`convert` under both NaN policies; the table and memory rules depend on the profile only through
`growMaySucceed`/`growMayFail`, which only read `P.grow`.

Pattern after `Silmaril.Proofs.Wasm.Det.NoMem.Transfer` (which excludes memory and `table.grow`;
here memory and grow are allowed and the grow policy is fixed instead). New proof.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.Micro

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Models
  Silmaril.Wasm.Models.Rt

variable {S : FeatureSet} {H : Type}

theorem no_simd (hf : S.has .floatNum = false) : S.has .simd = false := by
  cases h : S.has .simd
  · rfl
  · exact absurd (has_pre h (by decide : Cap.floatNum ∈ Cap.pre .simd)) (by simp [hf])

theorem no_satConv (hf : S.has .floatNum = false) : S.has .satConv = false := by
  cases h : S.has .satConv
  · rfl
  · exact absurd (has_pre h (by decide : Cap.floatNum ∈ Cap.pre .satConv)) (by simp [hf])

theorem growMaySucceed_congr {P P' : Profile} (hg : P.grow = P'.grow) :
    P'.growMaySucceed = P.growMaySucceed := by
  funext k a s d
  simp only [Profile.growMaySucceed, hg]

theorem growMayFail_congr {P P' : Profile} (hg : P.grow = P'.grow) :
    P'.growMayFail = P.growMayFail := by
  funext k a s d
  simp only [Profile.growMayFail, hg]

theorem table_transfer {P P' : Profile} (hg : P.grow = P'.grow) {c c' : Config H}
    (h : TableStep P c c') : TableStep P' c c' := by
  cases h <;> (constructor <;> (try rw [growMaySucceed_congr hg]) <;>
    (try rw [growMayFail_congr hg]) <;> assumption)

theorem memory_transfer {P P' : Profile} (hg : P.grow = P'.grow) {c c' : Config H}
    (h : MemoryStep P c c') : MemoryStep P' c c' := by
  cases h <;> (constructor <;> (try rw [growMaySucceed_congr hg]) <;>
    (try rw [growMayFail_congr hg]) <;> assumption)

/-- A conversion without floats is an integer conversion, which does not depend on the
profile. -/
theorem convertP_int {P P' : Profile} {op : ConvertOp} (hf : S.has .floatNum = false)
    (hop : ConvertOp.inFeatB S op = true) {x : NumValue op.source}
    {r : Except FloatTrap (NumValue op.target)} (h : convertP P op x r) : convertP P' op x r := by
  have hs := no_satConv hf
  have hr : r = convert op x := by
    cases op <;> simp_all [ConvertOp.inFeatB] <;> (unfold convertP at h; split at h <;> exact h)
  subst hr
  unfold convertP
  split <;> first | rfl | (cases op <;> simp_all [ConvertOp.inFeatB, convertRel])

theorem numeric_transfer {P P' : Profile} (hf : S.has .floatNum = false) {is is' : List Admin}
    (h : NumericStep P is is') (hc : CodeIn S is) : NumericStep P' is is' := by
  cases h with
  | intUnOp => exact .intUnOp
  | intBinOp hz => exact .intBinOp hz
  | intBinOpTrap he => exact .intBinOpTrap he
  | intTestOp => exact .intTestOp
  | intRelOp => exact .intRelOp
  | floatRelOp => exact .floatRelOp
  | floatUnOp => exact absurd hc (by simp [instrB, Instr.inFeatB, Instr.headB, hf])
  | floatBinOp => exact absurd hc (by simp [instrB, Instr.inFeatB, Instr.headB, hf])
  | @convert op _ _ hz =>
    have hop : ConvertOp.inFeatB S op = true := by
      simpa [instrB, Instr.inFeatB, Instr.headB] using hc
    exact .convert (convertP_int hf hop hz)
  | @convertTrap op _ _ hz =>
    have hop : ConvertOp.inFeatB S op = true := by
      simpa [instrB, Instr.inFeatB, Instr.headB] using hc
    exact .convertTrap (convertP_int hf hop hz)

theorem not_vector {P : Profile} (hf : S.has .floatNum = false) {is is' : List Admin}
    (h : VectorStep P is is') (hc : CodeIn S is) : False := by
  have hs := no_simd hf
  cases h <;> simp_all [instrB, Instr.inFeatB, Instr.headB, vecB, vconst]

theorem codeIn_mid {vs : List Val} {is rest : List Admin} (h : CodeIn S (vals vs ++ is ++ rest)) :
    CodeIn S is := by
  have h' : CodeIn S is ∧ CodeIn S rest := by
    simpa [Silmaril.Proofs.Wasm.Models.Rt.codeIn_append] using h
  exact h'.1

theorem codeIn_label {n : Nat} {cont : List Instr} {is : List Admin}
    (h : CodeIn S [.label n cont is]) : CodeIn S is := h.1.2

theorem codeIn_handler {n : Nat} {cs : List Catch} {is : List Admin}
    (h : CodeIn S [.handler n cs is]) : CodeIn S is := h.1.2

theorem codeIn_frame {n : Nat} {f : Frame} {is : List Admin}
    (h : CodeIn S [.frame n f is]) : CodeIn S is := h.1

/-- **Profile transfer of one step** on runtime code without floats: only the grow policy
matters. -/
theorem step_transfer {P P' : Profile} (hf : S.has .floatNum = false) (hg : P.grow = P'.grow)
    {host : HostSemantics H} {c c' : Config H} (h : Step P host c c') (hc : CodeIn S c.code) :
    Step P' host c c' := by
  induction h with
  | parametric h => exact .parametric h
  | numeric h => exact .numeric (numeric_transfer hf h hc)
  | vector h => exact (not_vector hf h hc).elim
  | «variable» h => exact .«variable» h
  | table h => exact .table (table_transfer hg h)
  | memory h => exact .memory (memory_transfer hg h)
  | reference h => exact .reference h
  | aggregate h => exact .aggregate h
  | ctxtInstrs _ hne ih => exact .ctxtInstrs (ih (codeIn_mid hc)) hne
  | ctxtLabel _ ih => exact .ctxtLabel (ih (codeIn_label hc))
  | ctxtHandler _ ih => exact .ctxtHandler (ih (codeIn_handler hc))
  | ctxtFrame _ ih => exact .ctxtFrame (ih (codeIn_frame hc))
  | block hbt hm => exact .block hbt hm
  | loop hbt hm => exact .loop hbt hm
  | ifTrue hc' => exact .ifTrue hc'
  | ifFalse => exact .ifFalse
  | labelVals => exact .labelVals
  | brLabelZero hl hn => exact .brLabelZero hl hn
  | brLabelSucc hl => exact .brLabelSucc hl
  | brHandler => exact .brHandler
  | brIfTrue hc' => exact .brIfTrue hc'
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
  | callRefNull hc' => exact .callRefNull hc'
  | callRefFunc hc' hf he hn hcode => exact .callRefFunc hc' hf he hn hcode
  | callRefHost hc' hf he hn hcode hhost => exact .callRefHost hc' hf he hn hcode hhost
  | callRefHostDiv hc' hf he hn hcode hhost => exact .callRefHostDiv hc' hf he hn hcode hhost
  | returnCall hx hf => exact .returnCall hx hf
  | returnCallRefLabel hc' => exact .returnCallRefLabel hc'
  | returnCallRefHandler hc' => exact .returnCallRefHandler hc'
  | returnCallRefFrameNull hc' => exact .returnCallRefFrameNull hc'
  | returnCallRefFrameAddr hc' hf he hn => exact .returnCallRefFrameAddr hc' hf he hn
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

theorem steps_transfer {P P' : Profile} (hf : S.has .floatNum = false) (hg : P.grow = P'.grow)
    {host : HostSemantics H} (hh : HostIn S host) {c c' : Config H} (h : Steps P host c c')
    (hc : InFeat S c) : Steps P' host c c' := by
  induction h with
  | refl => exact .refl
  | tail hs h₁ ih => exact .tail ih (step_transfer hf hg h₁ (steps_rtInFeat hh hs hc).1)

/-- The behaviours of a configuration of a float-free feature set only grow when the profile
changes and the grow policy does not. -/
theorem behavioursOf_sub {P P' : Profile} (hf : S.has .floatNum = false) (hg : P.grow = P'.grow)
    {host : HostSemantics H} (hh : HostIn S host) {c : Config H} (hc : InFeat S c) :
    behavioursOf P host c ⊆ behavioursOf P' host c := by
  rintro b (⟨c', r, hs, hc', rfl⟩ | ⟨rfl, ⟨tr, h0, ht⟩⟩)
  · exact Or.inl ⟨c', r, steps_transfer hf hg hh hs hc, hc', rfl⟩
  · have hi : ∀ n, InFeat S (tr n) := trace_rtInFeat hh ht (h0 ▸ hc)
    exact Or.inr ⟨rfl, tr, h0, fun n => step_transfer hf hg (ht n) (hi n).1⟩

end Silmaril.Proofs.Wasm.Models.Micro
