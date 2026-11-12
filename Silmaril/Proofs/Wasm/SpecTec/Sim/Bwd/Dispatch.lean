module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.Host
public import Silmaril.Wasm.SpecTec.Sim.IntNumeric.Thms
public import Silmaril.Wasm.SpecTec.Sim.State.Thms

/-!
# The dispatch skeleton

`backwardUpTo_of` assembles `BackwardUpTo (simEnv B)` from every per-rule backward lemma the
families and this track have proved (`pureDone`, `readDone`, `stepDone`), under their decoder
and helper structures (`BwdHyps`), plus one explicit obligation per rule that is still open
(`Remaining`). `simEnv_backward_upTo` composes it with the generic part (`backward_upTo`): it is
the second conjunct of `Task.wholeStepUpTo` for one `B`, conditional on `Remaining`, `BwdHyps`
and `TypingFacts`.

Each index of `pureDone`, `readDone` and `stepDone` is dispatched to its lemma below; every
other index is a field of `Remaining`. `Remaining` therefore lists exactly what is left of the
backward direction, rule by rule.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Bwd

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The `Step_pure` rules with a backward lemma (families N, C, X, M and this track). -/
def pureDone : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] ++
    [15, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 50] ++ [16, 18]

/-- The `Step_read` rules with a backward lemma (families C, X and this track). -/
def readDone : List Nat := [0, 1, 6, 7, 8, 9, 10] ++ [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

/-- The `Step_read` rules dispatched, `readDone` and rule 11, whose lemma holds up to
`CodeEq` only (`bwdUpTo_returnCallRefFrameAddr`). -/
def readDoneUpTo : List Nat := 11 :: readDone

/-- The store-changing `Step` rules with a backward lemma (families C, X and this track). -/
def stepDone : List Nat := [6, 7, 8, 9, 10]

/-- The decoder and helper structures the dispatched lemmas take. None is discharged here
(families E, C, X, M); `CtrlDecode` subsumes `StructDecode` (`structDecode_of_ctrl`). -/
structure BwdHyps (B : Builtins) (hn : H → String) (host : HostSemantics H) : Prop where
  /-- Family C: decoders of `adminToV` at the control tags, and of value sequences. -/
  ctrlDecode : CtrlDecode (simEnv B)
  /-- Family C: `$funcinst`, `$moduleinst`, `$blocktype_` on encoded states. -/
  ctrlState : CtrlState (simEnv B) hn
  /-- Family C: `Expand`, value-type typing and `$default_`. -/
  ctrlCall : CtrlCall (simEnv B)
  /-- Family C: `$hostcall`, `$lift_result` and result/funcinst typing. -/
  ctrlHost : CtrlHost (simEnv B) hn host
  /-- This track: `$hostcall` returns only allowed outcomes. -/
  hostInv : HostInv (simEnv B) hn host
  /-- Family X: typing of addresses, indices, block types and exception instances. -/
  exnTyping : Exn.Typing (simEnv B)
  /-- Family X: the exception store helpers. -/
  exnHelpers : Exn.Helpers (simEnv B) hn
  /-- Family X: decoders. -/
  exnDecoders : Exn.Decoders (simEnv B) hn
  /-- Family M: decoders. -/
  stateDecode : State.StateDecode (simEnv B)
  /-- This track: SpecTec's `Expand` read back. -/
  callInv : CallInv (simEnv B)
  /-- This track: `$blocktype_` read back. -/
  blockInv : BlockInv (simEnv B) hn

/-- **What is left of the backward direction**: one obligation per rule index without a
backward lemma, in the form of the `BackwardUpTo` field. -/
structure Remaining (env : Env) (hn : H → String) (P : Numerics.Profile)
    (host : HostSemantics H) : Prop where
  /-- `Step_pure` outside `pureDone`. -/
  pure : ∀ i, i ∉ pureDone → ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed env hn ⟨s, f, is⟩ → Fires env "Step_pure" i (.tuple [.list (adminsToV is), w]) →
    ∃ is' js, CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- `Step_read` outside `readDoneUpTo`. -/
  read : ∀ i, i ∉ readDoneUpTo → ∀ (c : Config H) (w : Value),
    Typed env hn c → Fires env "Step_read" i (.tuple [configV hn c, w]) →
    ∃ is' js, CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host c ⟨c.store, c.frame, is'⟩
  /-- `Step` (index `≥ 6`) outside `stepDone`. -/
  step : ∀ (i : Nat), 6 ≤ i → i ∉ stepDone → ∀ (c : Config H) (w : Value),
    Typed env hn c → Fires env "Step" i (.tuple [configV hn c, w]) → BwdUpTo hn P host c w

/-- An exact `Step_pure` lemma, up to `CodeEq`. -/
theorem pure_upTo {P : Numerics.Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {is : List Admin} {w : Value}
    (h : ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩) :
    ∃ is' js, CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨is', hw, hs⟩ := h
  exact ⟨is', is', CodeEq.refl _, hw, hs⟩

/-- An exact `Step_read` lemma, up to `CodeEq`. -/
theorem read_upTo {P : Numerics.Profile} {host : HostSemantics H} {c : Config H} {w : Value}
    (h : ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩) :
    ∃ is' js, CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  obtain ⟨is', hw, hs⟩ := h
  exact ⟨is', is', CodeEq.refl _, hw, hs⟩

/-- An exact `Step` lemma, up to `ConfigEq`. -/
theorem step_upTo {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}
    {c : Config H} {w : Value} (h : BwdP hn P host c w) : BwdUpTo hn P host c w := by
  obtain ⟨c', hw, hs⟩ := h
  exact ⟨c', c', ConfigEq.refl _, hw, hs⟩

section Dispatch

variable {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}
variable (B : Builtins) (Hy : BwdHyps B hn host) (T : TypingFacts (simEnv B) hn)

include Hy in
/-- `Step_pure`, the dispatched indices 0–14. -/
theorem pure_done₁ (i : Nat) (hi : i ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14])
    (s : Store H) (f : Frame) (is : List Admin) (w : Value) (hc : Typed (simEnv B) hn ⟨s, f, is⟩)
    (hf : Fires (simEnv B) "Step_pure" i (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  have D := Hy.ctrlDecode
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  exacts [IntNumeric.bwd_unreachable hf, IntNumeric.bwd_nop hf, IntNumeric.bwd_drop hf,
    IntNumeric.bwd_selectTrue hf, IntNumeric.bwd_selectFalse hf, bwd_ifTrue B D s f is w hc hf,
    bwd_ifFalse B D s f is w hc hf, bwd_labelVals B D s f is w hc hf,
    bwd_brLabelZero B D s f is w hc hf, bwd_brLabelSucc B D s f is w hc hf,
    bwd_brHandler B D s f is w hc hf, bwd_brIfTrue B D s f is w hc hf,
    bwd_brIfFalse B D s f is w hc hf, bwd_brTableLt B D s f is w hc hf,
    bwd_brTableGe B D s f is w hc hf]

include Hy in
/-- `Step_pure`, the dispatched indices 15–50. -/
theorem pure_done₂ (i : Nat) (hi : i ∈ [15, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 50])
    (s : Store H) (f : Frame) (is : List Admin) (w : Value) (hc : Typed (simEnv B) hn ⟨s, f, is⟩)
    (hf : Fires (simEnv B) "Step_pure" i (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  have D := Hy.ctrlDecode
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  exacts [bwd_brOnNullNull B D s f is w hc hf, bwd_brOnNonNullNull B D s f is w hc hf,
    bwd_callIndirect B D s f is w hc hf, bwd_returnCallIndirect B D s f is w hc hf,
    bwd_frameVals B D s f is w hc hf, bwd_returnFrame B D s f is w hc hf,
    bwd_returnLabel B D s f is w hc hf, bwd_returnHandler B D s f is w hc hf,
    Exn.bwd_pure_handlerVals (simEnv_execRules B) Hy.exnDecoders s f is w hc hf,
    bwd_trapInstrs B D s f is w hc hf, bwd_trapLabel B D s f is w hc hf,
    bwd_trapHandler B D s f is w hc hf, bwd_trapFrame B D s f is w hc hf,
    State.bwd_pure_localTee B Hy.stateDecode s f is w hc hf, IntNumeric.bwd_testop hf]

include Hy in
/-- `Step_pure`, the two `otherwise` rules. -/
theorem pure_done₃ (i : Nat) (hi : i ∈ [16, 18]) (s : Store H) (f : Frame) (is : List Admin)
    (w : Value) (hc : Typed (simEnv B) hn ⟨s, f, is⟩)
    (hf : Fires (simEnv B) "Step_pure" i (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl
  exacts [bwd_brOnNullAddr B Hy.ctrlDecode s f is w hc hf,
    bwd_brOnNonNullAddr B Hy.ctrlDecode s f is w hc hf]

include Hy in
/-- `Step_pure`, the dispatched indices. -/
theorem pure_done (i : Nat) (hi : i ∈ pureDone) (s : Store H) (f : Frame) (is : List Admin)
    (w : Value) (hc : Typed (simEnv B) hn ⟨s, f, is⟩)
    (hf : Fires (simEnv B) "Step_pure" i (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ :=
  (List.mem_append.1 hi).elim
    (fun h => (List.mem_append.1 h).elim (fun h => pure_done₁ B Hy i h s f is w hc hf)
      (fun h => pure_done₂ B Hy i h s f is w hc hf))
    (fun h => pure_done₃ B Hy i h s f is w hc hf)

include Hy in
/-- `Step_read`, the dispatched indices 0–10 (families C and this track). -/
theorem read_done₁ (i : Nat) (hi : i ∈ [0, 1, 6, 7, 8, 9, 10]) (c : Config H) (w : Value)
    (hc : Typed (simEnv B) hn c) (hf : Fires (simEnv B) "Step_read" i (.tuple [configV hn c, w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  have D := Hy.ctrlDecode
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [bwd_block B D Hy.blockInv c w hc hf, bwd_loop B D Hy.blockInv c w hc hf,
    bwd_call B D Hy.ctrlState c w hc hf, bwd_returnCall B D Hy.ctrlState c w hc hf,
    bwd_returnCallRefLabel B D retDecode c w hc hf,
    bwd_returnCallRefHandler B D retDecode c w hc hf,
    bwd_returnCallRefFrameNull B D retDecode c w hc hf]

include Hy T in
/-- `Step_read`, the dispatched indices 12–22 (family X). -/
theorem read_done₂ (i : Nat) (hi : i ∈ [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22])
    (c : Config H) (w : Value) (hc : Typed (simEnv B) hn c)
    (hf : Fires (simEnv B) "Step_read" i (.tuple [configV hn c, w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  have R := simEnv_readRules B
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Exn.bwd_read_throwRefNull R c w hc hf,
    Exn.bwd_read_throwRefInstrs R Hy.exnDecoders c w hc hf,
    Exn.bwd_read_throwRefLabel R c w hc hf, Exn.bwd_read_throwRefFrame R c w hc hf,
    Exn.bwd_read_throwRefHandlerEmpty R c w hc hf,
    Exn.bwd_read_throwRefHandlerCatch R Hy.exnHelpers c w hc hf,
    Exn.bwd_read_throwRefHandlerCatchRef R Hy.exnHelpers c w hc hf,
    Exn.bwd_read_throwRefHandlerCatchAll R c w hc hf,
    Exn.bwd_read_throwRefHandlerCatchAllRef R c w hc hf,
    Exn.bwd_read_throwRefHandlerNext R T Hy.exnTyping Hy.exnHelpers Hy.exnDecoders c w hc hf,
    Exn.bwd_read_tryTable R Hy.exnHelpers Hy.exnDecoders c w hc hf]

include Hy T in
/-- `Step_read`, the dispatched indices. -/
theorem read_done (i : Nat) (hi : i ∈ readDone) (c : Config H) (w : Value)
    (hc : Typed (simEnv B) hn c) (hf : Fires (simEnv B) "Step_read" i (.tuple [configV hn c, w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ :=
  (List.mem_append.1 hi).elim (fun h => read_done₁ B Hy i h c w hc hf)
    (fun h => read_done₂ B Hy T i h c w hc hf)

include Hy in
/-- `Step`, the dispatched indices. -/
theorem step_done (i : Nat) (hi : i ∈ stepDone) (c : Config H) (w : Value)
    (hc : Typed (simEnv B) hn c) (hf : Fires (simEnv B) "Step" i (.tuple [configV hn c, w])) :
    BwdP hn P host c w := by
  simp only [stepDone, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  exacts [bwd_callRefNull B Hy.ctrlDecode c w hc hf,
    bwd_callRefFunc B Hy.ctrlDecode Hy.ctrlState Hy.ctrlCall Hy.callInv c w hc hf,
    bwd_callRefHost B Hy.ctrlDecode Hy.ctrlState Hy.ctrlHost Hy.hostInv Hy.callInv c w hc hf,
    bwd_callRefHostDiv B Hy.ctrlDecode Hy.ctrlState Hy.hostInv Hy.callInv c w hc hf,
    Exn.bwd_step_throw (hasStepRules_simEnv B) Hy.exnHelpers Hy.exnDecoders c w hc hf]

include Hy T in
/-- **The dispatch**: the families' and this track's lemmas, plus `Remaining`, give
`BackwardUpTo (simEnv B)`. -/
theorem backwardUpTo_of (Rm : Remaining (simEnv B) hn P host) :
    BackwardUpTo (simEnv B) hn P host where
  pure i s f is w hc hf := by
    by_cases hi : i ∈ pureDone
    · exact pure_upTo (pure_done B Hy i hi s f is w hc hf)
    · exact Rm.pure i hi s f is w hc hf
  read i c w hc hf := by
    by_cases h11 : i = 11
    · exact bwdUpTo_returnCallRefFrameAddr B Hy.ctrlDecode Hy.ctrlState Hy.callInv c w hc
        (h11 ▸ hf)
    by_cases hi : i ∈ readDone
    · exact read_upTo (read_done B Hy T i hi c w hc hf)
    · exact Rm.read i (by simp [readDoneUpTo, h11, hi]) c w hc hf
  step i h6 c w hc hf := by
    by_cases hi : i ∈ stepDone
    · exact step_upTo (step_done B Hy i hi c w hc hf)
    · exact Rm.step i h6 hi c w hc hf

include Hy T in
/-- **The backward half of `Task.wholeStepUpTo`, for one `B`**, conditional on the families'
structures `BwdHyps`, the encoding's `TypingFacts` and the open rules `Remaining`. -/
theorem simEnv_backward_upTo (Rm : Remaining (simEnv B) hn P host) (c : Config H) (w : Value)
    (hc : Typed (simEnv B) hn c) (hs : SStep (simEnv B) (configV hn c) w) :
    ∃ c' d', ConfigEq c' d' ∧ w = configV hn d' ∧ Step P host c c' :=
  backward_upTo (backwardUpTo_of B Hy T Rm) (structDecode_of_ctrl Hy.ctrlDecode) T
    (hasStepRules_simEnv B) (findRel_of_ruleAt (simEnv_execRules B).unreachable)
    (findRel_of_ruleAt (simEnv_readRules B).call) c w hc hs

end Dispatch

/-- **`Task.wholeStepUpTo`, reduced.** It follows from: for every injectively named, finitely
branching host and every `nd`, `r`, one `B` with the forward direction up to `ConfigEq`, the
families' structures `BwdHyps`, the encoding's `TypingFacts`, and the open backward rules
`Remaining`. The backward conjunct is `simEnv_backward_upTo`. -/
theorem wholeStepUpTo_of
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → ∀ (nd : Bool) (r : Numerics.RelaxedChoice),
        ∃ B : Builtins,
          (∀ c c' : Config H, Typed (simEnv B) hn c → Typed (simEnv B) hn c' →
            Step (Numerics.Profile.spec nd r) host c c' →
            ∃ d', ConfigEq c' d' ∧ SStep (simEnv B) (configV hn c) (configV hn d')) ∧
          BwdHyps B hn host ∧ TypingFacts (simEnv B) hn ∧
          Remaining (simEnv B) hn (Numerics.Profile.spec nd r) host) :
    Task.wholeStepUpTo := by
  intro H hn hinj host hfin nd r
  obtain ⟨B, hf, Hy, T, Rm⟩ := h H hn hinj host hfin nd r
  exact ⟨B, hf, simEnv_backward_upTo B Hy T Rm⟩

end Silmaril.Wasm.SpecTec.Sim.Bwd
