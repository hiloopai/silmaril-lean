module

public import Silmaril.Wasm.SpecTec.Sim.Whole.Defs
public import Silmaril.Wasm.SpecTec.Sim.Control.Thms
public import Silmaril.Wasm.SpecTec.Sim.IntNumeric.Thms
public import Silmaril.Wasm.SpecTec.Sim.State.Thms
public import Silmaril.Wasm.SpecTec.Sim.RefsGC.Thms
public import Silmaril.Wasm.SpecTec.Sim.Exn.Thms
public import Silmaril.Wasm.SpecTec.Sim.Floats.Thms

/-!
# The forward simulation on the covered fragment

`forward_covered`: under the families' `Assumptions`, every Core step from a configuration in the
fragment `Covered` (no uncovered instruction in the active code) is a SpecTec step of the images,
whenever both configurations are typed. The recursion is `Step.rec`, with the four context rules
from `Assembly.lean`; every other constructor is either a family's `fwd_*` lemma or refuted
because its left-hand side holds an uncovered instruction.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Whole

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-! ## The fragment -/

/-- Every instruction of covered code is covered. -/
theorem CoveredCode.mem {l : List Admin} (h : CoveredCode l) {a : Admin} (ha : a ∈ l) :
    Admin.Uncovered a = false :=
  match l, h, ha with
  | _ :: _, .cons hb _ _, .head _ => hb
  | _ :: _, .cons _ _ hl, .tail _ hm => hl.mem hm

/-- Covered code holds no uncovered instruction. -/
theorem not_covered_of_mem {c : Config H} {a : Admin} (hm : a ∈ c.code)
    (hu : Admin.Uncovered a = true) : ¬ Covered c := fun hc => by
  have h : Admin.Uncovered a = false := CoveredCode.mem hc hm
  rw [hu] at h
  exact Bool.noConfusion h

/-- Covered code holds no uncovered instruction (existential form, for `simp`). -/
theorem not_covered_of_exists {c : Config H} (h : ∃ a ∈ c.code, Admin.Uncovered a = true) :
    ¬ Covered c := by
  obtain ⟨a, hm, hu⟩ := h
  exact not_covered_of_mem hm hu

/-- The nested active code of a covered instruction is covered. -/
theorem CoveredCode.inner {l : List Admin} (h : CoveredCode l) {a : Admin} (ha : a ∈ l) :
    CoveredCode (Admin.inner a) :=
  match l, h, ha with
  | _ :: _, .cons _ hi _, .head _ => hi
  | _ :: _, .cons _ _ hl, .tail _ hm => hl.inner hm

/-- Covered code splits over `++`. -/
theorem CoveredCode.append_left : ∀ {l r : List Admin}, CoveredCode (l ++ r) → CoveredCode l
  | [], _, _ => .nil
  | _ :: _, _, .cons ha hi hl => .cons ha hi hl.append_left

/-- Covered code splits over `++`. -/
theorem CoveredCode.append_right : ∀ {l r : List Admin}, CoveredCode (l ++ r) → CoveredCode r
  | [], _, h => h
  | _ :: _, _, .cons _ _ hl => hl.append_right

/-- The redex of `ctxtInstrs` is covered. -/
theorem covered_mid {s : Store H} {f : Frame} {vs : List Val} {is rest : List Admin}
    (h : Covered ⟨s, f, vals vs ++ is ++ rest⟩) {s' : Store H} {f' : Frame} :
    Covered (⟨s', f', is⟩ : Config H) :=
  (CoveredCode.append_left h).append_right

/-- The body of a covered label, handler or frame is covered. -/
theorem covered_inner {s : Store H} {f : Frame} {a : Admin} (h : Covered ⟨s, f, [a]⟩)
    {s' : Store H} {f' : Frame} : Covered (⟨s', f', Admin.inner a⟩ : Config H) :=
  CoveredCode.inner h (List.mem_singleton_self a)

/-- `RETURN_CALL_REF`, in either representation, is uncovered. -/
theorem uncovered_of_isReturnCallRef : ∀ {c : Admin}, c.IsReturnCallRef → Admin.Uncovered c = true
  | .plain (.returnCallRef _), _ => rfl
  | .returnCallRefType _, _ => rfl

/-- A frame returning through `RETURN_CALL_REF` is outside the fragment. -/
theorem not_covered_returnCallRefFrame {s : Store H} {f fi : Frame} {k : Nat} {vs' vs : List Val}
    {a : Nat} {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef) :
    ¬ Covered (⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩ :
      Config H) := fun h =>
  not_covered_of_mem (c := ⟨s, f, vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest⟩) (by simp)
    (uncovered_of_isReturnCallRef hc) (covered_inner h)

/-! ## The sub-families of `Step` -/

section Sub

variable {B : Builtins} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}
  (A : Assumptions B hn host)
include A

/-- Every constructor of `NumericStep`: the integer ones by family N, the float operators and the
conversions by family V's lemmas, whose interfaces the float track discharges
(`Floats.floatTyping_simEnv`, `Floats.floatAgree_simEnv`). -/
theorem fwd_numeric_covered (hF : Floats.FloatB P B) {s : Store H} {f : Frame}
    {is is' : List Admin} (h : NumericStep P is is') :
    FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  have TY : IntNumeric.IntTyping (simEnv B) := IntNumeric.intTyping_simEnv B
  have Fy : Vec.FloatTyping (simEnv B) := Floats.floatTyping_simEnv B
  have FA : Vec.FloatAgree (simEnv B) P := Floats.floatAgree_simEnv hF
  have hr : Silmaril.SpecTec.Equiv.Validation.HasRuleAt (simEnv B) "Step" "%~>%" 0
      Silmaril.SpecTec.Equiv.ExecStepRules.pureRule :=
    (hasStepRules_simEnv B).pure
  have N : Silmaril.SpecTec.Equiv.ExecNumeric.HasNumericRules (simEnv B) :=
    Vec.hasNumericRules_simEnv B
  cases h with
  | @intUnOp t op x =>
    exact if hv : op.valid t = true then IntNumeric.fwd_intUnOp A.intB TY A.typing hv
      else IntNumeric.fwd_intUnOp_invalid A.typing (by simpa using hv)
  | intBinOp hz => exact IntNumeric.fwd_intBinOp A.intB TY A.typing hz
  | intBinOpTrap he => exact IntNumeric.fwd_intBinOpTrap A.intB TY A.typing he
  | intTestOp => exact IntNumeric.fwd_intTestOp TY A.typing
  | intRelOp => exact IntNumeric.fwd_intRelOp TY A.typing
  | floatUnOp hz => exact Vec.fwd_floatUnOp A.typing hr N Fy FA hz
  | floatBinOp hz => exact Vec.fwd_floatBinOp A.typing hr N Fy FA hz
  | floatRelOp => exact Vec.fwd_floatRelOp A.typing hr N Fy FA
  | convert hz => exact Vec.fwd_convert A.typing hr N Fy FA hz
  | convertTrap he => exact Vec.fwd_convertTrap A.typing hr N Fy FA he

omit A in
/-- No `VectorStep` starts in the fragment. -/
theorem not_covered_vector {s : Store H} {f : Frame} {is is' : List Admin}
    (h : VectorStep P is is') : ¬ Covered (⟨s, f, is⟩ : Config H) := by
  cases h <;> exact not_covered_of_exists (by simp [Admin.Uncovered, Instr.Uncovered])

/-- The covered constructors of `TableStep`: `table.get`, `table.set`, `elem.drop`. -/
theorem fwd_table_covered {c c' : Config H} (h : TableStep P c c') (hc : Covered c) :
    FwdP (simEnv B) hn c c' := by
  cases h with
  | getOob h₁ h₂ => exact State.fwd_tableGetOob B A.typing A.state h₁ h₂
  | getVal h₁ h₂ => exact State.fwd_tableGetVal B A.typing A.state h₁ h₂
  | setOob h₁ h₂ => exact State.fwd_tableSetOob B A.typing A.state h₁ h₂
  | setVal h₁ h₂ => exact State.fwd_tableSetVal B A.typing A.state h₁ h₂
  | elemDrop h₁ => exact State.fwd_elemDrop B A.typing A.state h₁
  | _ => exact absurd hc (not_covered_of_exists (by simp [Admin.Uncovered, Instr.Uncovered]))

/-- The covered constructor of `MemoryStep`: `data.drop`. -/
theorem fwd_memory_covered {c c' : Config H} (h : MemoryStep P c c') (hc : Covered c) :
    FwdP (simEnv B) hn c c' := by
  cases h with
  | dataDrop h₁ => exact State.fwd_dataDrop B A.typing A.state h₁
  | _ => exact absurd hc (not_covered_of_exists (by simp [Admin.Uncovered, Instr.Uncovered]))

omit A in
/-- No `AggregateStep` starts in the fragment. -/
theorem not_covered_aggregate {c c' : Config H} (h : AggregateStep c c') : ¬ Covered c := by
  cases h <;> exact not_covered_of_exists (by simp [Admin.Uncovered, Instr.Uncovered])

end Sub

/-! ## The assembly -/

/-- **The forward simulation on the covered fragment.** Under the families' `Assumptions`, for
any numeric profile `P`, every Core step from a configuration whose active code holds no
uncovered instruction is a SpecTec `Step` of the images in `simEnv B`, whenever both
configurations are typed. -/
theorem forward_covered {B : Builtins} {hn : H → String} {P : Numerics.Profile}
    {host : HostSemantics H} (A : Assumptions B hn host) (hF : Floats.FloatB P B) {c c' : Config H}
    (h : Step P host c c') : Covered c → FwdP (simEnv B) hn c c' :=
  have T := A.typing
  have Ty := A.ctrlTyping
  have R := hasStepRules_simEnv B
  Step.rec (motive := fun c c' _ => Covered c → FwdP (simEnv B) hn c c')
    (fun hs _ => IntNumeric.fwd_parametric T hs)
    (fun hs _ => fwd_numeric_covered A hF hs)
    (fun hs hc => absurd hc (not_covered_vector hs))
    (fun hs _ => State.fwd_variable_ B T A.state hs)
    (fun hs hc => fwd_table_covered A hs hc)
    (fun hs hc => fwd_memory_covered A hs hc)
    (fun hs _ => RefsGC.fwd_reference B T A.rTyping A.rFuns A.rStore A.refOk hs)
    (fun hs hc => absurd hc (not_covered_aggregate hs))
    (fun _ hne ih hc => fwd_ctxtInstrs T R.ctxtInstrs hne (ih (covered_mid hc)))
    (fun _ ih hc => fwd_ctxtLabel T R.ctxtLabel (ih (covered_inner hc)))
    (fun _ ih hc => fwd_ctxtHandler T R.ctxtHandler (ih (covered_inner hc)))
    (fun _ ih hc => fwd_ctxtFrame T R.ctxtFrame (ih (covered_inner hc)))
    (fun h₁ h₂ _ => fwd_block B T Ty A.ctrlState h₁ h₂)
    (fun h₁ h₂ _ => fwd_loop B T Ty A.ctrlState h₁ h₂)
    (fun h₁ _ => fwd_ifTrue B T Ty h₁)
    (fun _ => fwd_ifFalse B T Ty)
    (fun _ => fwd_labelVals B T)
    (fun h₁ h₂ _ => fwd_brLabelZero B T Ty h₁ h₂)
    (fun h₁ _ => fwd_brLabelSucc B T Ty h₁)
    (fun _ => fwd_brHandler B T Ty)
    (fun h₁ _ => fwd_brIfTrue B T Ty h₁)
    (fun _ => fwd_brIfFalse B T Ty)
    (fun h₁ _ => fwd_brTableLt B T Ty h₁)
    (fun h₁ _ => fwd_brTableGe B T Ty h₁)
    (fun _ => fwd_brOnNullNull B T Ty)
    (fun h₁ _ => fwd_brOnNullAddr B T Ty h₁)
    (fun _ => fwd_brOnNonNullNull B T Ty)
    (fun h₁ _ => fwd_brOnNonNullAddr B T Ty h₁)
    (fun h₁ _ => RefsGC.fwd_brOnCastSucceed B T A.rTyping A.rStore A.refOk h₁)
    (fun h₁ _ => RefsGC.fwd_brOnCastFail B T A.rTyping A.rStore A.refOk h₁)
    (fun h₁ _ => RefsGC.fwd_brOnCastFailSucceed B T A.rTyping A.rStore A.refOk h₁)
    (fun h₁ _ => RefsGC.fwd_brOnCastFailFail B T A.rTyping A.rStore A.refOk h₁)
    (fun h₁ h₂ _ => fwd_call B T Ty A.ctrlState h₁ h₂)
    (fun h₁ _ => fwd_callRefNull B T Ty h₁)
    (fun h₁ h₂ h₃ h₄ h₅ _ =>
      fwd_callRefFunc B T Ty A.ctrlState A.ctrlCall A.ctrlHost h₁ h₂ h₃ h₄ h₅)
    (fun h₁ h₂ h₃ h₄ h₅ h₆ _ =>
      fwd_callRefHost B T Ty A.ctrlState A.ctrlCall A.ctrlHost h₁ h₂ h₃ h₄ h₅ h₆)
    (fun h₁ h₂ h₃ h₄ h₅ h₆ _ =>
      fwd_callRefHostDiv B T Ty A.ctrlState A.ctrlCall A.ctrlHost h₁ h₂ h₃ h₄ h₅ h₆)
    (fun h₁ h₂ _ => fwd_returnCall B T Ty A.ctrlState h₁ h₂)
    (fun h₁ _ => fwd_returnCallRefLabel B T Ty h₁)
    (fun h₁ _ => fwd_returnCallRefHandler B T Ty h₁)
    (fun h₁ _ => fwd_returnCallRefFrameNull B T Ty h₁)
    (fun h₁ _ _ _ hc => absurd hc (not_covered_returnCallRefFrame h₁))
    (fun _ => fwd_callIndirect B T Ty)
    (fun _ => fwd_returnCallIndirect B T Ty)
    (fun h₁ _ => fwd_frameVals B T h₁)
    (fun h₁ _ => fwd_returnFrame B T Ty h₁)
    (fun _ => fwd_returnLabel B T)
    (fun _ => fwd_returnHandler B T)
    (fun h₁ h₂ h₃ _ => Exn.fwd_throw B T A.exnTyping A.exnHelpers h₁ h₂ h₃)
    (fun _ => Exn.fwd_throwRefNull B T)
    (fun h₁ _ => Exn.fwd_throwRefInstrs B T A.exnTyping h₁)
    (fun _ => Exn.fwd_throwRefLabel B T A.exnTyping)
    (fun _ => Exn.fwd_throwRefFrame B T A.exnTyping)
    (fun _ => Exn.fwd_throwRefHandlerEmpty B T A.exnTyping)
    (fun h₁ h₂ _ => Exn.fwd_throwRefHandlerCatch B T A.exnTyping A.exnHelpers h₁ h₂)
    (fun h₁ h₂ _ => Exn.fwd_throwRefHandlerCatchRef B T A.exnTyping A.exnHelpers h₁ h₂)
    (fun _ => Exn.fwd_throwRefHandlerCatchAll B T A.exnTyping)
    (fun _ => Exn.fwd_throwRefHandlerCatchAllRef B T A.exnTyping)
    (fun h₁ _ => Exn.fwd_throwRefHandlerNext B T A.exnTyping A.exnHelpers h₁)
    (fun h₁ h₂ _ => Exn.fwd_tryTable B T A.exnTyping A.exnHelpers h₁ h₂)
    (fun _ => Exn.fwd_handlerVals B T)
    (fun h₁ _ => fwd_trapInstrs B T h₁)
    (fun _ => fwd_trapLabel B T)
    (fun _ => fwd_trapHandler B T)
    (fun _ => fwd_trapFrame B T)
    h

end Silmaril.Wasm.SpecTec.Sim.Whole
