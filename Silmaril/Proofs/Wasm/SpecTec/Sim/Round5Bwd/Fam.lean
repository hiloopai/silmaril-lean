module

public import Silmaril.Wasm.SpecTec.Sim.Round5Bwd.Defs

/-!
# Round 5: the family rules backward, without `Bwd.BwdHyps`

`Round4Int.FamBwdV` restates rounds 1–3's family rules rule by rule. Their lemmas took the bundle
`Bwd.BwdHyps`, which is refuted (`ConfigOk.not_ctrlCall`). The lemmas only read the inverse
fields of its structures, so they now take the smaller structures `CtrlReads`, `CtrlDefault`,
`CtrlLift` and `Exn.HelpersInv` (the full structures coerce to them). Each of those holds for the
concrete builtins, so every rule of `FamBwdV` follows except the two host-call rules
(`HostStepsV`), which need `Bwd.HostInv`.

* `ctrlReads_builtins`, `ctrlDefault_builtins`, `ctrlLift_builtins`, `helpersInv_builtins`,
  `decoders_builtins`: the structures, for `Prims.builtins`.
* `fam_pure`, `fam_read`, `fam_step`: the three fields of `FamBwdV`, the last for `i ∉ [8, 9]`.
* `hostStepsV_of_hostInv`, `famBwdV_of_hostSteps`, `famBwdV_of_hostRespects`: the assembly.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Bwd

open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation (Ty)
open Silmaril.Wasm.Numerics (Profile)
open Round4Read (ReadValid)
open Round4Int (BI FamBwdV)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- `$funcinst` and `$moduleinst` on images, for the concrete builtins. -/
theorem ctrlReads_builtins : CtrlReads (simEnv (BI P hn host)) hn :=
  ⟨Prims.applies_funcinst (Prims.projDefs_simEnv _) hn,
    Prims.applies_moduleinst (Prims.projDefs_simEnv _) hn⟩

/-- `$default_`, for the concrete builtins. -/
theorem ctrlDefault_builtins : CtrlDefault (simEnv (BI P hn host)) :=
  ⟨Integrate.ctrlCallDefault_simEnv _⟩

/-- `$lift_result`, for the concrete builtins. -/
theorem ctrlLift_builtins : CtrlLift (simEnv (BI P hn host)) :=
  ⟨Prims.applies_liftResult _⟩

/-- **The store helpers read back**, for the concrete builtins: `Prims.exnHelpers_builtins`
without the two forward fields, so without `Prims.TypingInputs`. -/
theorem helpersInv_builtins : Exn.HelpersInv (simEnv (BI P hn host)) hn where
  exninst := Prims.applies_exninst (Prims.projDefs_simEnv _) hn
  tagaddr := Prims.applies_tagaddr (Prims.projDefs_simEnv _) hn
  tag := Prims.applies_tag (Prims.projDefs_simEnv _) (State.stateDefs_simEnv _) hn
  tag_inv := Prims.tag_inv hn host
  asDeftype := Prims.applies_asDeftype _
  addExn := Prims.applies_addExn (Prims.projDefs_simEnv _) (State.stateDefs_simEnv _) hn
  expand_inv d tvs h := by
    obtain ⟨ct, hct, he⟩ := Prims.expand_of_dderives h
    obtain ⟨ts, rfl, hl⟩ := Prims.func_of_tyV he
    exact ⟨ts, hct, by simpa [Ty.length] using hl⟩
  blocktype_inv := Prims.blocktype_inv hn host

/-- The exception decoders, for every `B`. -/
theorem decoders_builtins (B : Builtins) : Exn.Decoders (simEnv B) hn :=
  ⟨fun ρ hρ l h => (Typing.ctrlDecode_simEnv _).vals ρ l hρ h, ConfigOk.exnFields_simEnv B hn⟩

/-- `FamBwdV.pure` at the rules 0–14. -/
theorem fam_pure₁ (i : Nat) (hi : i ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14])
    (s : Store H) (f : Frame) (is : List Admin) (w : Value)
    (hc : Typed (simEnv (BI P hn host)) hn ⟨s, f, is⟩)
    (hf : Fires (simEnv (BI P hn host)) "Step_pure" i (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  have D := Typing.ctrlDecode_simEnv (BI P hn host)
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  exacts [IntNumeric.bwd_unreachable hf, IntNumeric.bwd_nop hf, IntNumeric.bwd_drop hf,
    IntNumeric.bwd_selectTrue hf, IntNumeric.bwd_selectFalse hf, bwd_ifTrue _ D s f is w hc hf,
    bwd_ifFalse _ D s f is w hc hf, bwd_labelVals _ D s f is w hc hf,
    Bwd.bwd_brLabelZero _ D s f is w hc hf, bwd_brLabelSucc _ D s f is w hc hf,
    bwd_brHandler _ D s f is w hc hf, bwd_brIfTrue _ D s f is w hc hf,
    bwd_brIfFalse _ D s f is w hc hf, bwd_brTableLt _ D s f is w hc hf,
    bwd_brTableGe _ D s f is w hc hf]

/-- `FamBwdV.pure` at the rules 15–50. -/
theorem fam_pure₂ (i : Nat)
    (hi : i ∈ [15, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 50])
    (s : Store H) (f : Frame) (is : List Admin) (w : Value)
    (hc : Typed (simEnv (BI P hn host)) hn ⟨s, f, is⟩)
    (hf : Fires (simEnv (BI P hn host)) "Step_pure" i (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  have D := Typing.ctrlDecode_simEnv (BI P hn host)
  have Dc : Exn.Decoders (simEnv (BI P hn host)) hn := decoders_builtins _
  have Sd := Typing.stateDecode_simEnv (BI P hn host)
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  exacts [bwd_brOnNullNull _ D s f is w hc hf, bwd_brOnNonNullNull _ D s f is w hc hf,
    bwd_callIndirect _ D s f is w hc hf, bwd_returnCallIndirect _ D s f is w hc hf,
    Bwd.bwd_frameVals _ D s f is w hc hf, Bwd.bwd_returnFrame _ D s f is w hc hf,
    bwd_returnLabel _ D s f is w hc hf, bwd_returnHandler _ D s f is w hc hf,
    Exn.bwd_pure_handlerVals (simEnv_execRules _) Dc s f is w hc hf,
    bwd_trapInstrs _ D s f is w hc hf, bwd_trapLabel _ D s f is w hc hf,
    bwd_trapHandler _ D s f is w hc hf, bwd_trapFrame _ D s f is w hc hf,
    State.bwd_pure_localTee _ Sd s f is w hc hf, IntNumeric.bwd_testop hf]

/-- **`FamBwdV.pure`**, for the concrete builtins: rounds 1–3's `Step_pure` lemmas
(`Bwd.pure_done₁`–`₃` with the concrete decoders in place of `BwdHyps`). -/
theorem fam_pure (i : Nat) (hi : i ∈ Bwd.pureDone) (s : Store H) (f : Frame) (is : List Admin)
    (w : Value) (hc : Typed (simEnv (BI P hn host)) hn ⟨s, f, is⟩)
    (hf : Fires (simEnv (BI P hn host)) "Step_pure" i (.tuple [.list (adminsToV is), w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  rcases List.mem_append.1 hi with h | h
  · rcases List.mem_append.1 h with h | h
    · exact fam_pure₁ i h s f is w hc hf
    · exact fam_pure₂ i h s f is w hc hf
  · have D := Typing.ctrlDecode_simEnv (BI P hn host)
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl
    · exact Bwd.bwd_brOnNullAddr _ D s f is w hc hf
    · exact Bwd.bwd_brOnNonNullAddr _ D s f is w hc hf

/-- `FamBwdV.read` at the rules 0–10 of `Bwd.readDone`. -/
theorem fam_read₁ (i : Nat) (hi : i ∈ [0, 1, 6, 7, 8, 9, 10]) (c : Config H) (w : Value)
    (hc : Typed (simEnv (BI P hn host)) hn c)
    (hf : Fires (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  have D := Typing.ctrlDecode_simEnv (BI P hn host)
  have S : CtrlReads (simEnv (BI P hn host)) hn := ctrlReads_builtins
  have Bi : Bwd.BlockInv (simEnv (BI P hn host)) hn := Integrate.blockInv_concrete
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Bwd.bwd_block _ D Bi c w hc hf, Bwd.bwd_loop _ D Bi c w hc hf,
    bwd_call _ D S c w hc hf, bwd_returnCall _ D S c w hc hf,
    Bwd.bwd_returnCallRefLabel _ D Bwd.retDecode c w hc hf,
    Bwd.bwd_returnCallRefHandler _ D Bwd.retDecode c w hc hf,
    Bwd.bwd_returnCallRefFrameNull _ D Bwd.retDecode c w hc hf]

/-- `FamBwdV.read` at the rules 12–22 of `Bwd.readDone` (family X). -/
theorem fam_read₂ (i : Nat) (hi : i ∈ [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22])
    (c : Config H) (w : Value) (hc : Typed (simEnv (BI P hn host)) hn c)
    (hf : Fires (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, w])) :
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  have R := simEnv_readRules (BI P hn host)
  have T := Typing.typingFacts_simEnv (BI P hn host) hn
  have Hp : Exn.HelpersInv (simEnv (BI P hn host)) hn := helpersInv_builtins
  have Dc : Exn.Decoders (simEnv (BI P hn host)) hn := decoders_builtins _
  have X := Typing.exnTyping_simEnv' (BI P hn host)
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Exn.bwd_read_throwRefNull R c w hc hf, Exn.bwd_read_throwRefInstrs R Dc c w hc hf,
    Exn.bwd_read_throwRefLabel R c w hc hf, Exn.bwd_read_throwRefFrame R c w hc hf,
    Exn.bwd_read_throwRefHandlerEmpty R c w hc hf,
    Exn.bwd_read_throwRefHandlerCatch R Hp c w hc hf,
    Exn.bwd_read_throwRefHandlerCatchRef R Hp c w hc hf,
    Exn.bwd_read_throwRefHandlerCatchAll R c w hc hf,
    Exn.bwd_read_throwRefHandlerCatchAllRef R c w hc hf,
    Exn.bwd_read_throwRefHandlerNext R T X Hp Dc c w hc hf,
    Exn.bwd_read_tryTable R Hp Dc c w hc hf]

/-- **`FamBwdV.read`**, for the concrete builtins: `Step_read` 11 (up to `CodeEq`) and
`Bwd.readDone`. -/
theorem fam_read (i : Nat) (hi : i ∈ Bwd.readDoneUpTo) (c : Config H) (w : Value)
    (hc : Typed (simEnv (BI P hn host)) hn c)
    (hf : Fires (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩ := by
  by_cases h11 : i = 11
  · subst h11
    exact Bwd.bwdUpTo_returnCallRefFrameAddr _ (Typing.ctrlDecode_simEnv _) ctrlReads_builtins
      Integrate.callInv_concrete c w hc hf
  have h₀ : i ∈ Bwd.readDone := by simpa [Bwd.readDoneUpTo, h11] using hi
  refine Bwd.read_upTo ?_
  rcases List.mem_append.1 h₀ with h | h
  · exact fam_read₁ i h c w hc hf
  · exact fam_read₂ i h c w hc hf

/-- **`FamBwdV.step` outside the host-call rules**, for the concrete builtins: `Step` 6
(`call_ref-null`), 7 (`call_ref-func`) and 10 (`throw`). -/
theorem fam_step (i : Nat) (hi : i ∈ Bwd.stepDone) (h89 : i ∉ [8, 9]) (c : Config H) (w : Value)
    (hc : Typed (simEnv (BI P hn host)) hn c)
    (hf : Fires (simEnv (BI P hn host)) "Step" i (.tuple [configV hn c, w])) :
    Bwd.BwdUpTo hn P host c w := by
  have D := Typing.ctrlDecode_simEnv (BI P hn host)
  refine Bwd.step_upTo ?_
  simp only [Bwd.stepDone, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact bwd_callRefNull _ D c w hc hf
  · exact Bwd.bwd_callRefFunc _ D ctrlReads_builtins ctrlDefault_builtins
      Integrate.callInv_concrete c w hc hf
  · exact absurd (by simp) h89
  · exact absurd (by simp) h89
  · exact Exn.bwd_step_throw (hasStepRules_simEnv _) helpersInv_builtins (decoders_builtins _)
      c w hc hf

/-- **`HostStepsV` from `$hostcall` read back** (`Bwd.HostInv`), for the concrete builtins. -/
theorem hostStepsV_of_hostInv (Hi : Bwd.HostInv (simEnv (BI P hn host)) hn host) :
    HostStepsV (simEnv (BI P hn host)) hn P host := by
  intro i hi c w _ hc hf
  have D := Typing.ctrlDecode_simEnv (BI P hn host)
  refine Bwd.step_upTo ?_
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl
  · exact Bwd.bwd_callRefHost _ D ctrlReads_builtins ctrlLift_builtins Hi
      Integrate.callInv_concrete c w hc hf
  · exact Bwd.bwd_callRefHostDiv _ D ctrlReads_builtins Hi Integrate.callInv_concrete c w hc hf

/-- **`FamBwdV` for the concrete builtins, from the two host-call rules alone.** -/
theorem famBwdV_of_hostSteps (Hh : HostStepsV (simEnv (BI P hn host)) hn P host) :
    FamBwdV (simEnv (BI P hn host)) hn P host where
  pure i h s f is w _ hc hf := Bwd.pure_upTo (fam_pure i h s f is w hc hf)
  read i h c w _ hc hf := fam_read i h c w hc hf
  step i h c w hv hc hf := by
    by_cases h89 : i ∈ [8, 9]
    · exact Hh i h89 c w hv hc hf
    · exact fam_step i h h89 c w hc hf

/-- **`FamBwdV` for the concrete builtins**, for a finite host that respects the encoding. -/
theorem famBwdV_of_hostRespects (hf : HostFinite host) (hr : Prims.HostRespects hn host) :
    FamBwdV (simEnv (BI P hn host)) hn P host :=
  famBwdV_of_hostSteps (hostStepsV_of_hostInv (Integrate.hostInv_concrete hf hr))

end Silmaril.Wasm.SpecTec.Sim.Round5.Bwd
