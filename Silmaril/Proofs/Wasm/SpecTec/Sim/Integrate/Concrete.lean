module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Integrate.Forward
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Integrate.Default
public import Silmaril.Wasm.SpecTec.Sim.BwdPureStep.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdRead.Dispatch

/-!
# Round 2 integration: the concrete `B`, both directions

For `B := Prims.builtins prof hn host` (the float, integer and control primitives of the
builtins and float tracks), this file discharges what the tracks proved and leaves the rest as
the explicit bundles `Residue` (forward) and `BwdOpen` (backward):

* `assumptions_concrete`: `Whole.Assumptions B hn host` from `Residue`, a finite host and a host
  respecting the encoding, with every typing field from the typing track;
* `bwdHyps_concrete`: `Bwd.BwdHyps B hn host` from `Residue` and `BwdOpen`, with the decoders
  from the typing track, the control and exception helpers from the builtins track, and
  `CallInv`, `BlockInv` from the builtins track's `expand_of_dderives`, `blocktype_inv`;
* `remaining_concrete`: `Bwd.Remaining` from `RemainingW`, the float track's backward lemmas
  covering `Step_pure` 46–49 and 51–53.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Integrate

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV tyV_inj)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type} {prof : Numerics.Profile} {hn : H → String} {host : HostSemantics H}

/-- Every list of encoded source value types is a `valtype*`. -/
theorem locals_simEnv (B : Builtins) (ts : List ValType) :
    TypedV (simEnv B) valtypesT (.list (ts.map Encode.toValue)) := fun ρ hρ =>
  hasTyp_iterT_list_iff.2 ⟨_, rfl, hasTypList_iff.2 fun w hw => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hw
    exact Typing.typedV_valtype t ρ hρ⟩

/-- The builtins track's `TypingInputs`, from the typing track's proofs and `Residue`. -/
theorem typingInputs_concrete (O : Residue (simEnv (Prims.builtins prof hn host)) hn) :
    Prims.TypingInputs (simEnv (Prims.builtins prof hn host)) hn :=
  { typing := Typing.typingFacts_simEnv _ hn
    state := Typing.stateTyping_simEnv _
    rTyping := Typing.rTyping_simEnv _
    ctrlTyping := Typing.ctrlTyping_simEnv _
    exnTyping := Typing.exnTyping_simEnv' _
    types := O.types
    valtypes := O.valtypes
    locals := locals_simEnv _
    result := O.result
    funcinst := O.funcinst }

/-- The builtins track's `Residual`, with `CtrlCall.default` proved. -/
theorem residual_concrete (O : Residue (simEnv (Prims.builtins prof hn host)) hn) :
    Prims.Residual (simEnv (Prims.builtins prof hn host)) :=
  ⟨O.refOk, O.instReftype, ctrlCallDefault_simEnv _⟩

/-- **`Whole.Assumptions` for the concrete `B`**, from `Residue` alone (plus a finite host that
respects the encoding). -/
theorem assumptions_concrete (hf : HostFinite host) (hr : Prims.HostRespects hn host)
    (O : Residue (simEnv (Prims.builtins prof hn host)) hn) :
    Whole.Assumptions (Prims.builtins prof hn host) hn host :=
  Prims.assumptions_builtins hf hr (typingInputs_concrete O) (residual_concrete O)

/-- The composite type of an image `FUNC %(T₁) -> %(T₂)` is a function type of those arities. -/
theorem func2_of_tyV {ct : CCompType} {T₁ T₂ : List Value}
    (h : Value.case "FUNC%->%" (.tuple [.case "%" (.tuple [.list T₁]), .case "%" (.tuple [.list T₂])])
      = tyV ct) :
    ∃ ps rs : Ty (.list .val), ct = .func ps rs ∧ T₁.length = ps.length ∧ T₂.length = rs.length := by
  match ct, h with
  | .struct _, h => simp [tyV] at h
  | .array _, h => simp [tyV] at h
  | .func ps rs, h =>
    have hps : Value.list T₁ = tyV ps ∧ Value.list T₂ = tyV rs := by
      simpa [tyV, percentV, caseV]
        using h
    refine ⟨ps, rs, rfl, ?_, ?_⟩
    · have h₁ := hps.1
      rw [Silmaril.SpecTec.Equiv.Validation.tyV_list] at h₁
      simp only [Value.list.injEq] at h₁
      simp [h₁, Ty.length]
    · have h₂ := hps.2
      rw [Silmaril.SpecTec.Equiv.Validation.tyV_list] at h₂
      simp only [Value.list.injEq] at h₂
      simp [h₂, Ty.length]

/-- `Bwd.CallInv` for the concrete `B`: SpecTec's `Expand` on images is Core's. -/
theorem callInv_concrete : Bwd.CallInv (simEnv (Prims.builtins prof hn host)) := by
  refine ⟨fun d T₁ T₂ h => ?_⟩
  obtain ⟨ct, hct, he⟩ := Prims.expand_of_dderives h
  obtain ⟨ps, rs, rfl, h₁, h₂⟩ := func2_of_tyV he
  exact ⟨ps, rs, hct, h₁, h₂⟩

/-- `Bwd.BlockInv` for the concrete `B`: `$blocktype_` read back. -/
theorem blockInv_concrete : Bwd.BlockInv (simEnv (Prims.builtins prof hn host)) hn :=
  ⟨fun s f bt T₁ T₂ h => Prims.blocktype_inv hn host s f bt T₁ T₂ h⟩

/-- **`Bwd.HostInv` for the concrete `B`**: every member of `$hostcall`'s result is an outcome
the host allows. `$hostcall` lists the outcomes of a chosen call with the same image; a host
respecting the encoding (`HostRespects`, used from the chosen call back to the given one) allows
an outcome with the same image. -/
theorem hostInv_concrete (hf : HostFinite host) (hr : Prims.HostRespects hn host) :
    Bwd.HostInv (simEnv (Prims.builtins prof hn host)) hn host := by
  classical
  refine ⟨fun h s vs v x happ hm => ?_⟩
  have hex : ∃ p : H × Store H × List Val,
      Prims.hostArgs hn h s vs = Prims.hostArgs hn p.1 p.2.1 p.2.2 ∧
      ∃ os : List (Silmaril.Wasm.Execution.Host.Outcome (Store H) Result),
        ∀ o, host p.1 p.2.1 p.2.2 o ↔ o ∈ os := ⟨(h, s, vs), rfl, hf h s vs⟩
  have hcall : (Prims.builtins prof hn host).call "hostcall" (Prims.hostArgs hn h s vs) =
      some (.list (hex.choose_spec.2.choose.map (outcomeV hn))) := by
    rw [Prims.call_hostcall, Prims.hostcallCall]
    split
    · rfl
    · contradiction
  have happ' : Silmaril.SpecTec.Equiv.ExecNumeric.Applies (simEnv (Prims.builtins prof hn host))
      "hostcall" (Prims.hostArgs hn h s vs) (.list (hex.choose_spec.2.choose.map (outcomeV hn))) :=
    Prims.applies_of_noClause (Prims.findDef_hostcall _) hcall
  have hv : v = .list (hex.choose_spec.2.choose.map (outcomeV hn)) := happ.unique happ'
  have hmem : x ∈ hex.choose_spec.2.choose.map (outcomeV hn) := by
    rw [hv] at hm
    simpa [memValue] using hm
  obtain ⟨o', ho', hx⟩ := List.mem_map.1 hmem
  have hho' : host hex.choose.1 hex.choose.2.1 hex.choose.2.2 o' :=
    (hex.choose_spec.2.choose_spec o').2 ho'
  obtain ⟨o, ho, he⟩ := hr _ _ _ _ _ _ hex.choose_spec.1.symm o' hho'
  exact ⟨o, ho, hx.symm.trans he⟩

/-- **`Bwd.BwdHyps` for the concrete `B`**, from `Residue` and `BwdOpen`. -/
theorem bwdHyps_concrete (hf : HostFinite host) (hr : Prims.HostRespects hn host)
    (O : Residue (simEnv (Prims.builtins prof hn host)) hn)
    (Bo : BwdOpen (Prims.builtins prof hn host) hn prof host) :
    Bwd.BwdHyps (Prims.builtins prof hn host) hn host :=
  have T := typingInputs_concrete O
  { ctrlDecode := Typing.ctrlDecode_simEnv _
    ctrlState := Prims.ctrlState_builtins T
    ctrlCall := Prims.ctrlCall_builtins T (residual_concrete O)
    ctrlHost := Prims.ctrlHost_builtins hf hr T
    hostInv := hostInv_concrete hf hr
    exnTyping := Typing.exnTyping_simEnv' _
    exnHelpers := Prims.exnHelpers_builtins T
    exnDecoders := ⟨fun ρ hρ l h => (Typing.ctrlDecode_simEnv _).vals ρ l hρ h, Bo.exnFields⟩
    stateDecode := Typing.stateDecode_simEnv _
    callInv := callInv_concrete
    blockInv := blockInv_concrete }

/-- The float track's `Step_pure` rules (`floatDone`), backward, up to `CodeEq`. -/
theorem pure_floatDone {B : Builtins} (hI : IntNumeric.IntB B) (hF : Floats.FloatB prof B)
    {i : Nat} (hd : i ∈ floatDone) {s : Store H} {f : Frame} {is : List Admin} {w : Value}
    (hfi : Fires (simEnv B) "Step_pure" i (.tuple [.list (adminsToV is), w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧
      Step prof host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  simp only [floatDone, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bwd.pure_upTo (Floats.bwd_unopVal hI hF hfi)
  · exact (Floats.bwd_unopTrap hI hF hfi).elim
  · exact Bwd.pure_upTo (Floats.bwd_binopVal hI hF hfi)
  · exact Bwd.pure_upTo (Floats.bwd_binopTrap hI hF hfi)
  · exact Bwd.pure_upTo (Floats.bwd_relop hF hfi)
  · exact Bwd.pure_upTo (Floats.bwd_cvtopVal hF hfi)
  · exact Bwd.pure_upTo (Floats.bwd_cvtopTrap hF hfi)

/-- **`Bwd.Remaining` for any `B` with the integer and float primitives and no accessor
entries**, from `RemainingW`: the float track's backward lemmas cover `Step_pure` 46–49 and
51–53, `Step_pure` 31–45 and `Step` 11–14, 17, 18, 20, 28, 30, 33, 34
(under `BwdPureStep.BwdB`), and the bwd-read track's `Step_read` `BwdRead.readDone`. -/
theorem remaining_of_w {B : Builtins} (hI : IntNumeric.IntB B) (hF : Floats.FloatB prof B)
    (Hb : BwdPureStep.BwdB B) (NA : BwdRead.NoAcc B)
    (R : RemainingW (simEnv B) hn prof host) : Bwd.Remaining (simEnv B) hn prof host where
  pure i hi s f is w hc hfi :=
    if hd : i ∈ floatDone then pure_floatDone hI hF hd hfi
    else if h3 : i ∈ BwdPureStep.pureDone then Bwd.pure_upTo (BwdPureStep.pure_done B Hb i h3 hfi)
    else R.pure i hi hd h3 s f is w hc hfi
  read i hi c w hc hfi :=
    if hd : i ∈ BwdRead.readDone then Bwd.read_upTo (BwdRead.read_done B NA i hd c w hc hfi)
    else R.read i hi hd c w hc hfi
  step i h6 hi c w hc hfi :=
    if h3 : i ∈ BwdPureStep.stepDone then Bwd.step_upTo (BwdPureStep.step_done B Hb i h3 hfi)
    else R.step i h6 hi h3 c w hc hfi

end Silmaril.Wasm.SpecTec.Sim.Integrate
