module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Prims.Default
public import Silmaril.Wasm.SpecTec.Sim.Floats.Thms

/-!
# The concrete `B`: discharging `Whole.Assumptions`

For `B = builtins prof hn host`, every non-typing field of `Whole.Assumptions` is proved here, except
the three in `Residual` (`RefOkBridge`, `RStoreFuns.instReftype`, `CtrlCall.default`; the last is
proved in the integration branch, `Integrate.ctrlCallDefault_simEnv`). The typing parts are taken
as `TypingInputs`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Prims

variable {prof : Silmaril.Wasm.Numerics.Profile}

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Validation (tyV tyV_list tyV_inj)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-! ## Encodings of function types -/

/-- Family C's `FUNC t_1* -> t_2*` is the image of the function type. -/
theorem funcTypeV_eq (ps rs : Ty (.list .val)) : funcTypeV ps rs = tyV (Ty.func ps rs) := by
  simp [funcTypeV, tyV, tyV_list, percentV, caseV]

/-- Family X's `FUNC t* -> eps` is the image of the function type. -/
theorem exnFuncTypeV_eq (ts : Ty (.list .val)) :
    Exn.funcTypeV (ts.toList.map tyV) [] = tyV (Ty.func ts .nil) := by
  simp [Exn.funcTypeV, tyV, tyV_list, percentV, caseV]

/-- An image of a composite type of the shape `FUNC t* -> eps` is a function type with no
results. -/
theorem func_of_tyV {ct : CCompType} {tvs : List Value} (h : Exn.funcTypeV tvs [] = tyV ct) :
    ∃ ts : Ty (.list .val), ct = .func ts .nil ∧ tvs.length = ts.toList.length := by
  match ct, h with
  | .struct _, h => simp [Exn.funcTypeV, tyV] at h
  | .array _, h => simp [Exn.funcTypeV, tyV] at h
  | .func ps rs, h =>
    have hps : Value.list tvs = tyV ps ∧ Value.list [] = tyV rs := by
      simpa [Exn.funcTypeV, tyV, percentV, caseV] using h
    have hrs : rs = .nil := tyV_inj _ _ hps.2.symm
    have hl : tvs = ps.toList.map tyV := by simpa [tyV_list] using hps.1
    exact ⟨ps, by rw [hrs], by rw [hl, List.length_map]⟩

/-! ## The block types, typed -/

/-- `$blocktype_` on images, with typed result types. -/
theorem blocktype_typed {hn : H → String} {host : HostSemantics H}
    (T : TypingInputs (simEnv (builtins prof hn host)) hn) (s : Store H) (f : Frame) (bt : BlockType)
    (t₁ t₂ : List CValType) (h : f.module.blockType? bt = some (t₁, t₂)) :
    ∃ T₁ T₂ : List Value, T₁.length = t₁.length ∧ T₂.length = t₂.length ∧
      TypedV (simEnv (builtins prof hn host)) valtypesT (.list T₁) ∧
      TypedV (simEnv (builtins prof hn host)) valtypesT (.list T₂) ∧
      Applies (simEnv (builtins prof hn host)) "blocktype_"
        [.val (stateV hn s f), .val (Encode.toValue bt)] (Exn.instrTypeV T₁ T₂) := by
  obtain ⟨T₁, T₂, h₁, h₂, hT, ha⟩ := applies_blocktype hn host s f bt t₁ t₂ h
  rcases hT with ⟨ts, rfl, rfl⟩ | ⟨ps, rs, rfl, rfl⟩
  · exact ⟨_, _, h₁, h₂, T.locals [], T.locals ts, ha⟩
  · exact ⟨_, _, h₁, h₂, T.valtypes ps, T.valtypes rs, ha⟩

/-! ## The family structures -/

/-- `FloatB`: `B` answers the float and conversion primitives of `prof` first. -/
theorem floatB_builtins (hn : H → String) (host : HostSemantics H) :
    Floats.FloatB prof (builtins prof hn host) := by
  intro x ws v h
  show call prof hn host x ws = some v
  simp only [call, h]

/-- `IntB`: `B` answers the integer primitives. Where the float primitives answer too, they agree
with them (`Floats.intB_floatIntB`). -/
theorem intB_builtins (hn : H → String) (host : HostSemantics H) :
    IntNumeric.IntB (builtins prof hn host) := by
  intro x ws v h
  show call prof hn host x ws = some v
  cases hf : Floats.floatCall prof x ws with
  | none => simp only [call, hf, h]
  | some w =>
    simp only [call, hf]
    have hfi := Floats.intB_floatIntB prof x ws v h
    have hx : x ∈ Floats.floatNames := by
      by_contra hx
      simp [Floats.floatCall, hx] at hf
    simp only [Floats.floatCall, hx, ite_true] at hf
    simp only [Floats.floatIntB, hx, ite_true] at hfi
    rw [← hf, hfi]

/-- A scope binding term variables only renames no function. -/
theorem findDef_none_of_valsOnly {ρ : VarEnv} (hρ : ValsOnly ρ) (x : IL.Id) :
    ρ.findDef? x = none := by
  simp [VarEnv.findDef?, hρ.2.1]

/-- `RFuns`: `$wrap__` and `$extend__` are answered by the float track's primitives. -/
theorem rFuns_builtins (hn : H → String) (host : HostSemantics H) :
    RefsGC.RFuns (simEnv (builtins prof hn host)) :=
  have F := Floats.rFunsVals_of_floatB (floatB_builtins (prof := prof) hn host)
  ⟨fun ρ e i hρ he => F.wrap ρ hρ e i he, fun ρ es e sg i hρ hs he => F.extend ρ hρ es e sg i hs he⟩

/-- `RStoreFuns`, given `$inst_reftype`. -/
theorem rStoreFuns_builtins (hn : H → String) (host : HostSemantics H)
    (R : Residual (simEnv (builtins prof hn host))) : RefsGC.RStoreFuns (simEnv (builtins prof hn host)) :=
  have P := projDefs_simEnv (builtins prof hn host)
  ⟨fun hn' _ _ s f hρ he => evalExp_callArgs (findDef_none_of_valsOnly hρ _) (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
      (applies_moduleinst P hn' s f),
    fun hn' _ _ s f hρ he => evalExp_callArgs (findDef_none_of_valsOnly hρ _) (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
      (applies_arrayinst P hn' s f),
    fun hn' _ _ s f hρ he => evalExp_callArgs (findDef_none_of_valsOnly hρ _) (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
      (applies_structinst P hn' s f),
    fun hn' ρ ez ey s f y ea ei hρ h hz hy =>
      evalExp_elem_stateV (State.stateDefs_simEnv _) hn' ρ ez ey s f y ea ei h
        (findDef_none_of_valsOnly hρ _) hz hy,
    fun ρ e₁ e₂ m rt hρ => R.instReftype ρ e₁ e₂ m rt (findDef_none_of_valsOnly hρ _)⟩

/-- `CtrlState`. -/
theorem ctrlState_builtins {hn : H → String} {host : HostSemantics H}
    (T : TypingInputs (simEnv (builtins prof hn host)) hn) : CtrlState (simEnv (builtins prof hn host)) hn :=
  ⟨applies_funcinst (projDefs_simEnv _) hn, applies_moduleinst (projDefs_simEnv _) hn,
    blocktype_typed T⟩

/-- `CtrlCall`, given `CtrlCall.default`. -/
theorem ctrlCall_builtins {hn : H → String} {host : HostSemantics H}
    (T : TypingInputs (simEnv (builtins prof hn host)) hn) (R : Residual (simEnv (builtins prof hn host))) :
    CtrlCall (simEnv (builtins prof hn host)) :=
  ⟨fun d ps rs h => by
      rw [funcTypeV_eq]
      exact dderives_expand T.types _ h,
    T.valtypes, T.locals, R.default⟩

/-- `CtrlHost`, for a finite host that respects the encoding. -/
theorem ctrlHost_builtins {hn : H → String} {host : HostSemantics H} (hf : HostFinite host)
    (hr : HostRespects hn host) (T : TypingInputs (simEnv (builtins prof hn host)) hn) :
    CtrlHost (simEnv (builtins prof hn host)) hn host :=
  ⟨ctrlHost_hostcall hf hr, applies_liftResult _, T.result, T.funcinst⟩

/-- `Exn.Helpers`. -/
theorem exnHelpers_builtins {hn : H → String} {host : HostSemantics H}
    (T : TypingInputs (simEnv (builtins prof hn host)) hn) :
    Exn.Helpers (simEnv (builtins prof hn host)) hn :=
  have P := projDefs_simEnv (builtins prof hn host)
  have S := State.stateDefs_simEnv (builtins prof hn host)
  ⟨applies_exninst P hn, applies_tagaddr P hn, applies_tag P S hn, tag_inv hn host,
    applies_asDeftype _, applies_addExn P S hn,
    fun d ts h => ⟨ts.toList.map tyV, List.length_map _, T.valtypes ts, by
      rw [exnFuncTypeV_eq]
      exact dderives_expand T.types _ h⟩,
    fun d tvs h => by
      obtain ⟨ct, hct, he⟩ := expand_of_dderives h
      obtain ⟨ts, rfl, hl⟩ := func_of_tyV he
      exact ⟨ts, hct, by simpa [Ty.length] using hl⟩,
    blocktype_typed T, blocktype_inv hn host⟩

/-! ## The assembly -/

/-- **`Whole.Assumptions` for the concrete `B`**, from the typing parts (`TypingInputs`), the three
residual facts (`Residual`), a finite host and a host that respects the encoding. Every other
field (`IntB`, `RFuns`, `RStoreFuns` but `$inst_reftype`, `CtrlState`, `CtrlCall` but
`$default_`, `CtrlHost`, `Exn.Helpers`) is proved. `Residual.default` is proved separately
(`Integrate.ctrlCallDefault_simEnv`). -/
theorem assumptions_builtins {hn : H → String} {host : HostSemantics H} (hf : HostFinite host)
    (hr : HostRespects hn host) (T : TypingInputs (simEnv (builtins prof hn host)) hn)
    (R : Residual (simEnv (builtins prof hn host))) : Whole.Assumptions (builtins prof hn host) hn host :=
  { typing := T.typing
    intB := intB_builtins hn host
    state := T.state
    rTyping := T.rTyping
    rFuns := rFuns_builtins hn host
    rStore := rStoreFuns_builtins hn host R
    refOk := R.refOk
    ctrlTyping := T.ctrlTyping
    ctrlState := ctrlState_builtins T
    ctrlCall := ctrlCall_builtins T R
    ctrlHost := ctrlHost_builtins hf hr T
    exnTyping := T.exnTyping
    exnHelpers := exnHelpers_builtins T }

end Silmaril.Wasm.SpecTec.Sim.Prims
