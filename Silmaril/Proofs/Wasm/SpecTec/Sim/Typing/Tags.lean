module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Heads
public import Silmaril.Wasm.SpecTec.Sim.Control.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Float

/-!
# Decoders: tag inversion, and family C's `CtrlDecode`

`adminToV a = .case op w` determines `a`'s constructor (`adminToV_case`: `op = adminHead a`).
Each inversion below is a case split on `adminHead`, comparing string literals only.
`ctrlDecode_simEnv` discharges family C's decoder interface `CtrlDecode (simEnv B)` (its `vals`
field from the IL type `val`'s cases).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Typing

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.Execution (caseNilV)

/-- Invert an administrative head by cases: every mismatched head is refuted by comparing string
literals (`simp`'s literal simprocs), the matching constructor is named by `simp`. -/
macro "admin_head_inv" : tactic => `(tactic| (
  first
    | (cases ‹Admin› with
        | plain i => cases i <;> simp [adminHead, instrHead, Admin.IsCallRef]
        | ref r => cases r <;> simp [adminHead, refHead]
        | _ => simp [adminHead, Admin.IsCallRef])))

theorem head_trap {a : Admin} (h : adminHead a = "TRAP") : a = .trap := by
  revert h
  admin_head_inv

theorem head_label {a : Admin} (h : adminHead a = "LABEL_%{%}%") :
    ∃ n cont body, a = .label n cont body := by
  revert h
  admin_head_inv

theorem head_handler {a : Admin} (h : adminHead a = "HANDLER_%{%}%") :
    ∃ n cs body, a = .handler n cs body := by
  revert h
  admin_head_inv

theorem head_frame {a : Admin} (h : adminHead a = "FRAME_%{%}%") :
    ∃ n fi body, a = .frame n fi body := by
  revert h
  admin_head_inv

theorem head_ifElse {a : Admin} (h : adminHead a = "IF%%ELSE%") :
    ∃ bt b₁ b₂, a = .plain (.if_ bt b₁ b₂) := by
  revert h
  admin_head_inv

theorem head_brIf {a : Admin} (h : adminHead a = "BR_IF") : ∃ l, a = .plain (.brIf l) := by
  revert h
  admin_head_inv

theorem head_br {a : Admin} (h : adminHead a = "BR") : ∃ l, a = .plain (.br l) := by
  revert h
  admin_head_inv

theorem head_callIndirect {a : Admin} (h : adminHead a = "CALL_INDIRECT") :
    ∃ t y, a = .plain (.callIndirect t y) := by
  revert h
  admin_head_inv

theorem head_returnCallIndirect {a : Admin} (h : adminHead a = "RETURN_CALL_INDIRECT") :
    ∃ t y, a = .plain (.returnCallIndirect t y) := by
  revert h
  admin_head_inv

theorem head_ret {a : Admin} (h : adminHead a = "RETURN") : a = .plain .return_ := by
  revert h
  admin_head_inv

theorem head_brTable {a : Admin} (h : adminHead a = "BR_TABLE") :
    ∃ ls l', a = .plain (.brTable ls l') := by
  revert h
  admin_head_inv

theorem head_call {a : Admin} (h : adminHead a = "CALL") : ∃ y, a = .plain (.call y) := by
  revert h
  admin_head_inv

theorem head_returnCall {a : Admin} (h : adminHead a = "RETURN_CALL") :
    ∃ y, a = .plain (.returnCall y) := by
  revert h
  admin_head_inv

theorem head_refNull {a : Admin} (h : adminHead a = "REF.NULL_ADDR") : a = .ref .null := by
  revert h
  admin_head_inv

theorem head_brOnNull {a : Admin} (h : adminHead a = "BR_ON_NULL") :
    ∃ l, a = .plain (.brOnNull l) := by
  revert h
  admin_head_inv

theorem head_brOnNonNull {a : Admin} (h : adminHead a = "BR_ON_NON_NULL") :
    ∃ l, a = .plain (.brOnNonNull l) := by
  revert h
  admin_head_inv

theorem head_callRef {a : Admin} (h : adminHead a = "CALL_REF") : a.IsCallRef := by
  revert h
  admin_head_inv

theorem head_const {a : Admin} (h : adminHead a = "CONST") :
    (∃ t b, a = .plain (.intConst t b)) ∨ (∃ t b, a = .plain (.floatConst t b)) := by
  revert h
  admin_head_inv

/-- The heads of the IL type `val`'s cases. -/
def valHeads : List MixopS :=
  ["CONST", "VCONST", "REF.I31_NUM", "REF.NULL_ADDR", "REF.STRUCT_ADDR", "REF.ARRAY_ADDR",
    "REF.FUNC_ADDR", "REF.EXN_ADDR", "REF.HOST_ADDR", "REF.EXTERN"]

/-- An administrative instruction with a value head is a value. -/
theorem head_val {a : Admin} (h : adminHead a ∈ valHeads) : ∃ v : Val, a = v.toAdmin := by
  revert h
  cases a with
  | plain i =>
      cases i <;> simp [adminHead, instrHead, valHeads]
      · exact ⟨.num ⟨.int _, _⟩, rfl⟩
      · exact ⟨.num ⟨.float _, _⟩, rfl⟩
      · exact ⟨.vec _, rfl⟩
  | ref r => intro _; exact ⟨.ref r, rfl⟩
  | _ => simp [adminHead, valHeads]

variable {B : Builtins}

set_option maxRecDepth 100000 in
theorem valCases_heads :
    (IntNumeric.instCases Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d269 0).map
      (fun c : TypCase => match c with | .mk o _ _ _ => o) = valHeads := rfl

/-- A typed `val` is a `case` with one of `val`'s heads. -/
theorem head_of_typed_val {ρ : VarEnv} (hρ : ValsOnly ρ) {v : Value}
    (h : HasTyp (simEnv B) ρ (.varT "val" []) v) : ∃ op w, v = .case op w ∧ op ∈ valHeads := by
  have hl : localTyp? ρ "val" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [findTyp_val] at htd
  obtain rfl := (Option.some.inj htd).symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, -, hd⟩ | hrest
  · obtain ⟨op, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 hd
    obtain ⟨t, qs, prems, hm, -⟩ := hasTypCase_mem hc
    have hmem := List.mem_map_of_mem (f := fun c : TypCase => match c with | .mk o _ _ _ => o) hm
    rw [valCases_heads] at hmem
    exact ⟨op, w, rfl, hmem⟩
  · exact absurd hrest not_hasTypInsts_nil

/-- A code sequence whose image is a typed `val*` is a value sequence. -/
theorem vals_of_typed {ρ : VarEnv} (hρ : ValsOnly ρ) :
    ∀ {l : List Admin}, HasTyp (simEnv B) ρ valsT (.list (adminsToV l)) → ∃ vs, l = vals vs
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
      obtain ⟨vs₀, hvs, hl⟩ := hasTyp_iterT_list_iff.1 h
      obtain rfl := (Value.list.inj hvs).symm
      have hall := hasTypList_iff.1 hl
      obtain ⟨op, w, hw, hop⟩ := head_of_typed_val hρ (hall (adminToV a) (by simp [adminsToV]))
      obtain ⟨v, rfl⟩ := head_val ((adminToV_case hw) ▸ hop)
      obtain ⟨vs, rfl⟩ := vals_of_typed hρ (l := l) (hasTyp_iterT_list_iff.2 ⟨_, rfl,
        hasTypList_iff.2 fun u hu => hall u (by simp [adminsToV, hu])⟩)
      exact ⟨v :: vs, rfl⟩

/-- **Family C's decoders hold in every `simEnv B`.** -/
theorem ctrlDecode_simEnv (B : Builtins) : CtrlDecode (simEnv B) where
  trap _ h := head_trap (adminToV_case h).symm
  label _ _ h := head_label (adminToV_case h).symm
  handler _ _ h := head_handler (adminToV_case h).symm
  frame _ _ h := head_frame (adminToV_case h).symm
  constI32 a cv h := by
    rcases head_const (adminToV_case h).symm with ⟨t, b, rfl⟩ | ⟨t, b, rfl⟩
    · cases t with
      | i32 => exact ⟨b, rfl⟩
      | i64 =>
          change valV (.num ⟨.int .i64, b⟩) = _ at h
          simp only [valV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq] at h
          rw [toValue_numType] at h
          simp [Vec.numTypeV, caseNilV] at h
    · change valV (.num ⟨.float t, b⟩) = _ at h
      simp only [valV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq] at h
      rw [toValue_numType] at h
      cases t <;> simp [Vec.numTypeV, caseNilV] at h
  ifElse _ _ h := head_ifElse (adminToV_case h).symm
  brIf _ _ h := head_brIf (adminToV_case h).symm
  callIndirect _ _ h := head_callIndirect (adminToV_case h).symm
  returnCallIndirect _ _ h := head_returnCallIndirect (adminToV_case h).symm
  br _ _ h := head_br (adminToV_case h).symm
  ret _ h := head_ret (adminToV_case h).symm
  brTable _ _ h := head_brTable (adminToV_case h).symm
  call _ _ h := head_call (adminToV_case h).symm
  returnCall _ _ h := head_returnCall (adminToV_case h).symm
  refNull _ h := head_refNull (adminToV_case h).symm
  brOnNull _ _ h := head_brOnNull (adminToV_case h).symm
  brOnNonNull _ _ h := head_brOnNonNull (adminToV_case h).symm
  callRef _ _ h := head_callRef (adminToV_case h).symm
  vals _ _ hρ h := vals_of_typed hρ h

end Silmaril.Wasm.SpecTec.Sim.Typing
