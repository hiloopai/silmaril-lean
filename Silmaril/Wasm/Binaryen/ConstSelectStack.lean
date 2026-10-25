module

public import Silmaril.Wasm.Binaryen.ConstSelectMacro
public import Silmaril.Wasm.SingleThreaded.Soundness

@[expose] public section

/-! # Operand availability for typed constant-select configurations

Core progress and inert-head inversion provide the two operand values required
by the local select/drop certificate. The resulting local equivalence permits
any numerical profile, host and continuation. The short-stack witness from
`ConstSelectMacro.lean` cannot satisfy `ConfigOk`.

This discharges the standalone local stack-shape obligation. `ConstSelectAny`
uses the general-context `TypedFragment` arity law and typed closure/module/session
transport for the full recursive closed-host pass.
-/

namespace Silmaril.Wasm.Binaryen.ConstSelect

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- A pending select cannot be a terminal result, regardless of its continuation. -/
theorem select_not_terminal {s : Store H} {f : Frame} {vs : List Val}
    {c : BitVec 32} {ts : Option (List ValType)} {rest : List Admin} :
    ¬ (⟨s, f, vals vs ++ [constI32 c, .plain (.select ts)] ++ rest⟩ : Config H).Terminal := by
  rintro ⟨r, hr⟩
  have hm : Admin.plain (.select ts) ∈ vals vs ++ [constI32 c, .plain (.select ts)] ++ rest := by
    simp
  change vals vs ++ [constI32 c, .plain (.select ts)] ++ rest = r.toAdmin at hr
  rw [hr] at hm
  cases r with
  | values ws => exact (Det.mem_vals hm) rfl
  | trap => simp [Result.toAdmin] at hm
  | throw a => simp [Result.toAdmin] at hm

/-- A typed active select has both operand values, without a numerical-profile hypothesis. -/
theorem select_operands_of_configOk {s : Store H} {f : Frame} {vs : List Val}
    {c : BitVec 32} {ts : Option (List ValType)} {rest : List Admin} {results : List CValType}
    (hok : ConfigOk ⟨s, f, vals vs ++ [constI32 c, .plain (.select ts)] ++ rest⟩ results) :
    ∃ (pre : List Val) (a b : Val), vs = pre ++ [a, b] := by
  obtain ht | ⟨cfg, hs⟩ := Config.progress (P := .spec true) divHost_ok hok
  · exact (select_not_terminal ht).elim
  · have hs' : Step (.spec true) divHost
        ⟨s, f, vals (vs ++ [Val.i32 c]) ++ .plain (.select ts) :: rest⟩ cfg := by
      simpa [vals, Val.i32, constI32, List.append_assoc] using hs
    obtain ⟨pre, args, cfg', hW, hh, he⟩ :=
      SimplifyLocalsLite.inert_head_inv rfl (by simp) rfl hs'
    obtain ⟨a, b, k, rfl, rfl⟩ := head_select hh
    have hW' : vs ++ [Val.i32 c] = (pre ++ [a, b]) ++ [Val.i32 k] := by
      simpa [Val.i32, List.append_assoc] using hW
    exact ⟨pre, a, b, (Det.append_singleton_inj.mp hW').1⟩

/-- Typed local nonzero select/drop equivalence for every numerical profile,
arbitrary host and continuation, with no explicit operand witnesses required. -/
theorem selectTrue_macro_of_configOk {s : Store H} {f : Frame} {vs : List Val}
    {c : BitVec 32} {ts : Option (List ValType)} {rest : List Admin} {results : List CValType}
    (hc : c ≠ 0)
    (hok : ConfigOk ⟨s, f, vals vs ++ [constI32 c, .plain (.select ts)] ++ rest⟩ results) :
    behavioursOf P host ⟨s, f, vals vs ++ [constI32 c, .plain (.select ts)] ++ rest⟩ =
      behavioursOf P host ⟨s, f, vals vs ++ [.plain .drop] ++ rest⟩ := by
  obtain ⟨pre, a, b, rfl⟩ := select_operands_of_configOk hok
  simpa [vals, List.append_assoc] using selectTrue_macro_behaviours
    (P := P) (host := host) (s := s) (f := f) (vs := pre) (a := a) (b := b)
    (ts := ts) (rest := rest) hc

/-- The short-stack operational counterexample is excluded by the typed invariant. -/
theorem selectTrue_short_stack_not_configOk {s : Store H} {f : Frame} (v : Val)
    (ts : Option (List ValType)) (results : List CValType) :
    ¬ ConfigOk ⟨s, f, [v.toAdmin, constI32 1, .plain (.select ts)]⟩ results := by
  intro hok
  have hok' : ConfigOk
      ⟨s, f, vals [v] ++ [constI32 1, .plain (.select ts)] ++ []⟩ results := by
    simpa [vals] using hok
  obtain ⟨pre, a, b, hpre⟩ := select_operands_of_configOk hok'
  have hlen := congrArg List.length hpre
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  omega

end Silmaril.Wasm.Binaryen.ConstSelect
