module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Bwd.Control

/-!
# The syntactic decoders, discharged

`StructDecode`'s `label`, `handler` and `frame` fields and `RetDecode` are syntactic facts about
`adminToV`, proved here by a case split over every instruction (family X's
`Exn.adminToV_case` for the three contexts, `instrToV_returnCallRef` for `RETURN_CALL_REF`).
What is left of the decoders the generic backward part needs is the `vals` field
(`structDecode_of_vals`): that a code sequence whose image is a typed `val*` is a value sequence,
which is a fact about the IL type `val` (family E, track "typing").
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Bwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

set_option maxHeartbeats 4000000 in
/-- Only `return_call_ref` is encoded with the tag `RETURN_CALL_REF`. -/
theorem instrToV_returnCallRef {i : Instr} {w : Value}
    (h : instrToV i = .case "RETURN_CALL_REF" w) : ∃ y, i = .returnCallRef y := by
  cases i
  all_goals try first
    | exact ⟨_, rfl⟩
    | exact absurd (Value.case.inj h).1 (by decide)
    | (have h' : schemaInstrV (Silmaril.Wasm.SpecTecEnc.encodeInstruction _) = _ := h
       obtain ⟨w', hw'⟩ := Exn.schemaInstrV_case (Silmaril.Wasm.SpecTecEnc.encodeInstruction _)
       rw [hw'] at h'
       exact absurd (Value.case.inj h').1 (by simp [Silmaril.Wasm.SpecTecEnc.encodeInstruction]))
  iterate 4 (all_goals (try (rename_i x; cases x)))
  all_goals first
    | exact absurd (Value.case.inj h).1 (by decide)
    | exact Value.noConfusion h

/-- **`RetDecode`, proved.** -/
theorem retDecode : RetDecode where
  returnCallRef a x h := by
    cases a with
    | plain i =>
      obtain ⟨y, rfl⟩ := instrToV_returnCallRef h
      exact trivial
    | returnCallRefType d => exact trivial
    | ref r => cases r <;> exact absurd (Value.case.inj h).1 (by decide)
    | callRefType d => exact absurd (Value.case.inj h).1 (by decide)
    | label n c b => exact absurd (Value.case.inj h).1 (by decide)
    | handler n c b => exact absurd (Value.case.inj h).1 (by decide)
    | frame n f b => exact absurd (Value.case.inj h).1 (by decide)
    | trap => exact absurd (Value.case.inj h).1 (by decide)

/-- **`StructDecode` from its `vals` field alone**: the context decoders are syntactic
(`Exn.adminToV_case`). -/
theorem structDecode_of_vals {env : Env}
    (hv : ∀ (ρ : VarEnv) (l : List Admin), ValsOnly ρ → HasTyp env ρ valsT (.list (adminsToV l)) →
      ∃ vs, l = vals vs) : StructDecode env where
  label a x h := by
    obtain ⟨n, cont, body, e, -⟩ := (Exn.adminToV_case h).2.2.2.2.2.2.1 rfl
    exact ⟨n, cont, body, e⟩
  handler a x h := by
    obtain ⟨n, cs, body, e, -⟩ := (Exn.adminToV_case h).2.2.2.2.2.1 rfl
    exact ⟨n, cs, body, e⟩
  frame a x h := by
    obtain ⟨n, fi, body, e, -⟩ := (Exn.adminToV_case h).2.2.2.2.2.2.2 rfl
    exact ⟨n, fi, body, e⟩
  vals := hv

/-- Family C's decoders give `StructDecode`. -/
theorem structDecode_of_ctrl {env : Env} (D : CtrlDecode env) : StructDecode env :=
  structDecode_of_vals D.vals

end Silmaril.Wasm.SpecTec.Sim.Bwd
