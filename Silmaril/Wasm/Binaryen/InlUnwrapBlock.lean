module

public import Silmaril.Wasm.Binaryen.InlUnwrapLabel
public import Silmaril.Wasm.Behaviour.Semantics.CorePrefix
public import Silmaril.Wasm.SingleThreaded.InertHead

@[expose] public section

/-! # Actual block entry and escape-free unwrapping without determinism

The entry step of a block is locally unique when the active stack contains
exactly its parameters. Combined with the direct runtime-label law, this
proves exact unwrapping for the actual block instruction at an arbitrary
numerical profile and host. This is a local certificate, not yet the recursive
module-pass converse or a contextual congruence theorem.
-/

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim SingleThreaded Validation

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- Block entry has a unique successor without requiring later computations
or host calls to be deterministic. -/
theorem block_entry_unique {s : Store H} {f : Frame} {bt : BlockType}
    {body : List Instr} {args : List Val} {ps rs : List CValType}
    (resolved : f.module.blockType? bt = some (ps, rs)) (arity : args.length = ps.length)
    {next : Config H}
    (step : Step P host ⟨s, f, vals args ++ [.plain (.block bt body)]⟩ next) :
    next = ⟨s, f, [.label rs.length [] (vals args ++ expression body)]⟩ := by
  obtain ⟨pre, operands, cfg, stack, head, after⟩ :=
    SingleThreaded.inert_head_inv rfl (by simp) rfl step
  obtain ⟨ps', rs', resolved', operandsArity, cfgEq⟩ := SingleThreaded.head_block head
  rw [resolved] at resolved'
  cases resolved'
  have lengths := congrArg List.length stack
  simp only [List.length_append] at lengths
  have preEmpty : pre = [] := List.length_eq_zero_iff.mp (by omega)
  subst pre
  simp only [List.nil_append] at stack
  subst operands
  rw [cfgEq] at after
  simpa only [vals, List.map_nil, List.nil_append, List.append_nil] using after

/-- The actual block and its unwrapped body have the same observations with
the same arbitrary numerical profile and host. -/
theorem block_behaviours_eq {s : Store H} {f : Frame} {bt : BlockType}
    {body : List Instr} {args : List Val} {ps rs : List CValType}
    (resolved : f.module.blockType? bt = some (ps, rs)) (arity : args.length = ps.length)
    (safe : NoEsc (vals args ++ expression body)) :
    behavioursOf P host ⟨s, f, vals args ++ [.plain (.block bt body)]⟩ =
      behavioursOf P host ⟨s, f, vals args ++ expression body⟩ := by
  exact (behavioursOf_eq_of_step_unique (.block resolved arity)
    (fun _ hs => block_entry_unique resolved arity hs)).trans
      (label_behaviours_eq safe rs.length [])

/-- Actual block unwrapping preserves the complete terminal configuration. -/
theorem block_steps_result_iff {s : Store H} {f : Frame} {bt : BlockType}
    {body : List Instr} {args : List Val} {ps rs : List CValType}
    (resolved : f.module.blockType? bt = some (ps, rs)) (arity : args.length = ps.length)
    (safe : NoEsc (vals args ++ expression body)) {final : Config H}
    (result : Result) (terminal : final.code = result.toAdmin) :
    Steps P host ⟨s, f, vals args ++ [.plain (.block bt body)]⟩ final ↔
      Steps P host ⟨s, f, vals args ++ expression body⟩ final := by
  rw [← label_steps_result_iff safe rs.length [] result terminal]
  constructor
  · intro run
    rcases run.cases_head with rfl | ⟨next, step, rest⟩
    · apply (Step.not_quiet (Step.block (P := P) (host := host) (s := s)
        (body := body) resolved arity)).elim
      rw [terminal]
      cases result with
      | values vs => exact quiet_vals vs
      | throw a => exact quiet_throwing a
      | trap => exact quiet_trap
    · rw [block_entry_unique resolved arity step] at rest
      exact rest
  · exact fun run => .head (.block resolved arity) run

end Silmaril.Wasm.Binaryen.Unwrap
