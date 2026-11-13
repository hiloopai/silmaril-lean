module

public import Silmaril.Cerberus.Core.Dynamics.Defs

/-! # Local Core steps for compiler simulations

These rules are parametric in the entire memory and continuation. In particular
introducing memory objects or nested procedures does not change these statements.
Effectful expressions use empty annotations here: source-location annotations
may introduce an additional `setLocation` step and must not be silently erased.
-/

@[expose] public section

namespace Silmaril.Cerberus.Core.Dynamics

/-- Package a deterministic continuation request as an actual LTS transition. -/
theorem step_of_next {file : Program} {labels : Labels} {s : State}
    {control : Control} {frames : List Frame}
    (live : ∀ o, s.control ≠ .halt o)
    (next : request file labels s = .next control frames) :
    Step file labels s .tau ⟨control, frames, s.memory⟩ := by
  apply Step.respond live
  rw [next]
  exact Respond.next

variable (file : Program) (labels : Labels) (memory : Mem.Concrete.State)
    (env : Env) (stack : List Frame)

/-- Reading a literal preserves all objects and suspended callers. -/
theorem step_literal (ann : List Annot) (v : Value Codec.wireModel) :
    Step file labels ⟨.pureExpr (.mk ann () (.val v)) env, stack, memory⟩ .tau
      ⟨.value (runtimeValue v), stack, memory⟩ := by
  apply step_of_next (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling]

/-- Pure let installs a binding continuation without changing memory. -/
theorem step_pure_let (ann : List Annot) (pat : Pattern Sym) (value body : PE) :
    Step file labels ⟨.pureExpr (.mk ann () (.let_ pat value body)) env, stack, memory⟩ .tau
      ⟨.pureExpr value env, .pureBind pat body env :: stack, memory⟩ := by
  apply step_of_next (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling]

/-- Effectful let uses the same state shape even inside a caller or a loop. -/
theorem step_effect_let (pat : Pattern Sym) (value : PE) (body : EE) :
    Step file labels ⟨.effectExpr (.mk [] (.let_ pat value body)) env, stack, memory⟩ .tau
      ⟨.pureExpr value env, .effectBind pat body env :: stack, memory⟩ := by
  apply step_of_next (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling]

theorem step_effect_if (condition : PE) (yes no : EE) :
    Step file labels ⟨.effectExpr (.mk [] (.if_ condition yes no)) env, stack, memory⟩ .tau
      ⟨.pureExpr condition env, .effectIf yes no env :: stack, memory⟩ := by
  apply step_of_next (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling]

/-- Save without parameters enters its body under the existing procedure's
label environment; it does not allocate a new call frame. -/
theorem step_save_empty (label : Sym × BaseType) (body : EE) :
    Step file labels ⟨.effectExpr (.mk [] (.save label [] body)) env, stack, memory⟩ .tau
      ⟨.effectExpr body env, stack, memory⟩ := by
  apply step_of_next (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling]

/-- A zero-argument transfer uses jumpDestination, which retains the nearest
procedure boundary. This applies to backward loop edges and forward returns. -/
theorem step_run_empty (label : Sym) (body : EE) (targetEnv : Env) (frames : List Frame)
    (destination : jumpDestination labels label [] env stack =
      .ok (.effectExpr body targetEnv, frames)) :
    Step file labels ⟨.effectExpr (.mk [] (.run () label [])) env, stack, memory⟩ .tau
      ⟨.effectExpr body targetEnv, frames, memory⟩ := by
  apply step_of_next (by intro o h; cases h)
  by_cases boundary : hasBoundary stack
  all_goals simp [request, requestAux, awaitsScheduling, requestJump, boundary, jump, destination]

/-- C calls first evaluate the callee and retain the full caller continuation.
The type expression is static metadata in this Core transition. -/
theorem step_ccall (ty callee : PE) (args : List PE) :
    Step file labels ⟨.effectExpr (.mk [] (.ccall () ty callee args)) env, stack, memory⟩ .tau
      ⟨.pureExpr callee env, .arguments (.procedure env) [] args env :: stack, memory⟩ := by
  apply step_of_next (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling, arguments]

/-- Enter a known user procedure, installing its own saved-label environment
while retaining every suspended caller frame. Scheduling is explicit in the LTS. -/
theorem step_procedure (callee : Sym) (args : List Val) (body : EE) (bindings : Bindings)
    (ordinary : libraryCall file callee = none)
    (resolved : procedureBody file callee args = .ok (body, bindings)) :
    Step file labels
      ⟨.apply (.procedure env) (.loaded (.specified (.pointer (.function callee))) :: args),
        stack, memory⟩ .tau
      ⟨.effectExpr body (extendEnv bindings env),
        .procedureReturn (Map.ofList (saves body).reverse) :: stack, memory⟩ := by
  apply Step.respond (by intro o h; cases h)
  have next : request file labels
      ⟨.apply (.procedure env) (.loaded (.specified (.pointer (.function callee))) :: args),
        stack, memory⟩ =
      .scheduled [(.effectExpr body (extendEnv bindings env),
        .procedureReturn (Map.ofList (saves body).reverse) :: stack)] := by
    simp [request, requestAux, awaitsScheduling, ordinary, resolved, scheduledRequest]
  rw [next]
  exact Respond.scheduled (by simp)

/-- Applying a pure arithmetic primitive preserves arbitrary memory. The
premise exposes its actual success/overflow check for each arithmetic rung. -/
theorem step_binop (op : BinOp) (args : List Val) (result : Val)
    (computed : primitive (.bin op) args ⟨file.tagDefs, memory.enumTypes⟩ = .ok result) :
    Step file labels ⟨.apply (.bin op) args, stack, memory⟩ .tau
      ⟨.value result, stack, memory⟩ := by
  apply step_of_next (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling, computed]

/-- Finish a pure binding using simultaneous, shadowing substitution. -/
theorem step_pure_bind (pat : Pattern Sym) (body : PE) (value : Val) (bindings : Bindings)
    (matched : matchPattern pat value = some bindings) :
    Step file labels ⟨.value value, .pureBind pat body env :: stack, memory⟩ .tau
      ⟨.pureExpr body (extendEnv bindings env), stack, memory⟩ := by
  apply step_of_next (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling, matched]

/-- Finish a weak binding; the strong-binding rule has the same state shape. -/
theorem step_effect_bind (pat : Pattern Sym) (body : EE) (value : Val) (bindings : Bindings)
    (matched : matchPattern pat value = some bindings) :
    Step file labels ⟨.value value, .effectBind pat body env :: stack, memory⟩ .tau
      ⟨.effectExpr body (extendEnv bindings env), stack, memory⟩ := by
  apply step_of_next (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling, matched]

theorem step_effect_if_true (yes no : EE) :
    Step file labels ⟨.value .true, .effectIf yes no env :: stack, memory⟩ .tau
      ⟨.effectExpr yes env, stack, memory⟩ := by
  apply step_of_next (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling]

theorem step_effect_if_false (yes no : EE) :
    Step file labels ⟨.value .false, .effectIf yes no env :: stack, memory⟩ .tau
      ⟨.effectExpr no env, stack, memory⟩ := by
  apply step_of_next (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling]

/-- Returning from a procedure discards only that procedure's label environment. -/
theorem step_procedure_return (ownLabels : Labels) (value : Val) :
    Step file labels ⟨.value value, .procedureReturn ownLabels :: stack, memory⟩ .tau
      ⟨.value value, stack, memory⟩ := by
  apply step_of_next (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling]

end Silmaril.Cerberus.Core.Dynamics
