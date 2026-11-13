module

public import Silmaril.Wasm.Replace.Congruence.Thms
public import Silmaril.Proofs.Wasm.Replace.Example.Run

/-!
# A non-identity instance of the replacement congruence: theorems

Over the closed host, for the store of `Silmaril.Wasm.Replace.Example.Defs`:

* `replaceFunc_store_ne`: replacing address `0` by address `1` changes the store;
* `callSimOn_Reach`: yet `CallSimOn Reach host ⟨0⟩ ⟨1⟩` holds (both functions return the value
  stack they are invoked on, at any value stack), while `CallSim` at every store fails
  (`not_forall_callSim`);
* **`moduleEquiv_replace_example`**: `moduleEquiv_replaceOn` applies, with every hypothesis
  discharged, and gives module equivalence for the replacement;
* `exists_nontrivial_callSimOn`: the same, as one existential statement.

Ported from an earlier development `Silmaril/Wasm/Equiv/ReplaceExample.lean`, with a
different pair of functions (see `Silmaril.Wasm.Replace.Example.Defs`).
-/

@[expose] public section

namespace Silmaril.Wasm.Replace.Example

open Silmaril.Wasm.V1.Execution
open Silmaril.Wasm.Execution.Runtime

variable (host : HostSemantics Empty)

/-- After the replacement, address `0` holds `idleFn [.i32]`. -/
theorem replaceFunc_store_funcs :
    (store.replaceFunc ⟨0⟩ ⟨1⟩).funcs[(⟨0⟩ : FuncAddr).value]? =
      some (.wasm unitType inst (idleFn [.i32])) := rfl

/-- **The replacement is not the identity.** -/
theorem replaceFunc_store_ne : store.replaceFunc ⟨0⟩ ⟨1⟩ ≠ store := by
  intro h
  have h₀ : (some (.wasm unitType inst (idleFn [.i32])) : Option (FuncInst _ Empty)) =
      some (.wasm unitType inst (idleFn [])) := by
    rw [← replaceFunc_store_funcs, h]; rfl
  have hfn : idleFn [.i32] = idleFn [] := by simpa using h₀
  have hl : [Silmaril.Wasm.V1.ValType.i32] = [] := congrArg (·.locals) hfn
  exact absurd hl (by simp)

/-- `Reach` is closed under reduction: the store has no globals and no memories. -/
theorem stepClosed_Reach : StepClosed host Reach :=
  stepClosed_eq_of_fixed store rfl rfl

/-- The two addresses hold functions of the same type. -/
theorem sameFuncTypeOn_Reach : SameFuncTypeOn Reach ⟨0⟩ ⟨1⟩ := by
  rintro s rfl
  rfl

/-- **`CallSimOn` at the reachable store**, for two distinct addresses. -/
theorem callSimOn_Reach : CallSimOn Reach host ⟨0⟩ ⟨1⟩ := by
  rintro s rfl
  exact callSim_idle (md := inst) (ls := []) rfl (replaceFunc_store_funcs)

/-- At every store, `CallSim` for the pair fails, as for any pair of distinct addresses. -/
theorem not_forall_callSim : ¬ ∀ s : Store Empty, CallSim host ⟨0⟩ ⟨1⟩ s :=
  fun h => absurd (eq_of_forall_callSim h) (by decide)

/-- **The replacement congruence at a non-identity replacement.** -/
theorem moduleEquiv_replace_example :
    ModuleEquiv (· = ·) host store (store.replaceFunc ⟨0⟩ ⟨1⟩) :=
  moduleEquiv_replaceOn (HostRespectsReplace.empty host ⟨0⟩ ⟨1⟩) (stepClosed_Reach host)
    (callSimOn_Reach host) sameFuncTypeOn_Reach rfl

/-- **Non-vacuity, as one statement**: a step-closed `Reach`, a store satisfying it and two
distinct addresses whose replacement changes the store, for which `CallSimOn` holds and the
replacement is a module equivalence. -/
theorem exists_nontrivial_callSimOn :
    ∃ (R : Store Empty → Prop) (s : Store Empty) (a b : FuncAddr),
      R s ∧ a ≠ b ∧ s.replaceFunc a b ≠ s ∧ StepClosed host R ∧ CallSimOn R host a b ∧
        SameFuncTypeOn R a b ∧ ModuleEquiv (· = ·) host s (s.replaceFunc a b) :=
  ⟨Reach, store, ⟨0⟩, ⟨1⟩, rfl, by decide, replaceFunc_store_ne, stepClosed_Reach host,
    callSimOn_Reach host, sameFuncTypeOn_Reach, moduleEquiv_replace_example host⟩

end Silmaril.Wasm.Replace.Example
