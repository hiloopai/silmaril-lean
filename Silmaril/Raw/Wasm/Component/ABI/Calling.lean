module

public import Silmaril.Wasm.Component.Reference.ABI.Calling.Defs

public import Silmaril.Raw.Wasm.Component.ABI.Flatten
public import Silmaril.Wasm.V1.Types
public import Mathlib.Tactic.SplitIfs

/-!
# Canonical ABI function calling conventions

These are the static core signatures selected by canonical lift/lower options.
Asynchronous signature calculation does not implement task scheduling,
callbacks, streams, futures, resource ownership, or post-return behavior.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.ABI

universe u

theorem fitParams_length_le (limit : Nat) (positive : 0 < limit) (p : AddrType) (xs : List CoreType) :
    (fitParams limit p xs).length ≤ limit := by
  unfold fitParams
  split <;> simp_all
  omega

/-- Every convention returns at most one core scalar, including async status. -/
theorem flattenFunc_results_le_one {Resource : Type u} (opts : Options) (d : Direction)
    (ft : FuncType Resource) : (flattenFunc opts d ft).results.length ≤ 1 := by
  cases d <;> simp only [flattenFunc]
  all_goals split_ifs <;> simp_all [maxFlatResults]

/-- A lowered synchronous call may add one result pointer beyond the sixteen
ordinary parameter slots. No calling convention exceeds that bound. -/
theorem flattenFunc_params_le_seventeen {Resource : Type u} (opts : Options) (d : Direction)
    (ft : FuncType Resource) : (flattenFunc opts d ft).params.length ≤ 17 := by
  have syncBound := fitParams_length_le 16 (by decide) opts.memory (flattenTypes opts.memory ft.params)
  have asyncBound := fitParams_length_le 4 (by decide) opts.memory (flattenTypes opts.memory ft.params)
  cases d <;> simp only [flattenFunc]
  all_goals split_ifs <;>
    simp only [maxFlatParams, maxFlatAsyncParams, List.length_append, List.length_cons, List.length_nil] <;> omega

/-- The direct synchronous convention preserves all flattened parameter and
result slots when both limits are satisfied. -/
theorem flattenFunc_sync_direct {Resource : Type u} (memory : AddrType) (d : Direction)
    (ft : FuncType Resource)
    (params : (flattenTypes memory ft.params).length ≤ 16)
    (results : (flattenTypes memory ft.results).length ≤ 1) :
    flattenFunc ⟨memory, false, false⟩ d ft =
      ⟨flattenTypes memory ft.params, flattenTypes memory ft.results⟩ := by
  simp [flattenFunc, maxFlatResults, results, fitParams, maxFlatParams, params]

/-- Indirect synchronous lowering consumes a result pointer and returns no
scalar; lifting instead returns the result pointer. -/
theorem flattenFunc_sync_indirect_result {Resource : Type u} (memory : AddrType)
    (ft : FuncType Resource) (results : 1 < (flattenTypes memory ft.results).length) :
    (flattenFunc ⟨memory, false, false⟩ .lower ft).results = [] ∧
    (flattenFunc ⟨memory, false, false⟩ .lift ft).results = [pointerType memory] := by
  have large : ¬ (flattenTypes memory ft.results).length ≤ 1 := by omega
  simp [flattenFunc, maxFlatResults, large]

end Silmaril.Wasm.Component.ABI
