module

public import Silmaril.Wasm.Component.FXRes.ContEngine.Defs
public import Silmaril.Proofs.Wasm.Component.FXRes.ContEngine.Basic

/-!
# The WasmFX engine with a continuation table: results

Proofs of the step lemmas in `Silmaril.Proofs.Wasm.Component.FXRes.ContEngine.Basic`.

* `bstep_tab`, `internalC_tab`: a built-in call of `fxCE P` moves the continuation table by its
  table event; every other internal step keeps the table. `prepareC_tab`, `allocHostC_tab`,
  `memWriteC_tab`: instantiation, host-function allocation and memory writes keep it, so the
  table changes only by built-in calls;
* `bstep_kstep`, `internalC_kstep`: the thread's continuation store changes by a `KStep`
  (`new` consumes the moved continuation, `take` appends the taken one);
* `CRun P`: the runs of one thread (internal steps, and resumptions after store changes that
  keep the table);
* **`cRun_table_protocol`**: along every thread run from an empty table, the table history is
  accepted by the handle protocol in both roles: `new` hands out fresh representations, and
  `take`/`drop` succeed only on live ones (a stale representation traps, rule `BStep.dead`);
* **`cRun_store_protocol`**, **`cRun_one_shot`**: from a Core thread (as `invoke` starts every
  export call) the store history is accepted by the handle protocol in both roles, and each
  store index is consumed at most once, built-in calls included.

The table is shared by the threads of the engine store; that it and the threads' stores never
hold the same continuation is in `Silmaril.Wasm.Component.FXRes.ContPool`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.ContEngine

open Silmaril.Wasm.Resource Silmaril.Wasm.Component.FXRes Silmaril.Wasm.Component.FXEngineV
open Silmaril.Wasm.Component.Runtime (Table)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- **The continuation table of every thread run respects the handle protocol.** -/
theorem cRun_table_protocol {s : EStore H} {t : ThreadV (CH H)} {y : EStore H × ThreadV (CH H)}
    (hs : s.tab = Table.empty) (h : CRun P (s, t) y) :
    ∃ evs, Table.Steps Table.empty evs y.1.tab ∧ ∀ r, (handleProto ℕ r).Accepts (evs.map tableEv) := by
  obtain ⟨evs, he⟩ := cRun_tab h
  have he' : Table.Steps Table.empty evs y.1.tab := hs ▸ he
  exact ⟨evs, he', table_steps_accepts he'⟩

/-- **The store history of a thread run from a Core thread respects the handle protocol.** -/
theorem cRun_store_protocol {s : EStore H} {t : Silmaril.Wasm.SingleThreaded.Thread}
    {y : EStore H × ThreadV (CH H)} (h : CRun P (s, .core t) y) :
    ∃ evs, KSteps [] (threadConts y.2) evs ∧ ∀ r, (handleProto ℕ r).Accepts evs := by
  obtain ⟨evs, hs⟩ := cRun_ksteps h
  refine ⟨evs, hs, fun r => ?_⟩
  obtain ⟨L, hL, -⟩ := ksteps_run hs r kRel_nil
  show ((handleProto ℕ r).run (some []) evs).isSome
  rw [hL]
  rfl

/-- **One-shot continuations with built-in calls.** -/
theorem cRun_one_shot {x y : EStore H × ThreadV (CH H)} (h : CRun P x y) :
    ∃ evs, KSteps (threadConts x.2) (threadConts y.2) evs ∧ ∀ k, evs.count (.free k) ≤ 1 := by
  obtain ⟨evs, hs⟩ := cRun_ksteps h
  exact ⟨evs, hs, ksteps_count_free hs⟩

/-- info: 'Silmaril.Wasm.Component.FXRes.ContEngine.cRun_table_protocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cRun_table_protocol

/-- info: 'Silmaril.Wasm.Component.FXRes.ContEngine.cRun_store_protocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cRun_store_protocol

end Silmaril.Wasm.Component.FXRes.ContEngine
