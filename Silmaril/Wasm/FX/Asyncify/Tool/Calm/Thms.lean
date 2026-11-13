module

public import Silmaril.Wasm.FX.Asyncify.Tool.Selective.Thms
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Calm.Run

/-!
# Calm functions never suspend: results

The header of `Defs`.

* **`mayS_fix`**: `mayS P` is a fixed point of one round of the analysis (`suspStep`): the
  `L + 1` rounds of `mayS` (for `L` defined functions) reach the least fixed point, because
  every round that changes the set adds a defined function (`suspSet_stable`).
* **`calm_defined`**, **`calm_calls`**: a calm function is a defined function, and each of its
  call statements calls a calm function (`mayS P` is closed under callers, as the selective mode
  assumes).
* **`calm_step`**: from calm frames, a machine step never calls an import, and the frames stay
  calm.
* **`calm_runN`**, **`calm_beh_host`**: a source run of a calm function never consults the host:
  the host state stays as it was, and the behaviours are the same under every host.

These are the facts about calm callees that `SelectiveBeh` needs (a calm call inside a pure
statement runs a callee that never suspends); the simulation itself is `SelSim`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

variable {σ : Type}

/-- The entry frame of a calm function is calm. -/
theorem calm_entry {P : Prog} {e : Nat} {fn : FnSrc} (hfn : P.fnAt e = some fn)
    (hcalm : mayS P e = false) (args : List W) : CalmCfg P (srcCfg e fn args) := by
  intro fr hfr
  simp only [srcCfg, List.mem_singleton] at hfr
  subst hfr
  have hge := Prog.fnAt_ge hfn
  have hget : P.fns[e - P.imps.length]? = some fn := by
    unfold Prog.fnAt at hfn; simpa [hge] using hfn
  exact ⟨fn, hge, hget, hcalm, [], by simp [entry, FnSrc.body]⟩

/-- **A call of a calm function behaves the same under every host.** -/
theorem calm_beh_host {P : Prog} (hP : P.WF) {e : Nat} {fn : FnSrc} (hfn : P.fnAt e = some fn)
    (hcalm : mayS P e = false) (args : List W) (s : σ) (H H' : Host σ) :
    beh (srcStep P.env H) (srcCfg e fn args, s) = beh (srcStep P.env H') (srcCfg e fn args, s) := by
  have h : ∀ n, runN (srcStep P.env H) n (srcCfg e fn args, s) =
      runN (srcStep P.env H') n (srcCfg e fn args, s) :=
    fun n => (calm_runN hP H H' n _ s (calm_entry hfn hcalm args)).1
  unfold beh
  simp only [h]

/-- **A call of a calm function never changes the host state.** -/
theorem calm_host_state {P : Prog} (hP : P.WF) {e : Nat} {fn : FnSrc} (hfn : P.fnAt e = some fn)
    (hcalm : mayS P e = false) (args : List W) (s : σ) (H : Host σ) (n : Nat) (y : Cfg × σ)
    (hy : runN (srcStep P.env H) n (srcCfg e fn args, s) = .next y) : y.2 = s :=
  ((calm_runN hP H H n _ s (calm_entry hfn hcalm args)).2 y hy).1

/-- info: 'Silmaril.Wasm.FX.Asyncify.Tool.calm_beh_host' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms calm_beh_host

/-- info: 'Silmaril.Wasm.FX.Asyncify.Tool.calm_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms calm_calls

end Silmaril.Wasm.FX.Asyncify.Tool
