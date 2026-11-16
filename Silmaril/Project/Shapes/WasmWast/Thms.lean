module

public import Silmaril.Project.Shapes.WasmWast.Defs
import Silmaril.Proofs.Project.Shapes.WasmWast

/-!
# Standard problem shapes: WAST script commands (transfer lemmas)

* `ScriptHolds.of_kernel h`: every command of the script `m`, `cmds` holds, from one kernel
  evaluation `h : scriptK o fuel m cmds = true` (`decide +kernel`). The kernel validates and
  instantiates `m` and runs the commands in order with the kernel-evaluable interpreter
  `runInvokeK`; the claims are about Core reduction, through the interpreter's soundness and
  stopping theorems and determinism at `profile o`.
* `ScriptHolds.of_kernelKM h`: the same from `h : scriptKM o fuel m cmds = true`, the checker
  that instantiates and runs on `KMem` stores (`scriptK_of_scriptKM`). Needed when the module's
  instantiation writes data segments into a memory: the kernel cannot evaluate `ByteArray`
  writes into a 64 KiB memory.
* `ScriptHolds.returnsOnly`, `ScriptHolds.trapsOnly`: the row of command `k`.
* `ReturnsOnly.returns`, `TrapsOnly.traps`: the weaker existence shapes;
  `ReturnsOnly.not_traps`, `TrapsOnly.not_returns`: an `…_only` claim excludes the other
  outcome.
* `ScriptAt.unique`: under `profile o`, the earlier actions leave at most one state.
* `Only.unique`: under `profile o`, a script and an action have at most one outcome.
* `Reaches.always`, `ReturnsOnly.always`, `TrapsOnly.always`, `ScriptHolds.always`: under
  `profile o`, a row also excludes divergence: no host-free run of the action is infinite, and
  every finite run extends to a normal form with the row's outcome (`Always`).

Proofs: `Silmaril.Proofs.Project.Shapes.WasmWast`.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.WasmWast

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

/-- **Every command of a script, from one kernel evaluation.** -/
theorem ScriptHolds.of_kernel {o : GrowOracle} {fuel : Nat} {m : Module} {cmds : List Cmd}
    (h : scriptK o fuel m cmds = true) : ScriptHolds o m cmds :=
  Silmaril.Proofs.Project.Shapes.WasmWast.scriptHolds_of_kernel h

/-- **The `KMem` checker implies the `ByteArray` checker**: a kernel evaluation of `scriptKM`
(instantiation and runs on `KMem` stores) gives `scriptK … = true`, through the simulation
lemmas `instantiateOnce?_toBytes` and `runI_toBytes`. -/
theorem scriptK_of_scriptKM {o : GrowOracle} {fuel : Nat} {m : Module} {cmds : List Cmd}
    (h : scriptKM o fuel m cmds = true) : scriptK o fuel m cmds = true :=
  Silmaril.Proofs.Project.Shapes.WasmWast.scriptK_of_scriptKM h

/-- **Every command of a script, from one kernel evaluation on `KMem` stores.** The claims are
the same as those of `ScriptHolds.of_kernel`, about `ByteArray` stores and `Step (profile o)`. -/
theorem ScriptHolds.of_kernelKM {o : GrowOracle} {fuel : Nat} {m : Module} {cmds : List Cmd}
    (h : scriptKM o fuel m cmds = true) : ScriptHolds o m cmds :=
  .of_kernel (scriptK_of_scriptKM h)

/-- The row of an `assert_return` command `k`. -/
theorem ScriptHolds.returnsOnly {o : GrowOracle} {m : Module} {cmds : List Cmd}
    (h : ScriptHolds o m cmds) (k : Nat) {act : Action} {vs : List Val}
    (hk : cmds[k]? = some ⟨act, some (.values vs)⟩) : ReturnsOnly o m (pre cmds k) act vs :=
  h k _ hk

/-- The row of an `assert_trap` command `k`. -/
theorem ScriptHolds.trapsOnly {o : GrowOracle} {m : Module} {cmds : List Cmd}
    (h : ScriptHolds o m cmds) (k : Nat) {act : Action}
    (hk : cmds[k]? = some ⟨act, some .trap⟩) : TrapsOnly o m (pre cmds k) act :=
  h k _ hk

theorem ReturnsOnly.returns {o : GrowOracle} {m : Module} {pre : List Action} {act : Action}
    {vs : List Val} (h : ReturnsOnly o m pre act vs) : Returns o m pre act vs := h.1

theorem TrapsOnly.traps {o : GrowOracle} {m : Module} {pre : List Action} {act : Action}
    (h : TrapsOnly o m pre act) : Traps o m pre act := h.1

/-- At `profile o`, the script `m`, `pre` reaches at most one state. -/
theorem ScriptAt.unique {o : GrowOracle} {m : Module} {pre : List Action} {mi mi' : ModuleInst}
    {s s' : Store Nat} (h : ScriptAt o m pre mi s) (h' : ScriptAt o m pre mi' s') :
    mi = mi' ∧ s = s' :=
  Silmaril.Proofs.Project.Shapes.WasmWast.scriptAt_unique h h'

/-- If every normal form has the outcome `r` and some normal form has `r'`, then `r' = r`. -/
theorem Only.unique {o : GrowOracle} {m : Module} {pre : List Action} {act : Action}
    {r r' : Result} (h : Only o m pre act r) (h' : Reaches o m pre act r') : r' = r := by
  obtain ⟨mi, s, a, c, hS, ha, hc, hr⟩ := h'
  have := h mi s a c hS ha hc
  rw [hr] at this
  exact Option.some.inj this

theorem ReturnsOnly.not_traps {o : GrowOracle} {m : Module} {pre : List Action} {act : Action}
    {vs : List Val} (h : ReturnsOnly o m pre act vs) : ¬ Traps o m pre act :=
  fun ht => nomatch h.2.unique ht

theorem TrapsOnly.not_returns {o : GrowOracle} {m : Module} {pre : List Action} {act : Action}
    {vs : List Val} (h : TrapsOnly o m pre act) : ¬ Returns o m pre act vs :=
  fun hr => nomatch h.2.unique hr

/-! ## Termination -/

/-- **One run decides every run** (at `profile o`): if some host-free normal form of `act` has
the outcome `r`, then no host-free run of `act` is infinite and every finite one extends to a
normal form with the outcome `r`. -/
theorem Reaches.always {o : GrowOracle} {m : Module} {pre : List Action} {act : Action}
    {r : Result} (h : Reaches o m pre act r) : Always o m pre act r :=
  Silmaril.Proofs.Project.Shapes.WasmWast.reaches_always h

theorem ReturnsOnly.always {o : GrowOracle} {m : Module} {pre : List Action} {act : Action}
    {vs : List Val} (h : ReturnsOnly o m pre act vs) : Always o m pre act (.values vs) :=
  h.1.always

theorem TrapsOnly.always {o : GrowOracle} {m : Module} {pre : List Action} {act : Action}
    (h : TrapsOnly o m pre act) : Always o m pre act .trap :=
  h.1.always

/-- The row of an assertion `k`, with termination: its expected outcome is reached, it is the
outcome of every normal form, no run is infinite, and every run extends to that outcome. -/
theorem ScriptHolds.always {o : GrowOracle} {m : Module} {cmds : List Cmd}
    (h : ScriptHolds o m cmds) (k : Nat) {act : Action} {e : Expect}
    (hk : cmds[k]? = some ⟨act, some e⟩) :
    Reaches o m (pre cmds k) act e.result ∧ Only o m (pre cmds k) act e.result ∧
      Always o m (pre cmds k) act e.result := by
  have := h k _ hk
  cases e <;> exact ⟨this.1, this.2, this.1.always⟩

end Silmaril.Project.Shapes.WasmWast

end
