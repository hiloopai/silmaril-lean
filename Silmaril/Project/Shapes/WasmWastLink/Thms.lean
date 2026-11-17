module

public import Silmaril.Project.Shapes.WasmWastLink.Defs
public import Silmaril.Wasm.Execution.Core.Instantiation
import Silmaril.Proofs.Project.Shapes.WasmWastLink

/-!
# Standard problem shapes: linked WAST scripts (transfer lemmas)

* `ScriptHolds.of_kernel h`: every claim of the linked script `cmds` holds, from one kernel
  evaluation `h : scriptLK o fuel cmds = true` (`decide +kernel`). The kernel instantiates
  `Spectest.module`, then validates, links (`resolve?`, `externAddrsOk?`), instantiates and runs
  the modules and actions in order on `KMem` stores; the claims are about `ByteArray` stores and
  Core reduction, through `instantiateOnce?_toBytes`, `runI_toBytes`, the interpreter's soundness
  and stopping theorems, `Game.instantiateOnce?_configOk` (instantiation keeps the store typed)
  and determinism at `profile o`.
* `ScriptHolds.returnsOnly`, `….trapsOnly`, `….unlinkable`, `….uninstantiable`: the row of
  command `k`.
* `ScriptAt.unique`: at `profile o`, a script prefix reaches at most one context.
* `Only.unique`, `ReturnsOnly.not_traps`, `TrapsOnly.not_returns`.
* `Reaches.always`, `ReturnsOnly.always`, `TrapsOnly.always`: a row also excludes divergence.
* `Unlinkable.not_instantiate`: no `Instantiate` derivation (silmaril-lean's transcription of the
  specification's `$instantiate`) exists for the resolved addresses, under any profile and host.
* `Spectest.valid`: `Spectest.module` validates, with no imports. `Spectest.print_nf`: each
  function export of the `spectest` instance, called with typed arguments in any store that holds
  it, returns no values and leaves the store unchanged (its body is empty).

Proofs: `Silmaril.Proofs.Project.Shapes.WasmWastLink`.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.WasmWastLink

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded
open Silmaril.Project.Shapes.WasmWast (Expect exportFunc? invokeOkB)

/-- **Every claim of a linked script, from one kernel evaluation.** -/
theorem ScriptHolds.of_kernel {o : GrowOracle} {fuel : Nat} {cmds : List Cmd}
    (h : scriptLK o fuel cmds = true) : ScriptHolds o cmds :=
  Silmaril.Proofs.Project.Shapes.WasmWastLink.scriptHolds_of_kernel h

/-- The row of an `assert_return` command `k`. -/
theorem ScriptHolds.returnsOnly {o : GrowOracle} {cmds : List Cmd} (h : ScriptHolds o cmds)
    (k : Nat) {act : Action} {vs : List Val}
    (hk : cmds[k]? = some (.action act (some (.values vs)))) :
    ReturnsOnly o (pre cmds k) act vs :=
  h k _ hk

/-- The row of an `assert_trap` command `k`. -/
theorem ScriptHolds.trapsOnly {o : GrowOracle} {cmds : List Cmd} (h : ScriptHolds o cmds)
    (k : Nat) {act : Action} (hk : cmds[k]? = some (.action act (some .trap))) :
    TrapsOnly o (pre cmds k) act :=
  h k _ hk

/-- The row of an `assert_unlinkable` command `k`. -/
theorem ScriptHolds.unlinkable {o : GrowOracle} {cmds : List Cmd} (h : ScriptHolds o cmds)
    (k : Nat) {m : Module} (hk : cmds[k]? = some (.unlinkable m true)) :
    Unlinkable o (pre cmds k) m :=
  h k _ hk

/-- The row of an `assert_uninstantiable` command `k`. -/
theorem ScriptHolds.uninstantiable {o : GrowOracle} {cmds : List Cmd} (h : ScriptHolds o cmds)
    (k : Nat) {m : Module} (hk : cmds[k]? = some (.uninstantiable m true)) :
    Uninstantiable o (pre cmds k) m :=
  h k _ hk

/-- At `profile o`, a script prefix reaches at most one context. -/
theorem ScriptAt.unique {o : GrowOracle} {pre : List Cmd} {ctx ctx' : Ctx}
    (h : ScriptAt o pre ctx) (h' : ScriptAt o pre ctx') : ctx = ctx' :=
  Silmaril.Proofs.Project.Shapes.WasmWastLink.scriptAt_unique h h'

/-- If every normal form has the outcome `r` and some normal form has `r'`, then `r' = r`. -/
theorem Only.unique {o : GrowOracle} {pre : List Cmd} {act : Action} {r r' : Result}
    (h : Only o pre act r) (h' : Reaches o pre act r') : r' = r := by
  obtain ⟨ctx, s, hS, hA⟩ := h'
  exact Option.some.inj (h ctx _ s hS hA)

theorem ReturnsOnly.not_traps {o : GrowOracle} {pre : List Cmd} {act : Action} {vs : List Val}
    (h : ReturnsOnly o pre act vs) : ¬ Reaches o pre act .trap :=
  fun ht => nomatch h.2.unique ht

theorem TrapsOnly.not_returns {o : GrowOracle} {pre : List Cmd} {act : Action} {vs : List Val}
    (h : TrapsOnly o pre act) : ¬ Reaches o pre act (.values vs) :=
  fun hr => nomatch h.2.unique hr

/-- **One run decides every run** (at `profile o`): if some host-free normal form of an invoked
function has the outcome `r`, no host-free run of it is infinite and every finite one extends to
a normal form with the outcome `r`. -/
theorem Reaches.always {o : GrowOracle} {pre : List Cmd} {act : Action} {r : Result}
    (h : Reaches o pre act r) : Always o pre act r :=
  Silmaril.Proofs.Project.Shapes.WasmWastLink.reaches_always h

theorem ReturnsOnly.always {o : GrowOracle} {pre : List Cmd} {act : Action} {vs : List Val}
    (h : ReturnsOnly o pre act vs) : Always o pre act (.values vs) :=
  h.1.always

theorem TrapsOnly.always {o : GrowOracle} {pre : List Cmd} {act : Action}
    (h : TrapsOnly o pre act) : Always o pre act .trap :=
  h.1.always

/-- **An unlinkable module has no instantiation** for the addresses its imports resolve to: no
`Instantiate` derivation exists, under any profile `P` and host, in a context of the prefix. -/
theorem Unlinkable.not_instantiate {o : GrowOracle} {pre : List Cmd} {m : Module}
    (h : Unlinkable o pre m) {ctx : Ctx} (hS : ScriptAt o pre ctx) {xas : List ExternAddr}
    (hr : resolve? ctx.regs m.imports = some xas) {P : Silmaril.Wasm.Numerics.Profile}
    {host : HostSemantics Nat} {c : Config Nat} : ¬ Instantiate P host ctx.store m xas c :=
  Silmaril.Proofs.Project.Shapes.WasmWastLink.unlinkable_not_instantiate h hS hr

/-- `Spectest.module` validates, with no imports. -/
theorem Spectest.valid :
    ((validate? Spectest.module).map fun mt => mt.imports.isEmpty) = some true := by
  decide +kernel

/-- The kernel check `Spectest.printsEmptyB`. -/
theorem Spectest.printsEmptyB_eq : Spectest.printsEmptyB = true := by decide +kernel

/-- **The print functions of the `spectest` instance return no values and leave the store
unchanged**: every function export `a` of the instance registered as `"spectest"` in the initial
context, called with arguments of its parameter types in any store `s` that holds the same
function instance at `a`, reaches the empty code in the same store `s`, a host-free normal form. -/
theorem Spectest.print_nf {o : GrowOracle} {ctx₀ : Ctx} (h₀ : Init ctx₀) {mi : ModuleInst}
    (hmi : lookup ctx₀.regs "spectest" = some mi) {name : String} {a : Nat}
    (ha : exportFunc? mi name = some a) {fi : FuncInst Nat}
    (hf : ctx₀.store.funcs[a]? = some fi) {s : Store Nat} (hs : s.funcs[a]? = some fi)
    {args : List Val} (hargs : invokeOkB s a args = true) :
    NF o (invoke s a args) ⟨s, {}, []⟩ :=
  Silmaril.Proofs.Project.Shapes.WasmWastLink.print_nf Spectest.printsEmptyB_eq h₀ hmi ha hf hs
    hargs

end Silmaril.Project.Shapes.WasmWastLink

end
