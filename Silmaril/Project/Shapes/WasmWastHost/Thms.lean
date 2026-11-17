module

public import Silmaril.Project.Shapes.WasmWastHost.Defs
public import Silmaril.Wasm.Abstract.HostDet.Thms
public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Wasm.Execution.Core.Instantiation
import Silmaril.Proofs.Project.Shapes.WasmWastHost

/-!
# Standard problem shapes: linked WAST scripts against the typed `spectest` host (transfer lemmas)

**The host.**

* `Spectest.hostDet : HostDet Spectest.host`: each call has at most one outcome.
* `Spectest.hostTyped : HostTyped Spectest.host`: every answer keeps the store typed, extends it
  (it is unchanged) and has the callee's result type.
* `Spectest.print_nf`: a call of a host function of code `k` that the host answers returns no
  values, leaves the store unchanged and appends `(k, args)` to the log, in one logged step to a
  normal form.

**The registry** (`Spectest.lookup?`): `Spectest.lookup?_print`, `Spectest.lookup?_global`: a
print function or a global is allocated fresh, at the next address; `Spectest.lookup?_shared`:
`table`, `table64`, `memory` resolve to the shared instance without allocating.
`Spectest.resolve?_print_twice`, `….resolve?_global_twice`: two imports of one print function
(global) get two different addresses; `Spectest.resolve?_memory_twice`: two imports of `memory`
get the same one.

**Scripts.**

* `ScriptHolds.of_kernel h`: every claim of the linked script `cmds` holds against
  `Spectest.host`, from one kernel evaluation `h : scriptHK o fuel cmds = true`
  (`decide +kernel`): `KMem` stores to `ByteArray` stores (`instantiateOnce?_toBytes`,
  `runI_toBytes`, `decompose?_toBytes`), the interpreter's soundness and stopping theorems between
  host calls, `Ctx.fill_callout_typed` at host calls, `Game.instantiateOnce?_configOk`, and
  determinism with a deterministic host (`LSteps.nf_unique_of_hostDet`).
* `LogIs.of_kernel h`: the host-call log after the script, from `h : logHK o fuel cmds = some l`
  (`decide +kernel`).
* `ScriptHolds.returnsOnly`, `….trapsOnly`, `….unlinkable`, `….uninstantiable`: the row of
  command `k`.
* `ScriptAt.unique`: at `profile o`, a script prefix reaches at most one context: one store,
  registry and **host-call log** (so the printed output `Spectest.printed ctx.log` is determined).
* `Only.unique`, `ReturnsOnly.not_traps`, `TrapsOnly.not_returns`.
* `Reaches.always`, `ReturnsOnly.always`, `TrapsOnly.always`: a row also excludes infinite runs
  under `Spectest.host` (`Steps.always_of_hostDet`).
* `Unlinkable.not_instantiate`: no `Instantiate` derivation exists for the resolved store and
  addresses, under any profile and host.

Proofs: `Silmaril.Proofs.Project.Shapes.WasmWastHost`.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.WasmWastHost

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Abstract
open Silmaril.Project.Shapes.WasmWast (Expect exportFunc? invokeOkB)
open Silmaril.Project.Shapes.WasmWastLink (exportAddr? Action Cmd)

/-! ## The host -/

/-- **The `spectest` host is deterministic.** -/
theorem Spectest.hostDet : HostDet Spectest.host :=
  Silmaril.Proofs.Project.Shapes.WasmWastHost.hostDet

/-- **The answers of the `spectest` host are typed.** -/
theorem Spectest.hostTyped : HostTyped Spectest.host :=
  Silmaril.Proofs.Project.Shapes.WasmWastHost.hostTyped

/-- **A print call returns no values, leaves the store unchanged and is logged.** -/
theorem Spectest.print_nf {o : GrowOracle} {s : Store Nat} {a k : Nat} {fi : FuncInst Nat}
    {ps rs : List CValType} {args : List Val} (l : HostLog Nat) (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .host k) (ht : fi.type.funcType? = some (ps, rs))
    (hn : args.length = ps.length) (hk : Spectest.answers s k = true) :
    NF o (invoke s a args, l) (⟨s, {}, []⟩, l ++ [(k, args)]) :=
  Silmaril.Proofs.Project.Shapes.WasmWastHost.print_nf l hf hcode ht hn hk

/-! ## The registry: fresh and shared entities -/

/-- A print function is allocated fresh at every lookup, at the next function address. -/
theorem Spectest.lookup?_print {R : Type} {sh : ModuleInst} {s : Store Nat R} {name : String}
    {k : Nat} {ps : List NumType} (h : Spectest.entry? name = some (.print k ps)) :
    Spectest.lookup? sh s name = some
      ({ s with funcs := s.funcs ++ [⟨ofFlatType ⟨ps, []⟩, {}, .host k⟩] }, .func s.funcs.length) := by
  simp [Spectest.lookup?, h, allocHost, allocFunc]

/-- A global is allocated fresh at every lookup, at the next global address. -/
theorem Spectest.lookup?_global {R : Type} {sh : ModuleInst} {s : Store Nat R} {name : String}
    {t : NumType} {b : BitVec t.width} (h : Spectest.entry? name = some (.global t b)) :
    Spectest.lookup? sh s name = some
      ({ s with globals := s.globals ++ [⟨⟨.const, .num t⟩, .num ⟨t, b⟩⟩] },
        .global s.globals.length) := by
  simp [Spectest.lookup?, h, allocGlobal]

/-- `table`, `table64` and `memory` are the exports of the shared instance; the store is
unchanged. -/
theorem Spectest.lookup?_shared {R : Type} {sh : ModuleInst} {s : Store Nat R} {name : String}
    (h : Spectest.entry? name = some .shared) :
    Spectest.lookup? sh s name = (exportAddr? sh name).map fun xa => (s, xa) := by
  simp [Spectest.lookup?, h]

/-- **Two imports of one print function are two functions.** -/
theorem Spectest.resolve?_print_twice {R : Type} {regs : Regs} {sh : ModuleInst}
    (hreg : lookupReg regs "spectest" = some (.spectest sh)) (s : Store Nat R)
    (t t' : ExternType) :
    ∃ s', resolve? regs s [⟨"spectest", "print_i32", t⟩, ⟨"spectest", "print_i32", t'⟩] =
      some (s', [.func s.funcs.length, .func (s.funcs.length + 1)]) := by
  have he : Spectest.entry? "print_i32" = some (.print 1 [.int .i32]) := rfl
  simp [resolve?, hreg, Spectest.lookup?_print he]

/-- **Two imports of one global are two globals.** -/
theorem Spectest.resolve?_global_twice {R : Type} {regs : Regs} {sh : ModuleInst}
    (hreg : lookupReg regs "spectest" = some (.spectest sh)) (s : Store Nat R)
    (t t' : ExternType) :
    ∃ s', resolve? regs s [⟨"spectest", "global_i32", t⟩, ⟨"spectest", "global_i32", t'⟩] =
      some (s', [.global s.globals.length, .global (s.globals.length + 1)]) := by
  have he : Spectest.entry? "global_i32" = some (.global (.int .i32) 666) := rfl
  simp [resolve?, hreg, Spectest.lookup?_global he]

/-- **Two imports of `memory` are the same memory**, and the store is unchanged. -/
theorem Spectest.resolve?_memory_twice {R : Type} {regs : Regs} {sh : ModuleInst}
    (hreg : lookupReg regs "spectest" = some (.spectest sh)) (s : Store Nat R)
    (t t' : ExternType) :
    resolve? regs s [⟨"spectest", "memory", t⟩, ⟨"spectest", "memory", t'⟩] =
      (exportAddr? sh "memory").map fun xa => (s, [xa, xa]) := by
  have he : Spectest.entry? "memory" = some .shared := rfl
  cases hx : exportAddr? sh "memory" <;> simp [resolve?, hreg, Spectest.lookup?_shared he, hx]

/-! ## Scripts -/

/-- **Every claim of a linked script against the `spectest` host, from one kernel
evaluation.** -/
theorem ScriptHolds.of_kernel {o : GrowOracle} {fuel : Nat} {cmds : List Cmd}
    (h : scriptHK o fuel cmds = true) : ScriptHolds o cmds :=
  Silmaril.Proofs.Project.Shapes.WasmWastHost.scriptHolds_of_kernel h

/-- **The host-call log of a script, from one kernel evaluation**; the printed values are
`Spectest.printed l`. -/
theorem LogIs.of_kernel {o : GrowOracle} {fuel : Nat} {cmds : List Cmd} {l : HostLog Nat}
    (h : logHK o fuel cmds = some l) : LogIs o cmds l :=
  Silmaril.Proofs.Project.Shapes.WasmWastHost.logIs_of_kernel h

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

/-- **At `profile o`, a script prefix reaches at most one context**: store, registry, named
modules, current module and host-call log. -/
theorem ScriptAt.unique {o : GrowOracle} {pre : List Cmd} {ctx ctx' : Ctx}
    (h : ScriptAt o pre ctx) (h' : ScriptAt o pre ctx') : ctx = ctx' :=
  Silmaril.Proofs.Project.Shapes.WasmWastHost.scriptAt_unique h h'

/-- If every normal form has the outcome `r` and some normal form has `r'`, then `r' = r`. -/
theorem Only.unique {o : GrowOracle} {pre : List Cmd} {act : Action} {r r' : Result}
    (h : Only o pre act r) (h' : Reaches o pre act r') : r' = r := by
  obtain ⟨ctx, s, l, hS, hA⟩ := h'
  exact Option.some.inj (h ctx _ s l hS hA)

theorem ReturnsOnly.not_traps {o : GrowOracle} {pre : List Cmd} {act : Action} {vs : List Val}
    (h : ReturnsOnly o pre act vs) : ¬ Reaches o pre act .trap :=
  fun ht => nomatch h.2.unique ht

theorem TrapsOnly.not_returns {o : GrowOracle} {pre : List Cmd} {act : Action} {vs : List Val}
    (h : TrapsOnly o pre act) : ¬ Reaches o pre act (.values vs) :=
  fun hr => nomatch h.2.unique hr

/-- **One run decides every run** (at `profile o`, against `Spectest.host`). -/
theorem Reaches.always {o : GrowOracle} {pre : List Cmd} {act : Action} {r : Result}
    (h : Reaches o pre act r) : Always o pre act r :=
  Silmaril.Proofs.Project.Shapes.WasmWastHost.reaches_always h

theorem ReturnsOnly.always {o : GrowOracle} {pre : List Cmd} {act : Action} {vs : List Val}
    (h : ReturnsOnly o pre act vs) : Always o pre act (.values vs) :=
  h.1.always

theorem TrapsOnly.always {o : GrowOracle} {pre : List Cmd} {act : Action}
    (h : TrapsOnly o pre act) : Always o pre act .trap :=
  h.1.always

/-- **An unlinkable module has no instantiation** for the store and addresses its imports
resolve to, under any profile `P` and host. -/
theorem Unlinkable.not_instantiate {o : GrowOracle} {pre : List Cmd} {m : Module}
    (h : Unlinkable o pre m) {ctx : Ctx} (hS : ScriptAt o pre ctx) {s₀ : Store Nat}
    {xas : List ExternAddr} (hr : resolve? ctx.regs ctx.store m.imports = some (s₀, xas))
    {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics Nat} {c : Config Nat} :
    ¬ Instantiate P host s₀ m xas c :=
  Silmaril.Proofs.Project.Shapes.WasmWastHost.unlinkable_not_instantiate h hS hr

end Silmaril.Project.Shapes.WasmWastHost

end
