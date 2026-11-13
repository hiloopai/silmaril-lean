module

public import Silmaril.Wasm.Resource.CompTable.Defs
public import Silmaril.Proofs.Wasm.Resource.CompTable.Basic
public import Silmaril.Proofs.Wasm.Resource.CompTable.Machine
public import Silmaril.Proofs.Wasm.Resource.CompTable.RefSem

@[expose] public section

/-!
# The resource built-ins of the reference machine and their handle tables: results

Proofs in `Silmaril.Proofs.Wasm.Resource.CompTable.{Basic,Machine,RefSem}`.

**Built-ins as table events** (`Basic`). A successful store-only run (`SRun`) of
* `resourceNewCore lim inst rt rep` returning `i` is the table event `added i (resource hid)` on
  `inst`, `hid` a fresh handle object holding `ResourceHandle(rt, rep, own)`
  (`resourceNewCore_tab`);
* `resourceRepCore lim inst rt i` returning `n` is `got i (resource hid)`, `n` the
  representation of `hid`, of type `rt`, and the store is unchanged (`resourceRepCore_tab`);
* `resourceDropCore lim inst rt i` is `removed i (resource hid)`, `hid` of type `rt` with no
  lends (`resourceDropCore_tab`);
each leaves the other instances' tables unchanged. **`resScript_tab`**: a script of such calls
makes every instance's table follow a successful history whose handle events are the calls'
events (`instEvs`); **`resScript_accepts`**: from an empty table these are accepted by
`handleProto ℕ r` for both roles.

**On the machine** (`Machine`). The cores are store-only programs (`storeProg_resScript`);
`SRun.steps`: store-only runs are `tau` runs of `Machine.Step`; **`steps_storeProg`**: every
machine run from a configuration running `p >>= f`, `p` store-only, stops inside `p`, traps
(the machine is then dead, `steps_dead`) or completes `p` through `SRun p s a s₁`.
**`machine_resScript`**, **`machine_resScript_accepts`**: every machine run that completes a
script of resource built-in cores makes each instance's handle table follow a successful table
history; from an empty table its handle events are accepted by `handleProto ℕ r` (both roles).

**On `refSem`** (`RefSem`). `refSem_compProvider`, `refSem_noUseAfterDrop`: both component
handle sentences hold of every reference component in `refSem`, vacuously, because `refSem`
observes one call per fresh instance.

Not covered: the destructor call of `resource.drop` and the `may_leave`/current-instance entry
of the full built-ins (`Builtins.resourceNew/Drop/Rep`), the handle-table operations of
lifting/lowering (`liftOwn`, `liftBorrow`, `lowerOwn`, `lowerBorrow`), waitables, error contexts
and subtasks, which share the same table; runs that stop inside or trap inside a script; and
any link from table indices to the representations `own r`/`borrow r` seen in component traces.
-/
