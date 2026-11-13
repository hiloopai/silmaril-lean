module

public import Silmaril.Wasm.Resource.MachineTab.Defs
public import Silmaril.Proofs.Wasm.Resource.MachineTab.Runs
public import Silmaril.Proofs.Wasm.Resource.MachineTab.Hosts

@[expose] public section

/-!
# Handle tables along whole runs of the reference machine: results

Proofs in `Silmaril.Proofs.Wasm.Resource.MachineTab.{Frame,Step,Frames,Dispatch,Runs}`, for every
core engine (in particular `core3P P`, Core 3.0 at every profile) and component choice profile.

**The frame lemma.** `step_cfgTab`, `step_tabMove`, `steps_tab`: every machine step (all rules of
`Machine.Step`, traps and faults included) from a configuration whose programs are
table-moving (`CfgTab`), with a table-moving dispatcher (`TabDispatch`), reaches a table-moving
configuration, and moves every instance's handle table by a successful table history
(`TabMove`); `steps_init_tab`: from the initial configuration every handle table stays on a
successful history from `Table.empty`.

**The reference dispatcher.** `tabDispatch_canon`: `Canon.dispatch lim q hr host` is table-moving
for every host whose own programs are (`TabHost`; `tabHost_none`). The only store updates
that change a handle table are `InstState.addHandle` and `InstState.removeHandle`
(`tabMove_addHandle`, `tabMove_removeHandle`), issued through `handlesAdd`/`handlesRemove` and
`LowerSt.addSubtaskSt` by the resource built-ins (`resource.new`/`drop`), lifting and lowering
(`own`, `borrow`, stream/future ends, error contexts), waitable sets, subtasks and error
contexts; `resource.rep` and the lifts of borrows only read the table. Every other named store
update leaves the instance's handle table unchanged
(`Silmaril.Proofs.Wasm.Resource.MachineTab.Frames`). `tabProg_instantiateProg`: root and nested
instantiation allocate instances with empty tables. **Hosts with functions**: `tabHost_ofFns`;
the answering hosts of the component soundness theorems are table-moving
(`tabHost_answerImplS`, `tabHost_answerImpl`, `Silmaril.Proofs.Wasm.Resource.MachineTab.Hosts`),
so `refMulti_tables_host` applies to them.

**Multi-call runs.** `calls_tab`, `instantiates_tab`, `runCalls_tab`, `refMulti_tables`,
**`refMulti_tables_host`**: on every run of `refMultiSem` (instantiation from the empty store,
resolved calls, and a last call with any outcome, traps included) the handle table of every
instance is on a successful history from `Table.empty` accepted by `handleProto ℕ r` in both
orientations: indices are allocated fresh and only live indices are removed (dropped, lifted
`own`, dropped waitables, ...). This is a statement about table *states*: a `resource.rep`
or failed `get` does not change the table and is not recorded; a guest use of a dropped index
traps (`Table.get?`/`remove?` of a free index fail).
-/
