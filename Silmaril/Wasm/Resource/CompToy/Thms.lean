module

public import Silmaril.Wasm.Resource.CompToy.Defs
public import Silmaril.Proofs.Wasm.Resource.CompToy.Runs
public import Silmaril.Proofs.Wasm.Resource.CompToy.Init
public import Silmaril.Proofs.Wasm.Resource.CompToy.Get
public import Silmaril.Proofs.Wasm.Resource.CompToy.MakeCall
public import Silmaril.Proofs.Wasm.Resource.CompToy.Provider

@[expose] public section

/-!
# A toy component defining a resource: results

Proofs in `Silmaril.Proofs.Wasm.Resource.CompToy.Runs`, over `core3 neverFail` (Core 3.0 with the
never-failing grow oracle), the first-alternative oracle's choice profile and the host without
functions:

* **`bug_not_compProvider`**: the buggy component `bugProg` (`make` is `resource.new(7)`)
  violates the provider sentence `compProviderSpec makeE dropE` over several calls
  (`refMultiSem`): two `make` calls on one instance return `own 7` twice, a live
  representation (`compProvider_refuted_of_reuse`, the run by kernel evaluation of the copied
  drivers, `session_bug`);
* `toySession_trace`, `toySession_accepted`: the toy's session `make`, `make`, `get(borrow 0)`,
  `drop(own 0)`, `make` answers `own 0`, `own 1`, `u32 0`, `[]`, `own 2` on the machine
  (`session_toy`), and that trace is accepted by the provider sentence; `sessionCtrs_toy`:
  along it the counter `toyCtr` meets the inequalities of `CtrVCOn`;
* `toyComp_valid`, `bugComp_valid`: the reference validator accepts both components;
* `session_runCalls`: any successful executable session is an instantiation followed by a
  `RunCalls` run.

Over **every** profile `P` (`core3P P`), choice profile and host
(`Silmaril.Proofs.Wasm.Resource.CompToy.Init`):

* **`toy_instBehaviours`**: the only result of instantiating the toy (`toyProgP P`) is the
  instance at `toyInst P` (computed by `silentRun`, the instantiation being one deterministic
  silent run) with root instance `0` and exports `toyEs`; no trap, no divergence;
* **`toyR_init`**: the reachability invariant `toyR` holds after every instantiation, at the
  configuration `toyCfg P 0 {} (ToyGarb.empty P)` (`CtrVCOn.init`); `toyCtrP_toyCfg`: the
  counter of `toyCfg P c ι G` is `c`.

Calls of `get` (`Silmaril.Proofs.Wasm.Resource.CompToy.{Call,Get}`), every profile and choice
profile, host `refHost P`:

* `toy_callAt`, `toy_callAt_trap`: the deterministic parts of an export call of the toy from
  a configuration between calls (`toyCfgX`, `toyCfg_eq`), given the runs of the lowering and
  lifting; `resolved_of_lrun`, `not_resolved_of_trap`; `toyR_next`;
* **`toy_get`**: a resolved call of `get` was on `[borrow rep]` and ends at the next
  configuration between calls with the same counter and handle objects (core phase by the
  every-run program logic, `getSpec_valid`, `get_core`);
* **`toyR_get`**: resolved calls of `get` from `toyR` keep `toyR` and the counter
  (`CtrVCOn.step` and `CtrVCOn.mono` at `get`).

Calls of `make` (`Silmaril.Proofs.Wasm.Resource.CompToy.{Core,MakeCore,Make,MakeCall}`), every
profile and choice profile, host `refHost P`, with no hypothesis on the built-in's answers:

* `core_inv`: the core phase of an export call whose core code calls canon built-ins, related
  callout by callout (`CalloutsAns`) to the every-run program logic under a host relation; each
  callout is the machine's dispatch program (`builtin_lrun`, `builtin_traps`);
* `makeSpec_valid`: core function `2` under `Open.specHost` of the `resource.new` stub
  specification (`Γnew c J`); `make_calloutsAns`: the machine's `resource.new` (`runs_newCallout`,
  `traps_newCallout`, `Table.add?` through `add?_tabB`) answers as that specification allows,
  adding an own handle of representation `c` at a fresh index below `2^32`;
* `runs_lift_make`, `traps_lift_make`: `liftOwn` of the result;
* **`toy_make`**, **`toyR_make`**: a resolved call of `make` from `toyR` keeps `toyR`, increments
  the counter and answers `own` of the counter before the call (`CtrVCOn.step`, `mono` and
  `fresh` at `make`).

Calls of `drop` (`Silmaril.Proofs.Wasm.Resource.CompToy.{DropRun,DropCore,CallX,DropLower,DropCall,
DropMain}`), same setting, with no hypothesis on the built-in's answers:

* `lrun_dropCallout`: the machine run of the callout to `resource.drop` of an own handle of the
  toy's resource: the entry is removed and REF's no-op destructor runs (`destructorCall`,
  `canonLiftNoop`: a new task and thread of instance `0`, `Thread.resume`, the thread body
  `liftNoopThreadBody` with `on_start`/`on_resolve` of the `destructor` caller record, the
  synchronous loop); `traps_dropCallout`: a drop of an index that is not live traps;
* `dropSpec_valid`: core function `4` under the `resource.drop` stub specification;
  `drop_calloutsAns`: the machine's `resource.drop` answers as it allows (first drop of the
  lowered entry runs the destructor, later ones trap);
* `toy_callAtX`: `toy_callAt` whose return half allows records appended during the core phase
  (`runs_returnMT`, `runs_exitMT`, `runs_ite_loopM`); `runs_lower_drop`, `lower_drop_traps`:
  `lower_own` of the argument;
* **`toy_drop`**, **`toyR_drop`**: a resolved call of `drop` from `toyR` answers `[]` and keeps
  `toyR` and the counter (`CtrVCOn.step` and `mono` at `drop`). `ThreadsFree` allows the thread
  table `⟨#[none, none, none], [1, 2]⟩` that a destructor call leaves; a call's instance is
  `callIn ι t`.

The positive theorem (`Silmaril.Proofs.Wasm.Resource.CompToy.Provider`), at every profile `P` and
choice profile `prof`:

* **`toy_ctrVCOn`**: `CtrVCOn prof (refHost P) () (toyProgP P) makeE (toyCtrP P) (toyR P)`;
* **`toy_compProvider`**: `Models (protoLogic CFn (List RVal) Component.Outcome
  (Option (List ℕ))) (refMultiSem prof (refHost P) ()) (toyProgP P)
  (compProviderSpec makeE dropE)`.

Not covered: hosts other than `refHost P` for the calls (no host functions; `init` holds for
every host).
-/
