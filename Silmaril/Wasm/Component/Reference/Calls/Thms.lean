module

public import Silmaril.Wasm.Component.Reference.Silent.Thms
public import Silmaril.Proofs.Wasm.Component.Reference.MultiCall
public import Silmaril.Proofs.Wasm.Component.Reference.CalloutCore

@[expose] public section

/-!
# Export calls of the copied component machine between other calls

An interface to the call-run tools of the reference proofs, for analyses of concrete
components outside the `Simple` fragment (`Silmaril.Wasm.Resource.CompToy`):

* live deterministic runs `LRun`, `RunsQ` (big-step runs keeping the lockdown flag) with
  `RunsQ.chunk`, `RunsQ.lrun`, `LRun.inv`, and the `mstep` tactic;
* the programs of a synchronous `canon lift` call over arenas with leftovers of earlier calls
  (`runs_enter`, `runs_start`, `runs_return`, `runs_exit`, `runs_callUnit_loop`);
* the core phase: `coreCfg`, `retCfg`, `CoreExit`, `coreCfg_steps_inv'`, `status_values`,
  `status_callout_redex`, `resume_values`;
* quiet configurations (`quiet`: after a resolution only ticks and the call's own
  cancellation, returning to the same configuration or through live ones), `steps_of_locked`,
  `TrapsNext`.

Proofs in `Silmaril.Proofs.Wasm.Component.Reference.{CallBase,CallCore,CallPath,CallRun,
MultiBase,MultiProgs,MultiPath,MultiCall,CalloutCore}`.
-/
