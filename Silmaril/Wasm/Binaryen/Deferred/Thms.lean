module

public import Silmaril.Wasm.Binaryen.Deferred.Defs
public import Silmaril.Wasm.Binaryen.CoalesceLocalsClosure
import Silmaril.Proofs.Wasm.Binaryen.Deferred.Module

@[expose] public section

/-! # Frame-aware simulation through forced local steps

Results for the definitions of `Silmaril.Wasm.Binaryen.Deferred.Defs`, proved in
`Silmaril.Proofs.Wasm.Binaryen.Deferred.{Forced,Closure,Module}`: a
generalisation of silmaril's CoalesceLocals deferred simulation
(`Silmaril.Wasm.Binaryen.CoalesceLocals{Completion,Deferred,Closure,Profile}`, pinned
silmaril-lean) in which, after a matched step, the left side may run a finite chain of
**forced** local steps (`Forced`: an in-bounds `local.set`, a `local.get` of a set
local, a `local.tee` expansion, under any context) before its frame agrees with the
right side.

This is how base pairs relate states that agree only *through the frame*: e.g. the
original `local.set x; local.get x` after its store is at `local.get x`, while the
rewritten `local.tee x` already holds the value; the left side's read is forced and
completes the match. Forced steps are the unique closed-host step of their
configuration at every numerical profile (`Forced.unique`) and decrease the
payload-independent rank `fwRank`, so `DeferredCfgRel` is a stuttering `ConfigSim`.

* `DeferredBaseSim P F BI B`: base obligations (silmaril's `BaseFacts` at rank
  `fwRank`, and a step law ending in a `DeferredMatched`);
* `deferred_closure_configSim`: the simulation, at every profile `P`;
* `deferred_exportRefines_of_bodiesRel`: modules with related bodies refine each
  other's exports at every numerical profile under the closed host.

A candidate for upstreaming into silmaril-lean (it subsumes silmaril's single-set
`Completion`).
-/

namespace Silmaril.Wasm.Binaryen.Deferred

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {F : FuncInst H → FuncInst H → Prop}
  {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}

/-- `fwRank` is a lawful code rank: contexts, infixes, labels, handlers and frames
decrease it as silmaril's closure lemmas require. -/
instance : LawfulCodeRank fwRank := lawfulCodeRank_fwRank

/-- **A genuine stuttering simulation**, including the transient left frames, at every
numerical profile under the closed host. -/
theorem deferred_closure_configSim (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F closedHost) (hB : DeferredBaseSim P F BI B) :
    ∃ sim : ConfigSim P closedHost (DeferredCfgRel F BI B),
      sim.toForwardSim.measure = fun c => fwRank c.code :=
  Silmaril.Proofs.Wasm.Binaryen.Deferred.deferred_closure_configSim hF hhost hB

/-- **Export refinement from a deferred base simulation**, at every numerical profile:
the left module's behaviours are behaviours of the right module. -/
theorem deferred_exportRefines_of_bodiesRel
    (hB : DeferredBaseSim P (FuncRel (H := H) BI) BI B)
    {m m' : Module} (hrel : ModuleBodiesRel BI m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportRefines (· = ·) P (closedHost (H := H)) m m' :=
  Silmaril.Proofs.Wasm.Binaryen.Deferred.deferred_exportRefines_of_bodiesRel hB hrel hm hm'

/-- Invocations in related stores start related. -/
theorem invoke_cfgRel {s t : Store H} (a : Nat) (vs : List Val)
    (hst : StoreRel (FuncRel (H := H) BI) s t) :
    CfgRel (FuncRel (H := H) BI) (AdminsRel BI B) (invoke s a vs) (invoke t a vs) :=
  Silmaril.Proofs.Wasm.Binaryen.Deferred.invoke_cfgRel a vs hst

/-- Completed runs retain final stores for subsequent invocations. -/
theorem deferred_closure_run_transport (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F closedHost) (hB : DeferredBaseSim P F BI B)
    {c d c' : Config H} {r : Result} (h : CfgRel F (AdminsRel BI B) c d)
    (hs : Steps P closedHost c c') (hc : c'.code = r.toAdmin) :
    ∃ d', Steps P closedHost d d' ∧ d'.code = r.toAdmin ∧ StoreRel F c'.store d'.store :=
  Silmaril.Proofs.Wasm.Binaryen.Deferred.deferred_closure_run_transport hF hhost hB h hs hc

/-- Divergence transports along related configurations. -/
theorem deferred_closure_diverges_transport (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F closedHost) (hB : DeferredBaseSim P F BI B)
    {c d : Config H} (h : CfgRel F (AdminsRel BI B) c d)
    (hd : Diverges P closedHost c) : Diverges P closedHost d :=
  Silmaril.Proofs.Wasm.Binaryen.Deferred.deferred_closure_diverges_transport hF hhost hB h hd

end Silmaril.Wasm.Binaryen.Deferred
