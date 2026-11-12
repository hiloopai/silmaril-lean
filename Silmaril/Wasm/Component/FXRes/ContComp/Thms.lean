module

public import Silmaril.Wasm.Component.FXRes.ContComp.Defs
public import Silmaril.Wasm.Resource.MachineTab.Thms
public import Silmaril.Wasm.Component.Param.Defs

/-!
# `cont` as a resource type of a component run by the reference machine: results

* **`contProg_tables`**: on every multi-call run of the reference component machine over the
  WasmFX engine with a continuation table `fxCE P` running `contProg P` (root instantiation from
  the empty store, resolved calls, and a last call with any outcome, traps included), with the
  reference host `refHostE`, the handle table of every instance, in particular the table of the
  `cont` handles, is on a successful history from `Table.empty`, accepted by the handle protocol
  in both roles: `make`'s `resource.new` returns fresh handles, and `run`'s `resource.rep` and
  `resource.drop` act only on live ones.

This instantiates `Resource.refMulti_tables_host`, which holds for every core engine; it is a
statement about the machine's handle tables, not about the engine's continuation table, whose
protocols are `ContEngine.cRun_table_protocol` (thread runs) and
`ContPool.pool_identities` (a pool of threads). Linking the two (the representation in a live
handle names a live entry of the engine's table) needs an invariant along machine runs that is
not proved.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.ContComp

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Resource Silmaril.Wasm.Spec.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.FXRes.ContEngine
open Silmaril.Wasm.Numerics (Profile)

/-- **The `cont` handle tables of every machine run of the component respect the handle
protocol.** -/
theorem contProg_tables (P : Profile) (prof : ProfileKind) (j : InstId)
    {m₀ : Config (fxCE P) Unit} {inst : InstId} {es : List (String × FuncId)}
    (hi : InstResult.instance m₀ inst es ∈
      instBehaviours prof (Silmaril.Wasm.Component.Param.refHostE (fxCE P)) (initConfig ())
        (contProg P).comp (contProg P).args)
    {ds : List (DoneCall Xc)} {mₙ : Config (fxCE P) Unit}
    (hr : RunCalls prof (Silmaril.Wasm.Component.Param.refHostE (fxCE P)) (contProg P).names es m₀ 0
      ds mₙ)
    {c : CallId} {f : FuncId} {args : List Silmaril.Wasm.Component.Value.Val}
    {m' : Config (fxCE P) Unit} {out : CallOutcome}
    (hc : Calls prof (Silmaril.Wasm.Component.Param.refHostE (fxCE P)).hr
      (Silmaril.Wasm.Component.Param.refHostE (fxCE P)).dispatch mₙ c f args m' out) :
    ∃ evs, Table.Steps Table.empty evs (vtab m'.store j) ∧
      ∀ r, (handleProto ℕ r).Accepts (evs.map tableEv) :=
  refMulti_tables_host tabHost_none hi hr hc

/-- info: 'Silmaril.Wasm.Component.FXRes.ContComp.contProg_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms contProg_tables

end Silmaril.Wasm.Component.FXRes.ContComp
