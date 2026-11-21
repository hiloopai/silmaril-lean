module

public import Silmaril.Wasm.Game.IOAccept.HostRound.Defs
public import Silmaril.Wasm.Abstract.HostSessionXP.Thms
import Silmaril.Proofs.Wasm.Game.IOAccept.HostRound.Basic

/-! One completed invocation from a ready configuration, with one export address and a
fixed host embedded by `SEnv.uOfHost`. The raw `EvRun` log retains the host identifiers,
arguments, replies and stores; its projection uses the existing role decoders, so a hidden
tag does not imply an absent call. The comparison with `natTripleSXP` is relational, not
an extension of the executable folded interpreter. The theorems do not compare module
instantiation, unfinished prefixes, or arbitrary stateful environments. -/

public section

namespace Silmaril.Wasm.Game.IOAccept

open Silmaril.Accept.IO Silmaril.Games.Abstract Silmaril.Wasm
open Silmaril.Wasm.Abstract (EvRun wasmHostSig)
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Game.Accept (Finished)

variable {X I O C : Type} {P : Numerics.Profile} {host : HostSemantics Nat}
  {m : Module} {mem : Option Nat} {R : Roles X I O C} {ready : Config Nat} {addr : Nat}

/-- At an already-ready instance, completed one-entry `TSession` traces are exactly
the projected finite Core host-event runs, with the same final configuration. -/
theorem TSession.completed_iff_evRun {done : Config Nat} {tags : List (Tag X I O C)}
    (fin : Finished false ready) :
    (TSession P (SEnv.uOfHost host) m mem R ready () [addr] .idle false (done, ()) tags ∧ entryCount tags = 1) ↔
    ∃ args events result, InvokeOk ready.store addr args ∧
      EvRun P host (Execution.Core.invoke ready.store addr args) events done ∧ done.code = result.toAdmin ∧
      tags = [.enter (R.entry addr args)] ++ events.flatMap (answerEventTags m mem R) ++
        [.exit (R.exitVal result (memOf mem done.store))] :=
  Silmaril.Proofs.Wasm.Game.IOAccept.HostRound.completed_iff_evRun fin

open Silmaril.Wasm.Abstract (HostTyped InvOkXP natTripleSXP)
open Silmaril.Wasm.Interp (HostSliceT HostSliceE StoreChkE ehExt TagsOk)

/-- The same completed round, read against the checked folded native session triple.
The result and final store are retained before projecting through `Roles`. -/
theorem TSession.completed_iff_native {o : GrowOracle} {tagTypes : List TagInst}
    {done : Config Nat} {tags : List (Tag X I O C)} (hframe : done.frame = {})
    (fin : Finished false ready) (hstore : StoreOk ready.store)
    (hcheck : StoreChkE (ehExt tagTypes) ready.store.funcs) (htags : TagsOk tagTypes ready.store)
    (htyped : HostTyped host) (hslice : HostSliceT host) (heh : HostSliceE tagTypes host) :
    (TSession (profile o) (SEnv.uOfHost host) m mem R ready () [addr] .idle false (done, ()) tags ∧
        entryCount tags = 1) ↔
    ∃ args events result, done.code = result.toAdmin ∧
      (events, .ret (nativeResult result) done.store) ∈
        (natTripleSXP host (InvOkXP tagTypes)).1 ready.store (addr, args) ∧
      tags = [.enter (R.entry addr args)] ++ events.flatMap (answerEventTags m mem R) ++
        [.exit (R.exitVal result (memOf mem done.store))] :=
  Silmaril.Proofs.Wasm.Game.IOAccept.HostRound.completed_iff_native
    hframe fin hstore hcheck htags htyped hslice heh

end Silmaril.Wasm.Game.IOAccept
