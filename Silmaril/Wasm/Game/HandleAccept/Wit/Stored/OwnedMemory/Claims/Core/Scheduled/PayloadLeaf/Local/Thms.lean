module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadLeaf.Local.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.CanonicalTree.Defs
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Grows.Defs
public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LocalLeaf

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Stored.Endpoints.RecordLower (Field)
open ReturnFrame.Occurrence (RetainsActiveSlots)

/-- The actual memory and flat handle programs perform only local store
operations. Ordinary owner lowering (including allocation before insertion),
endpoint lowering, and error context insertion need no host response. -/
theorem canonical_handle_local {E : CoreEngine} {Host : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) (item : Field) (output : Stored.Lower.Output)
    (handle : CanonicalHandle item) :
    Prog.Every (S := Eff E Host) LocalStoreOp
      (Endpoints.RecordLower.CanonicalTree.leaf limits quirks cx width item output) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LocalLeaf.localHandle limits quirks cx width item output handle

/-- Compare the checked and canonical programs at a reached handle cursor.
A typed refusal runs just the checked guard; the canonical side stays before
the leaf. After successful admission, both sides execute the real canonical
leaf with the same value or trap and reached store. Earlier store effects and
the checked spend survive a late trap. The two success continuations and host
states need not match. -/
theorem RecordDestination.compare_handle_leaf {grow : SingleThreaded.GrowOracle} {sig : Signature}
    {profile : ProfileKind} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {checked canonical : Config (core3 grow) (HostState sig)}
    (sameStore : checked.store = canonical.store) (destination : RecordDestination) (inst : InstId)
    (item : Field) (handle : CanonicalHandle item) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow))) {thread checkFrames checkRest canonFrames canonRest}
    (checkAt : checked.ctl = ⟨thread, .prog (Record.Effects.checkedLeaf recordClaims Component.Limits.spec Quirks.none
      (destination.context inst) destination.width item index output >>= checkNext), checkFrames⟩ :: checkRest)
    (canonAt : canonical.ctl = ⟨thread, .prog (Endpoints.RecordLower.CanonicalTree.leaf Component.Limits.spec Quirks.none
      (destination.context inst) destination.width item output >>= canonNext), canonFrames⟩ :: canonRest) :
    match liveLeafPlan checked.store checked.host.writer index item with
    | .error issue => ∃ labels, (∀ label ∈ labels, label = .tau) ∧ RetainsActiveSlots profile ready dispatch checked labels
        { checked with ctl := ⟨thread, .prog (checkNext (.error issue)), checkFrames⟩ :: checkRest }
    | .ok plan =>
      let host := plan.elim checked.host (fun spend => { checked.host with writer := spend.apply checked.host.writer })
      ∃ reached outcome leading checkLabels canonLabels,
        Core3.Grows canonical.store.core reached.core ∧
        (∀ label ∈ leading, label = .tau) ∧ LocalLeafLabels outcome checkLabels ∧ LocalLeafLabels outcome canonLabels ∧
        Steps profile ready dispatch checked (leading ++ checkLabels)
          (localLeafEnd checked host reached thread checkFrames checkRest (fun result => checkNext (.ok result)) outcome) ∧
        Steps profile ready dispatch canonical canonLabels
          (localLeafEnd canonical canonical.host reached thread canonFrames canonRest canonNext outcome) ∧
        ∀ value, outcome = .ok value →
          RetainsActiveSlots profile ready dispatch checked (leading ++ checkLabels)
            (localLeafEnd checked host reached thread checkFrames checkRest (fun result => checkNext (.ok result)) (.ok value)) ∧
          RetainsActiveSlots profile ready dispatch canonical canonLabels
            (localLeafEnd canonical canonical.host reached thread canonFrames canonRest canonNext (.ok value)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LocalLeaf.compare
    sameStore destination inst item handle index output checkNext canonNext checkAt canonAt

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
