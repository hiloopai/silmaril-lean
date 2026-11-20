module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadLeaf.Local.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.CanonicalTree.Defs
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Grows.Defs
public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs
import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
import Silmaril.Wasm.Component.Reference.Canon.Flat.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadLeaf.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LocalLeaf

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.AsyncRef
open Silmaril.Wasm.Game.HandleAccept.Wit Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence

variable {E : CoreEngine} {Host Result : Type}

local notation "LocalProg" => Prog.Every (S := Eff E Host) LocalStoreOp

theorem eval {body : P E Host Result} (only : LocalProg body) (thread : Option ThreadId) (store : CStore E) :
    ∃ (reached : CStore E) (outcome : Except TrapReason Result), ∀ host,
      Plain.runBody body store host (some thread) = (reached, host, outcome.mapError .trapped) := by
  induction only generalizing store with
  | pure value => exact ⟨store, .ok value, fun _ => rfl⟩
  | @op op next allowed continuation ih =>
    cases op <;> try contradiction
    · exact ih store store
    · rename_i update
      exact ih () (update store)
    · rename_i reason
      exact ⟨store, .error reason, fun _ => rfl⟩
    · exact ih thread store

private theorem localGet : LocalProg (getStore : P E Host (CStore E)) :=
  .op trivial (fun _ => .pure _)

private theorem localModify (update : CStore E → CStore E) : LocalProg (modifyStore (σ := Host) update) :=
  .op trivial (fun _ => .pure _)

private theorem localTrap (reason : TrapReason) : LocalProg (trap reason : P E Host Result) :=
  .op trivial (fun answer => nomatch answer)

private theorem localOrTrap (reason : TrapReason) (value : Option Result) :
    LocalProg (orTrap reason value : P E Host Result) := by
  cases value
  · exact localTrap reason
  · exact .pure _

private theorem localInst (inst : InstId) : LocalProg (getInst inst : P E Host InstState) := by
  unfold getInst getObj
  refine localGet.bind fun store => ?_
  cases ArenaField.insts.get? store inst
  · exact localTrap _
  · exact .pure _

private theorem localAdd (inst : InstId) (entry : HandleEntry) :
    LocalProg (handlesAdd inst entry : P E Host Nat) := by
  unfold handlesAdd
  refine (localInst inst).bind fun state => ?_
  split
  · exact localTrap _
  · exact (localModify _).bind (fun _ => .pure _)

private theorem localOwn (limits : Component.Limits) (cx : LiftLowerContext E) (rt : RtId) (rep : Nat) :
    LocalProg (lowerOwn limits cx rt rep : P E Host Nat) :=
  localGet.bind fun _ => (localModify _).bind fun _ => localAdd cx.inst _

private theorem localEnd (limits : Component.Limits) (kind : EndKind) (cx : LiftLowerContext E) (id : EndId) :
    LocalProg (lowerAsyncValue limits kind cx id : P E Host Nat) :=
  (localModify _).bind fun _ => (localAdd cx.inst _).bind fun _ => (localModify _).bind fun _ => .pure _

private theorem localWord (cx : LiftLowerContext E) (word : Nat) (ptr : Nat) :
    LocalProg (storeInt cx word ptr 4 : P E Host Unit) := by
  unfold storeInt writeMem memAddr
  refine (localOrTrap _ _).bind fun address => localGet.bind fun store => ?_
  split
  · exact localTrap _
  · exact localModify _

theorem localHandle (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (width : AddrType) (item : Field) (output : Stored.Lower.Output) (handle : CanonicalHandle item) :
    LocalProg (CanonicalTree.leaf limits quirks cx width item output : P E Host output.Result) := by
  cases item with
  | owner receipt =>
    have lower := localOwn (Host := Host) limits cx receipt.1 receipt.2.representation
    cases output with
    | memory ptr =>
      simp only [CanonicalTree.leaf, Field.type, Field.value, store]
      exact lower.bind fun word => localWord cx word ptr
    | flat => exact lower.bind fun _ => .pure _
  | endpoint channel element id =>
    cases channel <;> cases output
    · rename_i ptr
      simp only [CanonicalTree.leaf, Field.type, Field.value, Stored.Endpoints.ListLower.endpointType, store]
      exact (localEnd limits .readableStream cx id).bind fun word => localWord cx word ptr
    · exact (localEnd limits .readableStream cx id).bind fun _ => .pure _
    · rename_i ptr
      simp only [CanonicalTree.leaf, Field.type, Field.value, Stored.Endpoints.ListLower.endpointType, store]
      exact (localEnd limits .readableFuture cx id).bind fun word => localWord cx word ptr
    · exact (localEnd limits .readableFuture cx id).bind fun _ => .pure _
  | context id =>
    cases output with
    | memory ptr =>
      simp only [CanonicalTree.leaf, Field.type, Field.value, store]
      exact (localAdd cx.inst (.errCtx id)).bind fun word => localWord cx word ptr
    | flat => exact (localAdd cx.inst (.errCtx id)).bind fun _ => .pure _
  | _ => contradiction

private theorem execute {profile : ProfileKind} {ready : HostReady Host} {dispatch : Call E → P E Host (Ret E)}
    (body : P E Host Result) (start : Config E Host) (reached : CStore E) (outcome : Except TrapReason Result)
    (finish : Result → P E Host (Ret E)) {thread frames rest}
    (focused : start.ctl = ⟨thread, .prog (body >>= finish), frames⟩ :: rest)
    (evaluated : Plain.runBody body start.store start.host (some thread) =
      (reached, start.host, outcome.mapError .trapped)) :
    ∃ labels, LocalLeafLabels outcome labels ∧ Steps profile ready dispatch start labels
      (localLeafEnd start start.host reached thread frames rest finish outcome) ∧
      (∀ value, outcome = .ok value → RetainsActiveSlots profile ready dispatch start labels
        (localLeafEnd start start.host reached thread frames rest finish (.ok value))) := by
  cases outcome with
  | ok value =>
    obtain ⟨labels, silent, tracks⟩ := Plain.runBody_thread_tracks body start reached start.host value finish thread frames rest
      profile ready dispatch focused evaluated
    exact ⟨labels, silent, (prefix_survives (tracks 0)).1, fun _ equal => by cases equal; exact tracks⟩
  | error reason =>
    obtain ⟨count, steps⟩ := Plain.runBody_trap_steps body start reached start.host reason finish thread frames rest
      profile ready dispatch focused evaluated
    exact ⟨_, ⟨count, rfl⟩, steps, fun _ equal => by cases equal⟩

variable {grow : SingleThreaded.GrowOracle} {sig : Stored.Signature}
  {profile : ProfileKind} {ready : HostReady (HostState sig)}
  {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}

private theorem chain {before middle after : Config (core3 grow) (HostState sig)} {front back}
    (left : Steps profile ready dispatch before front middle) (right : Steps profile ready dispatch middle back after) :
    Steps profile ready dispatch before (front ++ back) after := by
  induction left with
  | refl => exact right
  | cons step _ ih => exact .cons step (ih right)

private theorem runBody_keeps {keep : CStore E → Prop} {body : P E Host Result}
    (invariant : P.Inv keep body) (thread : Option ThreadId) (reference : CStore E) (host : Host)
    (valid : keep reference) : keep (Plain.runBody body reference host (some thread)).1 := by
  induction invariant generalizing reference host with
  | pure result => exact valid
  | @op operation next admitted _ ih =>
    cases operation <;> simp only [Plain.runBody]
    all_goals first
      | exact valid
      | exact ih reference reference host valid
      | exact ih () _ host (admitted reference valid)
      | exact ih host reference host valid
      | exact ih () reference _ valid
      | exact ih thread reference host valid

private theorem canonical_growth (base : CStore (core3 grow)) (destination : RecordDestination) (inst : InstId)
    (item : Field) (output : Stored.Lower.Output) :
    P.Inv (fun (store : CStore (core3 grow)) => Core3.Grows base.core store.core)
      (CanonicalTree.leaf Component.Limits.spec Quirks.none (destination.context inst) destination.width item output :
        Session grow sig output.Result) := by
  let keep := fun (store : CStore (core3 grow)) => Core3.Grows base.core store.core
  have laws : P.Inv.StorePres keep :=
    ⟨fun mem ptr bytes store valid => valid.trans (writeMemSt_grows store mem ptr bytes),
      fun _ _ valid => valid, fun _ _ _ valid => valid, fun _ _ valid => valid,
      fun _ _ _ valid => valid, fun _ _ _ valid => valid⟩
  cases output with
  | memory ptr => exact P.Inv.store laws _ _ _ _ _ ptr
  | flat => exact P.Inv.lowerFlatAt laws _ _ _ _ _ _

theorem compare {checked canonical : Config (core3 grow) (HostState sig)}
    (sameStore : checked.store = canonical.store) (destination : RecordDestination) (inst : InstId)
    (item : Field) (handle : CanonicalHandle item) (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow))) {thread checkFrames checkRest canonFrames canonRest}
    (checkAt : checked.ctl = ⟨thread, .prog (Record.Effects.checkedLeaf recordClaims Component.Limits.spec Quirks.none
      (destination.context inst) destination.width item index output >>= checkNext), checkFrames⟩ :: checkRest)
    (canonAt : canonical.ctl = ⟨thread, .prog (CanonicalTree.leaf Component.Limits.spec Quirks.none
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
            (localLeafEnd canonical canonical.host reached thread canonFrames canonRest canonNext (.ok value)) := by
  let body := (CanonicalTree.leaf Component.Limits.spec Quirks.none (destination.context inst)
    destination.width item output : Session grow sig output.Result)
  obtain ⟨guardLabels, guardSilent, guardSteps⟩ := RecordDestination.checked_leaf_prefix
    (profile := profile) (ready := ready) (dispatch := dispatch) checked destination inst item index output checkNext checkAt
  cases verdict : liveLeafPlan checked.store checked.host.writer index item with
  | error issue =>
    exact ⟨guardLabels, guardSilent, by simpa only [verdict] using guardSteps⟩
  | ok plan =>
    let host := plan.elim checked.host (fun spend => { checked.host with writer := spend.apply checked.host.writer })
    let checkedNext := { checked with host, ctl := ⟨thread, .prog (body >>= fun result => checkNext (.ok result)),
      checkFrames⟩ :: checkRest }
    have prefixTracks : RetainsActiveSlots profile ready dispatch checked guardLabels checkedNext := by
      cases plan <;> simpa only [verdict, checkedNext, host, body, Option.elim] using guardSteps
    obtain ⟨reached, outcome, evaluated⟩ := eval
      (localHandle Component.Limits.spec Quirks.none (destination.context inst) destination.width item output handle)
      thread checked.store
    have checkedEval : Plain.runBody body checkedNext.store checkedNext.host (some thread) =
        (reached, checkedNext.host, outcome.mapError .trapped) := evaluated host
    have canonEval : Plain.runBody body canonical.store canonical.host (some thread) =
        (reached, canonical.host, outcome.mapError .trapped) := sameStore ▸ evaluated canonical.host
    have grown : Core3.Grows canonical.store.core reached.core := by
      have kept := runBody_keeps (canonical_growth (sig := sig) canonical.store destination inst item output)
        thread canonical.store canonical.host (Core3.Grows.refl _)
      change Core3.Grows canonical.store.core (Plain.runBody body canonical.store canonical.host (some thread)).1.core at kept
      rw [canonEval] at kept
      exact kept
    obtain ⟨checkLabels, checkTrace, checkRun, checkTracks⟩ := execute (profile := profile) (ready := ready) (dispatch := dispatch)
      body checkedNext reached outcome (fun result => checkNext (.ok result)) (thread := thread)
      (frames := checkFrames) (rest := checkRest) rfl checkedEval
    obtain ⟨canonLabels, canonTrace, canonRun, canonTracks⟩ := execute (profile := profile) (ready := ready) (dispatch := dispatch)
      body canonical reached outcome canonNext canonAt canonEval
    refine ⟨reached, outcome, guardLabels, checkLabels, canonLabels, grown, guardSilent, checkTrace, canonTrace, ?_, canonRun, ?_⟩
    · cases outcome <;> exact chain (prefix_survives (prefixTracks 0)).1 checkRun
    · intro value success
      exact ⟨fun depth => (prefixTracks depth).append (checkTracks value success depth), canonTracks value success⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.LocalLeaf
