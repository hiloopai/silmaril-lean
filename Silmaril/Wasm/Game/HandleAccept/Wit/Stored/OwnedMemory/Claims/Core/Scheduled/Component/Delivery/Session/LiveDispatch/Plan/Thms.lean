module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Plan.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.StringPlan.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Allocation.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Thms

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core
open ComponentCall.Delivery.FiniteSession
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core
open Stored.Endpoints.RecordLower

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind} {ready : HostReady (HostState sig)}
  {bindings : List (Binding sig)} {base : HostImpl (core3 grow) (HostState sig)}
  {start finish incoming : Config (core3 grow) (HostState sig)} {labels : Trace grow sig}
  {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}

/-- An actual Core engine step in the callback needs no host-write,
dispatch or readiness premise. The reached store need not equal the old one. -/
theorem ClosedCallbackPrefix.core_internal {protectedReturn thread core next frames rest store coreNext}
    (focused : start.ctl = ⟨thread, .core core next, frames⟩ :: rest)
    (running : (core3 grow).status start.store.core core = .running ∨ (core3 grow).status start.store.core core = .stuck)
    (executed : (core3 grow).Internal (start.store.core, core) (store, coreNext))
    (tail : ClosedCallbackPrefix bindings profile ready base protectedReturn
      { start with store := { start.store with core := store }, ctl := ⟨thread, .core coreNext next, frames⟩ :: rest } labels finish) :
    ClosedCallbackPrefix bindings profile ready base protectedReturn start (.core :: labels) finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.coreInternal focused running executed tail

/-- Replay a finite classified callback under the live canonical dispatcher.
Ordinary steps may change the reached store (including guest writes and
growth); confined gives take their real status replies. Accepted observations
are retained on both sides of this prefix, not by arbitrary hooks or later pops. -/
theorem ClosedCallbackPrefix.replay {protectedReturn}
    (path : ClosedCallbackPrefix bindings profile ready base protectedReturn start labels finish)
    (embedder : base.embedder = (Core.Scheduled.host (grow := grow) bindings).embedder)
    (covers : ∀ first second, older first second → protectedReturn first)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ checkedLabels canonLabels reached,
      Steps profile ready (specDispatch ready base) start checkedLabels finish ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming canonLabels reached ∧
      HostFrame.Related.Paired older finish reached ∧
      PayloadPrefix.visible checkedLabels = labels ∧ PayloadPrefix.visible canonLabels = labels ∧
      Core3.Grows start.store.core finish.store.core ∧
      finish.host.writer.accepted = start.host.writer.accepted ∧ reached.host.writer.accepted = incoming.host.writer.accepted :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.replay path embedder covers paired

/-- The real string allocation or resize installs the shorter plan on both
sides. Compare the finite callback under the live overlay, without requiring
it to return and without losing older active or suspended frames. -/
theorem ClosedCallbackPrefix.string_realloc (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (oldSize : Option Nat)
    (alignment : Alignment) (size : Nat) (steps : List StoreStep)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon)
    (checkAt : start.ctl = check.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= checkNext))
    (canonAt : incoming.ctl = canon.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= canonNext))
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (path : ClosedCallbackPrefix bindings profile ready base
      (fun resume => (∃ peer, older resume peer) ∨ resume = PayloadPrefix.stringPlanResume cx steps checkNext)
      (LinkedCallback.stringReallocEntry ready bindings cx ptr oldSize alignment size steps checkNext start check) labels finish) :
    ∃ checkedLabels canonLabels reached mark,
      Steps profile ready (specDispatch ready base) start (.tau :: checkedLabels) finish ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming (.tau :: canonLabels) reached ∧
      HostFrame.Related.Paired (ReturnFrame.Extend older (PayloadPrefix.stringPlanResume cx steps checkNext)
        (PayloadPrefix.stringPlanResume cx steps canonNext)) finish reached ∧
      PayloadPrefix.visible checkedLabels = labels ∧ PayloadPrefix.visible canonLabels = labels ∧
      Core3.Grows start.store.core finish.store.core ∧
      finish.host.writer.accepted = start.host.writer.accepted ∧ reached.host.writer.accepted = incoming.host.writer.accepted ∧
      AllocatorMark profile ready base bindings older
        (LinkedCallback.stringReallocEntry ready bindings cx ptr oldSize alignment size steps checkNext start check)
        (stringAllocatorEntry (specDispatch ready (LiveDispatch.host bindings base)) cx ptr oldSize alignment size incoming canon
          (PayloadPrefix.stringPlanResume cx steps canonNext)) checkedLabels canonLabels finish reached mark :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.stringReallocPrefix
    cx ptr oldSize alignment size steps checkNext canonNext frame checkAt canonAt embedder path

/-- Replay a reached dynamic collection allocation under the live dispatcher.
The saved canonical continuation retains its allocation-time placement mode
(including indirect maps). The dry run is only for entry: it is not evidence
that a claim remains live after an allocator return. -/
theorem ClosedCallbackPrefix.collection_alloc (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Field) (output : Stored.Lower.Output) (index : Nat)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older start incoming check canon)
    (width : (core3 grow).memAddrType? incoming.store.core destination.memory = some destination.width)
    (prepared : Stored.OwnedMemory.Claims.Record.prepare start.store start.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : start.ctl = check.control (Stored.OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : incoming.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext))
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    let area := layout destination.width element
    let first := PayloadPrefix.checkedCollectionResume destination inst entries area index output checkNext
    let second := PayloadPrefix.canonicalCollectionResume destination inst entries area output canonNext
      (CanonicalTree.EntryMode.forOutput destination.width type output)
    ClosedCallbackPrefix bindings profile ready base (fun resume => (∃ peer, older resume peer) ∨ resume = first)
      (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready base) start check first) labels finish →
    ∃ checkedLabels canonLabels reached mark,
      Steps profile ready (specDispatch ready base) start ([.tau, .tau, .tau] ++ checkedLabels) finish ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming ([.tau, .tau] ++ canonLabels) reached ∧
      HostFrame.Related.Paired (ReturnFrame.Extend older first second) finish reached ∧
      PayloadPrefix.visible checkedLabels = labels ∧ PayloadPrefix.visible canonLabels = labels ∧
      Core3.Grows start.store.core finish.store.core ∧
      finish.host.writer.accepted = start.host.writer.accepted ∧ reached.host.writer.accepted = incoming.host.writer.accepted ∧
      AllocatorMark profile ready base bindings older
        (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready base) start check first)
        (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
          incoming canon second) checkedLabels canonLabels finish reached mark :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.collectionPrefix
    destination inst type element entries output index checkNext canonNext frame width prepared checkAt canonAt embedder

/-- Consume the installed allocator frame only at its actual top return.
The canonical continuation is recovered by following its occurrence from the
install, not by comparing continuation code at the reached position. -/
theorem AllocatorMark.pop {checkEntry canonEntry : Config (core3 grow) (HostState sig)} {checkTrace canonTrace : Trace grow sig}
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {value : Ret (core3 grow)}
    {first second : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (marked : AllocatorMark profile ready base bindings older checkEntry canonEntry checkTrace canonTrace finish incoming (some (.active 0 0)))
    (paired : HostFrame.Related.Paired wider finish incoming)
    (returning : finish.ctl = { check with frames := .prog first :: check.frames }.control (.pure value))
    (installed : ReturnFrame.Occurrence.segmentAt (ReturnFrame.Occurrence.segmentStorage canonEntry) (.active 0 0) = some (.prog second)) :
    ∃ canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig),
      LinkedCallback.ChildFrameOver older finish incoming check canon ∧
      Step profile ready (specDispatch ready base) finish .tau { finish with ctl := check.control (first value) } ∧
      Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming .tau
        { incoming with ctl := canon.control (second value) } ∧
      ReturnFrame.Occurrence.RetainsBelowTop profile ready (specDispatch ready base) checkEntry (checkTrace ++ [.tau])
        { finish with ctl := check.control (first value) } ∧
      ReturnFrame.Occurrence.RetainsBelowTop profile ready (specDispatch ready (LiveDispatch.host bindings base))
        canonEntry (canonTrace ++ [.tau]) { incoming with ctl := canon.control (second value) } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.pop marked paired returning installed

/-- A reached marked collection return uses the live memory and claim table.
Both paths take the actual range checks under their respective dispatchers.
Invalid range traps both; valid range hands the checked suffix its fresh
verdict without running any children, and keeps the canonical entry mode. -/
theorem AllocatorMark.collection_range (destination : RecordDestination) (inst : InstId) (type element : Stored.TypeOf)
    (entries : List Field) (output : Stored.Lower.Output) (index pointer : Nat)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {canonStart checked canonical : Config (core3 grow) (HostState sig)}
    {checkEntry canonEntry cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace} :
    let area := layout destination.width element
    let mode := CanonicalTree.EntryMode.forOutput destination.width type output
    let first := PayloadPrefix.checkedCollectionResume destination inst entries area index output checkNext
    let second := PayloadPrefix.canonicalCollectionResume destination inst entries area output canonNext mode
    AllocatorMark profile ready base bindings older
      (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready base) start checkEntry first)
      (PayloadPrefix.collectionEntry destination inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        canonStart canonEntry second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { cursor with frames := .prog first :: cursor.frames }.control (.pure (.nat pointer)) →
    (core3 grow).memAddrType? start.store.core destination.memory = some destination.width →
    Core3.Grows start.store.core checked.store.core →
    CollectionRangeCut profile ready base bindings older checked canonical cursor destination area entries.length pointer
      (Field.listObjects entries)
      (fun addr verdict => PayloadPrefix.checkedCollectionTail destination inst entries area index output addr verdict >>= checkNext)
      (fun addr => PayloadPrefix.canonicalCollectionTail destination inst entries area output addr mode >>= canonNext) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.collectionRange
    destination inst type element entries output index pointer checkNext canonNext

/-- Finish a reached allocating list root on either scheduled public give
route. The compiler certificate determines the entries. The installed mark
and its lower-slot trail identify the original Core caller; a returned pointer
does not promise successful range checks, element writes or publication. -/
theorem AllocatorMark.local_list_replies {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field)
    (data : PayloadPrefix.LocalDataType element) (field : site.field = .dynamic (.list element) element entries) (pointer : Nat)
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)}
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace} :
    let area := layout site.destination.width element
    let first := PayloadPrefix.checkedCollectionResume site.destination site.inst entries area 0 route.output site.reply
    let second := PayloadPrefix.canonicalCollectionResume site.destination site.inst entries area route.output site.referenceReply
    AllocatorMark profile ready base bindings older
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        (site.reference site.referenceReply) site.cursor second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
    Core3.Grows site.checked.store.core checked.store.core →
    CollectionReplies profile ready base bindings older site checked canonical
      (PayloadPrefix.canonicalCollectionTail site.destination site.inst entries area route.output pointer >>= site.referenceReply) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.localListReplies
    site linked element entries data field pointer

/-- Compare every compiled nominal list element after the actual allocator
return on either public give route. Live guards run in sequence against the
reached writer and store. The descriptor is published only after all children
return; a refusal rejoins only the checked caller at the reached stop. -/
theorem AllocatorMark.nominal_list_replies {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field)
    (nominal : NominalElement element) (field : site.field = .dynamic (.list element) element entries) (pointer : Nat)
    (admitted : OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)}
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace} :
    let area := layout site.destination.width element
    let first := PayloadPrefix.checkedCollectionResume site.destination site.inst entries area 0 route.output site.reply
    let second := PayloadPrefix.canonicalCollectionResume site.destination site.inst entries area route.output site.referenceReply
    AllocatorMark profile ready base bindings older
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        (site.reference site.referenceReply) site.cursor second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
    Core3.Grows site.checked.store.core checked.store.core →
    CollectionSegmentReplies profile ready base bindings older site checked canonical
      (ListReturnStop site.destination site.inst entries area route.output pointer site.referenceReply) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.nominalListReplies
    site linked element entries nominal field pointer admitted

/-- Replay a reached memory-map return through every compiled data entry,
descriptor writes, and the original public `givePayload` caller reply.
The canonical offsets are those selected when the allocation was installed. -/
theorem AllocatorMark.local_map_replies {outputPointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory outputPointer))
    (linked : site.Linked bindings) (key : WIT.KeyType) (element : Stored.TypeOf) (entries : List Field)
    (keyData : PayloadPrefix.LocalDataType (.prim key.toPrimitive)) (valueData : PayloadPrefix.LocalDataType element)
    (field : site.field = .dynamic (.map key element) (.record (mapEntryFields key element)) entries) (pointer : Nat)
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)}
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace} :
    let area := layout site.destination.width (.record (mapEntryFields key element))
    let mode := CanonicalTree.EntryMode.memoryMap site.destination.width key element
    let output := (GiveEffectRoute.memory outputPointer).output
    let first := PayloadPrefix.checkedCollectionResume site.destination site.inst entries area 0 output site.reply
    let second := PayloadPrefix.canonicalCollectionResume site.destination site.inst entries area output site.referenceReply mode
    AllocatorMark profile ready base bindings older
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        (site.reference site.referenceReply) site.cursor second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
    Core3.Grows site.checked.store.core checked.store.core →
    CollectionReplies profile ready base bindings older site checked canonical
      (PayloadPrefix.canonicalCollectionTail site.destination site.inst entries area output pointer mode >>= site.referenceReply) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.localMapReplies
    site linked key element entries keyData valueData field pointer

/-- Replay local string effects and finite classified allocator prefixes at
both reached stores. Only a pop of the marked natural-pointer return enters
the smaller plan, with older frame substitutions and Core growth retained. -/
theorem string_plan_replay (cx : LiftLowerContext (core3 grow)) (pointer : Nat) (steps : List StoreStep)
    (checkNext canonNext : Nat → Session grow sig (Ret (core3 grow)))
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {origin : CStore (core3 grow)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (checkAt : left.ctl = check.control (runStoreSteps cx pointer steps >>= checkNext))
    (canonAt : right.ctl = canon.control (runStoreSteps cx pointer steps >>= canonNext))
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    {ends : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop}
    (finish : ∀ pointer lhs rhs check canon, LinkedCallback.ChildFrameOver older lhs rhs check canon →
      Core3.Grows origin.core lhs.store.core → lhs.ctl = check.control (checkNext pointer) →
      rhs.ctl = canon.control (canonNext pointer) → ends pointer lhs rhs check canon) :
    LiveStringReplay profile ready base bindings older cx checkNext canonNext ends steps.length left right check canon :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.stringReplay
    cx pointer steps checkNext canonNext frame growth checkAt canonAt embedder finish

/-- Compare the actual string-key plan in either map placement mode. Static
fit and allocator availability follow the compiled descendant path. Compare
finite classified callback prefixes; only the reached marked return resumes
the residual plan. The live descriptor precedes the value continuation. -/
theorem string_map_key (destination : RecordDestination) (inst : InstId) (element : Stored.TypeOf)
    (output : Stored.Lower.Output) (key : LinkedCallback.StringField) (value root : Field) {schema : Stored.TypeOf}
    (layoutRoot : root.LayoutMatches schema)
    (fitRoot : Stored.Lower.fits Quirks.none destination.encoding destination.width schema root.value = true)
    (allocator : Field.AllocatorFor destination.realloc root)
    (path : Field.Descendant root (.aggregate (.record (mapEntryFields .string element)) [key.field, value]))
    (origin : CStore (core3 grow)) (basePtr bytes count entryIndex issueIndex : Nat)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : basePtr = alignTo basePtr (layout destination.width (.record (mapEntryFields .string element))).alignment)
    (bounds : basePtr + count * (layout destination.width (.record (mapEntryFields .string element))).size ≤ bytes)
    (entry : entryIndex < count)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core right.store.core)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    let cx := destination.context inst
    let type : Stored.TypeOf := .record (mapEntryFields .string element)
    let ptr := basePtr + entryIndex * (layout destination.width type).size
    let keySlot := fun reached => alignTo ptr (layout reached key.field.type).alignment
    let valueSlot := fun keyWidth reached => alignTo
      (keySlot keyWidth + (layout keyWidth key.field.type).size) (layout reached value.type).alignment
    let mode := CanonicalTree.EntryMode.forOutput destination.width (.map .string element) output
    let afterKey := fun keyWidth (_ : Unit) => mapFieldPlacement cx mode fun reached =>
      CanonicalTree.field Limits.spec Quirks.none cx destination.width value (.memory (valueSlot keyWidth reached)) >>= canonNext
    let following := fun verdict : Except Stored.Endpoints.RecordLower.Issue Unit => (match verdict with
      | .error issue => pure (.error issue)
      | .ok () => OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width value 1
          (.memory (valueSlot destination.width destination.width))) >>= fun result => checkNext (result.mapError (.nested issueIndex))
    left.ctl = check.control (OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width
      (.aggregate type [key.field, value]) issueIndex (.memory ptr) >>= checkNext) →
    right.ctl = canon.control (mapFieldPlacement cx mode fun reached =>
      CanonicalTree.field Limits.spec Quirks.none cx destination.width key.field (.memory (keySlot reached)) >>= afterKey reached) →
    StringKeyReplay profile ready base bindings older origin destination inst key (keySlot destination.width) left right check canon
      following (afterKey destination.width) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.stringMapKey
    destination inst element output key value root layoutRoot fitRoot allocator path origin basePtr bytes count entryIndex issueIndex
    width sized aligned bounds entry checkNext canonNext frame growth embedder

/-- After the real key descriptor, check the nominal value against the
reached store and writer. A late refusal stops before canonical value
placement, while a later trap retains the descriptor and earlier effects. -/
theorem string_key_nominal_value (origin : CStore (core3 grow)) (destination : RecordDestination) (inst : InstId)
    (element : Stored.TypeOf) (output : Stored.Lower.Output) (key : LinkedCallback.StringField) (value : Field) (address issueIndex : Nat)
    (nominal : NominalElement element) (matched : value.LayoutMatches element) (emitted : value.Emitted)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} :
    StringKeyNominalValue profile ready base bindings older origin destination inst element output key value address issueIndex
      left right check canon checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.stringKeyNominalValue
    origin destination inst element output key value address issueIndex nominal matched emitted width checkNext canonNext

/-- Accumulate actual paired paths and occurrence trails from string replay.
Finite callback prefixes compare at the reached states without popping;
only the marked return can advance the residual plan. -/
theorem LiveStringReplay.paths {cx : LiftLowerContext (core3 grow)}
    {checkNext canonNext : Nat → Session grow sig (Ret (core3 grow))}
    {leftStart rightStart : Config (core3 grow) (HostState sig)}
    {first : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Prop}
    {second : Nat → Config (core3 grow) (HostState sig) → Config (core3 grow) (HostState sig) →
      PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → PayloadPrefix.Cursor (E := core3 grow) (HostState sig) → Trace grow sig → Prop}
    (next : ∀ ptr lhs rhs check canon seen, first ptr lhs rhs check canon →
      ComparedSlots profile ready base bindings leftStart rightStart seen lhs rhs → second ptr lhs rhs check canon seen)
    {length : Nat} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {seen : Trace grow sig}
    (leading : ComparedSlots profile ready base bindings leftStart rightStart seen left right)
    (run : LiveStringReplay profile ready base bindings older cx checkNext canonNext first length left right check canon) :
    LiveStringPaths profile ready base bindings older cx checkNext canonNext leftStart rightStart second length left right check canon seen :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix.stringPaths next leading run

/-- Derive the selected string key, nominal value and allocator option from
the linked public compiler result. Compare the actual entry programs under
the two dispatchers, after a successful root fit and reached range check. -/
theorem linked_string_map_entry {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field) (index : Fin entries.length)
    (nominal : NominalElement element)
    (field : site.field = .dynamic (.map .string element) (.record (mapEntryFields .string element)) entries)
    (fits : Stored.Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag) site.payload.val.value = true)
    (origin : CStore (core3 grow)) (basePtr bytes : Nat)
    (width : (core3 grow).memAddrType? origin.core site.destination.memory = some site.destination.width)
    (sized : (core3 grow).memSize? origin.core site.destination.memory = some bytes)
    (aligned : basePtr = alignTo basePtr (layout site.destination.width (.record (mapEntryFields .string element))).alignment)
    (bounds : basePtr + entries.length * (layout site.destination.width (.record (mapEntryFields .string element))).size ≤ bytes)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core right.store.core)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    LinkedStringMapEntry profile ready base bindings older site element entries index origin basePtr left right check canon
      checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedStringMapEntry
    site linked element entries index nominal field fits origin basePtr bytes width sized aligned bounds checkNext canonNext frame growth embedder
      _ (fun _ _ _ _ _ grown _ _ => grown)

/-- Compare every reached string-key nominal map entry in either public
give. Advance only on actual returns, retaining the stopped value suffix,
the reached trap, or the finite classified allocator prefix at each entry. -/
theorem linked_string_map_traversal {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field) (index : Nat)
    (nominal : NominalElement element)
    (field : site.field = .dynamic (.map .string element) (.record (mapEntryFields .string element)) entries)
    (fits : Stored.Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag) site.payload.val.value = true)
    (origin : CStore (core3 grow)) (basePtr bytes : Nat)
    (width : (core3 grow).memAddrType? origin.core site.destination.memory = some site.destination.width)
    (sized : (core3 grow).memSize? origin.core site.destination.memory = some bytes)
    (aligned : basePtr = alignTo basePtr (layout site.destination.width (.record (mapEntryFields .string element))).alignment)
    (bounds : basePtr + entries.length * (layout site.destination.width (.record (mapEntryFields .string element))).size ≤ bytes)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core right.store.core)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder)
    (atSuffix : LinkedStringMapAt site element entries index basePtr left right check canon checkNext canonNext) :
    LinkedStringMapTraversal profile ready base bindings older site element entries index origin basePtr left right check canon
      checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedStringMapTraversal
    site linked element entries index nominal field fits origin basePtr bytes width sized aligned bounds checkNext canonNext frame growth embedder atSuffix
      _ (fun _ _ _ _ _ _ _ => trivial)

/-- After the outer range and fresh preparation succeed, compare the actual
recursive map body through descriptor publication. Refused or suspended
children cannot enter the descriptor; a descriptor trap retains reached writes. -/
theorem linked_string_map_body {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field)
    (nominal : NominalElement element)
    (field : site.field = .dynamic (.map .string element) (.record (mapEntryFields .string element)) entries)
    (fits : Stored.Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag) site.payload.val.value = true)
    (basePtr bytes : Nat)
    {left right : Config (core3 grow) (HostState sig)} {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (width : (core3 grow).memAddrType? left.store.core site.destination.memory = some site.destination.width)
    (sized : (core3 grow).memSize? left.store.core site.destination.memory = some bytes)
    (aligned : basePtr = alignTo basePtr (layout site.destination.width (.record (mapEntryFields .string element))).alignment)
    (bounds : basePtr + entries.length * (layout site.destination.width (.record (mapEntryFields .string element))).size ≤ bytes)
    (frame : LinkedCallback.ChildFrameOver older left right check canon)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    let area := layout site.destination.width (.record (mapEntryFields .string element))
    let mode := CanonicalTree.EntryMode.forOutput site.destination.width (.map .string element) route.output
    left.ctl = check.control (PayloadPrefix.checkedCollectionTail site.destination site.inst entries area 0 route.output basePtr (.ok ()) >>= site.reply) →
    right.ctl = canon.control (PayloadPrefix.canonicalCollectionTail site.destination site.inst entries area route.output basePtr mode >>= site.referenceReply) →
    LinkedStringMapBody profile ready base bindings older site element entries basePtr left right check canon :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedStringMapBody
    site linked element entries nominal field fits basePtr bytes width sized aligned bounds frame embedder

/-- Follow the marked outer allocator return through reached alignment, bounds,
and fresh preparation. An invalid range traps without reply; typed preparation
refusal replies on checked only. A successful check starts the recursive map
body with exact visible range prefixes and the original caller occurrence. -/
theorem AllocatorMark.string_map_return {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field)
    (nominal : NominalElement element)
    (field : site.field = .dynamic (.map .string element) (.record (mapEntryFields .string element)) entries)
    (fits : Stored.Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag) site.payload.val.value = true)
    (pointer : Nat) (admitted : OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)}
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace}
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    let entryType : Stored.TypeOf := .record (mapEntryFields .string element)
    let area := layout site.destination.width entryType
    let output := route.output
    let mode := CanonicalTree.EntryMode.forOutput site.destination.width (.map .string element) output
    let first := PayloadPrefix.checkedCollectionResume site.destination site.inst entries area 0 output site.reply
    let second := PayloadPrefix.canonicalCollectionResume site.destination site.inst entries area output site.referenceReply mode
    AllocatorMark profile ready base bindings older
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        (site.reference site.referenceReply) site.cursor second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
    Core3.Grows site.checked.store.core checked.store.core →
    LinkedStringMapReturn profile ready base bindings older site element entries pointer checked canonical check :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedStringMapReturn
    site linked element entries nominal field fits pointer admitted embedder

/-- Compare the reached string-key nominal map paths through the original public
caller rejoins. A finite suspended key keeps its accumulated occurrence path;
late refusal rejoins only checked and traps execute neither reply. -/
theorem AllocatorMark.string_map_paths {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (element : Stored.TypeOf) (entries : List Field)
    (nominal : NominalElement element)
    (field : site.field = .dynamic (.map .string element) (.record (mapEntryFields .string element)) entries)
    (fits : Stored.Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag) site.payload.val.value = true)
    (pointer : Nat) (admitted : OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)}
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace}
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    let entryType : Stored.TypeOf := .record (mapEntryFields .string element)
    let area := layout site.destination.width entryType
    let output := route.output
    let mode := CanonicalTree.EntryMode.forOutput site.destination.width (.map .string element) output
    let first := PayloadPrefix.checkedCollectionResume site.destination site.inst entries area 0 output site.reply
    let second := PayloadPrefix.canonicalCollectionResume site.destination site.inst entries area output site.referenceReply mode
    AllocatorMark profile ready base bindings older
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        (site.reference site.referenceReply) site.cursor second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
    Core3.Grows site.checked.store.core checked.store.core →
    LinkedStringMapReturnPaths profile ready base bindings older site element entries pointer checked canonical check :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.linkedStringMapReturnPaths
    site linked element entries nominal field fits pointer admitted embedder

/-- Traverse the actual map lowering for either public give after a reached allocator return.
The compiler determines each scalar key and nominal value; successful keys
remain written if a later value refuses or traps. Flat entries read the
reached width at their own field boundaries; memory entries use the captured
width. Only a completed map publishes the descriptor and rejoins both callers. -/
theorem AllocatorMark.nominal_map_replies {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (linked : site.Linked bindings) (key : WIT.KeyType) (element : Stored.TypeOf) (entries : List Field)
    (keyData : PayloadPrefix.LocalDataType (.prim key.toPrimitive)) (nominal : NominalElement element)
    (field : site.field = .dynamic (.map key element) (.record (mapEntryFields key element)) entries) (pointer : Nat)
    (admitted : OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
    {wider : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {checked canonical : Config (core3 grow) (HostState sig)}
    {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)} {checkTrace canonTrace} :
    let entryType : Stored.TypeOf := .record (mapEntryFields key element)
    let area := layout site.destination.width entryType
    let output := route.output
    let mode := CanonicalTree.EntryMode.forOutput site.destination.width (.map key element) output
    let first := PayloadPrefix.checkedCollectionResume site.destination site.inst entries area 0 output site.reply
    let second := PayloadPrefix.canonicalCollectionResume site.destination site.inst entries area output site.referenceReply mode
    AllocatorMark profile ready base bindings older
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready base) site.checked site.cursor first)
      (PayloadPrefix.collectionEntry site.destination site.inst area entries.length (specDispatch ready (LiveDispatch.host bindings base))
        (site.reference site.referenceReply) site.cursor second) checkTrace canonTrace checked canonical (some (.active 0 0)) →
    HostFrame.Related.Paired wider checked canonical →
    checked.ctl = { check with frames := .prog first :: check.frames }.control (.pure (.nat pointer)) →
    Core3.Grows site.checked.store.core checked.store.core →
    CollectionSegmentReplies profile ready base bindings older site checked canonical
      (MapReturnStop site.destination site.inst key element entries output pointer site.referenceReply) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.nominalMapReplies
    site linked key element entries keyData nominal field pointer admitted

/-- At a reached owner, endpoint, or error-context leaf, use the live
checked writer, not the enclosing dry run. Neither branch dispatches a
callback at this leaf. A checked refusal leaves canonical before the leaf;
after a successful check the actual spend survives a later canonical trap. -/
theorem reached_handle_field (destination : RecordDestination) (inst : InstId) (item : Field) (handle : CanonicalHandle item)
    (index : Nat) (output : Stored.Lower.Output)
    (checkNext : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {origin : CStore (core3 grow)} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : LinkedCallback.ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (checkAt : left.ctl = check.control (OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width item index output >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width item output >>= canonNext)) :
    LinkedCallback.HandleFieldThenBetween profile ready (specDispatch ready base) (specDispatch ready (LiveDispatch.host bindings base))
      item index output left right check canon checkNext canonNext (fun value reached reference lhs rhs =>
        LinkedCallback.ChildFrameOver older reached reference lhs rhs ∧ Core3.Grows origin.core reached.store.core ∧
        reached.ctl = lhs.control (checkNext (.ok value)) ∧ reference.ctl = rhs.control (canonNext value)) :=
  frame.handle_field_then_between destination inst item handle index output checkNext canonNext growth checkAt canonAt
    (fun _ _ _ _ _ related grown lhs rhs => ⟨related, grown, lhs, rhs⟩)

/-- On a valid reached range with failed live preparation, execute exactly
the checked refusal reply. This applies to the actual map entry mode as
well as ordinary list placement; canonical never enters those children. -/
theorem CollectionRangeCut.refused_reply {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route)
    (type element : Stored.TypeOf) (entries : List Field) (index pointer bytes : Nat)
    {checked canonical : Config (core3 grow) (HostState sig)} {check : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    {leading issue} :
    let area := layout site.destination.width element
    let child := PayloadPrefix.canonicalCollectionTail site.destination site.inst entries area route.output pointer
      (CanonicalTree.EntryMode.forOutput site.destination.width type route.output) >>= site.referenceReply
    let reply := route.reply site.destination site.start.host.nextTicket
      (.error (LinkedCallback.CollectionVisit.afterAllocation index issue))
    CollectionRangeCut profile ready base bindings older checked canonical check site.destination area entries.length pointer
      (Field.listObjects entries)
      (fun addr live => PayloadPrefix.checkedCollectionTail site.destination site.inst entries area index route.output addr live >>= site.reply)
      (fun addr => PayloadPrefix.canonicalCollectionTail site.destination site.inst entries area route.output addr
        (CanonicalTree.EntryMode.forOutput site.destination.width type route.output) >>= site.referenceReply) →
    ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready base) site.checked (.active 0 0) leading checked (.active 0 1) →
    (core3 grow).memSize? checked.store.core site.destination.memory = some bytes →
    pointer = alignTo pointer area.alignment → pointer + entries.length * area.size ≤ bytes →
    Stored.OwnedMemory.Claims.Record.prepare checked.store checked.host.writer (Field.listObjects entries) = .error issue →
    ∃ (canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (checkedLabels canonLabels : Trace grow sig)
      (segments : List (Seg (core3 grow) (HostState sig))),
      (∀ label ∈ checkedLabels, label = .tau) ∧ (∀ label ∈ canonLabels, label = .tau) ∧
      Steps profile ready (specDispatch ready base) checked (checkedLabels ++ [.tau, .tau, .tau])
        { checked with
          host := checked.host.record reply.1
          ctl := ⟨check.thread, .core ((core3 grow).resume checked.store.core site.core (.values reply.2)) site.resume,
            segments⟩ :: check.rest } ∧
      ReturnFrame.Occurrence.RetainsBelowTop profile ready (specDispatch ready (LiveDispatch.host bindings base)) canonical canonLabels
        { canonical with ctl := canon.control child } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackRange.refusalReply site type element entries index pointer bytes

theorem NestedPlan.source (plan : NestedPlan bindings profile ready base start labels finish) :
    Steps profile ready (specDispatch ready base) start labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.source plan

/-- Decompose an actual prefix at its reached foci. Local steps replay fully;
nonlocal steps still go through the live request/read/return classifier. -/
theorem NestedPlan.of_steps (run : Steps profile ready (specDispatch ready base) start labels finish) :
    NestedPlan bindings profile ready base start labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.planOfSteps run

/-- Derive a closed reentry edge at the reached caller and binding under the
same component dispatcher used by the worker. No checked body, padding,
or older-frame equality is supplied by the caller of the theorem. -/
theorem linked_closed_give_plan {callees : List (ComponentCall.Callee sig)} (callout : LinkedCallback.ClosedGive bindings start) :
    ∃ count, NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) start
      (List.replicate count .tau) callout.resume :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.closedGivePlan callout rfl

/-- Reuse the allocator's finite callback classification rather than
flattening closed reentries and classified readiness reads into raw steps.
The endpoint may still be parked. Unclassified steps retain the ordinary
live replay boundaries. -/
theorem NestedPlan.of_callback_prefix {protectedReturn}
    (path : LinkedCallback.PrefixFor profile ready bindings protectedReturn start labels finish) :
    ∃ trace, NestedPlan bindings profile ready (Scheduled.host bindings) start trace finish ∧
      PayloadPrefix.visible trace = labels :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.callbackPlan path

/-- Lift the very trace used to track an allocator occurrence, not another
prefix with the same visible labels. The resulting plan still classifies
ordinary steps at the live dispatcher boundary. -/
theorem NestedPlan.of_callback_trace {right reference : Config (core3 grow) (HostState sig)} {referenceLabels}
    (trace : LinkedCallback.ReplayTrace profile ready bindings start labels finish right referenceLabels reference) :
    NestedPlan bindings profile ready (Scheduled.host bindings) start labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.callbackPlanExact trace

/-- The substituted canonical body has its own exact callback classifications,
including the actual confined caller and readiness read at each reentry. -/
theorem NestedPlan.of_callback_peer {right reference : Config (core3 grow) (HostState sig)} {referenceLabels}
    (trace : LinkedCallback.ReplayTrace profile ready bindings start labels finish right referenceLabels reference) :
    NestedPlan bindings profile ready (Scheduled.host bindings) right referenceLabels reference :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.callbackPeerPlanExact trace

/-- Lift the exact classified reference trace to the fixed component worker
dispatcher. The actual confined reentry cannot invoke a direct dispatch,
and each readiness read keeps its own reached agreement. Unclassified
segments can still end at an explicit dispatch lookup boundary. -/
theorem linked_callback_peer_plan {right reference : Config (core3 grow) (HostState sig)} {referenceLabels}
    {callees : List (ComponentCall.Callee sig)}
    (trace : LinkedCallback.ReplayTrace profile ready bindings start labels finish right referenceLabels reference) :
    CallbackOverlayPlan bindings profile ready callees right referenceLabels reference ∨
      CallbackOverlayCut bindings profile ready callees right referenceLabels reference :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.linkedCallbackPeer trace

/-- Extract the canonical body plan from a reached public give comparison.
It uses the same trace as the recursive traversal and does not rebuild a plan
from unclassified steps. Component-only dispatch extensions are not asserted
compatible by this theorem. -/
theorem rejoined_give_body_plan {route : GiveEffectRoute} {site : PayloadRoot.Site grow sig route}
    {value : route.output.Result} {checked reference : Config (core3 grow) (HostState sig)}
    (comparison : LinkedCallback.MemorySequence.RejoinedGive site value profile ready bindings checked reference) :
    ∃ checkLabels referenceLabels,
      Steps profile ready (specDispatch ready (Scheduled.host bindings)) site.checked checkLabels checked ∧
      NestedPlan bindings profile ready (Scheduled.host bindings) (site.reference site.referenceReply) referenceLabels reference ∧
      PayloadPrefix.visible checkLabels = PayloadPrefix.visible referenceLabels :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.rejoinedBodyPlan comparison

/-- At the reached linked memory give, use the public entry guards and the
compiled recursive body. A preflight refusal becomes a checked reply and a
stopped live canonical prefix, not a canonical error. A placement trap is
also a stopped prefix: canonical store requires valid root placement. -/
theorem linked_memory_admission {pointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory pointer))
    (linked : site.Linked bindings) {callees : List (ComponentCall.Callee sig)} :
    ∃ depth, RootAdmission bindings profile ready (ComponentCall.hostWithComponent bindings callees) site
      (LinkedCallback.MemorySequence.ParkedRejoinedMemory site depth profile ready bindings) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.memoryAdmission site linked

/-- The flat ABI uses the same admission split and the recursive flat body
with its actual memory-emitting descendants. -/
theorem linked_flat_admission {schema : Stored.TypeOf} (site : PayloadRoot.Site grow sig (.flat schema))
    (linked : site.Linked bindings) {callees : List (ComponentCall.Callee sig)} :
    ∃ flatDepth entryDepth, RootAdmission bindings profile ready (ComponentCall.hostWithComponent bindings callees) site
      (LinkedCallback.MemorySequence.ParkedRejoinedFlat site flatDepth entryDepth profile ready bindings) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.flatAdmission site linked

/-- Join a recursive public give's reached checked and canonical bodies to
the actual caller replies. This constructs the replay plan from the compared
paths; it does not assume that a reached nested callout can be replayed. -/
theorem compared_give_plan {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {entryLabels checkLabels canonLabels reached reference checked baseline} (value : route.output.Result)
    (entry : Transition profile ready base site.start (.give route .entered) entryLabels site.checked)
    (left : Steps profile ready (specDispatch ready base) site.checked checkLabels reached)
    (right : Steps profile ready (specDispatch ready base) (site.reference site.referenceReply) canonLabels reference)
    (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels)
    (replies : LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline) :
    NestedPlan bindings profile ready base site.start (entryLabels ++ checkLabels ++ [.tau, .tau, .tau]) checked :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.comparedGive
    site linked value entry left right seen replies

/-- For either recursive public give that reaches its successful caller
rejoin, build the session plan on the Core binding dispatcher without a
separate child/body plan. Finite checked refusal and trap are not successful
rejoins. When run live, an intervening nested give may still cut the plan. -/
theorem rejoined_give_plan {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {entryLabels reached reference} (value : route.output.Result)
    (entry : Transition profile ready (Scheduled.host bindings) site.start (.give route .entered) entryLabels site.checked)
    (compared : LinkedCallback.MemorySequence.RejoinedGive site value profile ready bindings reached reference) :
    ∃ checkLabels checked baseline,
      NestedPlan bindings profile ready (Scheduled.host bindings) site.start (entryLabels ++ checkLabels ++ [.tau, .tau, .tau]) checked ∧
      LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.rejoinedGive site linked value entry compared

/-- Classify the successful recursive rejoin under the worker's linked
dispatcher. No agreement premise is needed at ordinary allocation, local
operations or Core callouts. An unequal direct install is exposed at its
actual common-prefix cut, not converted to a refusal or canonical trap. -/
theorem linked_rejoined_give_plan {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {callees : List (ComponentCall.Callee sig)} {entryLabels reached reference} (value : route.output.Result)
    (entry : Transition profile ready (ComponentCall.hostWithComponent bindings callees)
      site.start (.give route .entered) entryLabels site.checked)
    (compared : LinkedCallback.MemorySequence.RejoinedGive site value profile ready bindings reached reference) :
    LinkedGiveExit bindings profile ready callees site entryLabels value reached reference :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.linkedRejoinedGive site linked value entry compared

/-- Derive entry and the recursive success continuation at the reached memory
give. The caller supplies neither a body comparison nor a replay plan. -/
theorem linked_memory_exit {pointer : FlatValue} (site : PayloadRoot.Site grow sig (.memory pointer))
    (linked : site.Linked bindings) {callees : List (ComponentCall.Callee sig)} :
    ∃ depth, RootAdmission bindings profile ready (ComponentCall.hostWithComponent bindings callees) site
      (LinkedCallback.MemorySequence.ParkedMemoryBody site depth profile ready bindings (fun reached reference =>
        ∃ entryLabels, LinkedGiveExit bindings profile ready callees site entryLabels () reached reference)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.linkedMemoryExit site linked

/-- The flat give specializes the same reached-entry construction, with its
computed ABI words in the returned comparison. -/
theorem linked_flat_exit {schema : Stored.TypeOf} (site : PayloadRoot.Site grow sig (.flat schema))
    (linked : site.Linked bindings) {callees : List (ComponentCall.Callee sig)} :
    ∃ flatDepth entryDepth, RootAdmission bindings profile ready (ComponentCall.hostWithComponent bindings callees) site
      (LinkedCallback.MemorySequence.ParkedFlatResult site flatDepth entryDepth profile ready bindings (fun value reached reference =>
        ∃ entryLabels, LinkedGiveExit bindings profile ready callees site entryLabels value reached reference)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.linkedFlatExit site linked

/-- At a reached Core give with successful ABI selection, compute the
compiler outcome and obtain the corresponding public checked path. If the
body is entered, its recursive continuation comes from the actual compiler,
without a supplied body comparison or replay plan. -/
theorem CoreGiveRequest.Selected.linked_admission {route : GiveEffectRoute} {request : CoreGiveRequest bindings start}
    (selection : request.Selected route) {callees : List (ComponentCall.Callee sig)} :
    ReachedGiveAdmission profile ready callees selection :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.reachedGiveAdmission selection

/-- Reach both sides of the compiler boundary under the linked worker
dispatchers. Compilation supplies the checked refusal or recursive exit;
the canonical side is at the actual pending program, not a status reply. -/
theorem CoreGiveRequest.Selected.paired_linked_admission {route : GiveEffectRoute} {request : CoreGiveRequest bindings start}
    (selection : request.Selected route) {callees : List (ComponentCall.Callee sig)}
    (paired : HostFrame.Related.Paired older start incoming)
    (reads : ∀ handle, request.lookupDemand = some handle →
      Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle =
        Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted handle) :
    ∃ entryLabels entered, entryLabels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings (ComponentCall.hostWithComponent bindings callees)))
        incoming entryLabels entered ∧
      HostFrame.Related.Paired older selection.canonicalPending entered ∧
      ReachedGiveAdmission profile ready callees selection :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.pairedLinkedAdmission selection paired reads

/-- Follow a classified delivery interleaving to an actually selected give.
The reached lookup and compiler cut follow from the starting accepted
observations even when the interleaving registered new roots. -/
theorem CoreGiveRequest.Selected.linked_admission_after_interleaving {route : GiveEffectRoute}
    {request : CoreGiveRequest bindings finish} (selection : request.Selected route)
    {callees : List (ComponentCall.Callee sig)} {actions incoming outgoing}
    (between : JournalInterleaving profile ready (ComponentCall.hostWithComponent bindings callees)
      start incoming actions labels finish outgoing)
    (roots : incoming.writer.accepted = start.host.writer.accepted) :
    ∃ entryLabels canonical, entryLabels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings (ComponentCall.hostWithComponent bindings callees)))
        (HostFrame.replace start incoming) (labels ++ entryLabels) canonical ∧
      HostFrame.Related.Paired (fun _ _ => False) selection.canonicalPending canonical ∧
      canonical.host.writer.accepted = finish.host.writer.accepted ∧
      ReachedGiveAdmission profile ready callees selection :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.linkedAdmissionAfterInterleaving selection between roots

/-- A closed allocator prefix that reaches another selected give derives the
live lookup from the observations at entry to the prefix. The nested canonical
emitter is installed with all older frames still paired; the reached checked
compiler determines the next branch. The nested body is not assumed equivalent. -/
theorem ClosedCallbackPrefix.linked_admission {route : GiveEffectRoute} {request : CoreGiveRequest bindings finish}
    (selection : request.Selected route) {callees : List (ComponentCall.Callee sig)} {protectedReturn}
    (path : ClosedCallbackPrefix bindings profile ready (ComponentCall.hostWithComponent bindings callees)
      protectedReturn start labels finish)
    (covers : ∀ first second, older first second → protectedReturn first)
    (paired : HostFrame.Related.Paired older start incoming)
    (roots : start.host.writer.accepted = incoming.host.writer.accepted) :
    ∃ checkedLabels canonLabels entryLabels canonical,
      Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees)) start checkedLabels finish ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings (ComponentCall.hostWithComponent bindings callees)))
        incoming (canonLabels ++ entryLabels) canonical ∧
      PayloadPrefix.visible checkedLabels = labels ∧ PayloadPrefix.visible (canonLabels ++ entryLabels) = labels ∧
      HostFrame.Related.Paired older selection.canonicalPending canonical ∧
      canonical.host.writer.accepted = finish.host.writer.accepted ∧ ReachedGiveAdmission profile ready callees selection :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.linkedAdmissionAfterCallback
    selection path covers paired roots

/-- When the checked compiler refuses, only that side rejoins the caller.
The canonical run ends before its emitter; neither side undoes the
interleaving and their accepted observations agree at the cut. -/
theorem CoreGiveRequest.Selected.compiler_refusal_after_interleaving {route : GiveEffectRoute}
    {request : CoreGiveRequest bindings finish} (selection : request.Selected route)
    {callees : List (ComponentCall.Callee sig)} {actions incoming outgoing}
    (between : JournalInterleaving profile ready (ComponentCall.hostWithComponent bindings callees)
      start incoming actions labels finish outgoing)
    (roots : incoming.writer.accepted = start.host.writer.accepted) {issue : Stored.Endpoints.RecordLower.Issue}
    (refused : selection.preflight = .error issue) :
    ∃ count entryLabels canonical, entryLabels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (ComponentCall.hostWithComponent bindings callees))
        start (labels ++ List.replicate count .tau) (selection.compilerRefused issue) ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings (ComponentCall.hostWithComponent bindings callees)))
        (HostFrame.replace start incoming) (labels ++ entryLabels) canonical ∧
      HostFrame.Related.Paired (fun _ _ => False) selection.canonicalPending canonical ∧
      canonical.host.writer.accepted = (selection.compilerRefused issue).host.writer.accepted :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.compilerRefusalAfterInterleaving selection between roots refused

/-- The reached compiler refusal is a finite session edge. On the live
canonical side, replay stops before the emitter, including when the
checked path continues after its typed Core reply. -/
theorem CoreGiveRequest.Selected.compiler_refusal_plan {route : GiveEffectRoute} {request : CoreGiveRequest bindings start}
    (selection : request.Selected route) {issue : Stored.Endpoints.RecordLower.Issue}
    (refused : selection.preflight = .error issue)
    (embedder : base.embedder = (Scheduled.host (grow := grow) bindings).embedder) :
    ∃ count, NestedPlan bindings profile ready base start (List.replicate count .tau) (selection.compilerRefused issue) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.compilerRefusalPlan selection refused embedder

/-- Classify the actual matched body prefix of a typed refusal or canonical
trap. Reaching a refusal does not pop a canonical caller or emit its checked
error there. A canonical trap is compared with its reached store, not the
entry store. Neither branch requires an unvisited callback suffix. -/
theorem linked_stopped_give_plan {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    {callees : List (ComponentCall.Callee sig)} {entryLabels checkLabels canonLabels reached reference check phase}
    (entry : Transition profile ready (ComponentCall.hostWithComponent bindings callees)
      site.start (.give route .entered) entryLabels site.checked)
    (left : Steps profile ready (Dispatch.coreOnly ready bindings) site.checked checkLabels reached)
    (right : Steps profile ready (Dispatch.coreOnly ready bindings) (site.reference site.referenceReply) canonLabels reference)
    (stop : GiveStop site check phase canonLabels reached reference) (store : reached.store = reference.store)
    (seen : PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels) :
    NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) site.start
        (entryLabels ++ checkLabels) reached ∨
      Dispatch.LookupCut profile ready bindings callees site.checked checkLabels reached ∨
      Dispatch.LookupCut profile ready bindings callees (site.reference site.referenceReply) canonLabels reference :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.linkedGiveStop
    site linked entry left right stop store seen

/-- Classify the actual finite callback of a public give, preserving active,
saved and absent occurrence marks. An absent mark is not evidence of return.
The canonical plan keeps the already executed classified edges without a
premise that the allocator makes further progress. -/
theorem linked_allocator_cut {route : GiveEffectRoute} {site : PayloadRoot.Site grow sig route}
    {callees : List (ComponentCall.Callee sig)} {changes : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    {beforeCheck beforeCanon left right reached reference : Config (core3 grow) (HostState sig)}
    {checkEntryLabels canonEntryLabels checkLabels canonLabels mark}
    (cut : AllocatorCut profile ready bindings older changes left right reached reference checkLabels canonLabels mark)
    (checkEntry : Dispatch.Compatible profile ready bindings callees site.checked checkEntryLabels beforeCheck)
    (canonEntry : Dispatch.Compatible profile ready bindings callees (site.reference site.referenceReply) canonEntryLabels beforeCanon)
    (seenEntry : PayloadPrefix.visible checkEntryLabels = PayloadPrefix.visible canonEntryLabels)
    (checkInstall : Steps profile ready (Dispatch.linked ready bindings callees) beforeCheck [.tau, .tau, .tau] left)
    (canonInstall : Steps profile ready (Dispatch.linked ready bindings callees) beforeCanon [.tau, .tau] right) :
    let checkTrace := checkEntryLabels ++ [.tau, .tau, .tau] ++ checkLabels
    let canonTrace := canonEntryLabels ++ [.tau, .tau] ++ canonLabels
    (Transition profile ready (ComponentCall.hostWithComponent bindings callees) site.checked
        (.give route (.allocatorPrefix mark)) checkTrace reached ∧
      NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees)
        (site.reference site.referenceReply) canonTrace reference ∧
      PayloadPrefix.visible checkTrace = PayloadPrefix.visible canonTrace) ∨
      CallbackOverlayCut bindings profile ready callees left checkLabels reached ∨
      CallbackOverlayCut bindings profile ready callees right canonLabels reference :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.linkedAllocatorCut
    cut checkEntry canonEntry seenEntry checkInstall canonInstall

/-- A closed local segment replays to the end, even with a different host and
older paired continuations. It leaves both hosts' accepted observations and
claims unchanged: the reached foci exclude host updates as well as reads and
callouts. No corresponding frame is implied for a callback. -/
theorem local_segment_replay (run : PayloadPrefix.LocalSteps profile ready (specDispatch ready base) start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ reached, Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming labels reached ∧
      HostFrame.Related.Paired older finish reached ∧ finish.host = start.host ∧ reached.host = incoming.host :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.replayLocal run paired

/-- Descend through compared nested bodies, then continue from the actual
caller rejoin with the reached host. Only the completed case has the full
checked observable trace as a guarantee. A cut records a reached configuration
and a matching observable prefix, not execution of the unvisited suffix. -/
theorem NestedPlan.runs (plan : NestedPlan bindings profile ready base start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ trace reached, Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming trace reached ∧
      PayloadPrefix.visible trace <+: PayloadPrefix.visible labels ∧
      ((PayloadPrefix.visible labels = PayloadPrefix.visible trace ∧ HostFrame.Related.Paired older finish reached) ∨
        NestedCut bindings profile ready base older reached) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.runs plan paired

/-- Join actual argument lowering and Core entry to a classified body,
worker completion and delivery under one linked dispatcher. The body may
contain nested gives; it is selected only at the reached Core entry. An
argument trap or suspension instead ends the finite plan before entry. -/
theorem stackful_worker_plan {reached first : Config (core3 grow) (HostState sig)} {site : OnStartSite start} {handoff : LowerStartAt site}
    {returned : LowerArgumentReturn handoff reached} {callees : List (ComponentCall.Callee sig)}
    (args : CalleeArguments returned) {Result : Type} (words : Result → List FlatValue)
    (lowered : StringPlanPair profile ready bindings callees first (fun result => args.enter (words result)))
    (asyncMode : args.record.opts.async_ = true) (callback : args.record.opts.callback = none)
    (body : ∀ (entry : Config (core3 grow) (HostState sig)) (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (flat : List FlatValue),
      entry.ctl = ⟨cursor.thread, .core ((core3 grow).invoke args.callee flat) (stackfulTail args.task), cursor.frames⟩ :: cursor.rest →
      ∃ bodyLabels afterBody exitLabels afterExit deliveryLabels last,
        NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) entry bodyLabels afterBody ∧
        StackfulBodyEnd args.task afterBody exitLabels afterExit ∧
        (∀ (site : StackfulReturn afterBody), site.segments = []) ∧
        NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) afterExit deliveryLabels last) :
    ∃ leading entry trailing last,
      Steps profile ready (Dispatch.linked ready bindings callees) first leading entry ∧
      NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) first (leading ++ trailing) last ∧
      ((∃ (cursor : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)) (flat : List FlatValue),
          entry.ctl = ⟨cursor.thread, .core ((core3 grow).invoke args.callee flat) (stackfulTail args.task), cursor.frames⟩ :: cursor.rest ∧
          NestedPlan bindings profile ready (ComponentCall.hostWithComponent bindings callees) entry trailing last) ∨
        (StringPlanStopped profile ready bindings first leading entry ∧ trailing = [] ∧ last = entry)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.stackfulWorker
    args words lowered asyncMode callback body

/-- A placed public memory or flat give with a nonallocating data root has
its body comparison derived from the compiled field and linked width.
It rejoins the original Core caller on success; a canonical trap instead
keeps the common reached store and does not issue a completion reply. -/
theorem local_data_give_plan {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    (data : PayloadPrefix.LocalDataType (sig.payload site.tag)) (payload : Stored.Payload (sig.payload site.tag))
    (field : site.field = .data (sig.payload site.tag) payload) {entryLabels}
    (entryPath : Steps profile ready (specDispatch ready base) site.start entryLabels site.checked)
    (silent : PayloadPrefix.visible entryLabels = [])
    (placed : PayloadPrefix.rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .ok ())
    (prepared : Stored.OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ()) :
    ∃ bodyLabels reached, NestedPlan bindings profile ready base site.start (entryLabels ++ bodyLabels) reached ∧
      ((∃ value checkedLabels atReply,
        Steps profile ready (specDispatch ready base) site.checked checkedLabels atReply ∧
        atReply.ctl = site.cursor.control (site.reply (.ok value)) ∧ bodyLabels = checkedLabels ++ [.tau, .tau, .tau] ∧
        reached.host = atReply.host.record (route.reply site.destination site.start.host.nextTicket (.ok value)).1) ∨
      (reached.ctl = [] ∧ ∃ leading reason, PayloadPrefix.visible bodyLabels = leading ++ [.trap reason])) := by
  obtain ⟨labels, reached, plan, outcome, _⟩ := Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.localDataGive
    site linked data payload field entryPath silent placed prepared
  exact ⟨labels, reached, plan, outcome⟩

/-- Compare the actual checked and live canonical paths of a placed
nonallocating data give, through caller rejoin or a common canonical trap.
The closed body maintains accepted observations without requiring equal
host journals or discarding writes at a trap. -/
theorem paired_local_data_give {route : GiveEffectRoute} (site : PayloadRoot.Site grow sig route) (linked : site.Linked bindings)
    (data : PayloadPrefix.LocalDataType (sig.payload site.tag)) (payload : Stored.Payload (sig.payload site.tag))
    (field : site.field = .data (sig.payload site.tag) payload) {entryLabels}
    (entryPath : Steps profile ready (specDispatch ready base) site.start entryLabels site.checked)
    (silent : PayloadPrefix.visible entryLabels = [])
    (placed : PayloadPrefix.rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .ok ())
    (prepared : Stored.OwnedMemory.Claims.Record.prepare site.start.store site.start.host.writer site.field.objects = .ok ())
    (paired : HostFrame.Related.Paired older site.start incoming)
    (roots : site.start.host.writer.accepted = incoming.host.writer.accepted) :
    ∃ checkLabels canonLabels checked canonical,
      Steps profile ready (specDispatch ready base) site.start checkLabels checked ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming canonLabels canonical ∧
      HostFrame.Related.Paired older checked canonical ∧ PayloadPrefix.visible checkLabels = PayloadPrefix.visible canonLabels ∧
      checked.host.writer.accepted = canonical.host.writer.accepted :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan.pairedLocalDataGive
    site linked data payload field entryPath silent placed prepared paired roots

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch
