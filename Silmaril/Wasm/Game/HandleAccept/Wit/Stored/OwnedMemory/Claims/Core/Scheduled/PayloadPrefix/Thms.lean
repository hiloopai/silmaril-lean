module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Defs
public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.StringFront
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core
open Stored.Endpoints
open Stored.Endpoints.RecordLower

/-- Prepend replayed segments with equal visible labels. The two segments
may take different numbers of internal steps. -/
theorem LocalSteps.steps {E : CoreEngine} {Host : Type} {profile : ProfileKind} {ready : HostReady Host}
    {dispatch : Call E → P E Host (Ret E)} {before finish labels}
    (run : LocalSteps profile ready dispatch before labels finish) : Steps profile ready dispatch before labels finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.localSteps run

theorem LocalSteps.append {E : CoreEngine} {Host : Type} {profile : ProfileKind} {ready : HostReady Host}
    {dispatch : Call E → P E Host (Ret E)} {before middle finish leading trailing}
    (front : LocalSteps profile ready dispatch before leading middle)
    (back : LocalSteps profile ready dispatch middle trailing finish) :
    LocalSteps profile ready dispatch before (leading ++ trailing) finish :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.localAppend front back

theorem ReachesKeeping.prepend {E : CoreEngine} {Host Result : Type} {profile : ProfileKind}
    {ready : HostReady Host} {dispatch : Call E → P E Host (Ret E)} {keep : CStore E → Prop}
    {left left' right right' : Config E Host} {checkLabels canonLabels : List (Label E Host)}
    {checkCursor canonCursor : Cursor (E := E) Host}
    {checkNext : Except RecordLower.Issue Result → P E Host (Ret E)} {canonNext : Result → P E Host (Ret E)}
    (lhs : Steps profile ready dispatch left checkLabels left') (rhs : Steps profile ready dispatch right canonLabels right')
    (seen : visible checkLabels = visible canonLabels)
    (rest : ReachesKeeping profile ready dispatch keep left' right' checkCursor canonCursor checkNext canonNext) :
    ReachesKeeping profile ready dispatch keep left right checkCursor canonCursor checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.prependKeeping lhs rhs seen rest

theorem ReachesKeeping.weaken {E : CoreEngine} {Host Result : Type} {profile : ProfileKind}
    {ready : HostReady Host} {dispatch : Call E → P E Host (Ret E)} {keep weaker : CStore E → Prop}
    {left right : Config E Host} {checkCursor canonCursor : Cursor (E := E) Host}
    {checkNext : Except RecordLower.Issue Result → P E Host (Ret E)} {canonNext : Result → P E Host (Ret E)}
    (rest : ReachesKeeping profile ready dispatch keep left right checkCursor canonCursor checkNext canonNext)
    (weaken : ∀ store, keep store → weaker store) :
    ReachesKeeping profile ready dispatch weaker left right checkCursor canonCursor checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.weakenKeeping rest weaken

theorem ReachesKeeping.forget {E : CoreEngine} {Host Result : Type} {profile : ProfileKind}
    {ready : HostReady Host} {dispatch : Call E → P E Host (Ret E)} {keep : CStore E → Prop}
    {left right : Config E Host} {checkCursor canonCursor : Cursor (E := E) Host}
    {checkNext : Except RecordLower.Issue Result → P E Host (Ret E)} {canonNext : Result → P E Host (Ret E)}
    (rest : ReachesKeeping profile ready dispatch keep left right checkCursor canonCursor checkNext canonNext) :
    Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.forgetKeeping rest

theorem Reaches.remember_true {E : CoreEngine} {Host Result : Type} {profile : ProfileKind}
    {ready : HostReady Host} {dispatch : Call E → P E Host (Ret E)}
    {left right : Config E Host} {checkCursor canonCursor : Cursor (E := E) Host}
    {checkNext : Except RecordLower.Issue Result → P E Host (Ret E)} {canonNext : Result → P E Host (Ret E)}
    (rest : Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext) :
    ReachesKeeping profile ready dispatch (fun _ => True) left right checkCursor canonCursor checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.rememberTrue rest

/-- Continue a child at the cursors its run actually reaches. The saved
continuations are the real suffix programs; only a common return runs them. -/
theorem ReachesKeeping.bind_reached {E : CoreEngine} {Host Result Next : Type} {profile : ProfileKind}
    {ready : HostReady Host} {dispatch : Call E → P E Host (Ret E)} {keep : CStore E → Prop}
    {left right : Config E Host} {checkCursor canonCursor : Cursor (E := E) Host}
    (thread : checkCursor.thread = canonCursor.thread)
    {checkNext : Except RecordLower.Issue Next → P E Host (Ret E)} {canonNext : Next → P E Host (Ret E)}
    (mapIssue : RecordLower.Issue → RecordLower.Issue)
    (checkTail : Result → P E Host (Except RecordLower.Issue Next)) (canonTail : Result → P E Host Next)
    (first : ReachesKeeping profile ready dispatch keep left right checkCursor canonCursor
      (checkedSequenceNext mapIssue checkTail checkNext) (fun value => canonTail value >>= canonNext))
    (rest : ∀ value entered reference, keep reference.store →
      CompareKeepingAt profile ready dispatch keep entered reference (checkTail value) (canonTail value)) :
    ReachesKeeping profile ready dispatch keep left right checkCursor canonCursor checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.continueKeeping thread mapIssue
    checkTail canonTail first rest

theorem Reaches.prepend {E : CoreEngine} {Host Result : Type} {profile : ProfileKind}
    {ready : HostReady Host} {dispatch : Call E → P E Host (Ret E)}
    {left left' right right' : Config E Host} {checkLabels canonLabels : List (Label E Host)}
    {checkCursor canonCursor : Cursor (E := E) Host}
    {checkNext : Except RecordLower.Issue Result → P E Host (Ret E)} {canonNext : Result → P E Host (Ret E)}
    (lhs : Steps profile ready dispatch left checkLabels left') (rhs : Steps profile ready dispatch right canonLabels right')
    (seen : visible checkLabels = visible canonLabels)
    (rest : Reaches profile ready dispatch left' right' checkCursor canonCursor checkNext canonNext) :
    Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.prepend lhs rhs seen rest

/-- Compose actual paired scheduler prefixes at the reached store. Only a
successful child advances either traversal; refusal and trap retain the
child's prefixes. -/
theorem Compare.bind {E : CoreEngine} {Host Result Next : Type} {profile : ProfileKind}
    {ready : HostReady Host} {dispatch : Call E → P E Host (Ret E)}
    {checked : P E Host (Except RecordLower.Issue Result)} {canonical : P E Host Result}
    (first : Compare profile ready dispatch checked canonical)
    (checkTail : Result → P E Host (Except RecordLower.Issue Next)) (canonTail : Result → P E Host Next)
    (rest : ∀ value, Compare profile ready dispatch (checkTail value) (canonTail value)) :
    Compare profile ready dispatch
      (checked >>= fun result => match result with | .error issue => pure (.error issue) | .ok value => checkTail value)
      (canonical >>= canonTail) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.sequential first checkTail canonTail rest

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}

/-- Compare the actual flat lowering programs recursively for records,
tuples, fixed lists and well-tagged sums made from own, stream, future and
error-context leaves. The writers need not agree: each checked leaf re-reads
its live writer. -/
theorem flat_field (destination : RecordDestination) (inst : InstId) (item : Field)
    (fragment : HandleField item) (index : Nat) :
    Compare profile ready dispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width item index .flat)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item .flat) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.flatField destination inst item fragment index

/-- Prepend words already returned by a preceding field to the actual flat
sequence. Refusals and canonical traps do not return any words. -/
theorem flat_fields_prepend (destination : RecordDestination) (inst : InstId) (items : List Field)
    (fragment : HandleFieldsWhere Nat.lt items) (index : Nat) (words : List FlatValue) :
    Compare profile ready dispatch
      (do return (← Record.Effects.flat recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width items index).map (words ++ ·))
      (do return words ++ (← CanonicalTree.flat Limits.spec Quirks.none (destination.context inst)
        destination.width items)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.flatFieldsPrepend
    destination inst items fragment index words

/-- Coercion of already returned sum words is local and preserves a
reached-store predicate on common success. Its trap or choices remain visible. -/
theorem variant_tail_frame {E : CoreEngine} {Host : Type} {profile : ProfileKind}
    {ready : HostReady Host} {dispatch : Call E → P E Host (Ret E)}
    (count : Nat) (wanted : List CoreType) (tag : Nat) (haves : List CoreType)
    (words : List FlatValue) {keep : CStore E → Prop} (left right : Config E Host) (kept : keep right.store) :
    CompareLocalKeepingAt profile ready dispatch keep left right
      (do return .ok (← lowerFlatVariantWith count wanted tag haves (pure words)))
      (lowerFlatVariantWith count wanted tag haves (pure words)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.variantTailFrame count wanted tag haves words left right kept

/-- Compose a selected arm comparison with the actual flat coercion and
padding program. Coercion runs only on common success, and its canonical
choices and traps stay visible on both sides. -/
theorem flat_sum (destination : RecordDestination) (inst : InstId) (type : TypeOf)
    (arms : List (Option TypeOf)) (tag index : Nat) (selected : Option Field) (valid : tag < arms.length)
    (child : ∀ item, selected = some item → Compare profile ready dispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width item 0 .flat)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item .flat)) :
    Compare profile ready dispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        (.sum type arms tag selected) index .flat)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width
        (.sum type arms tag selected) .flat) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.flatSum
    destination inst type arms tag index selected valid child

/-- The canonical side reads width at this cursor. Both sides write the
actual discriminant, then enter the selected child at the computed address
only if the write returns. A later refusal does not undo the tag write. -/
theorem memory_sum (destination : RecordDestination) (inst : InstId) (type : TypeOf)
    (arms : List (Option TypeOf)) (tag index ptr : Nat) (selected : Option Field)
    (left right : Config (core3 grow) (HostState sig))
    (width : ptrTypeIn right.store (destination.context inst) = destination.width)
    (child : ∀ item address, selected = some item → Compare profile ready dispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width item 0 (.memory address))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item (.memory address))) :
    CompareAt profile ready dispatch left right
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        (.sum type arms tag selected) index (.memory ptr))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width
        (.sum type arms tag selected) (.memory ptr)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.memorySum
    destination inst type arms tag index ptr selected left right width child

/-- Compare the actual memory sum tag writes before entering the selected
child, retaining the reached store and original scheduler tails. -/
theorem memory_sum_tag (destination : RecordDestination) (inst : InstId) (type : TypeOf)
    (arms : List (Option TypeOf)) (tag index base : Nat) (selected : Option Field)
    (origin : CStore (core3 grow)) (left right : Config (core3 grow) (HostState sig))
    (check canon : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    (same : left.store = right.store) (thread : check.thread = canon.thread)
    (width : ptrTypeIn right.store (destination.context inst) = destination.width)
    (growth : Core3.Grows origin.core right.store.core)
    (checkAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.sum type arms tag selected) index (.memory base) >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.sum type arms tag selected) (.memory base) >>= canonNext)) :
    let address := sumPayloadAddress destination.width arms base
    LocalCutKeeping profile ready dispatch (fun store => Core3.Grows origin.core store.core) left right check canon
      (sumCheckedNext destination inst selected index address checkNext)
      (sumCanonicalNext destination inst selected address canonNext) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.memorySumTag
    destination inst type arms tag index base selected origin left right check canon checkNext canonNext same thread width growth checkAt canonAt

/-- The handle leaf in a placed memory entry has no allocator or width-read
prefix of its own. It rechecks live authority at the reached store. -/
theorem memory_handle (destination : RecordDestination) (inst : InstId) (item : Field)
    (index address : Nat) (handle : CanonicalHandle item) :
    Compare profile ready dispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
        destination.width item index (.memory address))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item (.memory address)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.memoryHandleLeaf
    destination inst item index address handle

/-- Both allocation-time memory-map offsets fit a validated entry slot.
The value slot remains valid after certified Core growth while storing
the key, even when a key allocator changed bytes. -/
theorem map_entry_placement (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : TypeOf)
    {origin reached : CStore (core3 grow)} {base count index bytes : Nat}
    (growth : Core3.Grows origin.core reached.core)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : base = alignTo base (layout destination.width (.record (mapEntryFields key element))).alignment)
    (bounds : base + count * (layout destination.width (.record (mapEntryFields key element))).size ≤ bytes)
    (entry : index < count) :
    let keyArea := layout destination.width (.prim key.toPrimitive : TypeOf)
    let valueArea := layout destination.width element
    let address := base + index * (layout destination.width (.record (mapEntryFields key element))).size
    let keyPtr := alignTo address keyArea.alignment
    let valuePtr := alignTo (keyPtr + keyArea.size) valueArea.alignment
    ptrTypeIn reached (destination.context inst) = destination.width ∧
      placement destination reached keyArea keyPtr = .ok () ∧
      placement destination reached valueArea valuePtr = .ok () :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.mapEntryPlacement
    destination inst key element growth width sized aligned bounds entry

/-- Compare every entry in a validated indirect memory map. Both fields of
the pair use the allocation-time width. The key's reached growth certificate
places the value, and a refused or trapped child does not enter the suffix. -/
theorem memory_map_elements (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : TypeOf)
    (origin : CStore (core3 grow)) (base count bytes : Nat)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : base = alignTo base (layout destination.width (.record (mapEntryFields key element))).alignment)
    (bounds : base + count * (layout destination.width (.record (mapEntryFields key element))).size ≤ bytes)
    (entries : List Field) (index : Nat) (room : index + entries.length ≤ count)
    (children : ∀ entry ∈ entries, MapEntryRules profile ready dispatch destination inst key element entry)
    (left right : Config (core3 grow) (HostState sig)) (growth : Core3.Grows origin.core right.store.core) :
    let cx := destination.context inst
    let stride := (layout destination.width (.record (mapEntryFields key element))).size
    CompareKeepingAt profile ready dispatch (fun store => Core3.Grows origin.core store.core) left right
      (Record.Effects.elements recordClaims Limits.spec Quirks.none cx destination.width entries stride (base + index * stride) index)
      (CanonicalTree.elements Limits.spec Quirks.none cx destination.width entries (.memoryMap destination.width key element)
        stride (base + index * stride)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.memoryMapElements
    destination inst key element origin base count bytes width sized aligned bounds entries index room children left right growth

/-- After the actual range and live-plan checks admit a memory map, compare
the whole entry traversal and descriptor writes. No descriptor is written
after a typed child refusal or a trap in an entry. -/
theorem memory_map_tail (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : TypeOf)
    (origin : CStore (core3 grow)) (pointer bytes index outputAddress : Nat)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (entries : List Field)
    (aligned : pointer = alignTo pointer (layout destination.width (.record (mapEntryFields key element))).alignment)
    (bounds : pointer + entries.length * (layout destination.width (.record (mapEntryFields key element))).size ≤ bytes)
    (children : ∀ entry ∈ entries, MapEntryRules profile ready dispatch destination inst key element entry)
    (left right : Config (core3 grow) (HostState sig)) (growth : Core3.Grows origin.core right.store.core) :
    let area := layout destination.width (.record (mapEntryFields key element))
    CompareKeepingAt profile ready dispatch (fun store => Core3.Grows origin.core store.core) left right
      (checkedCollectionTail destination inst entries area index (.memory outputAddress) pointer (.ok ()))
      (canonicalCollectionTail destination inst entries area (.memory outputAddress) pointer (.memoryMap destination.width key element)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.memoryMapTail
    destination inst key element origin pointer bytes index outputAddress width sized entries aligned bounds children left right growth

/-- A slot of a validated allocation stays aligned and in bounds across a
growth-certified prefix. Only the reached size and width are constrained. -/
theorem list_entry_placement {EHost : Type} {entryReady : HostReady EHost}
    {entryDispatch : Call (core3 grow) → P (core3 grow) EHost (Ret (core3 grow))}
    (destination : RecordDestination) (inst : InstId) (element : TypeOf)
    {before after : Config (core3 grow) EHost} {labels} {base count index bytes : Nat}
    (run : CoreGrowthSteps profile entryReady entryDispatch before labels after)
    (checked : destination.check before.store = .ok ())
    (sized : (core3 grow).memSize? before.store.core destination.memory = some bytes)
    (aligned : base = alignTo base (layout destination.width element).alignment)
    (bounds : base + count * (layout destination.width element).size ≤ bytes) (entry : index < count) :
    let area := layout destination.width element
    ptrTypeIn after.store (destination.context inst) = destination.width ∧
      placement destination after.store area (base + index * area.size) = .ok () :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.listEntryPlacement
    destination inst element run checked sized aligned bounds entry

/-- At a width-checked and placed cursor, a non-string primitive takes its
actual width and bounds reads, then shares the canonical scalar program,
including NaN choices and writes. Raw canonical store assumes placement. -/
theorem primitive_leaf (destination : RecordDestination) (inst : InstId) (primitive : WIT.Primitive)
    (payload : Stored.Payload (.prim primitive)) (nonString : primitive ≠ .string) (index : Nat) (output : Lower.Output)
    (left right : Config (core3 grow) (HostState sig))
    (width : ptrTypeIn left.store (destination.context inst) = destination.width)
    (placed : rootPlacement destination left.store (.prim primitive) output = .ok ()) :
    CompareAt profile ready dispatch left right
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        (.data (.prim primitive) payload) index output)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width
        (.data (.prim primitive) payload) output) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.primitiveLeaf
    destination inst primitive payload nonString index output left right width placed

/-- Keep the exact reached scheduler tails across the local primitive
program, including the same observable scalar choices on both sides. -/
theorem primitive_leaf_frame (destination : RecordDestination) (inst : InstId) (primitive : WIT.Primitive)
    (payload : Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Payload (.prim primitive))
    (nonString : primitive ≠ .string) (index : Nat) (output : Lower.Output) (origin : CStore (core3 grow))
    (left right : Config (core3 grow) (HostState sig)) (growth : Core3.Grows origin.core right.store.core)
    (width : ptrTypeIn left.store (destination.context inst) = destination.width)
    (placed : rootPlacement destination left.store (.prim primitive) output = .ok ()) :
    CompareLocalKeepingAt profile ready dispatch (fun store => Core3.Grows origin.core store.core) left right
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        (.data (.prim primitive) payload) index output)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width
        (.data (.prim primitive) payload) output) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.primitiveLeafFrame
    destination inst primitive payload nonString index output origin left right growth width placed

/-- A compiled local data leaf executes its actual canonical program after
the reached width and placement checks. Enum discriminants and packed flags
are ordinary local effects; no callback or host mutation is required. -/
theorem local_data_leaf_frame (destination : RecordDestination) (inst : InstId) (type : TypeOf)
    (data : LocalDataType type) (payload : Stored.Payload type) (index : Nat) (output : Lower.Output)
    (origin : CStore (core3 grow)) (left right : Config (core3 grow) (HostState sig))
    (growth : Core3.Grows origin.core right.store.core)
    (width : ptrTypeIn left.store (destination.context inst) = destination.width)
    (placed : rootPlacement destination left.store type output = .ok ()) :
    CompareLocalKeepingAt profile ready dispatch (fun store => Core3.Grows origin.core store.core) left right
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        (.data type payload) index output)
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width
        (.data type payload) output) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.localDataLeafFrame
    destination inst type data payload index output origin left right growth width placed

/-- Both actual string leaf programs reach the same canonical plan. The
checked path first discharges schema/options, the fit test at the reached
width, and (for memory) root placement. This cut precedes plan execution. -/
theorem string_plan_entry {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
    {ready : HostReady (HostState sig)} {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (destination : RecordDestination) (inst : InstId) (str : Value.StrVal) (valid : str.Valid)
    (index : Nat) (output : Lower.Output) (left right : Config (core3 grow) (HostState sig))
    (checkCursor canonCursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (same : left.store = right.store)
    (present : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width)
    {addr : Nat} (realloc : destination.realloc = some addr)
    (fit : StoreStringPre Quirks.none destination.encoding destination.width str)
    (placed : rootPlacement destination left.store (.prim .string) output = .ok ())
    (checkAt : left.ctl = checkCursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.data (.prim .string) ⟨.string str, .string valid⟩) index output >>= checkNext))
    (canonAt : right.ctl = canonCursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.data (.prim .string) ⟨.string str, .string valid⟩) output >>= canonNext)) :
    let cx := destination.context inst
    let plan := storePlanFor Quirks.none destination.encoding destination.width str
    let body := runStoreSteps cx 0 plan.steps
    ∃ reads, ReturnFrame.Occurrence.RetainsActiveSlots profile ready dispatch left (List.replicate reads .tau)
      { left with ctl := checkCursor.control (body >>= fun ptr => stringPlanTail cx destination.width output plan ptr >>=
          fun value => checkNext (.ok value)) } ∧
      ReturnFrame.Occurrence.RetainsActiveSlots profile ready dispatch right [.tau]
        { right with ctl := canonCursor.control (body >>= fun ptr => stringPlanTail cx destination.width output plan ptr >>= canonNext) } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.stringPlanEntry
    destination inst str valid index output left right checkCursor canonCursor checkNext canonNext same present realloc fit placed checkAt canonAt

/-- At a reached allocating string action, the actual call saves the remaining plan. -/
theorem string_realloc_focus {E : CoreEngine} {Host : Type} (cx : LiftLowerContext E)
    (ptr : Nat) (oldSize : Option Nat) (alignment : Alignment) (size : Nat) (steps : List StoreStep)
    (finish : Nat → P E Host (Ret E)) :
    let request := Call.reallocate cx (oldSize.elim 0 (fun _ => ptr)) (oldSize.getD 0) alignment.bytes size
    (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= finish) =
        .op (.call request) (stringPlanResume cx steps finish) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.stringReallocFocus
    cx ptr oldSize alignment size steps finish

/-- Take the actual scheduler call step for the next string allocation or
resize, saving the remaining plan. This does not assert the callback returns. -/
theorem string_realloc_install {E : CoreEngine} {Host : Type} {profile : ProfileKind} {ready : HostReady Host}
    {dispatch : Call E → P E Host (Ret E)} (cx : LiftLowerContext E) (ptr : Nat) (oldSize : Option Nat)
    (alignment : Alignment) (size : Nat) (steps : List StoreStep) (finish : Nat → P E Host (Ret E))
    (start : Config E Host) (cursor : Cursor (E := E) Host)
    (focused : start.ctl = cursor.control (runStoreSteps cx ptr
      ((oldSize.elim (.allocate alignment size) (fun old => .reallocate old alignment size)) :: steps) >>= finish)) :
    let request := Call.reallocate cx (oldSize.elim 0 (fun _ => ptr)) (oldSize.getD 0) alignment.bytes size
    let resumed := stringPlanResume cx steps finish
    Step profile ready dispatch start .tau
      { start with ctl := { cursor with frames := .prog resumed :: cursor.frames }.control (dispatch request) } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.stringReallocInstall
    cx ptr oldSize alignment size steps finish start cursor focused

/-- Compare any allocator-free segment of the actual string plan at its
reached store. Reads (including transcoding reads) see the current bytes,
and a trap preserves the earlier writes on both paths. -/
theorem local_string_steps {E : CoreEngine} {Host : Type} {profile : ProfileKind} {ready : HostReady Host}
    {dispatch : Call E → P E Host (Ret E)} (cx : LiftLowerContext E) (ptr : Nat) (steps : List StoreStep)
    (localSteps : ∀ action ∈ steps, LocalStringStep action) :
    Compare profile ready dispatch (do return .ok (← runStoreSteps cx ptr steps)) (runStoreSteps cx ptr steps) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.localStringSteps cx ptr steps localSteps

/-- The front and remaining program together are exactly the canonical plan. -/
theorem string_front_factor {E : CoreEngine} {Host : Type} (cx : LiftLowerContext E) (ptr : Nat) (steps : List StoreStep) :
    ((stringFront cx ptr steps : P E Host (StringFront steps.length)) >>= StringFront.remaining cx) = runStoreSteps cx ptr steps :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.StringFront.factor cx ptr steps

/-- Compare the local instructions of the actual plan at both reached stores,
stopping before the next allocation/resize or after a canonical trap. -/
theorem string_front_cut {grow : SingleThreaded.GrowOracle} {Host : Type} {profile : ProfileKind} {ready : HostReady Host}
    {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
    (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (steps : List StoreStep)
    (left right : Config (core3 grow) Host) (check canon : Cursor (E := core3 grow) Host)
    (checkNext canonNext : Nat → P (core3 grow) Host (Ret (core3 grow))) (same : left.store = right.store)
    (checkAt : left.ctl = check.control (runStoreSteps cx ptr steps >>= checkNext))
    (canonAt : right.ctl = canon.control (runStoreSteps cx ptr steps >>= canonNext)) :
    StringLocalCut profile ready dispatch left right check canon
      (fun front : StringFront steps.length => front.remaining cx >>= checkNext)
      (fun front : StringFront steps.length => front.remaining cx >>= canonNext) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.StringFront.cut
    cx ptr steps left right check canon checkNext canonNext same checkAt canonAt

/-- Local string instructions do not invoke either dispatcher. -/
theorem string_front_cut_between {grow : SingleThreaded.GrowOracle} {Host : Type} {profile : ProfileKind}
    {ready : HostReady Host} {dispatch reference : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
    (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (steps : List StoreStep)
    (left right : Config (core3 grow) Host) (check canon : Cursor (E := core3 grow) Host)
    (checkNext canonNext : Nat → P (core3 grow) Host (Ret (core3 grow))) (same : left.store = right.store)
    (checkAt : left.ctl = check.control (runStoreSteps cx ptr steps >>= checkNext))
    (canonAt : right.ctl = canon.control (runStoreSteps cx ptr steps >>= canonNext)) :
    StringLocalCutBetween profile ready dispatch reference left right check canon
      (fun front : StringFront steps.length => front.remaining cx >>= checkNext)
      (fun front : StringFront steps.length => front.remaining cx >>= canonNext) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.StringFront.cut
    cx ptr steps left right check canon checkNext canonNext same checkAt canonAt

/-- Complete a string at its reached pointer. Memory output reads pointer
size at this point and retains the first word if writing the second traps. -/
theorem string_descriptor_cut {grow : SingleThreaded.GrowOracle} {Host : Type} {profile : ProfileKind} {ready : HostReady Host}
    {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
    (cx : LiftLowerContext (core3 grow)) (width : AddrType) (output : Lower.Output) (plan : StorePlan) (ptr : Nat)
    (left right : Config (core3 grow) Host) (check canon : Cursor (E := core3 grow) Host)
    (checkNext canonNext : output.Result → P (core3 grow) Host (Ret (core3 grow))) (same : left.store = right.store)
    (checkAt : left.ctl = check.control (stringPlanTail cx width output plan ptr >>= checkNext))
    (canonAt : right.ctl = canon.control (stringPlanTail cx width output plan ptr >>= canonNext)) :
    StringLocalCut profile ready dispatch left right check canon checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.StringFront.descriptor
    cx width output plan ptr left right check canon checkNext canonNext same checkAt canonAt

/-- Encoding the reached pointer and count does not invoke either dispatcher. -/
theorem string_descriptor_cut_between {grow : SingleThreaded.GrowOracle} {Host : Type} {profile : ProfileKind}
    {ready : HostReady Host} {dispatch reference : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
    (cx : LiftLowerContext (core3 grow)) (width : AddrType) (output : Lower.Output) (plan : StorePlan) (ptr : Nat)
    (left right : Config (core3 grow) Host) (check canon : Cursor (E := core3 grow) Host)
    (checkNext canonNext : output.Result → P (core3 grow) Host (Ret (core3 grow))) (same : left.store = right.store)
    (checkAt : left.ctl = check.control (stringPlanTail cx width output plan ptr >>= checkNext))
    (canonAt : right.ctl = canon.control (stringPlanTail cx width output plan ptr >>= canonNext)) :
    StringLocalCutBetween profile ready dispatch reference left right check canon checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.StringFront.descriptor
    cx width output plan ptr left right check canon checkNext canonNext same checkAt canonAt

/-- A reached canonical write either commits or traps locally, without
using either dispatcher. Its memory and bounds checks read the live store. -/
theorem write_cut_between {grow : SingleThreaded.GrowOracle} {Host : Type} {profile : ProfileKind}
    {ready : HostReady Host} {dispatch reference : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
    (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (data : ByteArray)
    (left right : Config (core3 grow) Host) (check canon : Cursor (E := core3 grow) Host)
    (checkNext canonNext : Unit → P (core3 grow) Host (Ret (core3 grow))) (same : left.store = right.store)
    (checkAt : left.ctl = check.control (writeMem cx ptr data >>= checkNext))
    (canonAt : right.ctl = canon.control (writeMem cx ptr data >>= canonNext)) :
    StringLocalCutBetween profile ready dispatch reference left right check canon checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.StringFront.write
    cx ptr data left right check canon checkNext canonNext same checkAt canonAt

/-- Replay the actual pointer/count descriptor from the reached store, without
consulting either dispatcher. A late trap keeps the first write, if it ran. -/
theorem collection_descriptor_cut_between {grow : SingleThreaded.GrowOracle} {Host : Type} {profile : ProfileKind} {ready : HostReady Host}
    {dispatch reference : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
    (cx : LiftLowerContext (core3 grow)) (width : AddrType) (output : Lower.Output) (ptr count : Nat)
    (left right : Config (core3 grow) Host) (check canon : Cursor (E := core3 grow) Host)
    (checkNext canonNext : output.Result → P (core3 grow) Host (Ret (core3 grow))) (same : left.store = right.store)
    (checkAt : left.ctl = check.control (ListLower.publish cx width ptr count output >>= checkNext))
    (canonAt : right.ctl = canon.control (ListLower.publish cx width ptr count output >>= canonNext)) :
    StringLocalCutBetween profile ready dispatch reference left right check canon checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.StringFront.collectionDescriptor
    cx width output ptr count left right check canon checkNext canonNext same checkAt canonAt

abbrev collection_descriptor_cut {grow : SingleThreaded.GrowOracle} {Host : Type} {profile : ProfileKind} {ready : HostReady Host}
    {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))} :=
  @collection_descriptor_cut_between grow Host profile ready dispatch dispatch

theorem local_data_objects {element : TypeOf} {entries : List Field} (data : LocalDataType element)
    (matched : Field.EntriesMatch entries element) : Field.listObjects entries = [] :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.localDataObjects data matched

/-- Traverse the actual checked and canonical list elements, deriving each
child's program and placement from the validated interval and compiled layout.
Only a successful traversal executes the pointer/count descriptor. -/
theorem local_data_collection_tail
    {reference : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (destination : RecordDestination) (inst : InstId) (element : TypeOf) (data : LocalDataType element)
    (entries : List Field) (matched : Field.EntriesMatch entries element)
    (pointer bytes index : Nat) (output : Lower.Output) (left right : Config (core3 grow) (HostState sig))
    (width : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (aligned : pointer = alignTo pointer (layout destination.width element).alignment)
    (bounds : pointer + entries.length * (layout destination.width element).size ≤ bytes)
    (same : left.store = right.store) (check canon : Cursor (E := core3 grow) (HostState sig)) (thread : check.thread = canon.thread)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (checkAt : left.ctl = check.control (checkedCollectionTail destination inst entries (layout destination.width element)
      index output pointer (.ok ()) >>= checkNext))
    (canonAt : right.ctl = canon.control (canonicalCollectionTail destination inst entries (layout destination.width element)
      output pointer .value >>= canonNext)) :
    LocalCutKeepingBetween profile ready dispatch reference (fun store => Core3.Grows left.store.core store.core)
      left right check canon (fun value => checkNext (.ok value)) canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.localDataCollectionTail destination inst element data
    entries matched pointer bytes index output left right width sized aligned bounds same check canon thread checkNext canonNext checkAt canonAt

/-- Validate the checked record slot and execute the actual scalar map key
under either dispatcher, stopping at the value's effect program. The value
may allocate or use nominal claims; the key proof neither runs it nor
requires a comparison hypothesis about it. -/
theorem local_map_key_then_between {reference : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : TypeOf)
    (keyData : LocalDataType (.prim key.toPrimitive)) (keyPayload : Stored.Payload (.prim key.toPrimitive)) (valField : Field)
    (origin : CStore (core3 grow)) (base bytes count index : Nat)
    (width : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : base = alignTo base (layout destination.width (.record (mapEntryFields key element))).alignment)
    (bounds : base + count * (layout destination.width (.record (mapEntryFields key element))).size ≤ bytes)
    (entry : index < count) (issueIndex : Nat) (left right : Config (core3 grow) (HostState sig))
    (growth : Core3.Grows origin.core right.store.core) (same : left.store = right.store)
    (check canon : Cursor (E := core3 grow) (HostState sig)) (thread : check.thread = canon.thread)
    (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (refFollowing : Unit → Session grow sig (Ret (core3 grow))) :
    let cx := destination.context inst
    let type : TypeOf := .record (mapEntryFields key element)
    let addr := base + index * (layout destination.width type).size
    let keyArea := layout destination.width (.prim key.toPrimitive : TypeOf)
    let keyPtr := alignTo addr keyArea.alignment
    let valPtr := alignTo (keyPtr + keyArea.size) (layout destination.width valField.type).alignment
    let keyField := Field.data (.prim key.toPrimitive) keyPayload
    left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width
      (.aggregate type [keyField, valField]) issueIndex (.memory addr) >>= checkNext) →
    right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none cx destination.width keyField (.memory keyPtr) >>= refFollowing) →
    LocalCutKeepingBetween profile ready dispatch reference
      (fun store => Core3.Grows origin.core store.core) left right check canon
      (fun (_ : Unit) => Record.Effects.field recordClaims Limits.spec Quirks.none cx destination.width valField 1 (.memory valPtr) >>=
        fun result => checkNext (result.mapError (.nested issueIndex)))
      refFollowing :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.localMapKeyThen
    destination inst key element keyData keyPayload valField origin base bytes count index width sized aligned bounds entry
    issueIndex left right growth same check canon thread checkNext refFollowing

theorem local_data_map_objects {key : WIT.KeyType} {element : TypeOf} {entries : List Field}
    (data : LocalDataType element)
    (matched : Field.EntriesMatch entries (.record (mapEntryFields key element)))
    (emitted : Field.Emitted (.dynamic (.map key element) (.record (mapEntryFields key element)) entries)) :
    Field.listObjects entries = [] :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.localMapObjects data matched emitted

/-- Reached memory-map entries use allocation-time key and value offsets.
Follow every compiled data entry, then execute the real descriptor writes. -/
theorem local_map_collection_tail {reference : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (destination : RecordDestination) (inst : InstId) (key : WIT.KeyType) (element : TypeOf)
    (keyData : LocalDataType (.prim key.toPrimitive)) (valueData : LocalDataType element)
    (entries : List Field)
    (matched : Field.EntriesMatch entries (.record (mapEntryFields key element)))
    (emitted : Field.Emitted (.dynamic (.map key element) (.record (mapEntryFields key element)) entries))
    (pointer bytes index outputAddress : Nat) (left right : Config (core3 grow) (HostState sig))
    (width : (core3 grow).memAddrType? left.store.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (aligned : pointer = alignTo pointer (layout destination.width (.record (mapEntryFields key element))).alignment)
    (bounds : pointer + entries.length * (layout destination.width (.record (mapEntryFields key element))).size ≤ bytes)
    (same : left.store = right.store) (check canon : Cursor (E := core3 grow) (HostState sig)) (thread : check.thread = canon.thread)
    (checkNext : Except RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Unit → Session grow sig (Ret (core3 grow))) :
    let area := layout destination.width (.record (mapEntryFields key element))
    let mode := CanonicalTree.EntryMode.memoryMap destination.width key element
    left.ctl = check.control (checkedCollectionTail destination inst entries area index (.memory outputAddress) pointer (.ok ()) >>= checkNext) →
    right.ctl = canon.control (canonicalCollectionTail destination inst entries area (.memory outputAddress) pointer mode >>= canonNext) →
    LocalCutKeepingBetween profile ready dispatch reference (fun store => Core3.Grows left.store.core store.core)
      left right check canon (fun value => checkNext (.ok value)) canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.localMapCollectionTail
    destination inst key element keyData valueData entries matched emitted pointer bytes index outputAddress left right
    width sized aligned bounds same check canon thread checkNext canonNext

/-- Use the validated collection range, rather than a fresh placement
assumption for the scalar at its reached list index. -/
theorem primitive_list_entry (destination : RecordDestination) (inst : InstId) (primitive : WIT.Primitive)
    (payload : Stored.Payload (.prim primitive)) (nonString : primitive ≠ .string) (position : Nat)
    {before after : Config (core3 grow) (HostState sig)} {labels} {base count index bytes : Nat}
    (reference : Config (core3 grow) (HostState sig)) (run : CoreGrowthSteps profile ready dispatch before labels after)
    (checked : destination.check before.store = .ok ())
    (sized : (core3 grow).memSize? before.store.core destination.memory = some bytes)
    (aligned : base = alignTo base (layout destination.width (.prim primitive : TypeOf)).alignment)
    (bounds : base + count * (layout destination.width (.prim primitive : TypeOf)).size ≤ bytes) (entry : index < count) :
    let ptr := base + index * (layout destination.width (.prim primitive : TypeOf)).size
    CompareAt profile ready dispatch after reference
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        (.data (.prim primitive) payload) position (.memory ptr))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width
        (.data (.prim primitive) payload) (.memory ptr)) :=
  let placed := list_entry_placement destination inst (.prim primitive) run checked sized aligned bounds entry
  primitive_leaf destination inst primitive payload nonString position (.memory _) after reference placed.1 placed.2

/-- Derive each entry from the validated region and pass its reached store to
its child rule. Only successful children advance to the next entry and the
descriptor write. The enclosing issue index is distinct from the entry index. -/
theorem CollectionTailAt.memory_entries (destination : RecordDestination) (inst : InstId) (element : TypeOf)
    (entries : List Field) (child : ∀ item ∈ entries, MemoryChildRule profile ready dispatch destination inst item element)
    (output : Lower.Output) (index pointer bytes : Nat) (left right : Config (core3 grow) (HostState sig))
    (width : ptrTypeIn left.store (destination.context inst) = destination.width)
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes) :
    CollectionTailAt profile ready dispatch destination inst entries (layout destination.width element)
      output index pointer bytes left right :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.memoryCollectionTail
    destination inst element entries child output index pointer bytes left right width sized

/-- The same reached traversal carries its growth certificate through the
actual descriptor program on success. -/
theorem CollectionTailKeepingAt.memory_entries (destination : RecordDestination) (inst : InstId) (element : TypeOf)
    (entries : List Field) (child : ∀ item ∈ entries, MemoryChildRule profile ready dispatch destination inst item element)
    (output : Lower.Output) (index pointer bytes : Nat) (left right : Config (core3 grow) (HostState sig))
    (width : ptrTypeIn left.store (destination.context inst) = destination.width)
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes) :
    CollectionTailKeepingAt profile ready dispatch (fun store => Core3.Grows left.store.core store.core)
      destination inst entries (layout destination.width element) output index pointer bytes left right :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.memoryCollectionTailKeeping
    destination inst element entries child output index pointer bytes left right width sized

theorem entries_match_of_mem {entries : List Field} {element : TypeOf} {item : Field}
    (matched : Field.EntriesMatch entries element) (member : item ∈ entries) : item.LayoutMatches element :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.entriesMatchOfMem matched member

/-- Compose reached child comparisons inside an actual checked memory
record or tuple, using its compiled layout certificate and validating its
aggregate range. -/
theorem MemoryChildRule.aggregate (destination : RecordDestination) (inst : InstId) (type : TypeOf) (fields : List Field)
    (matched : Field.LayoutMatches (.aggregate type fields) type)
    (child : ∀ item ∈ fields, MemoryChildRule profile ready dispatch destination inst item item.type) :
    MemoryChildRule profile ready dispatch destination inst (.aggregate type fields) type :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.aggregateChildRule
    destination inst type fields matched child

theorem compiled_aggregate_layout (width : AddrType) {type : TypeOf} {fields : List Field}
    (matched : Field.LayoutMatches (.aggregate type fields) type) :
    layout width type = recordLayout (fields.map fun item => layout width item.type) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.aggregateLayout width matched

/-- Discharge the child rule for recursively nested local records and
tuples from the compiler's layout certificate. -/
theorem MemoryChildRule.local_memory (destination : RecordDestination) (inst : InstId) {item : Field} {type : TypeOf}
    (fragment : LocalMemory item) (matched : item.LayoutMatches type) : MemoryChildRule profile ready dispatch destination inst item type :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.localMemoryChild destination inst fragment matched

theorem memory_fields_at (destination : RecordDestination) (inst : InstId)
    {keep : CStore (core3 grow) → Prop} (fields : List Field) (cursor index : Nat)
    (width : ∀ store, keep store → ptrTypeIn store (destination.context inst) = destination.width)
    (child : ∀ slot item address, fields[slot]? = some item →
      (fieldOffsets cursor (fields.map fun field => layout destination.width field.type))[slot]? = some address →
      ∀ left right : Config (core3 grow) (HostState sig), keep right.store →
        CompareKeepingAt profile ready dispatch keep left right
          (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
            item (index + slot) (.memory address))
          (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item (.memory address)))
    (left right : Config (core3 grow) (HostState sig)) (kept : keep right.store) :
    CompareKeepingAt profile ready dispatch keep left right
      (Record.Effects.memory recordClaims Limits.spec Quirks.none (destination.context inst) destination.width fields cursor index)
      (CanonicalTree.memory Limits.spec Quirks.none (destination.context inst) destination.width fields cursor) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.memoryFieldsKeeping
    destination inst fields cursor index width child left right kept

/-- Traverse a validated non-string scalar list in order, deriving placement
at each reached cursor. Neither the scalar writes nor the final descriptor
write invalidate the region; a trapping prefix does not run the suffix. -/
theorem CollectionTailAt.scalar_entries (destination : RecordDestination) (inst : InstId) (primitive : WIT.Primitive)
    (nonString : primitive ≠ .string) (entries : List Field) (layoutMatch : Field.EntriesMatch entries (.prim primitive))
    (output : Lower.Output) (index pointer bytes : Nat) (left right : Config (core3 grow) (HostState sig))
    (width : ptrTypeIn left.store (destination.context inst) = destination.width)
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes) :
    CollectionTailAt profile ready dispatch destination inst entries (layout destination.width (.prim primitive : TypeOf))
      output index pointer bytes left right :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.scalarCollectionTail
    destination inst primitive nonString entries layoutMatch output index pointer bytes left right width sized

/-- Compare the actual memory-record/tuple cursor across a validated region
with handle and non-string scalar fields. A successful field retains Core
growth for the next width read and placement. Refusals and traps stop before
the remaining fields, retaining earlier writes and committed transfers. -/
theorem closed_memory_fields (destination : RecordDestination) (inst : InstId) (origin : CStore (core3 grow))
    (fields : List Field) (base index bytes : Nat)
    (memoryWidth : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : (recordAlignment (fields.map fun item => layout destination.width item.type)).bytes ∣ base)
    (bounds : base + (recordLayout (fields.map fun item => layout destination.width item.type)).size ≤ bytes)
    (closed : ∀ item ∈ fields, ClosedMemoryLeaf item)
    (left right : Config (core3 grow) (HostState sig)) (growth : Core3.Grows origin.core right.store.core) :
    CompareKeepingAt profile ready dispatch (fun store => Core3.Grows origin.core store.core) left right
      (Record.Effects.memory recordClaims Limits.spec Quirks.none (destination.context inst) destination.width fields base index)
      (CanonicalTree.memory Limits.spec Quirks.none (destination.context inst) destination.width fields base) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.closedMemoryFields
    destination inst origin fields base index bytes memoryWidth sized aligned bounds closed left right growth

/-- Enter an actual checked memory aggregate through its bounds read, compare
its canonical field sequence, and preserve its enclosing issue index on a
typed refusal. The compiler's layout certificate identifies the field region. -/
theorem closed_memory_aggregate (destination : RecordDestination) (inst : InstId) (origin : CStore (core3 grow))
    (type : TypeOf) (fields : List Field) (index address bytes : Nat)
    (matched : Field.LayoutMatches (.aggregate type fields) type)
    (memoryWidth : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    (aligned : address % (layout destination.width type).alignment.bytes = 0)
    (bounds : address + (layout destination.width type).size ≤ bytes)
    (closed : ∀ item ∈ fields, ClosedMemoryLeaf item)
    (left right : Config (core3 grow) (HostState sig)) (growth : Core3.Grows origin.core right.store.core) :
    CompareKeepingAt profile ready dispatch (fun store => Core3.Grows origin.core store.core) left right
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        (.aggregate type fields) index (.memory address))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width (.aggregate type fields)
        (.memory address)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.closedMemoryAggregate
    destination inst origin type fields index address bytes matched memoryWidth sized aligned bounds closed left right growth

/-- A failed nested initial dry run stops before installing realloc. Only the
checked diagnostic continuation is reached; the canonical prefix is empty. -/
theorem dynamic_refused_before_allocation (destination : RecordDestination) (inst : InstId) (type element : TypeOf)
    (entries : List Field) (output : Lower.Output) (index : Nat)
    (left right : Config (core3 grow) (HostState sig)) (cursor canonCursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (same : left.store = right.store) (issue : RecordLower.Issue)
    (refused : Record.prepare left.store left.host.writer (Field.listObjects entries) = .error issue)
    (checkAt : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    {keep : CStore (core3 grow) → Prop} :
    ReachesKeeping profile ready dispatch keep left right cursor canonCursor checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.dynamicRefusal
    destination inst type element entries output index left right cursor canonCursor checkNext canonNext same issue refused checkAt

/-- After the initial dry run admits this collection, the actual recursive
programs install the same allocator request at the reached memory width.
The saved checked continuation
validates range first and then re-reads the live plan. `mode` excludes the
memory-map case, whose entry offsets use allocation-time placement. -/
theorem collection_install (destination : RecordDestination) (inst : InstId) (type element : TypeOf)
    (entries : List Field) (output : Lower.Output) (index : Nat)
    (left right : Config (core3 grow) (HostState sig)) (cursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (reachedWidth : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width)
    (mode : CanonicalTree.EntryMode.forOutput destination.width type output = .value)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = cursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let area := layout destination.width element
    let checkResume := checkedCollectionResume destination inst entries area index output checkNext
    let canonResume := canonicalCollectionResume destination inst entries area output canonNext
    let checkCall := collectionEntry destination inst area entries.length dispatch left cursor checkResume
    let canonCall := collectionEntry destination inst area entries.length dispatch right cursor canonResume
    Machine.Steps profile ready dispatch left [.tau, .tau, .tau] checkCall ∧
    Machine.Steps profile ready dispatch right [.tau, .tau] canonCall ∧
    HostFrame.Paired checkResume canonResume checkCall canonCall :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.collectionInstall
    destination inst type element entries output index left right cursor checkNext canonNext same reachedWidth
    mode prepared checkAt canonAt

/-- Both install prefixes stop at the actual allocator with their own
reached cursors. A successful checked pre-read does not discharge the
different live-plan check in the saved continuation. -/
theorem collection_install_tracks (destination : RecordDestination) (inst : InstId) (type element : TypeOf)
    (entries : List Field) (output : Lower.Output) (index : Nat)
    (left right : Config (core3 grow) (HostState sig)) (check canon : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (reachedWidth : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let area := layout destination.width element
    let checkResume := checkedCollectionResume destination inst entries area index output checkNext
    let canonResume := canonicalCollectionResume destination inst entries area output canonNext
      (CanonicalTree.EntryMode.forOutput destination.width type output)
    let checkCall := collectionEntry destination inst area entries.length dispatch left check checkResume
    let canonCall := collectionEntry destination inst area entries.length dispatch right canon canonResume
    ∀ depth, ReturnFrame.Occurrence.Prefix profile ready dispatch left (.active 0 depth)
      [.tau, .tau, .tau] checkCall (.active 0 (depth + 1)) ∧
    ReturnFrame.Occurrence.Prefix profile ready dispatch right (.active 0 depth)
      [.tau, .tau] canonCall (.active 0 (depth + 1)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.collectionInstallTracks
    destination inst type element entries output index left right check canon checkNext canonNext
    reachedWidth prepared checkAt canonAt

theorem collection_install_steps (destination : RecordDestination) (inst : InstId) (type element : TypeOf)
    (entries : List Field) (output : Lower.Output) (index : Nat)
    (left right : Config (core3 grow) (HostState sig)) (check canon : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (reachedWidth : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = check.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = canon.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let area := layout destination.width element
    let checkResume := checkedCollectionResume destination inst entries area index output checkNext
    let canonResume := canonicalCollectionResume destination inst entries area output canonNext
      (CanonicalTree.EntryMode.forOutput destination.width type output)
    let checkCall := collectionEntry destination inst area entries.length dispatch left check checkResume
    let canonCall := collectionEntry destination inst area entries.length dispatch right canon canonResume
    Machine.Steps profile ready dispatch left [.tau, .tau, .tau] checkCall ∧
    Machine.Steps profile ready dispatch right [.tau, .tau] canonCall := by
  obtain ⟨checked, canonical⟩ := collection_install_tracks (profile := profile) (ready := ready) (dispatch := dispatch)
    destination inst type element entries output index left right check canon checkNext canonNext
    reachedWidth prepared checkAt canonAt 0
  exact ⟨(ReturnFrame.Occurrence.prefix_survives checked).1, (ReturnFrame.Occurrence.prefix_survives canonical).1⟩

/-- Install both actual allocator frames, including the allocation-time map
entry layout for indirect output. This does not compare the entry traversals. -/
theorem collection_install_mode (destination : RecordDestination) (inst : InstId) (type element : TypeOf)
    (entries : List Field) (output : Lower.Output) (index : Nat)
    (left right : Config (core3 grow) (HostState sig)) (cursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (same : { left with ctl := right.ctl, host := right.host } = right)
    (reachedWidth : (core3 grow).memAddrType? right.store.core destination.memory = some destination.width)
    (prepared : Record.prepare left.store left.host.writer (Field.listObjects entries) = .ok ())
    (checkAt : left.ctl = cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) index output >>= checkNext))
    (canonAt : right.ctl = cursor.control (CanonicalTree.field Limits.spec Quirks.none
      (destination.context inst) destination.width (.dynamic type element entries) output >>= canonNext)) :
    let area := layout destination.width element
    let checkResume := checkedCollectionResume destination inst entries area index output checkNext
    let canonResume := canonicalCollectionResume destination inst entries area output canonNext
      (CanonicalTree.EntryMode.forOutput destination.width type output)
    let checkCall := collectionEntry destination inst area entries.length dispatch left cursor checkResume
    let canonCall := collectionEntry destination inst area entries.length dispatch right cursor canonResume
    Machine.Steps profile ready dispatch left [.tau, .tau, .tau] checkCall ∧
    Machine.Steps profile ready dispatch right [.tau, .tau] canonCall ∧
    HostFrame.Paired checkResume canonResume checkCall canonCall :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.collectionInstallMode
    destination inst type element entries output index left right cursor checkNext canonNext same reachedWidth
    prepared checkAt canonAt

/-- From an actual paired return, use the reached memory and live writer.
Invalid ranges trap on both sides. A typed live refusal leaves the reference
before the element traversal. Otherwise compose the reached child rules and
the real descriptor, including a possible trap after its pointer write. -/
theorem collection_return (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index pointer : Nat)
    (left right : Config (core3 grow) (HostState sig)) (checkCursor canonCursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (checkResume canonResume : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (paired : HostFrame.Paired checkResume canonResume left right) (sameThread : checkCursor.thread = canonCursor.thread)
    (leftAt : left.ctl = { checkCursor with frames := .prog checkResume :: checkCursor.frames }.control (pure (.nat pointer)))
    (rightAt : right.ctl = { canonCursor with frames := .prog canonResume :: canonCursor.frames }.control (pure (.nat pointer)))
    (checkBody : checkResume (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      let live ← Record.Effects.reserve recordClaims (Field.listObjects entries)
      checkedCollectionTail destination inst entries area index output ptr live >>= checkNext))
    (canonBody : canonResume (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      canonicalCollectionTail destination inst entries area output ptr >>= canonNext))
    {bytes : Nat} (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (compared : ∀ item ∈ entries, ∀ address pos, Compare profile ready dispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        item pos (.memory address))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item (.memory address))) :
    Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.collectionReturnAt
    destination inst entries area output index pointer left right checkCursor canonCursor checkNext canonNext
    checkResume canonResume paired sameThread leftAt rightAt checkBody canonBody sized
    (Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.collectionTailFromChildren
      destination inst entries area output index pointer bytes left right compared)

/-- Rejoin the saved continuations with a tail rule using the actual reached
range and successful live recheck. Neither a range trap nor a live refusal
requires a comparison of the unvisited children. -/
theorem collection_return_at (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index pointer : Nat)
    (left right : Config (core3 grow) (HostState sig)) (checkCursor canonCursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (checkResume canonResume : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (paired : HostFrame.Paired checkResume canonResume left right) (sameThread : checkCursor.thread = canonCursor.thread)
    (leftAt : left.ctl = { checkCursor with frames := .prog checkResume :: checkCursor.frames }.control (pure (.nat pointer)))
    (rightAt : right.ctl = { canonCursor with frames := .prog canonResume :: canonCursor.frames }.control (pure (.nat pointer)))
    (checkBody : checkResume (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      let live ← Record.Effects.reserve recordClaims (Field.listObjects entries)
      checkedCollectionTail destination inst entries area index output ptr live >>= checkNext))
    (canonBody : canonResume (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      canonicalCollectionTail destination inst entries area output ptr >>= canonNext))
    {bytes : Nat} (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (compared : CollectionTailAt profile ready dispatch destination inst entries area output index pointer bytes left right) :
    Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.collectionReturnAt
    destination inst entries area output index pointer left right checkCursor canonCursor checkNext canonNext
    checkResume canonResume paired sameThread leftAt rightAt checkBody canonBody sized compared

theorem CollectionTailAt.of_children (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index pointer bytes : Nat) (left right : Config (core3 grow) (HostState sig))
    (compared : ∀ item ∈ entries, ∀ address pos, Compare profile ready dispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        item pos (.memory address))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item (.memory address))) :
    CollectionTailAt profile ready dispatch destination inst entries area output index pointer bytes left right :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.collectionTailFromChildren
    destination inst entries area output index pointer bytes left right compared

/-- Execute the actual saved return programs, carrying the tail's invariant
only on success. A failed live recheck stops at the checked diagnostic;
misalignment and range traps still compare the locked-down reached stores. -/
theorem collection_return_keeping_at (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index pointer : Nat)
    (left right : Config (core3 grow) (HostState sig)) (checkCursor canonCursor : Cursor (E := core3 grow) (HostState sig))
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    (checkResume canonResume : ReturnFrame.Continuation (core3 grow) (HostState sig))
    (paired : HostFrame.Paired checkResume canonResume left right) (sameThread : checkCursor.thread = canonCursor.thread)
    (leftAt : left.ctl = { checkCursor with frames := .prog checkResume :: checkCursor.frames }.control (pure (.nat pointer)))
    (rightAt : right.ctl = { canonCursor with frames := .prog canonResume :: canonCursor.frames }.control (pure (.nat pointer)))
    (checkBody : checkResume (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      let live ← Record.Effects.reserve recordClaims (Field.listObjects entries)
      checkedCollectionTail destination inst entries area index output ptr live >>= checkNext))
    (canonBody : canonResume (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      canonicalCollectionTail destination inst entries area output ptr >>= canonNext))
    {bytes : Nat} (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes) {keep}
    (compared : CollectionTailKeepingAt profile ready dispatch keep destination inst entries area output index pointer bytes left right) :
    ReachesKeeping profile ready dispatch keep left right checkCursor canonCursor checkNext canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.collectionReturnKeepingAt
    destination inst entries area output index pointer left right checkCursor canonCursor checkNext canonNext
    checkResume canonResume paired sameThread leftAt rightAt checkBody canonBody sized compared

/-- Replay a finite certified callback prefix, starting with the two saved
allocator continuations. At a reached natural return, compose validation,
live rechecking, element lowering and descriptor publication with that
prefix. A different host read is a cut, not a fabricated canonical error. -/
theorem collection_callback (destination : RecordDestination) (inst : InstId) (entries : List Field)
    (area : Layout) (output : Lower.Output) (index : Nat)
    {left right last : Config (core3 grow) (HostState sig)} {labels}
    (callback : CoreGrowthSteps profile ready dispatch left labels last)
    (destinationChecked : destination.check left.store = .ok ()) {bytes : Nat}
    (sized : (core3 grow).memSize? left.store.core destination.memory = some bytes)
    (checkNext : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (canonNext : output.Result → Session grow sig (Ret (core3 grow)))
    {checkResume canonResume : ReturnFrame.Continuation (core3 grow) (HostState sig)}
    (paired : HostFrame.Paired checkResume canonResume left right)
    (checkBody : ∀ pointer, checkResume (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      let live ← Record.Effects.reserve recordClaims (Field.listObjects entries)
      checkedCollectionTail destination inst entries area index output ptr live >>= checkNext))
    (canonBody : ∀ pointer, canonResume (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area entries.length pointer
      canonicalCollectionTail destination inst entries area output ptr >>= canonNext))
    (compared : ∀ item ∈ entries, ∀ address pos, Compare profile ready dispatch
      (Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst) destination.width
        item pos (.memory address))
      (CanonicalTree.field Limits.spec Quirks.none (destination.context inst) destination.width item (.memory address))) :
    (∃ other, CoreGrowthSteps profile ready dispatch right labels other ∧ HostFrame.Paired checkResume canonResume last other) ∨
    (∃ leading label trailing atLeft atRight afterLeft afterRight,
      labels = leading ++ label :: trailing ∧ CoreGrowthSteps profile ready dispatch left leading atLeft ∧
      CoreGrowthSteps profile ready dispatch right leading atRight ∧ HostFrame.Paired checkResume canonResume atLeft atRight ∧
      Step profile ready dispatch atLeft label afterLeft ∧ Step profile ready dispatch atRight label afterRight ∧
      CoreGrowthSteps profile ready dispatch afterLeft trailing last ∧
      ((∃ alternate, HostFrame.ReadCut atLeft atRight.host label afterLeft alternate ∧
          ReturnFrame.Paired checkResume canonResume alternate afterRight) ∨
       (∃ thread value frames rest,
          (∀ pointer, value ≠ .nat pointer) ∧
          atLeft.ctl = ⟨thread, .prog (.pure value), .prog checkResume :: frames⟩ :: rest ∧
          ReturnFrame.Returned checkResume canonResume (HostFrame.replace atLeft atRight.host) atRight label
            (HostFrame.replace afterLeft atRight.host) afterRight) ∨
       (∃ (pointer : Nat) (checkCursor canonCursor : Cursor (E := core3 grow) (HostState sig)),
          atLeft.ctl = { checkCursor with frames := .prog checkResume :: checkCursor.frames }.control (pure (.nat pointer)) ∧
          atRight.ctl = { canonCursor with frames := .prog canonResume :: canonCursor.frames }.control (pure (.nat pointer)) ∧
          canonCursor.thread = checkCursor.thread ∧
          Reaches profile ready dispatch left right checkCursor canonCursor checkNext canonNext))) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.collectionCallback
    destination inst entries area output index callback destinationChecked sized
    checkNext canonNext paired checkBody canonBody compared

/-- The compiler's layout certificate supplies the tag bounds at every
selected sum in the handle-only fragment. -/
theorem checked_fragment {field : Field} {type : TypeOf} (layout : Field.LayoutMatches field type)
    (shape : HandleShape field) : HandleField field :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.certifyField layout shape

/-- Execute a reached memory placement guard. A valid placement consumes
the bounds read; an invalid placement traps without entering the suffix. -/
theorem check_placement_steps {World : Type} {placementReady : HostReady World}
    {placementDispatch : Call (core3 grow) → P (core3 grow) World (Ret (core3 grow))}
    (destination : RecordDestination) (inst : InstId) (start : Config (core3 grow) World)
    (area : Layout) (ptr : Nat) (cursor : Cursor (E := core3 grow) World)
    (finish : P (core3 grow) World (Ret (core3 grow)))
    (focused : start.ctl = cursor.control (do
      checkAligned ptr area.alignment.bytes
      checkInBounds (destination.context inst) ptr area.size
      finish)) :
    match placement destination start.store area ptr with
    | .ok () => Steps profile placementReady placementDispatch start [.tau] { start with ctl := cursor.control finish }
    | .error reason => ∃ count, Steps profile placementReady placementDispatch start
        (List.replicate count .tau ++ [.trap reason]) (StepDefs.trapCfg start) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.checkPlacement
    destination inst start area ptr cursor finish focused

/-- Successful placement preserves the active return slots across the actual
bounds read. Failed placement instead runs to canonical lockdown. -/
theorem check_placement_tracks {World : Type} {placementReady : HostReady World}
    {placementDispatch : Call (core3 grow) → P (core3 grow) World (Ret (core3 grow))}
    (destination : RecordDestination) (inst : InstId) (start : Config (core3 grow) World)
    (area : Layout) (ptr : Nat) (cursor : Cursor (E := core3 grow) World)
    (finish : P (core3 grow) World (Ret (core3 grow)))
    (focused : start.ctl = cursor.control (do
      checkAligned ptr area.alignment.bytes
      checkInBounds (destination.context inst) ptr area.size
      finish)) :
    match placement destination start.store area ptr with
    | .ok () => ReturnFrame.Occurrence.RetainsActiveSlots profile placementReady placementDispatch start [.tau]
        { start with ctl := cursor.control finish }
    | .error reason => ∃ count, Steps profile placementReady placementDispatch start
        (List.replicate count .tau ++ [.trap reason]) (StepDefs.trapCfg start) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.checkPlacementRun
    destination inst start area ptr cursor finish focused

/-- Enter the actual compiled root body, or trap before any child runs. A
flat output has no placement steps; a memory output uses its reached store. -/
theorem root_placement_steps (destination : RecordDestination) (inst : InstId) (type : TypeOf)
    (field : Field) (output : Lower.Output) (start : Config (core3 grow) (HostState sig))
    (cursor : Cursor (E := core3 grow) (HostState sig))
    (finish : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (focused : start.ctl = cursor.control (Record.Effects.root recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width type field output >>= finish)) :
    let child := cursor.control (Record.Effects.field recordClaims Limits.spec Quirks.none
      (destination.context inst) destination.width field 0 output >>= finish)
    match rootPlacement destination start.store type output with
    | .ok () => ∃ labels, visible labels = [] ∧ Steps profile ready dispatch start labels { start with ctl := child }
    | .error reason => ∃ count, Steps profile ready dispatch start
        (List.replicate count .tau ++ [.trap reason]) (StepDefs.trapCfg start) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.rootPlacementSteps destination inst type
    field output start cursor finish focused

/-- The linked public `giveFlat` call reaches the same flat words as
`lowerFlatAt` for compiled handle-only aggregates, fixed lists and sums, or
stops at a typed refusal or common canonical trap. The same canonical choice
answers are recorded on both sides. Returned verdicts reach the
original ticketed reply program, not a claim that the enclosing export returns. -/
theorem parked_giveFlat (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (handleWord : BitVec IntType.i32.width) (destination : RecordDestination) (inst : InstId) (schema : TypeOf)
    (tag : sig.Tag) (payload : OwnedMemory.Payload (sig.payload tag)) {arity : Nat}
    (children : Fin arity → OwnedMemory.Tree sig) (field : Field) (plan : List Object)
    (compiled : Record.preflightValue (destination.context (grow := grow) inst) (sig.payload tag)
      payload .flat = .ok (field, plan)) (fragment : HandleShape field)
    (start reference : Config (core3 grow) (HostState sig)) (sameStore : start.store = reference.store)
    (canonCursor : Cursor (E := core3 grow) (HostState sig)) (canonNext : List FlatValue → Session grow sig (Ret (core3 grow)))
    {thread core continuation segments rest} (sameThread : thread = canonCursor.thread)
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) [.int .i32 handleWord])
    (linked : resolveBinding bindings name type = .ok ⟨name, inst, .giveFlat destination schema⟩)
    (caller : Plain.callerInstance start.store thread = .ok (some inst))
    (mayLeave : (start.store.inst? inst).any (·.mayLeave) = true)
    (destinationChecked : destination.check start.store = .ok ())
    (selected : Endpoints.Core.childFromHistory start.host.writer.accepted handleWord =
      some (.tag ⟨tag, payload⟩ arity children))
    (schemaChecked : rootHasSchema (.tag ⟨tag, payload⟩ arity children) schema = true)
    (canonicalAt : reference.ctl = canonCursor.control (lowerFlatAt Limits.spec Quirks.none (destination.context inst)
      destination.width payload.val.value (sig.payload tag) >>= canonNext)) :
    Reaches profile ready (specDispatch ready (host (grow := grow) bindings)) start reference
      ⟨thread, .core core continuation :: segments, rest⟩ canonCursor
      (flatReply destination schema start.host.nextTicket) canonNext :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.parkedFlat
    bindings name type handleWord destination inst schema tag payload children field plan compiled fragment start reference
    sameStore canonCursor canonNext sameThread parked calling linked caller mayLeave destinationChecked selected
    schemaChecked canonicalAt

/-- The public indirect route pairs its compiled handle leaf or selected
handle sum with actual `Canon.store`. The linked check establishes the width;
the checked route's extra alignment and bounds guards may trap before the
reference starts, since raw `store` treats placement as a precondition. -/
theorem parked_givePayload (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (handleWord : BitVec IntType.i32.width) (pointer : FlatValue) (destination : RecordDestination) (inst : InstId)
    (tag : sig.Tag) (payload : OwnedMemory.Payload (sig.payload tag)) {arity : Nat}
    (children : Fin arity → OwnedMemory.Tree sig) (field : Field) (plan : List Object)
    (compiled : Record.preflightValue (destination.context (grow := grow) inst) (sig.payload tag)
      payload (.memory (flatNat pointer)) = .ok (field, plan)) (fragment : MemoryHandleRoot field)
    (start reference : Config (core3 grow) (HostState sig)) (sameStore : start.store = reference.store)
    (canonCursor : Cursor (E := core3 grow) (HostState sig)) (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {thread core continuation segments rest} (sameThread : thread = canonCursor.thread)
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) [.int .i32 handleWord, pointer])
    (linked : resolveBinding bindings name type = .ok ⟨name, inst, .givePayload destination⟩)
    (caller : Plain.callerInstance start.store thread = .ok (some inst))
    (mayLeave : (start.store.inst? inst).any (·.mayLeave) = true)
    (destinationChecked : destination.check start.store = .ok ())
    (selected : Endpoints.Core.childFromHistory start.host.writer.accepted handleWord =
      some (.tag ⟨tag, payload⟩ arity children))
    (pointerChecked : Stored.flatType pointer = pointerType destination.width)
    (canonicalAt : reference.ctl = canonCursor.control (store Limits.spec Quirks.none (destination.context inst)
      payload.val.value (sig.payload tag) (flatNat pointer) >>= canonNext)) :
    MemoryReaches profile ready (specDispatch ready (host (grow := grow) bindings)) start reference
      ⟨thread, .core core continuation :: segments, rest⟩ canonCursor
      (memoryReply destination pointer start.host.nextTicket) canonNext
      (placement destination start.store (layout destination.width (sig.payload tag)) (flatNat pointer)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.parkedMemory
    bindings name type handleWord pointer destination inst tag payload children field plan compiled (.inl fragment) start reference
    sameStore canonCursor canonNext sameThread parked calling linked caller mayLeave destinationChecked selected
    pointerChecked canonicalAt

/-- The parked public indirect route compares the handle fragment and mixed
scalar/handle records and tuples with actual canonical storage. Its extra
root placement failure remains separate from canonical execution traps. -/
theorem parked_givePayload_closed (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (handleWord : BitVec IntType.i32.width) (pointer : FlatValue) (destination : RecordDestination) (inst : InstId)
    (tag : sig.Tag) (payload : OwnedMemory.Payload (sig.payload tag)) {arity : Nat}
    (children : Fin arity → OwnedMemory.Tree sig) (field : Field) (plan : List Object)
    (compiled : Record.preflightValue (destination.context (grow := grow) inst) (sig.payload tag)
      payload (.memory (flatNat pointer)) = .ok (field, plan)) (fragment : ClosedMemoryRoot field)
    (start reference : Config (core3 grow) (HostState sig)) (sameStore : start.store = reference.store)
    (canonCursor : Cursor (E := core3 grow) (HostState sig)) (canonNext : Unit → Session grow sig (Ret (core3 grow)))
    {thread core continuation segments rest} (sameThread : thread = canonCursor.thread)
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) [.int .i32 handleWord, pointer])
    (linked : resolveBinding bindings name type = .ok ⟨name, inst, .givePayload destination⟩)
    (caller : Plain.callerInstance start.store thread = .ok (some inst))
    (mayLeave : (start.store.inst? inst).any (·.mayLeave) = true)
    (destinationChecked : destination.check start.store = .ok ())
    (selected : Endpoints.Core.childFromHistory start.host.writer.accepted handleWord =
      some (.tag ⟨tag, payload⟩ arity children))
    (pointerChecked : Stored.flatType pointer = pointerType destination.width)
    (canonicalAt : reference.ctl = canonCursor.control (store Limits.spec Quirks.none (destination.context inst)
      payload.val.value (sig.payload tag) (flatNat pointer) >>= canonNext)) :
    MemoryReaches profile ready (specDispatch ready (host (grow := grow) bindings)) start reference
      ⟨thread, .core core continuation :: segments, rest⟩ canonCursor
      (memoryReply destination pointer start.host.nextTicket) canonNext
      (placement destination start.store (layout destination.width (sig.payload tag)) (flatNat pointer)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadPrefix.parkedMemory
    bindings name type handleWord pointer destination inst tag payload children field plan compiled fragment start reference
    sameStore canonCursor canonNext sameThread parked calling linked caller mayLeave destinationChecked selected
    pointerChecked canonicalAt

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix
