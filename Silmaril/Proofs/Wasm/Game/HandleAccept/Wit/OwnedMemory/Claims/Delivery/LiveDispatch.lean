module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadEffects.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Thms
import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LiveDispatch
open PayloadRoot ComponentCall.Delivery ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {route : GiveEffectRoute}
  {profile : ProfileKind} {ready : HostReady (HostState sig)} {base : HostImpl (core3 grow) (HostState sig)}
  {bindings : List (Binding sig)}

private theorem readStore {Result : Type} (next : CStore (core3 grow) → Session grow sig Result)
    (store : CStore (core3 grow)) (other : HostState sig) (thread : Option ThreadId) :
    Plain.runBody (getStore.bind next) store other (some thread) = Plain.runBody (next store) store other (some thread) := rfl

private theorem readSelection {Result : Type} (handle : BitVec IntType.i32.width)
    (next : Option (Stored.OwnedMemory.Tree sig) → Session grow sig Result) (store : CStore (core3 grow))
    (other : HostState sig) (thread : Option ThreadId) :
    Plain.runBody ((select handle).bind next) store other (some thread) =
      Plain.runBody (next (Stored.Endpoints.Core.childFromHistory other.writer.accepted handle))
        store other (some thread) := rfl

private theorem admitAt {Result : Type} (site : Site grow sig route) (linked : site.Linked bindings)
    (other : HostState sig) (selection : Session grow sig (Except Issue Result)) :
    Plain.runBody (admit site.inst selection) site.start.store other (some site.thread) =
      Plain.runBody selection site.start.store other (some site.thread) := by
  simp only [admit, Prog.bind_eq, Plain.runBody_currentInst, linked.caller, readStore,
    bne_self_eq_false, linked.mayLeave, Bool.not_true, Bool.or_false, Bool.false_eq_true, ite_false]

private theorem entryWith {Result : Type} (site : Site grow sig route) (linked : site.Linked bindings)
    (other : HostState sig) (selection : Session grow sig (Except Issue Result)) (selected : Result)
    (next : Except Issue Result → Session grow sig (List FlatValue))
    (words : (LiveDispatch.host bindings base).embedder site.name site.functionType (route.args site.handle) =
      admit site.inst selection >>= next)
    (evaluation : Plain.runBody selection site.start.store other (some site.thread) =
      (site.start.store, other, .ok (.ok selected)))
    (body : (next (.ok selected) >>= fun reply => pure (.flat reply)) = site.referenceProgram >>= site.referenceReply) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) (HostFrame.replace site.start other)
        labels (HostFrame.replace (site.reference site.referenceReply) other) := by
  let impl := LiveDispatch.host bindings base
  let finish : Except Issue Result → Session grow sig (Ret (core3 grow)) :=
    fun result => next result >>= fun reply => pure (.flat reply)
  let start := HostFrame.replace site.start other
  let active := { start with ctl := site.cursor.control (admit site.inst selection >>= finish) }
  obtain ⟨labels, silent, run⟩ := Plain.runBody_thread_steps (admit site.inst selection) active site.start.store other
    (.ok selected) finish site.thread _ site.rest profile ready (specDispatch ready impl) rfl
    ((admitAt site linked other selection).trans evaluation)
  have installed : calloutBody Limits.spec Quirks.none ready impl site.start.store site.thread
      (.embedder site.name site.functionType) (route.args site.handle) = admit site.inst selection >>= finish := by
    simp only [calloutBody, Plain.thread_may_leave linked.caller linked.mayLeave, ite_true,
      show impl.embedder site.name site.functionType (route.args site.handle) = _ from words, Prog.bind_eq, Prog.bind_assoc]
    rfl
  refine ⟨.tau :: .tau :: .tau :: labels, ?_, ?_⟩
  · apply List.all_eq_true.mpr
    intro label member
    simp only [List.mem_cons] at member
    rcases member with rfl | rfl | rfl | member
    · rfl
    · rfl
    · rfl
    · have tau := List.all_eq_true.mp silent label member
      cases label <;> first | rfl | contradiction
  · apply Plain.prepend_embedder_callout (start := start) linked.parked linked.calling
    rw [show start.store = site.start.store from rfl, installed]
    simpa only [active, start, finish, Site.cursor, PayloadPrefix.Cursor.control, HostFrame.replace, Site.reference, body] using run

theorem entry (site : Site grow sig route) (linked : site.Linked bindings) (other : HostState sig)
    (selected : Stored.Endpoints.Core.childFromHistory other.writer.accepted site.handle = some site.tree) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) (HostFrame.replace site.start other)
        labels (HostFrame.replace (site.reference site.referenceReply) other) := by
  cases route with
  | memory pointer =>
    let selection := selectMemoryDestination (grow := grow) (sig := sig) site.destination [.int .i32 site.handle, pointer]
    let next : Except Issue (Stored.OwnedMemory.Tree sig × Nat) → Session grow sig (List FlatValue)
      | .error issue => pure (completion 0 (.error issue)).2
      | .ok (tree, ptr) => memoryBody site.inst site.destination tree ptr
    have resolved := linked.linked
    have word := linked.admitted
    change Stored.flatType pointer = ABI.pointerType site.destination.width at word
    refine entryWith site linked other selection (site.tree, flatNat pointer) next ?_ ?_ ?_
    · simp only [LiveDispatch.host, selectBinding, resolved, GiveEffectRoute.action, GiveEffectRoute.args, memoryWords]
      rfl
    · simp only [selection, selectMemoryDestination, Execution.Runtime.Value.int, Prog.bind_eq, word,
        bne_self_eq_false, Bool.false_eq_true, ite_false, readStore, linked.destination, readSelection, selected]
      rfl
    · simp only [next, memoryBody, Site.tree, Site.referenceProgram,
        GiveEffectRoute.output, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind']
      rfl
  | flat schema =>
    let selection := selectFlatDestination (grow := grow) (sig := sig) site.destination schema [.int .i32 site.handle]
    let next : Except Issue (Stored.OwnedMemory.Tree sig) → Session grow sig (List FlatValue)
      | .error issue => pure (flatCompletion 0 (ABI.flatten site.destination.width schema) (.error issue)).2
      | .ok tree => flatBody site.inst site.destination schema tree
    have resolved := linked.linked
    have schemaMatches := linked.admitted
    change rootHasSchema site.tree schema = true at schemaMatches
    refine entryWith site linked other selection site.tree next ?_ ?_ ?_
    · simp only [LiveDispatch.host, selectBinding, resolved, GiveEffectRoute.action, GiveEffectRoute.args, flatWords]
      rfl
    · simp only [selection, selectFlatDestination, Execution.Runtime.Value.int, Prog.bind_eq,
        readStore, linked.destination, readSelection, selected, schemaMatches, Bool.not_true, Bool.false_eq_true, ite_false]
      rfl
    · simp only [next, flatBody, Site.tree, Site.referenceProgram, GiveEffectRoute.output,
        Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind']
      congr 1
      funext words
      change (Prog.pure (Ret.flat (E := core3 grow) (flatCompletion 0 _ (.ok words)).2) :
        Session grow sig (Ret (core3 grow))) =
        Prog.pure (Ret.flat (flatCompletion site.start.host.nextTicket _ (.ok words)).2)
      simp only [flatCompletion]
      split <;> rfl

theorem pairedEntry (site : Site grow sig route) (linked : site.Linked bindings)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {other : State grow sig}
    (paired : HostFrame.Related.Paired older site.start other)
    (selected : Stored.Endpoints.Core.childFromHistory other.host.writer.accepted site.handle = some site.tree) :
    ∃ labels entered,
      labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) other labels entered ∧
      HostFrame.Related.Paired older (site.reference site.referenceReply) entered ∧ entered.host = other.host := by
  have related : ReturnFrame.Related.Paired older (HostFrame.replace site.start other.host) other := paired
  obtain ⟨frames, rest, focused, residual⟩ := related.push_shared linked.parked
    (.prog (site.referenceProgram >>= site.referenceReply)) (.core site.core site.resume)
  let shadow : Site grow sig route := { site with start := HostFrame.replace other site.start.host, frames, rest }
  have shared := paired.data.1
  have shadowLinked : shadow.Linked bindings :=
    { parked := focused
      calling := shared ▸ linked.calling
      linked := linked.linked
      caller := shared ▸ linked.caller
      mayLeave := shared ▸ linked.mayLeave
      destination := shared ▸ linked.destination
      selected := linked.selected
      admitted := linked.admitted
      compiled := linked.compiled }
  obtain ⟨labels, silent, path⟩ := entry (profile := profile) (ready := ready) (base := base) shadow shadowLinked other.host selected
  exact ⟨labels, _, silent, path, residual, rfl⟩

theorem append {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {start middle finish : Config (core3 grow) (HostState sig)} {leading trailing}
    (first : Steps profile ready dispatch start leading middle) (tail : Steps profile ready dispatch middle trailing finish) :
    Steps profile ready dispatch start (leading ++ trailing) finish := by
  induction first with
  | refl => exact tail
  | cons step _ ih => exact .cons step (ih tail)

private theorem closedWords {start : State grow sig} (callout : LinkedCallback.ClosedGive bindings start) (other : HostState sig) :
    Plain.runBody (confine ((LiveDispatch.host bindings base).embedder callout.name callout.type callout.args))
      start.store other (some callout.thread) = (start.store, other, .ok callout.reply.2) := by
  have blocked : (start.store.inst? callout.inst).any (·.mayLeave) = false := by
    simp [callout.live, callout.closed]
  have read : ∀ {Result : Type} (next : CStore (core3 grow) → Session grow sig Result),
      Plain.runBody (confine (getStore.bind next)) start.store other (some callout.thread) =
        Plain.runBody (confine (next start.store)) start.store other (some callout.thread) := fun _ => rfl
  cases schema : callout.schema <;>
    simp only [LiveDispatch.host, selectBinding, callout.linked, schema, Option.elim, memoryWords, flatWords, admit,
      Prog.bind_eq, Prog.bind_assoc, Plain.runBody_confined_currentInst, callout.caller,
      read, blocked, LinkedCallback.ClosedGive.reply, bne_self_eq_false, Bool.false_or, Bool.not_false, ite_true] <;> rfl

private theorem closedPath {start : State grow sig} (callout : LinkedCallback.ClosedGive bindings start) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start labels
        (HostFrame.replace callout.resume start.host) := by
  let impl := LiveDispatch.host bindings base
  let body := confine (impl.embedder callout.name callout.type callout.args)
  let active := { start with ctl := ⟨callout.thread, .prog (body >>= fun words => pure (.flat words)),
    .core callout.core callout.next :: callout.frames⟩ :: callout.rest }
  obtain ⟨labels, silent, run⟩ := Plain.runBody_thread_steps body active start.store start.host callout.reply.2
    (fun words => pure (.flat words)) callout.thread _ callout.rest profile ready (specDispatch ready impl) rfl
    (closedWords (base := base) callout start.host)
  have tail : Steps profile ready (specDispatch ready impl) active (labels ++ [.tau])
      (HostFrame.replace callout.resume start.host) := append run (.cons (.popCore rfl) (.refl _))
  have leaves := Plain.thread_cannot_leave callout.caller callout.live callout.closed
  have path := Plain.prepend_embedder_callout (impl := impl) callout.parked callout.calling
    (by simpa only [active, calloutBody, leaves, Bool.false_eq_true, ite_false, body] using tail)
  refine ⟨.tau :: .tau :: .tau :: (labels ++ [.tau]), ?_, path⟩
  apply List.all_eq_true.mpr
  intro label member
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | inTrace | rfl <;> try rfl
  have observed := List.all_eq_true.mp silent label inTrace
  cases label <;> first | rfl | contradiction

theorem pairedClosedGive {start incoming : State grow sig} (callout : LinkedCallback.ClosedGive bindings start)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ labels reached, labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming labels reached ∧
      HostFrame.Related.Paired older callout.resume reached ∧ reached.host = incoming.host := by
  let next := Focus.core ((core3 grow).resume start.store.core callout.core (.values callout.reply.2)) callout.next
  obtain ⟨frames, rest, focused, aligned⟩ := paired.retarget callout.parked next callout.resume.host incoming.host
  have shared := paired.data.1
  let shadow : LinkedCallback.ClosedGive bindings incoming :=
    { name := callout.name, type := callout.type, args := callout.args, inst := callout.inst,
      destination := callout.destination, schema := callout.schema, thread := callout.thread, core := callout.core,
      next := callout.next, frames, rest, entry := callout.entry, parked := focused,
      calling := shared ▸ callout.calling, linked := callout.linked, caller := shared ▸ callout.caller,
      live := shared ▸ callout.live, closed := callout.closed }
  obtain ⟨labels, silent, run⟩ := closedPath (profile := profile) (ready := ready) (base := base) shadow
  have words : shadow.reply.2 = callout.reply.2 := by
    cases schema : callout.schema <;> simp [LinkedCallback.ClosedGive.reply, shadow, schema, completion, flatCompletion]
  refine ⟨labels, _, silent, run, ?_, rfl⟩
  simpa only [HostFrame.replace, LinkedCallback.ClosedGive.resume, next, words, shared,
    show shadow.thread = callout.thread from rfl, show shadow.core = callout.core from rfl,
    show shadow.next = callout.next from rfl, show shadow.frames = frames from rfl,
    show shadow.rest = rest from rfl] using aligned

theorem dispatchUnchanged {call : Call (core3 grow)} (unmodified : Unchanged bindings call) :
    specDispatch ready base call = specDispatch ready (LiveDispatch.host bindings base) call := by
  cases call with
  | hostCallout callee args =>
    cases callee with
    | embedder name kind =>
      change selectBinding bindings name kind = none at unmodified
      simp only [specDispatch, dispatch, hostCalloutProg, calloutBody, LiveDispatch.host, unmodified]
    | lowered | builtin => rfl
  | threadBody body => cases body <;> rfl
  | onCancel cancel => cases cancel <;> rfl
  | _ => rfl

variable {start finish : Config (core3 grow) (HostState sig)}

private theorem resolveName {name : String} {kind : V1.FuncType} {binding : Binding sig}
    (found : resolveBinding bindings name kind = .ok binding) : binding.name = name := by
  unfold resolveBinding at found
  cases hits : bindings.filter (·.name == name) with
  | nil => simp [hits] at found
  | cons candidate rest =>
    cases rest with
    | cons => simp [hits] at found
    | nil =>
      simp only [hits] at found
      split at found
      · contradiction
      · obtain rfl := Except.ok.inj found
        have member : candidate ∈ bindings.filter (·.name == name) := by simp [hits]
        exact beq_iff_eq.mp (List.mem_filter.mp member).2

private theorem resolvedGive {name : String} {kind : V1.FuncType} {inst : InstId} {destination : RecordDestination}
    {schema : Option Stored.TypeOf}
    (selected : selectBinding bindings name kind = some (inst, destination, schema)) :
    resolveBinding bindings name kind = .ok ⟨name, inst, schema.elim (.givePayload destination) (.giveFlat destination)⟩ := by
  cases found : resolveBinding bindings name kind with
  | error => simp [selectBinding, found] at selected
  | ok binding =>
    have named := resolveName found
    cases binding with
    | mk key target action =>
      change key = name at named
      subst key
      cases action <;> simp [selectBinding, found] at selected
      case givePayload =>
        obtain ⟨rfl, rfl, rfl⟩ := selected
        rfl
      case giveFlat =>
        obtain ⟨rfl, rfl, rfl⟩ := selected
        rfl

private theorem selectResolved {name : String} {kind : V1.FuncType}
    (changed : selectBinding bindings name kind ≠ none) :
    ∃ inst destination schema, resolveBinding bindings name kind =
      .ok ⟨name, inst, Option.elim schema (.givePayload destination) (.giveFlat destination)⟩ := by
  cases selected : selectBinding bindings name kind with
  | none => exact (changed selected).elim
  | some result =>
    obtain ⟨inst, destination, schema⟩ := result
    exact ⟨inst, destination, schema, resolvedGive selected⟩

theorem classifyGiveRequest {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))} {label}
    (install : GiveInstall bindings dispatch start label finish) :
    Nonempty (CoreGiveRequest bindings start) ∨ DirectGiveAt bindings start := by
  cases install with
  | @direct thread call next frames rest focused changed =>
    cases call <;> try exact (changed trivial).elim
    case hostCallout callee args =>
      cases callee <;> try exact (changed trivial).elim
      case embedder name kind =>
        obtain ⟨inst, destination, schema, linked⟩ := selectResolved changed
        exact .inr ⟨name, kind, args, thread, next, frames, rest, inst, destination, schema, focused, linked⟩
  | @core thread core next frames rest callee args focused calling changed =>
    cases callee <;> try exact (changed trivial).elim
    case embedder name kind =>
      obtain ⟨inst, destination, schema, linked⟩ := selectResolved changed
      exact .inl ⟨⟨name, kind, args, inst, destination, schema, thread, core, next, frames, rest, focused, calling, linked⟩⟩

private theorem selectedMemory {destination : RecordDestination} {args : List FlatValue} {thread : Option ThreadId}
    {tree : Stored.OwnedMemory.Tree sig} {address : Nat}
    (evaluation : Plain.runBody (selectMemoryDestination destination args) start.store start.host (some thread) =
      (start.store, start.host, .ok (.ok (tree, address)))) :
    ∃ handle pointer, args = (.memory pointer : GiveEffectRoute).args handle ∧
      (.memory pointer : GiveEffectRoute).admits destination tree ∧ destination.check start.store = .ok () ∧
      Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle = some tree ∧ address = flatNat pointer := by
  unfold selectMemoryDestination at evaluation
  split at evaluation
  next handle pointer =>
    by_cases width : Stored.flatType pointer = ABI.pointerType destination.width
    · simp only [width, bne_self_eq_false, Bool.false_eq_true, ite_false, Prog.bind_eq, readStore] at evaluation
      cases checked : destination.check start.store with
      | error => simp [checked, Prog.pure_eq, Plain.runBody] at evaluation
      | ok checkedValue =>
        cases checkedValue
        rw [checked] at evaluation
        simp only [readSelection] at evaluation
        cases chosen : Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle with
        | none => simp [chosen, Prog.pure_eq, Plain.runBody] at evaluation
        | some root =>
          simp [chosen, Prog.pure_eq, Plain.runBody] at evaluation
          obtain ⟨rfl, rfl⟩ := evaluation
          exact ⟨handle, pointer, rfl, width, rfl, chosen, rfl⟩
    · simp [width, Prog.pure_eq, Plain.runBody] at evaluation
  next => simp [Prog.pure_eq, Plain.runBody] at evaluation

private theorem selectedFlat {destination : RecordDestination} {args : List FlatValue} {thread : Option ThreadId}
    {tree : Stored.OwnedMemory.Tree sig} {schema : Stored.TypeOf}
    (evaluation : Plain.runBody (selectFlatDestination destination schema args) start.store start.host (some thread) =
      (start.store, start.host, .ok (.ok tree))) :
    ∃ handle, args = (.flat schema : GiveEffectRoute).args handle ∧
      (.flat schema : GiveEffectRoute).admits destination tree ∧ destination.check start.store = .ok () ∧
      Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle = some tree := by
  unfold selectFlatDestination at evaluation
  split at evaluation
  next handle =>
    simp only [Prog.bind_eq, readStore] at evaluation
    cases checked : destination.check start.store with
    | error => simp [checked, Prog.pure_eq, Plain.runBody] at evaluation
    | ok checkedValue =>
      cases checkedValue
      rw [checked] at evaluation
      simp only [readSelection] at evaluation
      cases chosen : Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle with
      | none => simp [chosen, Prog.pure_eq, Plain.runBody] at evaluation
      | some root =>
        by_cases matchesSchema : rootHasSchema root schema = true
        · simp [chosen, matchesSchema, Prog.pure_eq, Plain.runBody] at evaluation
          subst root
          exact ⟨handle, rfl, matchesSchema, rfl, chosen⟩
        · simp [chosen, Bool.eq_false_iff.mpr matchesSchema, Prog.pure_eq, Plain.runBody] at evaluation
  next => simp [Prog.pure_eq, Plain.runBody] at evaluation

private theorem admitSuccess {Result : Type} {inst : InstId} {thread : Option ThreadId}
    {selection : Session grow sig (Except Issue Result)} {chosen : Result}
    (evaluation : Plain.runBody (admit inst selection) start.store start.host (some thread) =
      (start.store, start.host, .ok (.ok chosen))) :
    Plain.callerInstance start.store thread = .ok (some inst) ∧
      (start.store.inst? inst).any (·.mayLeave) = true ∧
      Plain.runBody selection start.store start.host (some thread) = (start.store, start.host, .ok (.ok chosen)) := by
  simp only [admit, Prog.bind_eq, Plain.runBody_currentInst] at evaluation
  cases caller : Plain.callerInstance start.store thread with
  | error => simp [caller] at evaluation
  | ok actual =>
    by_cases same : actual = some inst
    · subst actual
      by_cases mayLeave : (start.store.inst? inst).any (·.mayLeave) = true
      · exact ⟨rfl, mayLeave, by simpa [caller, readStore, mayLeave] using evaluation⟩
      · simp [caller, readStore, Bool.eq_false_iff.mpr mayLeave, Prog.pure_eq, Plain.runBody] at evaluation
    · simp [caller, readStore, bne_iff_ne.mpr same, Prog.pure_eq, Plain.runBody] at evaluation

theorem memorySelection (request : CoreGiveRequest bindings start) (memory : request.schema = none)
    {tree : Stored.OwnedMemory.Tree sig} {address : Nat}
    (evaluation : Plain.runBody (admit request.inst (selectMemoryDestination request.destination request.args))
      start.store start.host (some request.thread) = (start.store, start.host, .ok (.ok (tree, address)))) :
    ∃ (pointer : FlatValue) (selection : request.Selected (.memory pointer)), selection.tree = tree ∧ flatNat pointer = address := by
  obtain ⟨caller, mayLeave, picked⟩ := admitSuccess evaluation
  obtain ⟨handle, pointer, args, admitted, destination, selected, addressEq⟩ := selectedMemory picked
  refine ⟨pointer, ⟨handle, tree, args, ?_, caller, mayLeave, destination, selected, admitted⟩, rfl, addressEq.symm⟩
  simpa [memory, GiveEffectRoute.action] using request.linked

theorem flatSelection (request : CoreGiveRequest bindings start) {schema : Stored.TypeOf} (flat : request.schema = some schema)
    {tree : Stored.OwnedMemory.Tree sig}
    (evaluation : Plain.runBody (admit request.inst (selectFlatDestination request.destination schema request.args))
      start.store start.host (some request.thread) = (start.store, start.host, .ok (.ok tree))) :
    ∃ selection : request.Selected (.flat schema), selection.tree = tree := by
  obtain ⟨caller, mayLeave, picked⟩ := admitSuccess evaluation
  obtain ⟨handle, args, admitted, destination, selected⟩ := selectedFlat picked
  refine ⟨⟨handle, tree, args, ?_, caller, mayLeave, destination, selected, admitted⟩, rfl⟩
  simpa [flat, GiveEffectRoute.action] using request.linked

theorem selectionLinked {request : CoreGiveRequest bindings start} (selection : request.Selected route)
    {tag : sig.Tag} {payload : Stored.OwnedMemory.Payload (sig.payload tag)} {arity : Nat}
    {children : Fin arity → Stored.OwnedMemory.Tree sig} {field : Stored.Endpoints.RecordLower.Field} {plan}
    (picked : selection.tree = .tag ⟨tag, payload⟩ arity children)
    (preflight : Stored.OwnedMemory.Claims.Record.preflightValue (request.destination.context (grow := grow) request.inst) (sig.payload tag)
      payload route.output = .ok (field, plan)) :
    (selection.site tag payload arity children field).Linked bindings := by
  refine ⟨request.focused, ?_, selection.linked, selection.caller, selection.mayLeave, selection.destination,
    ?_, ?_, ⟨plan, preflight⟩⟩
  · simpa only [CoreGiveRequest.Selected.site, ← selection.args] using request.calling
  · simpa only [picked, CoreGiveRequest.Selected.site, Site.tree] using selection.selected
  · simpa only [picked, CoreGiveRequest.Selected.site, Site.tree] using selection.admitted

theorem compilerSuccess {request : CoreGiveRequest bindings start} (selection : request.Selected route)
    {field : Stored.Endpoints.RecordLower.Field} {plan}
    (compiled : selection.preflight = .ok (field, plan)) :
    ∃ (tag : sig.Tag) (payload : Stored.OwnedMemory.Payload (sig.payload tag)) (arity : Nat)
      (children : Fin arity → Stored.OwnedMemory.Tree sig),
      selection.tree = .tag ⟨tag, payload⟩ arity children ∧
      (selection.site tag payload arity children field).Linked bindings := by
  cases picked : selection.tree with
  | atom impossible => exact impossible.elim
  | tag value arity children =>
    obtain ⟨tag, payload⟩ := value
    simp only [CoreGiveRequest.Selected.preflight, picked] at compiled
    exact ⟨tag, payload, arity, children, rfl, selectionLinked selection picked compiled⟩

theorem compilerRefusal {request : CoreGiveRequest bindings start} (selection : request.Selected route)
    {issue : Stored.Endpoints.RecordLower.Issue} (refused : selection.preflight = .error issue)
    (impl : HostImpl (core3 grow) (HostState sig))
    (embedder : impl.embedder = (Stored.OwnedMemory.Claims.Core.Scheduled.host (grow := grow) bindings).embedder) :
    ∃ count, Steps profile ready (specDispatch ready impl) start (List.replicate count .tau) (selection.compilerRefused issue) := by
  have calling := request.calling
  rw [selection.args] at calling
  obtain ⟨front, silent, entry⟩ := GiveEffectRoute.parked bindings request.name request.kind selection.handle route request.inst
    request.destination selection.tree start request.thread profile ready request.focused calling selection.linked
    selection.caller selection.mayLeave selection.destination selection.selected selection.admitted impl embedder
  have replyOnly : route.run (grow := grow) request.destination request.inst selection.tree start.host.nextTicket =
      (do return .flat (← writeCompletion (route.reply request.destination start.host.nextTicket (.error issue)))) := by
    cases chosen : selection.tree with
    | atom impossible => exact impossible.elim
    | tag value arity children =>
      simp only [CoreGiveRequest.Selected.preflight, chosen] at refused
      simp only [GiveEffectRoute.run, Stored.OwnedMemory.Claims.Record.Effects.lowerTree,
        Stored.Endpoints.RecordLower.Internal.lowerWithPlan, refused, Prog.pure_eq, Prog.bind_eq, Prog.pure_bind']
  rw [replyOnly] at entry
  have completed := Plain.give_completion_steps (profile := profile) (ready := ready) (dispatch := specDispatch ready impl)
    (start := { start with host := start.host.enter request.name request.kind (route.args selection.handle)
                           ctl := ⟨request.thread, .prog (route.run request.destination request.inst selection.tree start.host.nextTicket),
                             .core request.core request.next :: request.frames⟩ :: request.rest })
    (route.reply request.destination start.host.nextTicket (.error issue)) (by rw [replyOnly])
  rw [replyOnly] at completed
  have replicated : front = List.replicate front.length .tau := List.eq_replicate_length.mpr (fun label member => by
    have tau := List.all_eq_true.mp silent label member
    cases label <;> first | rfl | contradiction)
  refine ⟨front.length + 3, ?_⟩
  rw [List.replicate_add, ← replicated]
  exact append entry completed

private abbrev Observations {Result : Type} (program : Session grow sig Result) (store : CStore (core3 grow))
    (left right : HostState sig) (thread : Option ThreadId) : Prop :=
  ∃ verdict, Plain.runBody program store left (some thread) = (store, left, verdict) ∧
    Plain.runBody program store right (some thread) = (store, right, verdict)

private theorem admitObservations {Result : Type} {inst : InstId} {store : CStore (core3 grow)}
    {left right : HostState sig} {thread : Option ThreadId} {program : Session grow sig (Except Issue Result)}
    (observes : Plain.callerInstance store thread = .ok (some inst) →
      (store.inst? inst).any (·.mayLeave) = true → Observations program store left right thread) :
    Observations (admit inst program) store left right thread := by
  unfold Observations
  simp only [admit, Prog.bind_eq, Plain.runBody_currentInst]
  cases caller : Plain.callerInstance store thread with
  | error issue => exact ⟨.error issue, rfl, rfl⟩
  | ok actual =>
    by_cases same : actual = some inst
    · subst actual
      by_cases mayLeave : (store.inst? inst).any (·.mayLeave) = true
      · simpa [readStore, mayLeave] using observes caller mayLeave
      · simp [readStore, Bool.eq_false_iff.mpr mayLeave, Prog.pure_eq, Plain.runBody]
    · simp [readStore, bne_iff_ne.mpr same, Prog.pure_eq, Plain.runBody]

private theorem memoryObservations {destination : RecordDestination} {args : List FlatValue} {store : CStore (core3 grow)}
    {left right : HostState sig} {thread : Option ThreadId}
    (reads : ∀ handle pointer, args = [.int .i32 handle, pointer] →
      Stored.flatType pointer = ABI.pointerType destination.width → destination.check store = .ok () →
      Stored.Endpoints.Core.childFromHistory left.writer.accepted handle =
        Stored.Endpoints.Core.childFromHistory right.writer.accepted handle) :
    Observations (selectMemoryDestination destination args) store left right thread := by
  unfold Observations selectMemoryDestination
  split
  next _ handle pointer =>
    by_cases width : Stored.flatType pointer = ABI.pointerType destination.width
    · simp only [width, bne_self_eq_false, Bool.false_eq_true, ite_false, Prog.bind_eq, readStore]
      cases checked : destination.check store with
      | error issue => exact ⟨.ok (.error issue), rfl, rfl⟩
      | ok checkedValue =>
        cases checkedValue
        simp only [readSelection]
        rw [reads handle pointer rfl width checked]
        cases Stored.Endpoints.Core.childFromHistory right.writer.accepted handle <;> exact ⟨_, rfl, rfl⟩
    · simp [width, Prog.pure_eq, Plain.runBody]
  next => exact ⟨_, rfl, rfl⟩

private theorem flatObservations {destination : RecordDestination} {args : List FlatValue} {schema : Stored.TypeOf}
    {store : CStore (core3 grow)} {left right : HostState sig} {thread : Option ThreadId}
    (reads : ∀ handle, args = [.int .i32 handle] → destination.check store = .ok () →
      Stored.Endpoints.Core.childFromHistory left.writer.accepted handle =
        Stored.Endpoints.Core.childFromHistory right.writer.accepted handle) :
    Observations (selectFlatDestination destination schema args) store left right thread := by
  unfold Observations selectFlatDestination
  split
  next _ handle =>
    simp only [Prog.bind_eq, readStore]
    cases checked : destination.check store with
    | error issue => exact ⟨.ok (.error issue), rfl, rfl⟩
    | ok checkedValue =>
      cases checkedValue
      simp only [readSelection]
      rw [reads handle rfl checked]
      cases found : Stored.Endpoints.Core.childFromHistory right.writer.accepted handle with
      | none => exact ⟨_, rfl, rfl⟩
      | some tree =>
        cases sameSchema : rootHasSchema tree schema <;> simp [sameSchema, Plain.runBody, Prog.pure_eq]
  next => exact ⟨_, rfl, rfl⟩

private theorem selectionObservations (request : CoreGiveRequest bindings start) (other : HostState sig)
    (reads : ∀ handle, request.lookupDemand = some handle →
      Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle =
        Stored.Endpoints.Core.childFromHistory other.writer.accepted handle) :
    Observations request.selectionProgram start.store start.host other request.thread := by
  cases request with
  | mk name kind args inst destination schema thread core next frames rest focused calling linked =>
    cases schema with
    | none =>
      apply admitObservations
      intro caller mayLeave
      apply memoryObservations
      intro handle pointer arguments width checked
      apply reads handle
      change args = [.int .i32 handle, pointer] at arguments
      change Stored.flatType pointer = ABI.pointerType destination.width at width
      simp [CoreGiveRequest.lookupDemand, caller, mayLeave, arguments, Execution.Runtime.Value.int, width, checked]
    | some schema =>
      apply admitObservations
      intro caller mayLeave
      apply flatObservations
      intro handle arguments checked
      apply reads handle
      change args = [.int .i32 handle] at arguments
      simp [CoreGiveRequest.lookupDemand, caller, mayLeave, arguments, Execution.Runtime.Value.int, checked]

theorem pairedSelectionObservations (request : CoreGiveRequest bindings start)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {other : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start other)
    (reads : ∀ handle, request.lookupDemand = some handle →
      Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle =
        Stored.Endpoints.Core.childFromHistory other.host.writer.accepted handle) :
    ∃ otherFrames otherRest verdict,
      other.ctl = ⟨request.thread, .core request.core request.next, otherFrames⟩ :: otherRest ∧
      (core3 grow).status other.store.core request.core = .callout (.embedder request.name request.kind) request.args ∧
      Plain.runBody request.selectionProgram start.store start.host (some request.thread) = (start.store, start.host, verdict) ∧
      Plain.runBody request.selectionProgram other.store other.host (some request.thread) = (other.store, other.host, verdict) := by
  have sameStore := paired.data.1
  obtain ⟨otherFrames, otherRest, focused, _⟩ := paired.push_shared_frames request.focused
    (.core request.core request.next) []
  obtain ⟨verdict, left, right⟩ := selectionObservations request other.host reads
  exact ⟨otherFrames, otherRest, verdict, focused, sameStore ▸ request.calling, left, sameStore ▸ right⟩

theorem classifyPairedSelection (request : CoreGiveRequest bindings start)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {other : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start other) :
    (∃ otherFrames otherRest verdict,
      other.ctl = ⟨request.thread, .core request.core request.next, otherFrames⟩ :: otherRest ∧
      (core3 grow).status other.store.core request.core = .callout (.embedder request.name request.kind) request.args ∧
      Plain.runBody request.selectionProgram start.store start.host (some request.thread) = (start.store, start.host, verdict) ∧
      Plain.runBody request.selectionProgram other.store other.host (some request.thread) = (other.store, other.host, verdict)) ∨
    ∃ handle, request.lookupDemand = some handle ∧
      Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle ≠
        Stored.Endpoints.Core.childFromHistory other.host.writer.accepted handle := by
  classical
  by_cases reads : ∀ handle, request.lookupDemand = some handle →
      Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle =
        Stored.Endpoints.Core.childFromHistory other.host.writer.accepted handle
  · exact .inl (pairedSelectionObservations request paired reads)
  · push Not at reads
    exact .inr reads

private theorem runBind {Value Result : Type} (program : Session grow sig Value)
    (next : Value → Session grow sig Result) (store : CStore (core3 grow)) (state : HostState sig)
    (thread : Option ThreadId) :
    Plain.runBody (program >>= next) store state (some thread) =
      match Plain.runBody program store state (some thread) with
      | (reached, reachedHost, .ok value) => Plain.runBody (next value) reached reachedHost (some thread)
      | (reached, reachedHost, .error issue) => (reached, reachedHost, .error issue) := by
  induction program generalizing store state with
  | pure => rfl
  | op op continuation ih =>
    cases op <;> simp only [Prog.bind_eq, Prog.bind, Plain.runBody] <;> apply ih

private theorem confineBind {Value Result : Type} (program : Session grow sig Value)
    (next : Value → Session grow sig Result) :
    confine (program >>= next) = confine program >>= (fun value => confine (next value)) := by
  induction program with
  | pure => rfl
  | op op continuation ih =>
    simp only [Prog.bind_eq, Prog.bind, confine]
    split
    · congr 1
      funext answer
      exact ih answer
    · change Prog.op _ _ = Prog.op _ _
      congr 1
      funext impossible
      nomatch impossible

private theorem fixedBind {Value Result : Type} (program : Session grow sig Value)
    (next : Value → Session grow sig Result) (before : confine program = program)
    (after : ∀ value, confine (next value) = next value) :
    confine (program >>= next) = program >>= next := by
  rw [confineBind, before, funext after]

private theorem confineSelector (request : CoreGiveRequest bindings start) :
    confine request.selectionProgram = request.selectionProgram := by
  have object {Id Value : Type} (arena : ArenaField (core3 grow) Id Value) (id : Id) :
      confine (getObj arena id : Session grow sig Value) = getObj arena id := by
    unfold getObj
    apply fixedBind _ _ rfl
    intro reference
    split
    · rfl
    · simp only [internal, trap, confine, Op.observes, ite_true]
      congr 1
      funext impossible
      nomatch impossible
  have caller : confine (currentInst? : Session grow sig (Option InstId)) = currentInst? := by
    unfold currentInst? currentTask?
    apply fixedBind
    · apply fixedBind _ _ rfl
      intro thread
      cases thread with
      | none => rfl
      | some id => exact fixedBind _ _ (object ArenaField.threads id) (fun _ => rfl)
    · intro task
      cases task with
      | none => rfl
      | some id => exact fixedBind _ _ (object ArenaField.tasks id) (fun _ => rfl)
  have read (handle : BitVec IntType.i32.width) : confine (select handle : Session grow sig _) = select handle :=
    rfl
  have memory : confine (selectMemoryDestination request.destination request.args : Session grow sig _) =
      selectMemoryDestination request.destination request.args := by
    unfold selectMemoryDestination
    split
    · split
      · rfl
      · apply fixedBind _ _ rfl
        intro reference
        split
        · rfl
        · apply fixedBind _ _ (read _)
          intro root
          cases root <;> rfl
    · rfl
  have flat (schema : Stored.TypeOf) :
      confine (selectFlatDestination request.destination schema request.args : Session grow sig _) =
        selectFlatDestination request.destination schema request.args := by
    unfold selectFlatDestination
    split
    · apply fixedBind _ _ rfl
      intro reference
      split
      · rfl
      · apply fixedBind _ _ (read _)
        intro root
        cases root with
        | none => rfl
        | some tree =>
          let no : Session grow sig (Except Issue (Stored.OwnedMemory.Tree sig)) := pure (.error .wrongPayloadType)
          let yes : Session grow sig (Except Issue (Stored.OwnedMemory.Tree sig)) := pure (.ok tree)
          change confine (if !rootHasSchema tree schema then no else yes) = (if !rootHasSchema tree schema then no else yes)
          split <;> rfl
    · rfl
  unfold CoreGiveRequest.selectionProgram
  cases request.schema <;> unfold admit <;> apply fixedBind _ _ caller <;> intro inst <;>
    apply fixedBind _ _ rfl <;> intro reference <;> split <;> first | rfl | exact memory | apply flat

private def checkedTail (inst : InstId) (destination : RecordDestination) (ticket : Nat) :
    (schema : Option Stored.TypeOf) → Except Issue (SelectionValue sig schema) → Session grow sig (List FlatValue)
  | none, result =>
    (match result with
     | .error issue => pure (.error issue)
     | .ok (tree, ptr) => do
       let lowered ← Stored.OwnedMemory.Claims.Record.lowerPayloadRoot recordClaims Limits.spec Quirks.none
         (destination.context inst) tree (.memory ptr)
       return lowered.mapError Issue.lowerPayload |>.map (fun _ => 0)) >>= Stored.OwnedMemory.Claims.Core.Scheduled.finish ticket
  | some schema, result =>
    (match result with
     | .error issue => pure (.error issue)
     | .ok tree => do
       let lowered ← Stored.OwnedMemory.Claims.Record.lowerPayloadRoot recordClaims Limits.spec Quirks.none
         (destination.context inst) tree .flat
       return lowered.mapError Issue.lowerPayload) >>= fun lowered =>
      writeCompletion (flatCompletion ticket (ABI.flatten destination.width schema) lowered)

private noncomputable def referenceTail (inst : InstId) (destination : RecordDestination) :
    (schema : Option Stored.TypeOf) → Except Issue (SelectionValue sig schema) → Session grow sig (List FlatValue)
  | none, .error issue => pure (completion 0 (.error issue)).2
  | none, .ok (tree, ptr) => memoryBody inst destination tree ptr
  | some schema, .error issue => pure (flatCompletion 0 (ABI.flatten destination.width schema) (.error issue)).2
  | some schema, .ok tree => flatBody inst destination schema tree

private theorem checkedSplit (request : CoreGiveRequest bindings start) :
    (Stored.OwnedMemory.Claims.Core.Scheduled.host (grow := grow) bindings).embedder request.name request.kind request.args =
      (do
        let state ← hostGet
        hostSet (state.enter request.name request.kind request.args)
        let verdict ← request.selectionProgram
        checkedTail request.inst request.destination state.nextTicket request.schema verdict) := by
  rcases request with ⟨name, kind, args, inst, destination, schema, _, _, _, _, _, _, _, linked⟩
  cases schema <;> simp only [Stored.OwnedMemory.Claims.Core.Scheduled.host, dispatchImport, route, linked,
    Option.elim, CoreGiveRequest.selectionProgram, checkedTail, admit, giveFlat, invoke, givePayload, giveToMemory,
    Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq]
  all_goals
    congr 1
    funext state
    congr 1
    funext answer
    congr 1
    funext caller
    congr 1
    funext reference
    split
    · rfl
    · rw [Prog.bind_assoc]
      refine congrArg (fun next => Prog.bind _ next) ?_
      funext verdict
      cases verdict <;> rfl

private theorem referenceSplit (request : CoreGiveRequest bindings start) :
    (LiveDispatch.host bindings base).embedder request.name request.kind request.args =
      request.selectionProgram >>= referenceTail request.inst request.destination request.schema := by
  rcases request with ⟨name, kind, args, inst, destination, schema, _, _, _, _, _, _, _, linked⟩
  cases schema <;> simp only [LiveDispatch.host, selectBinding, linked, Option.elim,
    memoryWords, flatWords, CoreGiveRequest.selectionProgram] <;>
    congr 1 <;> funext verdict <;> cases verdict <;> rfl

private def effective {Result : Type} (store : CStore (core3 grow)) (thread : Option ThreadId)
    (words : Session grow sig Result) : Session grow sig Result :=
  if threadMayLeave store thread then words else confine words

private theorem evalEffectiveBind {Value Result : Type} (program : Session grow sig Value)
    (next : Value → Session grow sig Result) (store : CStore (core3 grow)) (state : HostState sig)
    (thread : Option ThreadId) (fixed : confine program = program) :
    Plain.runBody (effective store thread (program >>= next)) store state (some thread) =
      match Plain.runBody program store state (some thread) with
      | (reached, reachedHost, .ok value) => Plain.runBody (effective store thread (next value)) reached reachedHost (some thread)
      | (reached, reachedHost, .error issue) => (reached, reachedHost, .error issue) := by
  unfold effective
  split <;> rename_i leaves
  · simp only [runBind]
  · simp only [confineBind, fixed, runBind]

private theorem evalChecked (request : CoreGiveRequest bindings start)
    (impl : HostImpl (core3 grow) (HostState sig))
    (embedder : impl.embedder = (Stored.OwnedMemory.Claims.Core.Scheduled.host (grow := grow) bindings).embedder) :
    let entered := start.host.enter request.name request.kind request.args
    Plain.runBody (effective start.store request.thread (impl.embedder request.name request.kind request.args))
        start.store start.host (some request.thread) =
      match Plain.runBody request.selectionProgram start.store entered (some request.thread) with
      | (reached, reachedHost, .ok verdict) => Plain.runBody
          (effective start.store request.thread (checkedTail request.inst request.destination start.host.nextTicket request.schema verdict))
          reached reachedHost (some request.thread)
      | (reached, reachedHost, .error issue) => (reached, reachedHost, .error issue) := by
  rw [embedder, checkedSplit request, evalEffectiveBind _ _ _ _ _ rfl]
  change Plain.runBody (effective _ _ (hostSet _ >>= _)) _ _ _ = _
  rw [evalEffectiveBind _ _ _ _ _ rfl]
  change Plain.runBody (effective _ _ (request.selectionProgram >>= _)) _ _ _ = _
  rw [evalEffectiveBind _ _ _ _ _ (confineSelector request)]
  generalize Plain.runBody request.selectionProgram start.store (start.host.enter request.name request.kind request.args)
    (some request.thread) = evaluated
  rcases evaluated with ⟨_, _, verdict⟩
  cases verdict <;> rfl

private theorem checkedReply (request : CoreGiveRequest bindings start) (issue : Issue) (state : HostState sig) :
    Plain.runBody (effective start.store request.thread
      (checkedTail request.inst request.destination start.host.nextTicket request.schema (.error issue)))
      start.store state (some request.thread) =
        (start.store, state.record (request.admissionReply issue).1, .ok (request.admissionReply issue).2) := by
  rcases request with ⟨_, _, _, _, _, schema, thread, _, _, _, _, _, _, _⟩
  cases schema <;> unfold effective <;> split <;> rfl

private theorem referenceReply (request : CoreGiveRequest bindings start) (issue : Issue) (state : HostState sig) :
    Plain.runBody (effective start.store request.thread
      (referenceTail request.inst request.destination request.schema (.error issue))) start.store state (some request.thread) =
      (start.store, state, .ok (request.admissionReply issue).2) := by
  rcases request with ⟨_, _, _, _, _, schema, _, _, _, _, _, _, _, _⟩
  cases schema <;> unfold effective <;> split <;> rfl

private theorem returnPath (impl : HostImpl (core3 grow) (HostState sig))
    {thread core next frames rest name kind args reached words}
    (focused : start.ctl = ⟨thread, .core core next, frames⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name kind) args)
    (evaluated : Plain.runBody (effective start.store thread (impl.embedder name kind args))
        start.store start.host (some thread) = (start.store, reached, .ok words)) :
    ∃ count, Steps profile ready (specDispatch ready impl) start (List.replicate count .tau)
      { start with host := reached
                   ctl := ⟨thread, .core ((core3 grow).resume start.store.core core (.values words)) next, frames⟩ :: rest } := by
  let body := effective start.store thread (impl.embedder name kind args)
  let entered := { start with ctl := ⟨thread, .prog (body >>= fun reply => pure (.flat reply)), .core core next :: frames⟩ :: rest }
  obtain ⟨labels, silent, run⟩ := Plain.runBody_thread_steps body entered start.store reached words
    (fun reply => pure (.flat reply)) thread _ rest profile ready (specDispatch ready impl) rfl evaluated
  have returned := append run (.cons (.popCore rfl) (.refl _))
  have entire := Plain.prepend_embedder_callout (impl := impl) (profile := profile) (ready := ready) focused calling
    (by cases leaves : threadMayLeave start.store thread <;>
          simpa [entered, body, effective, calloutBody, leaves] using returned)
  have replicated : labels = List.replicate labels.length .tau := List.eq_replicate_length.mpr (fun label member => by
    have tau := List.all_eq_true.mp silent label member
    cases label <;> first | rfl | contradiction)
  refine ⟨3 + (labels.length + 1), ?_⟩
  rw [List.replicate_add, List.replicate_add, ← replicated]
  exact entire

private theorem trapPath (impl : HostImpl (core3 grow) (HostState sig))
    {thread core next frames rest name kind args reached reason}
    (focused : start.ctl = ⟨thread, .core core next, frames⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name kind) args)
    (evaluated : Plain.runBody (effective start.store thread (impl.embedder name kind args))
        start.store start.host (some thread) = (start.store, reached, .error (.trapped reason))) :
    ∃ count, Steps profile ready (specDispatch ready impl) start (List.replicate count .tau ++ [.trap reason])
      (StepDefs.trapCfg { start with host := reached }) := by
  let body := effective start.store thread (impl.embedder name kind args)
  let entered := { start with ctl := ⟨thread, .prog (body >>= fun reply => pure (.flat reply)), .core core next :: frames⟩ :: rest }
  obtain ⟨count, run⟩ := Plain.runBody_trap_steps body entered start.store reached reason
    (fun reply => pure (.flat reply)) thread _ rest profile ready (specDispatch ready impl) rfl evaluated
  have entire := Plain.prepend_embedder_callout (impl := impl) (profile := profile) (ready := ready) focused calling
    (by cases leaves : threadMayLeave start.store thread <;>
          simpa [entered, body, effective, calloutBody, StepDefs.trapCfg, leaves] using run)
  refine ⟨3 + count, ?_⟩
  rw [List.replicate_add, List.append_assoc]
  exact entire

private theorem selectionAfterEntry (request : CoreGiveRequest bindings start) {verdict}
    (evaluated : Plain.runBody request.selectionProgram start.store start.host (some request.thread) =
      (start.store, start.host, verdict)) :
    let entered := start.host.enter request.name request.kind request.args
    Plain.runBody request.selectionProgram start.store entered (some request.thread) = (start.store, entered, verdict) := by
  obtain ⟨_, before, after⟩ := selectionObservations request (start.host.enter request.name request.kind request.args)
    (fun _ _ => rfl)
  rw [evaluated] at before
  cases before
  exact after

theorem pairedAdmissionRefusal (request : CoreGiveRequest bindings start)
    (impl : HostImpl (core3 grow) (HostState sig))
    (embedder : impl.embedder = (Stored.OwnedMemory.Claims.Core.Scheduled.host (grow := grow) bindings).embedder)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {other : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start other) {issue : Issue}
    (refused : Plain.runBody request.selectionProgram start.store start.host (some request.thread) =
      (start.store, start.host, .ok (.error issue)))
    (reads : ∀ handle, request.lookupDemand = some handle →
      Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle =
        Stored.Endpoints.Core.childFromHistory other.host.writer.accepted handle) :
    ∃ leftCount rightCount checked canonical,
      Steps profile ready (specDispatch ready impl) start (List.replicate leftCount .tau) checked ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) other (List.replicate rightCount .tau) canonical ∧
      HostFrame.Related.Paired older checked canonical ∧
      checked.host = (start.host.enter request.name request.kind request.args).record (request.admissionReply issue).1 ∧
      canonical.host = other.host := by
  have selected : Plain.runBody request.selectionProgram start.store other.host (some request.thread) =
      (start.store, other.host, .ok (.error issue)) := by
    obtain ⟨_, before, after⟩ := selectionObservations request other.host reads
    rw [refused] at before
    cases before
    exact after
  have leftEval := evalChecked request impl embedder
  dsimp only at leftEval
  rw [selectionAfterEntry request refused] at leftEval
  have returned := leftEval.trans (checkedReply request issue _)
  have rightEval : Plain.runBody (effective start.store request.thread
      ((LiveDispatch.host bindings base).embedder request.name request.kind request.args))
      start.store other.host (some request.thread) = (start.store, other.host, .ok (request.admissionReply issue).2) := by
    rw [referenceSplit request, evalEffectiveBind _ _ _ _ _ (confineSelector request), selected]
    exact referenceReply request issue _
  have shared := paired.data.1
  let resumed := (core3 grow).resume start.store.core request.core (.values (request.admissionReply issue).2)
  have aligned : ReturnFrame.Related.Paired older (HostFrame.replace start other.host) other := paired
  obtain ⟨frames, rest, focused, residual⟩ := aligned.push_shared_frames request.focused (.core resumed request.next) []
  obtain ⟨leftCount, left⟩ := returnPath (profile := profile) (ready := ready) impl request.focused request.calling returned
  obtain ⟨rightCount, right⟩ := returnPath (profile := profile) (ready := ready) (LiveDispatch.host bindings base)
    focused (shared ▸ request.calling) (shared ▸ rightEval)
  refine ⟨leftCount, rightCount, _, _, left, right, ?_, rfl, rfl⟩
  change ReturnFrame.Related.Paired older _ _
  simpa only [HostFrame.replace, ← shared, resumed, List.nil_append] using residual

private theorem selectorCallerTrap (request : CoreGiveRequest bindings start) (observer : HostState sig)
    {reason : TrapReason} (trapped : Plain.callerInstance start.store request.thread = .error (.trapped reason)) :
    Plain.runBody request.selectionProgram start.store observer (some request.thread) =
      (start.store, observer, .error (.trapped reason)) := by
  unfold CoreGiveRequest.selectionProgram
  cases request.schema <;> simp only [admit, Prog.bind_eq, Plain.runBody_currentInst, trapped]

theorem pairedAdmissionTrap (request : CoreGiveRequest bindings start)
    (impl : HostImpl (core3 grow) (HostState sig))
    (embedder : impl.embedder = (Stored.OwnedMemory.Claims.Core.Scheduled.host (grow := grow) bindings).embedder)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {other : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start other) {reason : TrapReason}
    (trapped : Plain.callerInstance start.store request.thread = .error (.trapped reason)) :
    ∃ leftCount rightCount,
      Steps profile ready (specDispatch ready impl) start (List.replicate leftCount .tau ++ [.trap reason])
        (StepDefs.trapCfg { start with host := start.host.enter request.name request.kind request.args }) ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) other
        (List.replicate rightCount .tau ++ [.trap reason]) (StepDefs.trapCfg other) := by
  obtain ⟨_, _, focused, _⟩ := paired.push_shared_frames request.focused (.core request.core request.next) []
  have leftEval := evalChecked request impl embedder
  dsimp only at leftEval
  rw [selectorCallerTrap request _ trapped] at leftEval
  have shared := paired.data.1
  have rightEval : Plain.runBody (effective start.store request.thread
      ((LiveDispatch.host bindings base).embedder request.name request.kind request.args))
      start.store other.host (some request.thread) = (start.store, other.host, .error (.trapped reason)) := by
    rw [referenceSplit request, evalEffectiveBind _ _ _ _ _ (confineSelector request), selectorCallerTrap request _ trapped]
  obtain ⟨leftCount, left⟩ := trapPath (profile := profile) (ready := ready) impl request.focused request.calling leftEval
  obtain ⟨rightCount, right⟩ := trapPath (profile := profile) (ready := ready) (LiveDispatch.host bindings base)
    focused (shared ▸ request.calling) (shared ▸ rightEval)
  exact ⟨leftCount, rightCount, left, right⟩

theorem selectedDemand {request : CoreGiveRequest bindings start} (selection : request.Selected route) :
    request.lookupDemand = some selection.handle := by
  have action : request.schema.elim (.givePayload request.destination) (.giveFlat request.destination) =
      route.action (sig := sig) request.destination :=
    congrArg Binding.action (Except.ok.inj (request.linked.symm.trans selection.linked))
  unfold CoreGiveRequest.lookupDemand
  rw [selection.caller, selection.args]
  cases route with
  | memory pointer =>
    have width := selection.admitted
    change Stored.flatType pointer = ABI.pointerType request.destination.width at width
    cases schemaAt : request.schema with
    | none => simp [GiveEffectRoute.args, Execution.Runtime.Value.int, selection.mayLeave, width, selection.destination]
    | some schema => simp [schemaAt, GiveEffectRoute.action] at action
  | flat schema =>
    cases schemaAt : request.schema with
    | none => simp [schemaAt, GiveEffectRoute.action] at action
    | some _ => simp [GiveEffectRoute.args, Execution.Runtime.Value.int, selection.mayLeave, selection.destination]

private theorem installSelected {request : CoreGiveRequest bindings start} {other : Config (core3 grow) (HostState sig)}
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start other)
    (caller : Plain.callerInstance start.store request.thread = .ok (some request.inst))
    (mayLeave : (start.store.inst? request.inst).any (·.mayLeave) = true)
    {Value : Type} (program : Session grow sig Value) (verdict : Value)
    (tail : Value → Session grow sig (List FlatValue))
    (installed : (LiveDispatch.host bindings base).embedder request.name request.kind request.args = program >>= tail)
    (evaluated : Plain.runBody program start.store other.host (some request.thread) = (start.store, other.host, .ok verdict)) :
    ∃ labels entered, labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) other labels entered ∧
      entered.host = other.host ∧
      HostFrame.Related.Paired older
        { start with ctl := ⟨request.thread, .prog (tail verdict >>= fun words => pure (.flat words)),
          .core request.core request.next :: request.frames⟩ :: request.rest } entered := by
  let impl := LiveDispatch.host bindings base
  let next : Value → Session grow sig (Ret (core3 grow)) := fun result => tail result >>= fun words => pure (.flat words)
  have shared := paired.data.1
  have aligned : ReturnFrame.Related.Paired older (HostFrame.replace start other.host) other := paired
  obtain ⟨frames, rest, focused, entered⟩ := aligned.push_shared request.focused (.prog (next verdict)) (.core request.core request.next)
  let active := { other with ctl := ⟨request.thread, .prog (program >>= next), .core request.core request.next :: frames⟩ :: rest }
  obtain ⟨labels, silent, localRun⟩ := Plain.runBody_thread_steps program active other.store other.host verdict next
    request.thread _ rest profile ready (specDispatch ready impl) rfl (shared ▸ evaluated)
  have leaves : threadMayLeave other.store request.thread = true := shared ▸ Plain.thread_may_leave caller mayLeave
  have actual := Plain.prepend_embedder_callout (impl := impl) (profile := profile) (ready := ready)
    focused (shared ▸ request.calling)
    (by simpa only [active, next, calloutBody, leaves, ite_true, impl, installed, Prog.bind_eq, Prog.bind_assoc] using localRun)
  refine ⟨.tau :: .tau :: .tau :: labels, _, ?_, actual, rfl, ?_⟩
  · apply List.all_eq_true.mpr
    intro label member
    simp only [List.mem_cons] at member
    rcases member with rfl | rfl | rfl | member <;> try rfl
    have observed := List.all_eq_true.mp silent label member
    cases label <;> first | rfl | contradiction
  · simpa only [HostFrame.Related.Paired, HostFrame.replace, next, Prog.bind_eq] using entered

theorem pendingPaired {request : CoreGiveRequest bindings start} (selection : request.Selected route)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {other : Config (core3 grow) (HostState sig)}
    (paired : HostFrame.Related.Paired older start other)
    (reads : ∀ handle, request.lookupDemand = some handle →
      Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle =
        Stored.Endpoints.Core.childFromHistory other.host.writer.accepted handle) :
    ∃ labels entered, labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) other labels entered ∧
      entered.host = other.host ∧
      HostFrame.Related.Paired older selection.canonicalPending entered := by
  have selected := (reads selection.handle (selectedDemand selection)).symm.trans selection.selected
  have caller := selection.caller
  have mayLeave := selection.mayLeave
  have checked := selection.destination
  have args := selection.args
  have linked := selection.linked
  cases route with
  | memory pointer =>
    let program : Session grow sig (Except Issue (Stored.OwnedMemory.Tree sig × Nat)) :=
      admit request.inst (selectMemoryDestination request.destination request.args)
    let tail : Except Issue (Stored.OwnedMemory.Tree sig × Nat) → Session grow sig (List FlatValue)
      | .error issue => pure (completion 0 (.error issue)).2
      | .ok (tree, ptr) => memoryBody request.inst request.destination tree ptr
    have width := selection.admitted
    change Stored.flatType pointer = ABI.pointerType request.destination.width at width
    refine installSelected paired caller mayLeave program (.ok (selection.tree, flatNat pointer)) tail ?_ ?_
    · simp only [LiveDispatch.host, selectBinding, GiveEffectRoute.action] at linked ⊢
      simp only [linked, memoryWords, program, tail]
      rfl
    · simp only [program, admit, Prog.bind_eq, Plain.runBody_currentInst, caller, readStore,
        bne_self_eq_false, mayLeave, Bool.not_true, Bool.or_false, Bool.false_eq_true, ite_false]
      simp only [args, GiveEffectRoute.args, selectMemoryDestination, Execution.Runtime.Value.int, Prog.bind_eq,
        width, bne_self_eq_false, Bool.false_eq_true, ite_false, readStore, checked, readSelection, selected]
      rfl
  | flat schema =>
    let program : Session grow sig (Except Issue (Stored.OwnedMemory.Tree sig)) :=
      admit request.inst (selectFlatDestination request.destination schema request.args)
    let tail : Except Issue (Stored.OwnedMemory.Tree sig) → Session grow sig (List FlatValue)
      | .error issue => pure (flatCompletion 0 (ABI.flatten request.destination.width schema) (.error issue)).2
      | .ok tree => flatBody request.inst request.destination schema tree
    have schemaMatches := selection.admitted
    change rootHasSchema selection.tree schema = true at schemaMatches
    refine installSelected paired caller mayLeave program (.ok selection.tree) tail ?_ ?_
    · simp only [LiveDispatch.host, selectBinding, GiveEffectRoute.action] at linked ⊢
      simp only [linked, flatWords, program, tail]
      rfl
    · simp only [program, admit, Prog.bind_eq, Plain.runBody_currentInst, caller, readStore,
        bne_self_eq_false, mayLeave, Bool.not_true, Bool.or_false, Bool.false_eq_true, ite_false]
      simp only [args, GiveEffectRoute.args, selectFlatDestination, Execution.Runtime.Value.int, Prog.bind_eq,
        readStore, checked, readSelection, selected, schemaMatches, Bool.not_true, Bool.false_eq_true, ite_false]
      rfl

theorem pendingReference {request : CoreGiveRequest bindings start} (selection : request.Selected route)
    {tag : sig.Tag} {payload : Stored.OwnedMemory.Payload (sig.payload tag)} {arity : Nat}
    {children : Fin arity → Stored.OwnedMemory.Tree sig} (field : Stored.Endpoints.RecordLower.Field)
    (picked : selection.tree = .tag ⟨tag, payload⟩ arity children) :
    selection.canonicalPending = (selection.site tag payload arity children field).reference
      (selection.site tag payload arity children field).referenceReply := by
  cases route with
  | memory pointer =>
    simp only [CoreGiveRequest.Selected.canonicalPending, CoreGiveRequest.Selected.site, Site.reference, Site.cursor,
      PayloadPrefix.Cursor.control, memoryBody, picked, Site.referenceProgram, GiveEffectRoute.output,
      Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind']
    rfl
  | flat schema =>
    have padding (words : List FlatValue) :
        (flatCompletion 0 (ABI.flatten request.destination.width schema) (.ok words)).2 =
          (flatCompletion start.host.nextTicket (ABI.flatten request.destination.width schema) (.ok words)).2 := by
      simp only [flatCompletion]
      split <;> rfl
    simp only [CoreGiveRequest.Selected.canonicalPending, CoreGiveRequest.Selected.site, Site.reference, Site.cursor,
      PayloadPrefix.Cursor.control, flatBody, picked, Site.referenceProgram, GiveEffectRoute.output,
      Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind', padding]
    rfl

theorem classifyStep {label} (step : Step profile ready (specDispatch ready base) start label finish) :
    Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) start label finish ∨
      GiveInstall bindings (specDispatch ready base) start label finish := by
  classical
  cases step with
  | @call _ call _ _ _ focused =>
    by_cases unmodified : Unchanged bindings call
    · left
      rw [dispatchUnchanged unmodified]
      exact .call focused
    · exact .inr (.direct focused unmodified)
  | @coreCallout _ _ _ _ _ callee args focused calling =>
    by_cases unmodified : Unchanged bindings (.hostCallout callee args)
    · left
      rw [dispatchUnchanged unmodified]
      exact .coreCallout focused calling
    · exact .inr (.core focused calling unmodified)
  | newThread focused allocated =>
    left
    unfold StepDefs.threadAct
    rw [dispatchUnchanged (bindings := bindings) (call := .threadBody _) trivial]
    exact .newThread focused allocated
  | popProg focused => exact .inl (.popProg focused)
  | popCore focused => exact .inl (.popCore focused)
  | threadExit focused => exact .inl (.threadExit focused)
  | hostDone focused => exact .inl (.hostDone focused)
  | callCore focused => exact .inl (.callCore focused)
  | coreInternal focused status inner => exact .inl (.coreInternal focused status inner)
  | coreReturned focused status => exact .inl (.coreReturned focused status)
  | coreTrap focused status => exact .inl (.coreTrap focused status)
  | get focused => exact .inl (.get focused)
  | modify focused => exact .inl (.modify focused)
  | trap focused => exact .inl (.trap focused)
  | choose answer focused allowed => exact .inl (.choose answer focused allowed)
  | currentThread focused => exact .inl (.currentThread focused)
  | block focused => exact .inl (.block focused)
  | blockSwitch focused saved => exact .inl (.blockSwitch focused saved)
  | resumeThread focused saved => exact .inl (.resumeThread focused saved)
  | hostGet focused => exact .inl (.hostGet focused)
  | hostSet focused => exact .inl (.hostSet focused)
  | emit focused => exact .inl (.emit focused)
  | fault failed => exact .inl (.fault failed)
  | hostInvoke enabled fresh => exact .inl (.hostInvoke enabled fresh)
  | hostTick enabled => exact .inl (.hostTick enabled)
  | hostCancel enabled pending unresolved => exact .inl (.hostCancel enabled pending unresolved)
  | hostRun enabled => exact .inl (.hostRun enabled)

theorem replayStep {label} (step : Step profile ready (specDispatch ready base) start label finish)
    (unmodified : UnchangedAt bindings start) :
    Step profile ready (specDispatch ready (LiveDispatch.host bindings base)) start label finish := by
  rcases classifyStep (bindings := bindings) step with replayed | install
  · exact replayed
  · cases install with
    | direct focused give => exact (give (unmodified.direct focused)).elim
    | core focused calling give => exact (give (unmodified.core focused calling)).elim

theorem pairedReplay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {incoming : State grow sig} {labels}
    (paired : HostFrame.Related.Paired older start incoming)
    (run : Steps profile ready (specDispatch ready base) start labels finish) :
    PairedReplay bindings profile ready base older start incoming labels finish := by
  induction run generalizing incoming with
  | refl => exact .complete (.refl _) paired
  | cons step tail ih =>
    rcases classifyStep (bindings := bindings) step with unchanged | request
    · obtain ⟨_, replayed, aligned | boundary⟩ := HostFrame.Related.paired_step paired unchanged
      · cases ih aligned with
        | complete replay aligned => exact .complete (.cons replayed replay) aligned
        | request split baseline replay aligned install rest =>
          exact .request (congrArg (List.cons _) split) (.cons step baseline) (.cons replayed replay)
            aligned install rest
        | boundary split baseline replay aligned cut lhs rhs rest =>
          exact .boundary (congrArg (List.cons _) split) (.cons step baseline) (.cons replayed replay)
            aligned cut lhs rhs rest
      · exact .boundary (leading := []) rfl (.refl _) (.refl _) paired boundary step replayed tail
    · exact .request (leading := []) rfl (.refl _) (.refl _) paired request tail

theorem replay {labels} (run : Steps profile ready (specDispatch ready base) start labels finish)
    (closed : UnchangedThrough bindings profile ready base start labels finish) :
    Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start labels finish := by
  induction run with
  | refl => exact .refl _
  | @cons before middle after label labels step tail ih =>
    refine .cons (replayStep step (closed (leading := []) rfl (.refl _) (.cons step tail))) (ih ?_)
    intro leading cut next trailing split front back
    exact closed (leading := label :: leading) (congrArg (List.cons label) split) (.cons step front) back

theorem replayGrowing {labels} (run : CoreGrowthSteps profile ready (specDispatch ready base) start labels finish)
    (closed : UnchangedThrough bindings profile ready base start labels finish) :
    CoreGrowthSteps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start labels finish := by
  induction run with
  | refl => exact .refl _
  | @cons before middle after label labels grows step tail ih =>
    refine .cons grows (replayStep step (closed (leading := []) rfl (.refl _) (.cons step tail.steps))) (ih ?_)
    intro leading cut next trailing split front back
    exact closed (leading := label :: leading) (congrArg (List.cons label) split) (.cons step front) back

theorem nestedReturn (site : Site grow sig route) (linked : site.Linked bindings)
    {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {other checked baseline : State grow sig}
    (paired : HostFrame.Related.Paired older site.start other)
    (selected : Stored.Endpoints.Core.childFromHistory other.host.writer.accepted site.handle = some site.tree)
    {value : route.output.Result} {reached reference : State grow sig} {labels}
    (replies : LinkedCallback.MemorySequence.GiveReplies site value profile ready reached reference checked baseline)
    (body : CoreGrowthSteps profile ready (specDispatch ready base) (site.reference site.referenceReply) labels baseline)
    (closed : UnchangedThrough bindings profile ready base (site.reference site.referenceReply) labels baseline) :
    let dispatch := specDispatch ready (LiveDispatch.host bindings base)
    ∃ installed entered, installed.all (· matches .tau) = true ∧ Steps profile ready dispatch other installed entered ∧
      NestedReplay profile ready dispatch older (site.reference site.referenceReply) entered labels checked := by
  dsimp only
  obtain ⟨installed, entered, silent, install, inside, _⟩ := pairedEntry site linked paired selected
  refine ⟨installed, entered, silent, install, ?_⟩
  rcases HostFrame.Related.paired_growing_steps inside (replayGrowing (bindings := bindings) body closed) with completed | cut
  · obtain ⟨last, path, related⟩ := completed
    have aligned := replies.scheduler_rejoin
    have same := congrArg (fun state => HostFrame.replace state last.host) aligned
    change HostFrame.replace baseline last.host = HostFrame.replace checked last.host at same
    have basePair : ReturnFrame.Related.Paired older (HostFrame.replace baseline last.host) last := related
    have callerPair : ReturnFrame.Related.Paired older (HostFrame.replace checked last.host) last := same ▸ basePair
    exact .rejoined path.steps callerPair
  · obtain ⟨_, _, _, _, _, _, _, split, left, right, related, boundary, lstep, rstep, _⟩ := cut
    exact .boundary split left.steps right.steps related boundary lstep rstep

private theorem neutralRetarget {action labels} {impl : HostImpl (core3 grow) (HostState sig)}
    (edge : Transition profile ready base start action labels finish) (closed : JournalNeutralAction action) :
    Transition profile ready impl start action labels finish := by
  cases edge <;> try contradiction
  case invoke available fresh => exact .invoke available fresh
  case invokePrologue focused => exact .invokePrologue focused
  case liftedLookup focused lookup => exact .liftedLookup focused lookup
  case liftLaunch site => exact .liftLaunch site
  case liftAdmit site admission => exact .liftAdmit site admission
  case liftArguments site live => exact .liftArguments site live
  case invokeReturn focused => exact .invokeReturn focused
  case stackfulComplete exit => exact .stackfulComplete exit
  case stackfulUnresolved => exact .stackfulUnresolved (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  case stackfulExit exit empty => exact .stackfulExit exit empty
  case coreInternal focused running steps => exact .coreInternal focused running steps
  case coreReturned focused returned => exact .coreReturned focused returned
  case coreTrap focused trapped => exact .coreTrap focused trapped
  case coreReply focused => exact .coreReply focused
  case poll poll pending branch => exact .poll poll pending branch
  case waitBlock wait empty => exact .waitBlock wait empty
  case waitReady early allowed wait available => exact .waitReady wait available early allowed
  case waitResume resume saved => exact .waitResume resume saved
  case waitTake delivery focused pending branch => exact .waitTake delivery focused pending branch
  case cancelReturned cancel pending available => exact .cancelReturned cancel pending available
  case cancelReply cancel record cancelled pending focused live => exact .cancelReply cancel record focused live cancelled pending
  case cancelPark wait => exact .cancelPark wait
  case cancelResume resume saved => exact .cancelResume resume saved
  case cancelTake resume pending => exact .cancelTake resume pending

theorem interleavingRetarget {actions labels incoming outgoing} {impl : HostImpl (core3 grow) (HostState sig)}
    (run : JournalInterleaving profile ready base start incoming actions labels finish outgoing) :
    JournalInterleaving profile ready impl start incoming actions labels finish outgoing := by
  induction run with
  | stop state other => exact .stop state other
  | neutral edge closed _ ih => exact .neutral (neutralRetarget edge closed) closed ih
  | commit resolve registered sameHandle _ ih => exact .commit resolve registered sameHandle ih
  | tick tick agrees _ ih => exact .tick tick agrees ih

private theorem neutralHost {action labels} (edge : Transition profile ready base start action labels finish)
    (closed : JournalNeutralAction action) : finish.host = start.host := by
  cases edge <;> try contradiction
  case invokeReturn =>
    cases call : start.pending.getLast?.map (·.1) <;> simp [StepDefs.hostFinish, StepDefs.lastCall?, call, Config.setCancel]
  case poll poll pending branch => cases branch <;> rfl
  case waitReady early allowed wait available => cases early <;> rfl
  case waitTake delivery focused pending branch => cases branch <;> rfl
  all_goals rfl

theorem interleavingRoots {actions labels incoming outgoing}
    (run : JournalInterleaving profile ready base start incoming actions labels finish outgoing)
    (roots : incoming.writer.accepted = start.host.writer.accepted) : outgoing.writer.accepted = finish.host.writer.accepted := by
  induction run with
  | stop => exact roots
  | neutral edge closed _ ih => exact ih (roots.trans (congrArg (·.writer.accepted) (neutralHost edge closed)).symm)
  | commit resolve registered _ _ ih =>
    apply ih
    change _ = resolve.writer.accepted
    exact (Stored.OwnedMemory.Claims.register_claims registered).1.trans
      ((congrArg (resolve.tree :: ·) roots).trans (Stored.OwnedMemory.Claims.register_claims resolve.registered).1.symm)
  | tick tick _ _ ih => exact ih roots

theorem interleavingSteps {actions labels incoming outgoing}
    (between : JournalInterleaving profile ready base start incoming actions labels finish outgoing) :
    Steps profile ready (specDispatch ready (LiveDispatch.host bindings base))
      (HostFrame.replace start incoming) labels (HostFrame.replace finish outgoing) :=
  (interleavingRetarget (impl := LiveDispatch.host bindings base) between).runs.2.steps

private theorem selfList {Elem : Type} {rel : Elem → Elem → Prop} (same : ∀ elem, rel elem elem) (elems : List Elem) :
    List.Forall₂ rel elems elems := by
  induction elems with
  | nil => exact .nil
  | cons head _ ih => exact .cons (same head) ih

private theorem sameFrames (state : Config (core3 grow) (HostState sig)) :
    ReturnFrame.Related.Paired (fun _ _ => False) state state := by
  have active (activation : Activation (core3 grow) (HostState sig)) :
      ReturnFrame.Related.Active (fun _ _ => False) activation activation := by
    cases activation
    exact .mk (selfList ReturnFrame.Related.Segment.same _)
  have saved (activation : Option (Activation (core3 grow) (HostState sig))) :
      ReturnFrame.Related.Saved (fun _ _ => False) activation activation := by
    cases activation with
    | none => exact .none
    | some activation => exact .some (active activation)
  cases state
  exact .mk (selfList active _) (selfList saved _)

theorem pendingAfterInterleaving {request : CoreGiveRequest bindings finish} (selection : request.Selected route)
    {actions labels incoming outgoing} (between : JournalInterleaving profile ready base start incoming actions labels finish outgoing)
    (roots : incoming.writer.accepted = start.host.writer.accepted) :
    ∃ leading entered, leading.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) (HostFrame.replace start incoming)
        (labels ++ leading) entered ∧
      HostFrame.Related.Paired (fun _ _ => False) selection.canonicalPending entered ∧
      entered.host.writer.accepted = finish.host.writer.accepted := by
  have reached := interleavingRoots between roots
  have paired : HostFrame.Related.Paired (fun _ _ => False) finish (HostFrame.replace finish outgoing) :=
    sameFrames (HostFrame.replace finish outgoing)
  obtain ⟨leading, entered, silent, path, kept, aligned⟩ := pendingPaired (base := base) (profile := profile)
    (ready := ready) selection paired
    (fun handle _ => congrArg (fun accepted => Stored.Endpoints.Core.childFromHistory accepted handle) reached.symm)
  exact ⟨leading, entered, silent, append (interleavingSteps between) path, aligned, kept ▸ reached⟩

theorem afterRefusal (request : CoreGiveRequest bindings finish)
    (embedder : base.embedder = (Stored.OwnedMemory.Claims.Core.Scheduled.host (grow := grow) bindings).embedder)
    {actions labels incoming outgoing} (between : JournalInterleaving profile ready base start incoming actions labels finish outgoing)
    (roots : incoming.writer.accepted = start.host.writer.accepted) {issue : Issue}
    (refused : Plain.runBody request.selectionProgram finish.store finish.host (some request.thread) =
      (finish.store, finish.host, .ok (.error issue))) :
    ∃ leftCount rightCount checked canonical,
      Steps profile ready (specDispatch ready base) start (labels ++ List.replicate leftCount .tau) checked ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) (HostFrame.replace start incoming)
        (labels ++ List.replicate rightCount .tau) canonical ∧
      HostFrame.Related.Paired (fun _ _ => False) checked canonical ∧
      canonical.host.writer.accepted = checked.host.writer.accepted := by
  have reached := interleavingRoots between roots
  have paired : HostFrame.Related.Paired (fun _ _ => False) finish (HostFrame.replace finish outgoing) :=
    sameFrames (HostFrame.replace finish outgoing)
  obtain ⟨leftCount, rightCount, checked, canonical, left, right, aligned, checkedHost, canonHost⟩ :=
    pairedAdmissionRefusal (base := base) (profile := profile) (ready := ready) request base embedder paired refused
      (fun handle _ => congrArg (fun accepted => Stored.Endpoints.Core.childFromHistory accepted handle) reached.symm)
  refine ⟨leftCount, rightCount, checked, canonical, append between.runs.1.steps left,
    append (interleavingSteps between) right, aligned, ?_⟩
  rw [checkedHost, canonHost]
  exact reached

theorem afterInterleaving (site : Site grow sig route) (linked : site.Linked bindings) {incoming outgoing : HostState sig}
    (selected : Stored.Endpoints.Core.childFromHistory outgoing.writer.accepted site.handle = some site.tree)
    {leading middleLabels actions}
    (prior : Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start leading
      (HostFrame.replace finish incoming))
    (between : JournalInterleaving profile ready base finish incoming actions middleLabels site.start outgoing) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start
        (leading ++ middleLabels ++ labels) (HostFrame.replace (site.reference site.referenceReply) outgoing) := by
  obtain ⟨labels, silent, entered⟩ := entry (profile := profile) (ready := ready) (base := base) site linked outgoing selected
  exact ⟨labels, silent, append (append prior (interleavingSteps between)) entered⟩

theorem afterSameRoots (site : Site grow sig route) (linked : site.Linked bindings) {incoming outgoing : HostState sig}
    (roots : incoming.writer.accepted = finish.host.writer.accepted) {leading middleLabels actions}
    (prior : Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start leading
      (HostFrame.replace finish incoming))
    (between : JournalInterleaving profile ready base finish incoming actions middleLabels site.start outgoing) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) start
        (leading ++ middleLabels ++ labels) (HostFrame.replace (site.reference site.referenceReply) outgoing) := by
  have selected : Stored.Endpoints.Core.childFromHistory outgoing.writer.accepted site.handle = some site.tree := by
    rw [interleavingRoots between roots]
    exact linked.selected
  exact afterInterleaving site linked selected prior between

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LiveDispatch
