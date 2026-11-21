module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs
public import Silmaril.Wasm.Component.Reference.HostWrite.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Plain.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Thms
public import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Defs
public import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Defs
public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms
import Silmaril.Wasm.Component.Reference.Canon.Callout.Thms

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core (Contract checkChildren)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Scheduled (nodeCall)
open Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst (NodeArgs)

theorem prepend_embedder_callout {E : CoreEngine} {Host : Type}
    [∀ left right, Decidable (E.ExternSub left right)]
    {ready : HostReady Host} {impl : HostImpl E Host} {profile : ProfileKind}
    {start final : Machine.Config E Host} {thread continuation}
    {core : E.Thread (CanonHost E)} {segments rest name type args labels}
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : E.status start.store.core core = .callout (.embedder name type) args)
    (tail : Machine.Steps profile ready (specDispatch ready impl)
      { start with ctl := ⟨thread, .prog (calloutBody Limits.spec Quirks.none ready impl
          start.store thread (.embedder name type) args),
        .core core continuation :: segments⟩ :: rest } labels final) :
    Machine.Steps profile ready (specDispatch ready impl) start
      (.tau :: .tau :: .tau :: labels) final := by
  exact .cons (.coreCallout parked calling) (.cons (.currentThread rfl) (.cons (.get rfl) tail))

theorem threadMayLeave_of_caller {E : CoreEngine} {store : CStore E} {thread : Option ThreadId}
    {inst : InstId} (caller : Plain.callerInstance store thread = .ok (some inst))
    (mayLeave : (store.inst? inst).any (·.mayLeave) = true) : threadMayLeave store thread = true := by
  cases thread with
  | none => cases caller
  | some id =>
    cases active : ArenaField.threads.get? store id with
    | none => simp [Plain.callerInstance, active] at caller
    | some activeThread =>
      cases task : ArenaField.tasks.get? store activeThread.task with
      | none => simp [Plain.callerInstance, active, task] at caller
      | some activeTask =>
        have computed : Plain.callerInstance store (some id) = .ok (some activeTask.inst) := by
          simp only [Plain.callerInstance, active, task]
          rfl
        rw [computed] at caller
        cases caller
        cases found : store.inst? activeTask.inst <;>
          simp_all [threadMayLeave, instOfThread?, instMayLeave]

theorem body_tracks_at {E : CoreEngine} {Host Result : Type} (body : P E Host Result)
    (start : Machine.Config E Host) (updated : CStore E) (host : Host) (result : Result)
    (finish : Result → P E Host (Ret E)) (thread : Option ThreadId)
    (segs : List (Machine.Seg E Host)) (rest : List (Machine.Activation E Host))
    (profile : ProfileKind) (ready : HostReady Host) (dispatch : Call E → P E Host (Ret E))
    (focused : start.ctl = ⟨thread, .prog (body >>= finish), segs⟩ :: rest)
    (activation : Option (Option ThreadId)) (matchesThread : activation = none ∨ activation = some thread)
    (success : Plain.runBody body start.store start.host activation = (updated, host, .ok result)) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Machine.ReturnFrame.Occurrence.RetainsActiveSlots profile ready dispatch start labels
        { start with store := updated, host, ctl := ⟨thread, .prog (finish result), segs⟩ :: rest } := by
  induction body generalizing start with
  | pure value =>
    simp only [Plain.runBody, Prod.mk.injEq, Except.ok.injEq] at success
    obtain ⟨store_eq, host_eq, result_eq⟩ := success
    subst updated host result
    have frame : { start with ctl := ⟨thread, .prog (finish value), segs⟩ :: rest } = start := by
      cases start
      congr
      exact focused.symm
    rw [frame]
    exact ⟨[], rfl, fun _ => .done _ _⟩
  | op op next ih =>
    cases op <;> try simp only [Plain.runBody] at success
    case get =>
      obtain ⟨labels, silent, tail⟩ := ih start.store
        { start with ctl := ⟨thread, .prog (next start.store >>= finish), segs⟩ :: rest } rfl success
      exact ⟨.tau :: labels, silent, fun depth => .step (.get focused)
        (by rw [Machine.ReturnFrame.Occurrence.transitionEdit, focused]; rfl) (tail depth)⟩
    case modify update =>
      obtain ⟨labels, silent, tail⟩ := ih ()
        { start with store := update start.store, ctl := ⟨thread, .prog (next () >>= finish), segs⟩ :: rest }
        rfl success
      exact ⟨.tau :: labels, silent, fun depth => .step (.modify focused)
        (by rw [Machine.ReturnFrame.Occurrence.transitionEdit, focused]; rfl) (tail depth)⟩
    case hostGet =>
      obtain ⟨labels, silent, tail⟩ := ih start.host
        { start with ctl := ⟨thread, .prog (next start.host >>= finish), segs⟩ :: rest } rfl success
      exact ⟨.tau :: labels, silent, fun depth => .step (.hostGet focused)
        (by rw [Machine.ReturnFrame.Occurrence.transitionEdit, focused]; rfl) (tail depth)⟩
    case hostSet newHost =>
      obtain ⟨labels, silent, tail⟩ := ih ()
        { start with host := newHost, ctl := ⟨thread, .prog (next () >>= finish), segs⟩ :: rest }
        rfl success
      exact ⟨.tau :: labels, silent, fun depth => .step (.hostSet focused)
        (by rw [Machine.ReturnFrame.Occurrence.transitionEdit, focused]; rfl) (tail depth)⟩
    case currentThread =>
      rcases matchesThread with missing | known
      · rw [missing] at success
        cases success
      · rw [known] at success
        obtain ⟨labels, silent, tail⟩ := ih thread
          { start with ctl := ⟨thread, .prog (next thread >>= finish), segs⟩ :: rest } rfl
          (by simpa only [Plain.runBody, known] using success)
        exact ⟨.tau :: labels, silent, fun depth => .step (.currentThread focused)
          (by rw [Machine.ReturnFrame.Occurrence.transitionEdit, focused]; rfl) (tail depth)⟩
    all_goals cases success

theorem body_steps_at {E : CoreEngine} {Host Result : Type} (body : P E Host Result)
    (start : Machine.Config E Host) (updated : CStore E) (host : Host) (result : Result)
    (finish : Result → P E Host (Ret E)) (thread : Option ThreadId)
    (segs : List (Machine.Seg E Host)) (rest : List (Machine.Activation E Host))
    (profile : ProfileKind) (ready : HostReady Host) (dispatch : Call E → P E Host (Ret E))
    (focused : start.ctl = ⟨thread, .prog (body >>= finish), segs⟩ :: rest)
    (activation : Option (Option ThreadId)) (matchesThread : activation = none ∨ activation = some thread)
    (success : Plain.runBody body start.store start.host activation = (updated, host, .ok result)) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Machine.Steps profile ready dispatch start labels
        { start with store := updated, host, ctl := ⟨thread, .prog (finish result), segs⟩ :: rest } := by
  obtain ⟨labels, silent, tracking⟩ := body_tracks_at body start updated host result finish thread segs rest
    profile ready dispatch focused activation matchesThread success
  exact ⟨labels, silent, (Machine.ReturnFrame.Occurrence.prefix_survives (tracking 0)).1⟩

theorem body_trap_steps {E : CoreEngine} {Host Result : Type} (body : P E Host Result)
    (start : Machine.Config E Host) (updated : CStore E) (host : Host) (reason : TrapReason)
    (finish : Result → P E Host (Ret E)) (thread : Option ThreadId)
    (segs : List (Machine.Seg E Host)) (rest : List (Machine.Activation E Host))
    (profile : ProfileKind) (ready : HostReady Host) (dispatch : Call E → P E Host (Ret E))
    (focused : start.ctl = ⟨thread, .prog (body >>= finish), segs⟩ :: rest)
    (failed : Plain.runBody body start.store start.host (some thread) = (updated, host, .error (.trapped reason))) :
    ∃ count, Machine.Steps profile ready dispatch start (List.replicate count .tau ++ [.trap reason])
      (Machine.StepDefs.trapCfg { start with store := updated, host }) := by
  induction body generalizing start with
  | pure _ => cases failed
  | op op next ih =>
    cases op <;> simp only [Plain.runBody] at failed
    case get =>
      obtain ⟨count, tail⟩ := ih start.store
        { start with ctl := ⟨thread, .prog (next start.store >>= finish), segs⟩ :: rest } rfl failed
      exact ⟨count + 1, .cons (.get focused) tail⟩
    case modify update =>
      obtain ⟨count, tail⟩ := ih ()
        { start with store := update start.store, ctl := ⟨thread, .prog (next () >>= finish), segs⟩ :: rest }
        rfl failed
      exact ⟨count + 1, .cons (.modify focused) tail⟩
    case hostGet =>
      obtain ⟨count, tail⟩ := ih start.host
        { start with ctl := ⟨thread, .prog (next start.host >>= finish), segs⟩ :: rest } rfl failed
      exact ⟨count + 1, .cons (.hostGet focused) tail⟩
    case hostSet newHost =>
      obtain ⟨count, tail⟩ := ih ()
        { start with host := newHost, ctl := ⟨thread, .prog (next () >>= finish), segs⟩ :: rest } rfl failed
      exact ⟨count + 1, .cons (.hostSet focused) tail⟩
    case currentThread =>
      obtain ⟨count, tail⟩ := ih thread
        { start with ctl := ⟨thread, .prog (next thread >>= finish), segs⟩ :: rest } rfl failed
      exact ⟨count + 1, .cons (.currentThread focused) tail⟩
    case trap actual =>
      cases failed
      exact ⟨0, .cons (.trap focused) (.refl _)⟩
    all_goals cases failed

private theorem read_thread {E : CoreEngine} {Host Result : Type}
    (next : Option ThreadId → P E Host Result) (store : CStore E) (host : Host)
    (thread : Option ThreadId) :
    Plain.runBody (currentThread.bind next) store host (some thread) =
      Plain.runBody (next thread) store host (some thread) := rfl

private theorem read_store {E : CoreEngine} {Host Result : Type}
    (next : CStore E → P E Host Result) (store : CStore E) (host : Host)
    (activation : Option (Option ThreadId)) :
    Plain.runBody (getStore.bind next) store host activation =
      Plain.runBody (next store) store host activation := rfl

theorem resolve_caller {E : CoreEngine} {Host Result : Type} (rest : Option InstId → P E Host Result)
    (reference : CStore E) (host : Host) (thread : Option ThreadId) :
    Plain.runBody (currentInst?.bind rest) reference host (some thread) =
      match Plain.callerInstance reference thread with
      | .ok caller => Plain.runBody (rest caller) reference host (some thread)
      | .error issue => (reference, host, .error issue) := by
  cases thread with
  | none => rfl
  | some thread =>
    simp only [currentInst?, currentTask?, Prog.bind_eq, Prog.bind_assoc, read_thread]
    cases active : ArenaField.threads.get? reference thread with
    | none =>
      simp only [getThread, getObj, Prog.bind_eq, Prog.bind_assoc, read_store, active,
        Plain.callerInstance]
      rfl
    | some activeThread =>
      cases task : ArenaField.tasks.get? reference activeThread.task <;>
        simp only [getThread, getTask, getObj, Prog.bind_eq, Prog.bind_assoc, read_store,
          active, task, Prog.pure_eq, Prog.pure_bind', Plain.callerInstance] <;> rfl

private theorem confined_read_thread {E : CoreEngine} {Host Result : Type}
    (next : Option ThreadId → P E Host Result) (store : CStore E) (host : Host)
    (thread : Option ThreadId) :
    Plain.runBody (confine (currentThread.bind next)) store host (some thread) =
      Plain.runBody (confine (next thread)) store host (some thread) := rfl

private theorem confined_read_store {E : CoreEngine} {Host Result : Type}
    (next : CStore E → P E Host Result) (store : CStore E) (host : Host)
    (activation : Option (Option ThreadId)) :
    Plain.runBody (confine (getStore.bind next)) store host activation =
      Plain.runBody (confine (next store)) store host activation := rfl

theorem resolve_caller_confined {E : CoreEngine} {Host Result : Type}
    (rest : Option InstId → P E Host Result)
    (reference : CStore E) (host : Host) (thread : Option ThreadId) :
    Plain.runBody (confine (currentInst?.bind rest)) reference host (some thread) =
      match Plain.callerInstance reference thread with
      | .ok caller => Plain.runBody (confine (rest caller)) reference host (some thread)
      | .error issue => (reference, host, .error issue) := by
  cases thread with
  | none => rfl
  | some thread =>
    simp only [currentInst?, currentTask?, Prog.bind_eq, Prog.bind_assoc, confined_read_thread]
    cases active : ArenaField.threads.get? reference thread with
    | none =>
      simp only [getThread, getObj, Prog.bind_eq, Prog.bind_assoc, confined_read_store, active,
        Plain.callerInstance]
      rfl
    | some activeThread =>
      cases task : ArenaField.tasks.get? reference activeThread.task <;>
        simp only [getThread, getTask, getObj, Prog.bind_eq, Prog.bind_assoc, confined_read_store,
          active, task, Prog.pure_eq, Prog.pure_bind', Plain.callerInstance] <;> rfl

theorem invoke_memory {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (ticket : Nat) (contract : Contract sig) (memory : Option Nat) (args : List FlatValue)
    (reference : CStore (core3 grow)) (host : HostState sig) (thread : Option ThreadId) :
    let binding : Binding sig := ⟨contract.name.2, contract.inst, .accept contract memory⟩
    Plain.runBody (do finish ticket (← Claims.Core.Scheduled.invoke ticket binding args)) reference host (some thread) =
      match Plain.callerInstance reference thread with
      | .error issue => (reference, host, .error issue)
      | .ok caller =>
        if caller = some contract.inst ∧ (reference.inst? contract.inst).any (·.mayLeave) then
          Plain.runBody (do finish ticket (← accept ticket contract memory args)) reference host (some thread)
        else
          (reference, host.record (.refused ticket .wrongContext), .ok [i32Flat 1, i32Flat 0]) := by
  dsimp only
  simp only [Claims.Core.Scheduled.invoke, Prog.bind_eq, Prog.bind_assoc]
  rw [resolve_caller]
  cases evaluated : Plain.callerInstance reference thread with
  | error _ => rfl
  | ok caller =>
    by_cases same : caller = some contract.inst
    · subst caller
      simp [read_store]
      cases (reference.inst? contract.inst).any (·.mayLeave) with
      | false => rfl
      | true => rfl
    · simp [same, bne_iff_ne, read_store]
      rfl

theorem embedder_memory {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (contract : Contract sig) (memory : Option Nat) (args : List FlatValue)
    (reference : CStore (core3 grow)) (state : HostState sig) (thread : Option ThreadId)
    (linked : resolveBinding bindings name type = .ok ⟨contract.name.2, contract.inst, .accept contract memory⟩) :
    let entered := state.enter name type args
    let ticket := state.nextTicket
    Plain.runBody ((Claims.Core.Scheduled.host bindings).embedder name type args) reference state (some thread) =
      match Plain.callerInstance reference thread with
      | .error issue => (reference, entered, .error issue)
      | .ok caller =>
        if caller = some contract.inst ∧ (reference.inst? contract.inst).any (·.mayLeave) then
          Plain.runBody (do finish ticket (← accept ticket contract memory args)) reference entered (some thread)
        else (reference, entered.record (.refused ticket .wrongContext), .ok [i32Flat 1, i32Flat 0]) := by
  dsimp only
  change Plain.runBody (route state.nextTicket bindings name type args) reference
    (state.enter name type args) (some thread) = _
  simp only [route, linked]
  exact invoke_memory state.nextTicket contract memory args reference (state.enter name type args) thread

private theorem embedder_caller_refused_confined {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (contract : Contract sig) (memory : Option Nat) (args : List FlatValue)
    (reference : CStore (core3 grow)) (state : HostState sig) (thread : Option ThreadId)
    (linked : resolveBinding bindings name type = .ok ⟨contract.name.2, contract.inst, .accept contract memory⟩)
    (caller : Option InstId) (resolved : Plain.callerInstance reference thread = .ok caller)
    (refused : ¬(caller = some contract.inst ∧ (reference.inst? contract.inst).any (·.mayLeave))) :
    Plain.runBody (confine ((Claims.Core.Scheduled.host bindings).embedder name type args))
        reference state (some thread) =
      (reference, (state.enter name type args).record (.refused state.nextTicket .wrongContext),
        .ok [i32Flat 1, i32Flat 0]) := by
  change Plain.runBody (confine (route state.nextTicket bindings name type args)) reference
    (state.enter name type args) (some thread) = _
  simp only [route, linked, Claims.Core.Scheduled.invoke, Prog.bind_eq, Prog.bind_assoc]
  rw [resolve_caller_confined, resolved]
  by_cases same : caller = some contract.inst
  · subst caller
    have blocked : (reference.inst? contract.inst).any (·.mayLeave) = false := by
      cases flag : (reference.inst? contract.inst).any (·.mayLeave) <;> simp_all
    simp [confined_read_store, blocked]
    rfl
  · simp [same, bne_iff_ne, confined_read_store]
    rfl

theorem embedder_unresolved {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig)) (name : String) (type : V1.FuncType) (args : List FlatValue)
    (reference : CStore (core3 grow)) (state : HostState sig) (thread : Option ThreadId)
    (issue : Claims.Core.Scheduled.Issue)
    (unresolved : resolveBinding bindings name type = .error issue) :
    Plain.runBody ((Claims.Core.Scheduled.host bindings).embedder name type args) reference state (some thread) =
      (reference, (state.enter name type args).record (.bindingTrap state.nextTicket issue),
        .error (.trapped (.hostTrap "invalid mixed acceptor import binding"))) := by
  change Plain.runBody (route state.nextTicket bindings name type args) reference
    (state.enter name type args) (some thread) = _
  simp only [route, unresolved]
  rfl

theorem embedder_unresolved_confined {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig)) (name : String) (type : V1.FuncType) (args : List FlatValue)
    (reference : CStore (core3 grow)) (state : HostState sig) (thread : Option ThreadId)
    (issue : Claims.Core.Scheduled.Issue)
    (unresolved : resolveBinding bindings name type = .error issue) :
    Plain.runBody (confine ((Claims.Core.Scheduled.host bindings).embedder name type args))
        reference state (some thread) =
      (reference, (state.enter name type args).record (.bindingTrap state.nextTicket issue),
        .error (.trapped (.hostTrap "invalid mixed acceptor import binding"))) := by
  change Plain.runBody (confine (route state.nextTicket bindings name type args)) reference
    (state.enter name type args) (some thread) = _
  simp only [route, unresolved]
  rfl

private theorem bind_ok {Error Input Output : Type} {input : Except Error Input}
    {next : Input → Except Error Output} {output : Output} (success : input >>= next = .ok output) :
    ∃ value, input = .ok value ∧ next value = .ok output := by
  cases input with
  | error _ => cases success
  | ok value => exact ⟨value, rfl, success⟩

private theorem children_room {sig : Signature} (tag : sig.Tag) (length pointer count : Nat)
    (success : checkChildren sig tag length pointer count = .ok ()) : length + 1 < 2 ^ 32 := by
  unfold checkChildren at success
  dsimp only at success
  by_contra! exhausted
  split at success <;> try cases success
  split at success <;> try cases success
  split at success <;> cases success

private theorem preflight_room {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (contract : Contract sig) (memory : Option Nat) (world : Claims.Core.World grow sig) (call : UCall Nat)
    {operands : NodeArgs sig.Tag × List (Tree sig)}
    (success : Claims.Core.preflight contract memory world call = .ok operands) :
    world.writer.accepted.length + 1 < 2 ^ 32 := by
  unfold Claims.Core.preflight at success
  dsimp only at success
  split at success
  · cases success
  generalize checked_eq : contract.preflightOperands checkSchema memory world.writer.accepted call = checked at success
  cases checked with
  | error _ => cases success
  | ok result =>
    unfold Contract.preflightOperands at checked_eq
    obtain ⟨_, _, checked_eq⟩ := bind_ok checked_eq
    obtain ⟨_, _, checked_eq⟩ := bind_ok checked_eq
    obtain ⟨_, _, checked_eq⟩ := bind_ok checked_eq
    obtain ⟨_, _, checked_eq⟩ := bind_ok checked_eq
    obtain ⟨_, _, checked_eq⟩ := bind_ok checked_eq
    obtain ⟨_, _, checked_eq⟩ := bind_ok checked_eq
    obtain ⟨_, room, _⟩ := bind_ok checked_eq
    exact children_room _ _ _ _ room

private theorem load_room {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (contract : Contract sig) (memory : Option Nat) (world : Claims.Core.World grow sig) (call : UCall Nat)
    {store : CStore (core3 grow)} {tree : Tree sig}
    (success : Claims.Core.load contract memory world call = (store, .ok tree)) :
    world.writer.accepted.length + 1 < 2 ^ 32 := by
  unfold Claims.Core.load at success
  split at success
  next => cases success
  next checked => exact preflight_room contract memory world call checked

private theorem register_length {sig : Signature} {before after : Claims.State sig} {tree : Tree sig}
    (success : before.register tree = .ok after) : after.accepted.length = before.accepted.length + 1 := by
  unfold Claims.State.register at success
  dsimp only at success
  split at success
  · cases success
    rfl
  · cases success

theorem body {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (ticket : Nat) (contract : Contract sig) (memory : Option Nat) (args : List FlatValue)
    (reference : CStore (core3 grow)) (host : HostState sig)
    (activation : Option (Option ThreadId) := none) :
    let call := nodeCall contract reference args
    let attempt := Claims.Core.attempt contract memory ⟨reference, host.writer⟩ call
    let state : HostState sig := { host with writer := attempt.1.writer }
    let reply := match attempt.2 with
      | .ok handle => (state.record (.published ticket handle.toNat), completion ticket (.ok handle.toNat))
      | .error issue => (state, completion ticket (.error (.accept issue)))
    Plain.runBody (do finish ticket (← accept ticket contract memory args)) reference host activation =
      (attempt.1.reference, reply.1.record reply.2.1, .ok reply.2.2) := by
  dsimp only
  unfold Claims.Core.attempt
  change Plain.runBody
      ((match (Claims.Core.load contract memory ⟨reference, host.writer⟩
          (nodeCall contract reference args)).2 with
        | .error issue => pure (.error (.accept issue))
        | .ok tree => publishRoot ticket tree) >>= finish ticket)
      (Claims.Core.load contract memory ⟨reference, host.writer⟩
        (nodeCall contract reference args)).1 host activation = _
  generalize loaded : Claims.Core.load contract memory ⟨reference, host.writer⟩
    (nodeCall contract reference args) = lifted
  obtain ⟨updated, result⟩ := lifted
  cases result with
  | error _ => rfl
  | ok tree =>
    have room := load_room contract memory ⟨reference, host.writer⟩ _ loaded
    change Plain.runBody
        ((match host.writer.register tree with
          | .error issue => pure (.error (.accept (.claims issue)))
          | .ok writer =>
            if writer.accepted.length ≥ 2 ^ 32 then pure (.error (.accept (.boundary .exhaustedHandles)))
            else do
              hostSet (({ host with writer } : HostState sig).record (.published ticket writer.accepted.length))
              pure (.ok writer.accepted.length)) >>= finish ticket) updated host activation = _
    dsimp only [Except.bind]
    generalize registered : host.writer.register tree = registration
    cases registration with
    | error _ => rfl
    | ok writer =>
      have fits : writer.accepted.length < 2 ^ 32 := (register_length registered).symm ▸ room
      have handle : (BitVec.ofNat 32 writer.accepted.length).toNat = writer.accepted.length :=
        Nat.mod_eq_of_lt fits
      simp only [Except.mapError, handle, Nat.not_le.mpr fits, ite_false]
      rfl

theorem memory_plain (sig : PlainSignature) {grow : SingleThreaded.GrowOracle}
    (ticket : Nat) (contract : Contract sig.val) (memory : Option Nat) (args : List FlatValue)
    (reference : CStore (core3 grow)) (oldHost : Stored.Endpoints.Core.Scheduled.HostState sig.val)
    (journal : HostState sig.val)
    (writer : journal.writer = (Claims.Core.Plain.embedWorld sig (⟨reference, oldHost.writer⟩ :
      Stored.Endpoints.Core.World grow sig.val)).writer)
    (activation : Option (Option ThreadId) := none) :
    let old := Stored.Endpoints.Core.Scheduled.acceptAttempt contract memory oldHost reference args
    let new := Plain.runBody (do finish ticket (← accept ticket contract memory args)) reference journal activation
    let refused := new.2.1.newestFirst.head?.bind fun event => match event with
      | .refused _ issue => Plain.oldIssue issue
      | _ => none
    new.1 = old.1 ∧
      new.2.1.writer = (Claims.Core.Plain.embedWorld sig (⟨old.1, old.2.1.writer⟩ :
        Stored.Endpoints.Core.World grow sig.val)).writer ∧
      new.2.2 = .ok old.2.2 ∧ old.2.1.refusals = refused.toList ++ oldHost.refusals := by
  dsimp only
  rw [body ticket contract memory args reference journal activation]
  rw [writer]
  have agreed := Claims.Core.Plain.attempt_plain sig contract memory
    (⟨reference, oldHost.writer⟩ : Stored.Endpoints.Core.World grow sig.val) (nodeCall contract reference args)
  dsimp only at agreed
  unfold Stored.Endpoints.Core.Scheduled.acceptAttempt
  generalize old_eq : contract.attempt memory ⟨reference, oldHost.writer⟩
    (nodeCall contract reference args) = old at agreed ⊢
  generalize new_eq : Claims.Core.attempt contract memory
    (Claims.Core.Plain.embedWorld sig (⟨reference, oldHost.writer⟩ : Stored.Endpoints.Core.World grow sig.val))
    (nodeCall contract reference args) = new at agreed
  have new_eq_body : Claims.Core.attempt contract memory
      ⟨reference, (Claims.Core.Plain.embedWorld sig (⟨reference, oldHost.writer⟩ :
        Stored.Endpoints.Core.World grow sig.val)).writer⟩ (nodeCall contract reference args) = new := new_eq
  rw [new_eq_body]
  obtain ⟨oldWorld, oldResult⟩ := old
  obtain ⟨newWorld, newResult⟩ := new
  obtain ⟨frame, result⟩ := agreed
  dsimp only at frame result
  subst newWorld
  cases oldResult <;> cases newResult
  case error.error oldReason newReason =>
    have reason : Claims.Core.Plain.oldIssue newReason = some oldReason := Except.error.inj result
    simp [Stored.Endpoints.Core.Scheduled.HostState.finish, Except.mapError, Except.map,
      Claims.Core.Plain.embedWorld, completion, HostState.record, Plain.oldIssue, reason]
  case error.ok => cases result
  case ok.error => cases result
  case ok.ok oldHandle newHandle =>
    have handle : newHandle = oldHandle := Except.ok.inj result
    subst newHandle
    simp [Stored.Endpoints.Core.Scheduled.HostState.finish, Except.mapError, Except.map,
      Claims.Core.Plain.embedWorld, completion, HostState.record]

theorem embedder_admitted_plain (sig : PlainSignature) {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig.val)) (name : String) (type : V1.FuncType)
    (contract : Contract sig.val) (memory : Option Nat) (args : List FlatValue)
    (reference : CStore (core3 grow)) (oldHost : Stored.Endpoints.Core.Scheduled.HostState sig.val)
    (state : HostState sig.val) (thread : Option ThreadId)
    (linked : resolveBinding bindings name type = .ok ⟨contract.name.2, contract.inst, .accept contract memory⟩)
    (caller : Plain.callerInstance reference thread = .ok (some contract.inst))
    (mayLeave : (reference.inst? contract.inst).any (·.mayLeave) = true)
    (writer : state.writer = (Claims.Core.Plain.embedWorld sig (⟨reference, oldHost.writer⟩ :
      Stored.Endpoints.Core.World grow sig.val)).writer) :
    let old := Stored.Endpoints.Core.Scheduled.acceptAttempt contract memory oldHost reference args
    let new := Plain.runBody ((Claims.Core.Scheduled.host bindings).embedder name type args)
      reference state (some thread)
    let refused := new.2.1.newestFirst.head?.bind fun event => match event with
      | .refused _ issue => Plain.oldIssue issue
      | _ => none
    new.1 = old.1 ∧
      new.2.1.writer = (Claims.Core.Plain.embedWorld sig (⟨old.1, old.2.1.writer⟩ :
        Stored.Endpoints.Core.World grow sig.val)).writer ∧
      new.2.2 = .ok old.2.2 ∧ old.2.1.refusals = refused.toList ++ oldHost.refusals := by
  dsimp only
  rw [embedder_memory bindings name type contract memory args reference state thread linked, caller]
  simp only [mayLeave, eq_self, and_self, ite_true]
  exact memory_plain sig state.nextTicket contract memory args reference oldHost
    (state.enter name type args) writer (some thread)

private theorem embedder_admitted_publications {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (contract : Contract sig) (memory : Option Nat) (args : List FlatValue)
    (reference : CStore (core3 grow)) (state : HostState sig) (thread : Option ThreadId)
    (linked : resolveBinding bindings name type = .ok ⟨contract.name.2, contract.inst, .accept contract memory⟩)
    (caller : Plain.callerInstance reference thread = .ok (some contract.inst))
    (mayLeave : (reference.inst? contract.inst).any (·.mayLeave) = true) :
    let attempt := Claims.Core.attempt contract memory ⟨reference, state.writer⟩ (nodeCall contract reference args)
    (Plain.runBody ((host (grow := grow) bindings).embedder name type args)
      reference state (some thread)).2.1.publications = state.publications ++
        (attempt.2.toOption.map fun handle => (state.nextTicket, handle.toNat)).toList := by
  intro attempt
  rw [embedder_memory bindings name type contract memory args reference state thread linked, caller]
  simp only [mayLeave, eq_self, and_self, ite_true]
  rw [body state.nextTicket contract memory args reference (state.enter name type args) (some thread)]
  change (let next : HostState sig := { state.enter name type args with writer := attempt.1.writer }
    let reply := match attempt.2 with
      | .ok handle => (next.record (.published state.nextTicket handle.toNat), completion state.nextTicket (.ok handle.toNat))
      | .error issue => (next, completion state.nextTicket (.error (.accept issue)))
    (reply.1.record reply.2.1).publications) = _
  cases attempt.2 <;> simp [completion, HostState.publications, HostState.transcript, HostState.record,
    HostState.enter, Event.publication, List.reverse_cons, List.filterMap_append, List.append_assoc] <;> rfl

theorem embedder_admitted_plain_steps (sig : PlainSignature) {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig.val)) (name : String) (type : V1.FuncType)
    (contract : Contract sig.val) (memory : Option Nat) (args : List FlatValue)
    (start : Machine.Config (core3 grow) (HostState sig.val))
    (oldHost : Stored.Endpoints.Core.Scheduled.HostState sig.val) (thread : Option ThreadId)
    (segments : List (Machine.Seg (core3 grow) (HostState sig.val)))
    (rest : List (Machine.Activation (core3 grow) (HostState sig.val)))
    (profile : ProfileKind) (ready : HostReady (HostState sig.val))
    (focused : start.ctl = ⟨thread, .prog (.flat <$> (host (grow := grow) bindings).embedder name type args),
      segments⟩ :: rest)
    (linked : resolveBinding bindings name type = .ok ⟨contract.name.2, contract.inst, .accept contract memory⟩)
    (caller : Plain.callerInstance start.store thread = .ok (some contract.inst))
    (mayLeave : (start.store.inst? contract.inst).any (·.mayLeave) = true)
    (writer : start.host.writer = (Claims.Core.Plain.embedWorld sig (⟨start.store, oldHost.writer⟩ :
      Stored.Endpoints.Core.World grow sig.val)).writer) :
    let old := Stored.Endpoints.Core.Scheduled.acceptAttempt contract memory oldHost start.store args
    ∃ (labels : List (Machine.Label (core3 grow) (HostState sig.val))) (reached : HostState sig.val),
      (∀ label ∈ labels, label = .tau) ∧
      Machine.Steps profile ready (specDispatch ready (host (grow := grow) bindings)) start labels
        { start with
          store := old.1
          host := reached
          ctl := ⟨thread, .prog (.pure (.flat old.2.2)), segments⟩ :: rest } ∧
      reached.writer = (Claims.Core.Plain.embedWorld sig (⟨old.1, old.2.1.writer⟩ :
        Stored.Endpoints.Core.World grow sig.val)).writer ∧
      old.2.1.refusals = (reached.newestFirst.head?.bind fun event => match event with
        | .refused _ issue => Plain.oldIssue issue
        | _ => none).toList ++ oldHost.refusals ∧
      reached.publications = start.host.publications ++
        ((Claims.Core.attempt contract memory ⟨start.store, start.host.writer⟩
          (nodeCall contract start.store args)).2.toOption.map
            fun handle => (start.host.nextTicket, handle.toNat)).toList := by
  intro old
  let program := (host (grow := grow) bindings).embedder name type args
  let reached := Plain.runBody program start.store start.host (some thread)
  have agreed := embedder_admitted_plain sig bindings name type contract memory args start.store
    oldHost start.host thread linked caller mayLeave writer
  change reached.1 = old.1 ∧ _ ∧ reached.2.2 = .ok old.2.2 ∧ _ at agreed
  have ran : Plain.runBody program start.store start.host (some thread) = (old.1, reached.2.1, .ok old.2.2) := by
    change reached = _
    rw [← agreed.1, ← agreed.2.2.1]
  obtain ⟨labels, silent, steps⟩ := body_steps_at program start old.1 reached.2.1 old.2.2
    (fun words => .pure (.flat words)) thread segments rest profile ready
    (specDispatch ready (host (grow := grow) bindings))
    focused (some thread) (.inr rfl) ran
  refine ⟨labels, reached.2.1, ?_, steps, agreed.2.1, agreed.2.2.2,
    embedder_admitted_publications bindings name type contract memory args start.store start.host thread
      linked caller mayLeave⟩
  intro label member
  have tau := List.all_eq_true.mp silent label member
  cases label <;> first | rfl | contradiction

private theorem steps_then_step {E : CoreEngine} {Host : Type} {profile : ProfileKind}
    {ready : HostReady Host} {dispatch : Call E → P E Host (Ret E)}
    {start middle final : Machine.Config E Host} {labels label}
    (prefixSteps : Machine.Steps profile ready dispatch start labels middle)
    (last : Machine.Step profile ready dispatch middle label final) :
    Machine.Steps profile ready dispatch start (labels ++ [label]) final := by
  induction prefixSteps with
  | refl => exact .cons last (.refl _)
  | cons step _ ih => exact .cons step (ih last)

theorem parked_admitted_plain_steps (sig : PlainSignature) {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig.val)) (name : String) (type : V1.FuncType)
    (contract : Contract sig.val) (memory : Option Nat) (args : List FlatValue)
    (start : Machine.Config (core3 grow) (HostState sig.val))
    (oldHost : Stored.Endpoints.Core.Scheduled.HostState sig.val) (thread : Option ThreadId)
    (profile : ProfileKind) (ready : HostReady (HostState sig.val))
    {core continuation segments rest}
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) args)
    (linked : resolveBinding bindings name type = .ok ⟨contract.name.2, contract.inst, .accept contract memory⟩)
    (caller : Plain.callerInstance start.store thread = .ok (some contract.inst))
    (mayLeave : (start.store.inst? contract.inst).any (·.mayLeave) = true)
    (writer : start.host.writer = (Claims.Core.Plain.embedWorld sig (⟨start.store, oldHost.writer⟩ :
        Stored.Endpoints.Core.World grow sig.val)).writer) :
    let old := Stored.Endpoints.Core.Scheduled.acceptAttempt contract memory oldHost start.store args
    let attempt := Claims.Core.attempt contract memory ⟨start.store, start.host.writer⟩ (nodeCall contract start.store args)
    ∃ (labels : List (Machine.Label (core3 grow) (HostState sig.val))) (reached : HostState sig.val),
      (∀ label ∈ labels, label = .tau) ∧
      Machine.Steps profile ready (specDispatch ready (host (grow := grow) bindings)) start labels
        { start with
          store := old.1
          host := reached
          ctl := ⟨thread, .core ((core3 grow).resume old.1.core core (.values old.2.2)) continuation,
            segments⟩ :: rest } ∧
      reached.writer = (Claims.Core.Plain.embedWorld sig (⟨old.1, old.2.1.writer⟩ :
        Stored.Endpoints.Core.World grow sig.val)).writer ∧
      old.2.1.refusals = (reached.newestFirst.head?.bind fun event => match event with
        | .refused _ issue => Plain.oldIssue issue
        | _ => none).toList ++ oldHost.refusals ∧
      reached.publications = start.host.publications ++
        (attempt.2.toOption.map fun handle => (start.host.nextTicket, handle.toNat)).toList ∧
      ∀ handle, attempt.2 = .ok handle → Machine.CfgSafe CheckedWrite start →
        ∃ tree, reached.writer.accepted = tree :: start.host.writer.accepted ∧
          Stored.Endpoints.Core.childFromHistory reached.writer.accepted handle = some tree := by
  intro old attempt
  let body := calloutBody Limits.spec Quirks.none ready (host (grow := grow) bindings)
    start.store thread (.embedder name type) args
  let focused := { start with ctl := ⟨thread, .prog body, .core core continuation :: segments⟩ :: rest }
  have leaves := threadMayLeave_of_caller caller mayLeave
  have entered : focused.ctl = ⟨thread, .prog (.flat <$> (host (grow := grow) bindings).embedder name type args),
      .core core continuation :: segments⟩ :: rest := by
    simp only [focused, body, calloutBody, leaves, ite_true]
    rfl
  obtain ⟨labels, reached, silent, steps, keptWriter, refusals, publications⟩ :=
    embedder_admitted_plain_steps sig bindings name type contract memory args focused oldHost thread
      (.core core continuation :: segments) rest profile ready entered linked caller mayLeave writer
  have full := prepend_embedder_callout (impl := host (grow := grow) bindings) parked calling steps
  have silentFull : ∀ label ∈ (.tau :: .tau :: .tau :: labels) ++ [.tau], label = .tau := by
    intro label member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with ((rfl | rfl | rfl | member) | rfl)
    all_goals first | rfl | exact silent label member
  have resumed := steps_then_step full (.popCore rfl)
  refine ⟨_, reached, silentFull, resumed, keptWriter, refusals, publications, ?_⟩
  intro handle accepted safe
  have recorded : reached.publications = start.host.publications ++ [(start.host.nextTicket, handle.toNat)] := by
    change reached.publications = start.host.publications ++
      (attempt.2.toOption.map fun value => (start.host.nextTicket, value.toNat)).toList at publications
    rw [accepted] at publications
    exact publications
  obtain ⟨tree, roots, _, lookup, _⟩ := single_publication_survives bindings resumed (.refl _) safe
    (fun event member => by cases silentFull _ member) (fun _ member => False.elim (List.not_mem_nil member)) recorded
  exact ⟨tree, roots, by simpa using lookup⟩

theorem parked_binding_trap_steps {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig)) (name : String) (type : V1.FuncType) (args : List FlatValue)
    (start : Machine.Config (core3 grow) (HostState sig)) (thread : Option ThreadId)
    (profile : ProfileKind) (ready : HostReady (HostState sig)) (issue : Claims.Core.Scheduled.Issue)
    {core continuation segments rest}
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) args)
    (unresolved : resolveBinding bindings name type = .error issue) :
    let reached := (start.host.enter name type args).record (.bindingTrap start.host.nextTicket issue)
    let reason := TrapReason.hostTrap "invalid mixed acceptor import binding"
    ∃ count, Machine.Steps profile ready (specDispatch ready (host (grow := grow) bindings)) start
      (List.replicate count .tau ++ [.trap reason]) (Machine.StepDefs.trapCfg { start with host := reached }) := by
  intro reached reason
  let impl := host (grow := grow) bindings
  let program := if threadMayLeave start.store thread then impl.embedder name type args
    else confine (impl.embedder name type args)
  let focused := { start with ctl := ⟨thread, .prog (calloutBody Limits.spec Quirks.none ready impl
    start.store thread (.embedder name type) args), .core core continuation :: segments⟩ :: rest }
  have evaluated : Plain.runBody program start.store start.host (some thread) =
      (start.store, reached, .error (.trapped reason)) := by
    by_cases leaves : threadMayLeave start.store thread = true
    · simpa only [program, ite_eq_left leaves] using
        embedder_unresolved bindings name type args start.store start.host thread issue unresolved
    · simpa only [program, ite_eq_right leaves] using
        embedder_unresolved_confined bindings name type args start.store start.host thread issue unresolved
  have entered : focused.ctl = ⟨thread, .prog (program >>= fun words => .pure (.flat words)),
      .core core continuation :: segments⟩ :: rest := by
    by_cases leaves : threadMayLeave start.store thread = true
    · simp only [focused, calloutBody, program, ite_eq_left leaves]
      rfl
    · simp only [focused, calloutBody, program, ite_eq_right leaves]
      rfl
  obtain ⟨count, steps⟩ := body_trap_steps program focused start.store reached reason
    (fun words => .pure (.flat words)) thread (.core core continuation :: segments) rest profile ready
    (specDispatch ready impl) entered evaluated
  exact ⟨count + 3, prepend_embedder_callout (impl := impl) parked calling steps⟩

theorem parked_caller_refusal_steps {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (contract : Contract sig) (memory : Option Nat) (args : List FlatValue)
    (start : Machine.Config (core3 grow) (HostState sig)) (thread : Option ThreadId)
    (profile : ProfileKind) (ready : HostReady (HostState sig))
    {core continuation segments rest}
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) args)
    (linked : resolveBinding bindings name type = .ok ⟨contract.name.2, contract.inst, .accept contract memory⟩)
    (caller : Option InstId) (resolved : Plain.callerInstance start.store thread = .ok caller)
    (refused : ¬(caller = some contract.inst ∧ (start.store.inst? contract.inst).any (·.mayLeave))) :
    let reached := (start.host.enter name type args).record (.refused start.host.nextTicket .wrongContext)
    ∃ (labels : List (Machine.Label (core3 grow) (HostState sig))),
      (∀ label ∈ labels, label = .tau) ∧
      Machine.Steps profile ready (specDispatch ready (host (grow := grow) bindings)) start labels
        { start with
          host := reached
          ctl := ⟨thread, .core ((core3 grow).resume start.store.core core (.values [i32Flat 1, i32Flat 0]))
            continuation, segments⟩ :: rest } ∧
      reached.writer = start.host.writer ∧ reached.publications = start.host.publications := by
  intro reached
  let impl := host (grow := grow) bindings
  let program := if threadMayLeave start.store thread then impl.embedder name type args
    else confine (impl.embedder name type args)
  let focused := { start with ctl := ⟨thread, .prog (calloutBody Limits.spec Quirks.none ready impl
    start.store thread (.embedder name type) args), .core core continuation :: segments⟩ :: rest }
  have evaluated : Plain.runBody program start.store start.host (some thread) =
      (start.store, reached, .ok [i32Flat 1, i32Flat 0]) := by
    by_cases leaves : threadMayLeave start.store thread = true
    · simp only [program, ite_eq_left leaves, impl]
      rw [embedder_memory bindings name type contract memory args start.store start.host thread linked, resolved]
      simp [refused, reached]
    · simpa only [program, ite_eq_right leaves] using
        embedder_caller_refused_confined bindings name type contract memory args start.store start.host
          thread linked caller resolved refused
  have entered : focused.ctl = ⟨thread, .prog (program >>= fun words => .pure (.flat words)),
      .core core continuation :: segments⟩ :: rest := by
    by_cases leaves : threadMayLeave start.store thread = true
    · simp only [focused, calloutBody, program, ite_eq_left leaves]
      rfl
    · simp only [focused, calloutBody, program, ite_eq_right leaves]
      rfl
  obtain ⟨labels, silent, steps⟩ := body_steps_at program focused start.store reached [i32Flat 1, i32Flat 0]
    (fun words => .pure (.flat words)) thread (.core core continuation :: segments) rest profile ready
    (specDispatch ready impl) entered (some thread) (.inr rfl) evaluated
  have full := prepend_embedder_callout (impl := impl) parked calling steps
  refine ⟨(.tau :: .tau :: .tau :: labels) ++ [.tau], ?_, steps_then_step full (.popCore rfl), rfl, ?_⟩
  · intro label member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with ((rfl | rfl | rfl | member) | rfl)
    all_goals try rfl
    have tau := List.all_eq_true.mp silent label member
    cases label <;> first | rfl | contradiction
  · simp [reached, HostState.publications, HostState.transcript, HostState.record, HostState.enter,
      Event.publication]

theorem embedder_caller_refusal_steps {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig)) (name : String) (type : V1.FuncType)
    (contract : Contract sig) (memory : Option Nat) (args : List FlatValue)
    (start : Machine.Config (core3 grow) (HostState sig)) (thread : Option ThreadId)
    (segments : List (Machine.Seg (core3 grow) (HostState sig)))
    (rest : List (Machine.Activation (core3 grow) (HostState sig)))
    (profile : ProfileKind) (ready : HostReady (HostState sig))
    (focused : start.ctl = ⟨thread, .prog (.flat <$> (host (grow := grow) bindings).embedder name type args),
      segments⟩ :: rest)
    (linked : resolveBinding bindings name type = .ok ⟨contract.name.2, contract.inst, .accept contract memory⟩)
    (caller : Option InstId) (resolved : Plain.callerInstance start.store thread = .ok caller)
    (refused : ¬(caller = some contract.inst ∧ (start.store.inst? contract.inst).any (·.mayLeave))) :
    let reached := (start.host.enter name type args).record (.refused start.host.nextTicket .wrongContext)
    ∃ (labels : List (Machine.Label (core3 grow) (HostState sig))),
      (∀ label ∈ labels, label = .tau) ∧
      Machine.Steps profile ready (specDispatch ready (host (grow := grow) bindings)) start labels
        { start with
          host := reached
          ctl := ⟨thread, .prog (.pure (.flat [i32Flat 1, i32Flat 0])), segments⟩ :: rest } ∧
      reached.writer = start.host.writer ∧ reached.publications = start.host.publications := by
  intro reached
  have ran : Plain.runBody ((host (grow := grow) bindings).embedder name type args) start.store start.host
      (some thread) =
      (start.store, reached, .ok [i32Flat 1, i32Flat 0]) := by
    rw [embedder_memory bindings name type contract memory args start.store start.host thread linked, resolved]
    simp [refused, reached]
  obtain ⟨labels, silent, steps⟩ := body_steps_at ((host (grow := grow) bindings).embedder name type args)
    start start.store reached [i32Flat 1, i32Flat 0] (fun words => .pure (.flat words))
    thread segments rest profile ready (specDispatch ready (host (grow := grow) bindings)) focused
    (some thread) (.inr rfl) ran
  refine ⟨labels, ?_, steps, rfl, ?_⟩
  · intro label member
    have tau := List.all_eq_true.mp silent label member
    cases label <;> first | rfl | contradiction
  · simp [reached, HostState.publications, HostState.transcript, HostState.record, HostState.enter,
      Event.publication]

theorem closed_thread {E : CoreEngine} {store : CStore E} {thread : Option ThreadId}
    {inst : InstId} {entry : InstState}
    (caller : Plain.callerInstance store thread = .ok (some inst))
    (live : store.inst? inst = some entry) (closed : entry.mayLeave = false) :
    threadMayLeave store thread = false := by
  cases thread with
  | none => cases caller
  | some id =>
    cases active : ArenaField.threads.get? store id with
    | none => simp [Plain.callerInstance, active] at caller
    | some activeThread =>
      cases task : ArenaField.tasks.get? store activeThread.task with
      | none => simp [Plain.callerInstance, active, task] at caller
      | some activeTask =>
        have computed : Plain.callerInstance store (some id) = .ok (some activeTask.inst) := by
          simp only [Plain.callerInstance, active, task]
          rfl
        rw [computed] at caller
        cases caller
        simp [threadMayLeave, instOfThread?, instMayLeave, active, task, live, closed]

private theorem confined_give_refusal {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig)) (name : String) (type : V1.FuncType) (args : List FlatValue)
    (inst : InstId) (destination : RecordDestination) (schema : Option Stored.TypeOf)
    (reference : CStore (core3 grow)) (state : HostState sig) (thread : Option ThreadId)
    (linked : resolveBinding bindings name type = .ok ⟨name, inst,
      schema.elim (.givePayload destination) (.giveFlat destination)⟩)
    (caller : Plain.callerInstance reference thread = .ok (some inst))
    (blocked : (reference.inst? inst).any (·.mayLeave) = false) :
    let reply := schema.elim (completion state.nextTicket (.error .wrongContext))
      (fun payload => flatCompletion state.nextTicket (ABI.flatten destination.width payload) (.error .wrongContext))
    Plain.runBody (confine ((host bindings).embedder name type args)) reference state (some thread) =
      (reference, (state.enter name type args).record reply.1, .ok reply.2) := by
  change Plain.runBody (confine (route state.nextTicket bindings name type args)) reference
    (state.enter name type args) (some thread) = _
  cases schema with
  | none =>
    simp only [route, linked, Option.elim, Claims.Core.Scheduled.invoke, Prog.bind_eq, Prog.bind_assoc]
    rw [resolve_caller_confined, caller]
    simp [confined_read_store, blocked]
    rfl
  | some payload =>
    simp only [route, linked, Option.elim, giveFlat, Prog.bind_eq, Prog.bind_assoc]
    rw [resolve_caller_confined, caller]
    simp [confined_read_store, blocked]
    rfl

private theorem observing_body_growth {grow : SingleThreaded.GrowOracle} {Host Result : Type}
    (body : P (core3 grow) Host Result)
    (start : Machine.Config (core3 grow) Host) (updated : CStore (core3 grow))
    (reached : Host) (result : Result) (finish : Result → P (core3 grow) Host (Ret (core3 grow)))
    (thread : Option ThreadId) (segments : List (Machine.Seg (core3 grow) Host))
    (rest : List (Machine.Activation (core3 grow) Host))
    (profile : ProfileKind) (ready : HostReady Host)
    (dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow)))
    (focused : start.ctl = ⟨thread, .prog (body >>= finish), segments⟩ :: rest)
    (observes : Prog.Every (S := Eff (core3 grow) Host) (fun op => op.observes = true) body)
    (success : Plain.runBody body start.store start.host (some thread) = (updated, reached, .ok result)) :
    ∃ count, Machine.CoreGrowthSteps profile ready dispatch start (List.replicate count .tau)
      { start with
        store := updated
        host := reached
        ctl := ⟨thread, .prog (finish result), segments⟩ :: rest } ∧
      ∀ place, Machine.ReturnFrame.Occurrence.Prefix profile ready dispatch start place (List.replicate count .tau)
        { start with store := updated, host := reached, ctl := ⟨thread, .prog (finish result), segments⟩ :: rest } place := by
  induction observes generalizing start with
  | pure value =>
    simp only [Plain.runBody, Prod.mk.injEq, Except.ok.injEq] at success
    obtain ⟨store_eq, host_eq, result_eq⟩ := success
    subst updated reached result
    have frame : { start with ctl := ⟨thread, .prog (finish value), segments⟩ :: rest } = start := by
      cases start
      congr
      exact focused.symm
    rw [frame]
    exact ⟨0, .refl _, fun _ => .done _ _⟩
  | @op op next allowed _ ih =>
    have guard : Machine.CoreUpdateGrows start := by
      rw [Machine.CoreUpdateGrows, focused]
      cases op <;> trivial
    cases op
    case get =>
      obtain ⟨count, tail, tracking⟩ := ih start.store
        { start with ctl := ⟨thread, .prog (next start.store >>= finish), segments⟩ :: rest } rfl success
      exact ⟨count + 1, .cons guard (.get focused) tail, fun place => .step (.get focused)
        (by rw [Machine.ReturnFrame.Occurrence.transitionEdit, focused]; cases place <;> rfl) (tracking place)⟩
    case hostGet =>
      obtain ⟨count, tail, tracking⟩ := ih start.host
        { start with ctl := ⟨thread, .prog (next start.host >>= finish), segments⟩ :: rest } rfl success
      exact ⟨count + 1, .cons guard (.hostGet focused) tail, fun place => .step (.hostGet focused)
        (by rw [Machine.ReturnFrame.Occurrence.transitionEdit, focused]; cases place <;> rfl) (tracking place)⟩
    case hostSet newHost _ =>
      obtain ⟨count, tail, tracking⟩ := ih ()
        { start with host := newHost, ctl := ⟨thread, .prog (next () >>= finish), segments⟩ :: rest } rfl success
      exact ⟨count + 1, .cons guard (.hostSet focused) tail, fun place => .step (.hostSet focused)
        (by rw [Machine.ReturnFrame.Occurrence.transitionEdit, focused]; cases place <;> rfl) (tracking place)⟩
    case currentThread =>
      obtain ⟨count, tail, tracking⟩ := ih thread
        { start with ctl := ⟨thread, .prog (next thread >>= finish), segments⟩ :: rest } rfl success
      exact ⟨count + 1, .cons guard (.currentThread focused) tail, fun place => .step (.currentThread focused)
        (by rw [Machine.ReturnFrame.Occurrence.transitionEdit, focused]; cases place <;> rfl) (tracking place)⟩
    all_goals first | contradiction | cases success

theorem parked_closed_give_steps {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig)) (name : String) (type : V1.FuncType) (args : List FlatValue)
    (inst : InstId) (destination : RecordDestination) (schema : Option Stored.TypeOf)
    (start : Machine.Config (core3 grow) (HostState sig)) (thread : Option ThreadId)
    (profile : ProfileKind) (ready : HostReady (HostState sig)) {entry : InstState}
    {core continuation segments rest}
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) args)
    (linked : resolveBinding bindings name type = .ok ⟨name, inst,
      schema.elim (.givePayload destination) (.giveFlat destination)⟩)
    (caller : Plain.callerInstance start.store thread = .ok (some inst))
    (live : start.store.inst? inst = some entry) (closed : entry.mayLeave = false)
    (impl : HostImpl (core3 grow) (HostState sig) := host bindings)
    (embedder : impl.embedder = (host (grow := grow) bindings).embedder := by rfl) :
    let reply := schema.elim (completion start.host.nextTicket (.error .wrongContext))
      (fun payload => flatCompletion start.host.nextTicket (ABI.flatten destination.width payload)
        (.error .wrongContext))
    let reached := (start.host.enter name type args).record reply.1
    ∃ count, Machine.CoreGrowthSteps profile ready (specDispatch ready impl) start
      (List.replicate count .tau)
      { start with
        host := reached
        ctl := ⟨thread, .core ((core3 grow).resume start.store.core core (.values reply.2))
          continuation, segments⟩ :: rest } ∧ reached.writer = start.host.writer ∧
      (start.CoreGrowing → Machine.Config.CoreGrowing { start with
        host := reached
        ctl := ⟨thread, .core ((core3 grow).resume start.store.core core (.values reply.2))
          continuation, segments⟩ :: rest }) ∧
      (∀ place, Machine.ReturnFrame.Occurrence.Prefix profile ready (specDispatch ready impl)
        start place (List.replicate count .tau)
        { start with host := reached, ctl := ⟨thread,
          .core ((core3 grow).resume start.store.core core (.values reply.2)) continuation, segments⟩ :: rest } place) := by
  intro reply reached
  let program := confine (impl.embedder name type args)
  let focused := { start with ctl := ⟨thread, .prog (calloutBody Limits.spec Quirks.none ready impl
    start.store thread (.embedder name type) args), .core core continuation :: segments⟩ :: rest }
  have blocked : (start.store.inst? inst).any (·.mayLeave) = false := by simp [live, closed]
  have evaluated : Plain.runBody program start.store start.host (some thread) =
      (start.store, reached, .ok reply.2) :=
    by simpa only [program, embedder] using
      confined_give_refusal bindings name type args inst destination schema start.store start.host
        thread linked caller blocked
  have entered : focused.ctl = ⟨thread, .prog (program >>= fun words => .pure (.flat words)),
      .core core continuation :: segments⟩ :: rest := by
    simp only [focused, calloutBody, closed_thread caller live closed, Bool.false_eq_true, ite_false, program]
    rfl
  obtain ⟨count, steps, tracking⟩ := observing_body_growth program focused start.store reached reply.2
    (fun words => .pure (.flat words)) thread (.core core continuation :: segments) rest profile ready
    (specDispatch ready impl) entered (confine_every (fun _ fact => fact) _) evaluated
  have guard : Machine.CoreUpdateGrows start := by simp [Machine.CoreUpdateGrows, parked]
  have resumed := steps.append (.cons trivial (.popCore rfl) (.refl _))
  rw [← List.replicate_succ'] at resumed
  refine ⟨count + 1 + 1 + 1 + 1, .cons guard (.coreCallout parked calling)
    (.cons trivial (.currentThread rfl) (.cons trivial (.get rfl) resumed)), rfl,
    (fun growing => growing.replace_core_focus parked reached), ?_⟩
  intro place
  let bumped := ((Machine.ReturnFrame.Occurrence.Edit.push (.core core continuation)).follow place).getD place
  have push : (Machine.ReturnFrame.Occurrence.transitionEdit start .tau).follow place = some bumped := by
    simp only [Machine.ReturnFrame.Occurrence.transitionEdit, parked, calling, bumped]
    cases place with
    | active activation _ => cases activation <;> rfl
    | saved _ _ => rfl
  have pop : (Machine.ReturnFrame.Occurrence.Edit.pop (E := core3 grow) (Host := HostState sig)).follow bumped = some place := by
    cases place with
    | active activation _ => cases activation <;> rfl
    | saved _ _ => rfl
  refine .step (.coreCallout parked calling) push ?_
  refine Machine.ReturnFrame.Occurrence.Prefix.step (middle := bumped) (.currentThread rfl) ?_ ?_
  · cases bumped <;> rfl
  · refine Machine.ReturnFrame.Occurrence.Prefix.step (middle := bumped) (.get rfl) ?_ ?_
    · cases bumped <;> rfl
    · rw [List.replicate_succ']
      exact (tracking bumped).append (.step (.popCore rfl) pop (.done _ _))

theorem parked_closed_give_rejoin {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig)) (name : String) (type : V1.FuncType) (args : List FlatValue)
    (inst : InstId) (destination : RecordDestination) (schema : Option Stored.TypeOf)
    {start other : Machine.Config (core3 grow) (HostState sig)}
    {changes : Machine.ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (paired : Machine.HostFrame.Related.Paired changes start other) (thread : Option ThreadId)
    (profile : ProfileKind) (ready : HostReady (HostState sig)) {entry : InstState}
    {core continuation segments rest}
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) args)
    (linked : resolveBinding bindings name type = .ok ⟨name, inst,
      schema.elim (.givePayload destination) (.giveFlat destination)⟩)
    (caller : Plain.callerInstance start.store thread = .ok (some inst))
    (live : start.store.inst? inst = some entry) (closed : entry.mayLeave = false) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    let reply := schema.elim (completion start.host.nextTicket (.error .wrongContext))
      (fun payload => flatCompletion start.host.nextTicket (ABI.flatten destination.width payload)
        (.error .wrongContext))
    let next := Machine.Focus.core ((core3 grow).resume start.store.core core (.values reply.2)) continuation
    let leftNext := { start with
      host := (start.host.enter name type args).record reply.1, ctl := ⟨thread, next, segments⟩ :: rest }
    ∃ leftCount rightCount rightNext otherSegments otherRest,
      Machine.CoreGrowthSteps profile ready dispatch start (List.replicate leftCount .tau) leftNext ∧
      Machine.CoreGrowthSteps profile ready dispatch other (List.replicate rightCount .tau) rightNext ∧
      rightNext.ctl = ⟨thread, next, otherSegments⟩ :: otherRest ∧
      Machine.HostFrame.Related.Paired changes leftNext rightNext ∧
      leftNext.host.writer = start.host.writer ∧ rightNext.host.writer = other.host.writer ∧
      (∀ place, Machine.ReturnFrame.Occurrence.Prefix profile ready dispatch start place (List.replicate leftCount .tau)
        leftNext place) ∧
      (∀ place, Machine.ReturnFrame.Occurrence.Prefix profile ready dispatch other place (List.replicate rightCount .tau)
        rightNext place) ∧
      other.ctl = ⟨thread, .core core continuation, otherSegments⟩ :: otherRest ∧
      rightNext = { other with
        ctl := ⟨thread, next, otherSegments⟩ :: otherRest
        host := (other.host.enter name type args).record
          (schema.elim (completion other.host.nextTicket (.error .wrongContext))
            (fun payload => flatCompletion other.host.nextTicket (ABI.flatten destination.width payload) (.error .wrongContext))).1 } := by
  intro dispatch reply next leftNext
  let otherReply := schema.elim (completion other.host.nextTicket (.error .wrongContext))
    (fun payload => flatCompletion other.host.nextTicket (ABI.flatten destination.width payload) (.error .wrongContext))
  have sameReply : otherReply.2 = reply.2 := by cases schema <;> rfl
  obtain ⟨otherSegments, otherRest, otherParked, rejoined⟩ := paired.retarget parked next
    ((start.host.enter name type args).record reply.1) ((other.host.enter name type args).record otherReply.1)
  have sameStore := paired.data.1
  obtain ⟨leftCount, left, leftWriter, _, leftPrefix⟩ := parked_closed_give_steps
    bindings name type args inst destination schema start thread profile ready parked calling linked caller live closed
  obtain ⟨rightCount, right, rightWriter, _, rightPrefix⟩ := parked_closed_give_steps
    bindings name type args inst destination schema other thread profile ready otherParked
    (sameStore ▸ calling) linked (sameStore ▸ caller) (sameStore ▸ live) closed
  change Machine.CoreGrowthSteps profile ready dispatch other (List.replicate rightCount .tau)
    { other with
      host := (other.host.enter name type args).record otherReply.1
      ctl := ⟨thread, .core ((core3 grow).resume other.store.core core (.values otherReply.2)) continuation,
        otherSegments⟩ :: otherRest } at right
  have sameCore := congrArg CStore.core sameStore.symm
  change ∀ place, Machine.ReturnFrame.Occurrence.Prefix profile ready dispatch other place (List.replicate rightCount .tau)
    { other with host := (other.host.enter name type args).record otherReply.1, ctl := ⟨thread,
      .core ((core3 grow).resume other.store.core core (.values otherReply.2)) continuation, otherSegments⟩ :: otherRest }
    place at rightPrefix
  rw [sameReply, sameCore] at right rightPrefix
  exact ⟨leftCount, rightCount, _, otherSegments, otherRest, left, right, rfl, rejoined, leftWriter, rightWriter,
    leftPrefix, rightPrefix, otherParked, rfl⟩

private def admitGive {E : CoreEngine} {Host Result : Type} (inst : InstId)
    (selection : P E Host (Except Claims.Core.Scheduled.Issue Result)) :
    P E Host (Except Claims.Core.Scheduled.Issue Result) := do
  if (← currentInst?) != some inst || !((← getStore).inst? inst).any (·.mayLeave) then
    return .error .wrongContext
  selection

private theorem parked_give_prefix {sig : Signature} {grow : SingleThreaded.GrowOracle} {Result : Type}
    (bindings : List (Binding sig)) (name : String) (type : V1.FuncType) (args : List FlatValue)
    (start : Machine.Config (core3 grow) (HostState sig)) (thread : Option ThreadId) (inst : InstId)
    (profile : ProfileKind) (ready : HostReady (HostState sig))
    (selection : Session grow sig (Except Claims.Core.Scheduled.Issue Result)) (selected : Result)
    (next : Except Claims.Core.Scheduled.Issue Result → Session grow sig (List FlatValue))
    {core continuation segments rest}
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) args)
    (caller : Plain.callerInstance start.store thread = .ok (some inst))
    (mayLeave : (start.store.inst? inst).any (·.mayLeave) = true)
    (routed : route start.host.nextTicket bindings name type args = (admitGive inst selection >>= next))
    (checked : let entered := start.host.enter name type args
      Plain.runBody selection start.store entered (some thread) = (start.store, entered, .ok (.ok selected)))
    (impl : HostImpl (core3 grow) (HostState sig)) (embedder : impl.embedder = (host (grow := grow) bindings).embedder) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Machine.Steps profile ready (specDispatch ready impl) start labels
        { start with host := start.host.enter name type args
                     ctl := ⟨thread, .prog (next (.ok selected) >>= fun words => pure (.flat words)),
                       .core core continuation :: segments⟩ :: rest } := by
  let entered := start.host.enter name type args
  let saved := .core core continuation :: segments
  let admission := admitGive inst selection
  let finish := fun result => next result >>= fun words => pure (Ret.flat (E := core3 grow) words)
  let active := { start with host := entered, ctl := ⟨thread, .prog (admission >>= finish), saved⟩ :: rest }
  have evaluated : Plain.runBody admission start.store entered (some thread) =
      (start.store, entered, .ok (.ok selected)) := by
    dsimp only [admission, admitGive]
    simp only [Prog.bind_eq]
    rw [resolve_caller, caller]
    simp only [read_store, bne_self_eq_false, mayLeave, Bool.not_true, Bool.or_false, Bool.false_eq_true, ite_false]
    exact checked
  obtain ⟨labels, silent, steps⟩ := body_steps_at admission active start.store entered (.ok selected) finish
    thread saved rest profile ready (specDispatch ready impl) rfl (some thread) (.inr rfl) evaluated
  have unpack : (route start.host.nextTicket bindings name type args >>= fun words => pure (.flat words)) =
      (admission >>= finish) := by rw [routed]; exact Prog.bind_assoc _ _ _
  have leaves := threadMayLeave_of_caller caller mayLeave
  have installed : calloutBody Limits.spec Quirks.none ready impl start.store thread (.embedder name type) args =
      .op .hostGet (fun state => .op (.hostSet (state.enter name type args)) (fun _ =>
        route state.nextTicket bindings name type args >>= fun words => pure (.flat words))) := by
    simp only [calloutBody, leaves, ite_true, embedder]
    rfl
  have entry : Machine.Steps profile ready (specDispatch ready impl)
      { start with ctl := ⟨thread, .prog (calloutBody Limits.spec Quirks.none ready impl
          start.store thread (.embedder name type) args), saved⟩ :: rest } (.tau :: .tau :: labels)
      { active with ctl := ⟨thread, .prog (finish (.ok selected)), saved⟩ :: rest } := by
    refine .cons (.hostGet (by rw [installed])) (.cons (.hostSet rfl) ?_)
    change Machine.Steps profile ready (specDispatch ready impl)
      { start with host := entered, ctl := ⟨thread, .prog (route start.host.nextTicket bindings name type args >>=
        fun words => pure (.flat words)), saved⟩ :: rest } labels _
    rw [unpack]
    exact steps
  refine ⟨_, ?_, prepend_embedder_callout (impl := impl) parked calling entry⟩
  change labels.all (· matches .tau) = true
  apply List.all_eq_true.mpr
  intro label member
  have tau := List.all_eq_true.mp silent label member
  cases label <;> first | rfl | contradiction

private theorem read_selection {sig : Signature} {grow : SingleThreaded.GrowOracle} {Result : Type}
    (handle : BitVec IntType.i32.width) (next : Option (Tree sig) → Session grow sig Result)
    (store : CStore (core3 grow)) (state : HostState sig) (thread : Option ThreadId) :
    Plain.runBody ((select handle).bind next) store state (some thread) =
      Plain.runBody (next (Stored.Endpoints.Core.childFromHistory state.writer.accepted handle))
        store state (some thread) := rfl

theorem parked_give_payload {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig)) (name : String) (type : V1.FuncType) (handle : BitVec IntType.i32.width)
    (pointer : FlatValue) (inst : InstId) (destination : RecordDestination) (tree : Tree sig)
    (start : Machine.Config (core3 grow) (HostState sig)) (thread : Option ThreadId)
    (profile : ProfileKind) (ready : HostReady (HostState sig)) {core continuation segments rest}
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) [.int .i32 handle, pointer])
    (linked : resolveBinding bindings name type = .ok ⟨name, inst, .givePayload destination⟩)
    (caller : Plain.callerInstance start.store thread = .ok (some inst))
    (mayLeave : (start.store.inst? inst).any (·.mayLeave) = true)
    (word : Stored.flatType pointer = ABI.pointerType destination.width)
    (destinationChecked : destination.check start.store = .ok ())
    (selected : Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle = some tree)
    (impl : HostImpl (core3 grow) (HostState sig)) (embedder : impl.embedder = (host (grow := grow) bindings).embedder) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Machine.Steps profile ready (specDispatch ready impl) start labels
        { start with host := start.host.enter name type [.int .i32 handle, pointer]
                     ctl := ⟨thread, .prog (do
                       let result ← Claims.Record.lowerPayloadRoot recordClaims Limits.spec Quirks.none
                         (destination.context inst) tree (.memory (flatNat pointer))
                       return .flat (← finish start.host.nextTicket
                         (result.mapError .lowerPayload |>.map (fun _ => 0)))),
                       .core core continuation :: segments⟩ :: rest } := by
  let selection := selectMemoryDestination (grow := grow) (sig := sig) destination [.int .i32 handle, pointer]
  let next : Except Claims.Core.Scheduled.Issue (Tree sig × Nat) → Session grow sig (List FlatValue)
    | .error issue => finish start.host.nextTicket (.error issue)
    | .ok (root, address) => do
      let lowered ← Claims.Record.lowerPayloadRoot recordClaims Limits.spec Quirks.none
        (destination.context inst) root (.memory address)
      finish start.host.nextTicket (lowered.mapError .lowerPayload |>.map (fun _ => 0))
  have routed : route start.host.nextTicket bindings name type [.int .i32 handle, pointer] =
      (admitGive inst selection >>= next) := by
    simp only [route, linked, Claims.Core.Scheduled.invoke, givePayload, giveToMemory, admitGive, next,
      selection, Prog.bind_eq, Prog.bind_assoc]
    congr 1
    funext current
    congr 1
    funext store
    split
    · rfl
    · simp only [Prog.bind_assoc]
      congr 1
      funext choice
      cases choice with
      | error => rfl
      | ok pair =>
        obtain ⟨root, address⟩ := pair
        let lower := Claims.Record.lowerPayloadRoot (E := core3 grow) recordClaims Limits.spec Quirks.none
          (destination.context inst) root (.memory address)
        change ((lower.bind fun result => pure (result.mapError .lowerPayload |>.map (fun _ => 0))).bind
          (finish start.host.nextTicket)) = _
        exact Prog.bind_assoc lower _ _
  have checked : let entered := start.host.enter name type [.int .i32 handle, pointer]
      Plain.runBody selection start.store entered (some thread) =
        (start.store, entered, .ok (.ok (tree, flatNat pointer))) := by
    let entered := start.host.enter name type [.int .i32 handle, pointer]
    change Plain.runBody selection start.store entered (some thread) = _
    simp only [selection, selectMemoryDestination, Execution.Runtime.Value.int, Prog.bind_eq, word,
      bne_self_eq_false, Bool.false_eq_true, ite_false, read_store, destinationChecked, read_selection]
    rw [show Stored.Endpoints.Core.childFromHistory entered.writer.accepted handle = some tree from selected]
    rfl
  have actual := parked_give_prefix bindings name type _ start thread inst profile ready selection
    (tree, flatNat pointer) next parked calling caller mayLeave routed checked impl embedder
  simp only [next, Prog.bind_eq, Prog.bind_assoc] at actual ⊢
  exact actual

theorem parked_give_flat {sig : Signature} {grow : SingleThreaded.GrowOracle}
    (bindings : List (Binding sig)) (name : String) (type : V1.FuncType) (handle : BitVec IntType.i32.width)
    (inst : InstId) (destination : RecordDestination) (payload : Stored.TypeOf) (tree : Tree sig)
    (start : Machine.Config (core3 grow) (HostState sig)) (thread : Option ThreadId)
    (profile : ProfileKind) (ready : HostReady (HostState sig)) {core continuation segments rest}
    (parked : start.ctl = ⟨thread, .core core continuation, segments⟩ :: rest)
    (calling : (core3 grow).status start.store.core core = .callout (.embedder name type) [.int .i32 handle])
    (linked : resolveBinding bindings name type = .ok ⟨name, inst, .giveFlat destination payload⟩)
    (caller : Plain.callerInstance start.store thread = .ok (some inst))
    (mayLeave : (start.store.inst? inst).any (·.mayLeave) = true)
    (destinationChecked : destination.check start.store = .ok ())
    (selected : Stored.Endpoints.Core.childFromHistory start.host.writer.accepted handle = some tree)
    (schema : rootHasSchema tree payload = true)
    (impl : HostImpl (core3 grow) (HostState sig)) (embedder : impl.embedder = (host (grow := grow) bindings).embedder) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Machine.Steps profile ready (specDispatch ready impl) start labels
        { start with host := start.host.enter name type [.int .i32 handle]
                     ctl := ⟨thread, .prog (do
                       let result ← Claims.Record.lowerPayloadRoot recordClaims Limits.spec Quirks.none
                         (destination.context inst) tree .flat
                       return .flat (← writeCompletion (flatCompletion start.host.nextTicket
                         (ABI.flatten destination.width payload) (result.mapError .lowerPayload)))),
                       .core core continuation :: segments⟩ :: rest } := by
  let selection := selectFlatDestination (grow := grow) (sig := sig) destination payload [.int .i32 handle]
  let reply := fun result => writeCompletion (grow := grow) (sig := sig)
    (flatCompletion start.host.nextTicket (ABI.flatten destination.width payload) result)
  let next : Except Claims.Core.Scheduled.Issue (Tree sig) → Session grow sig (List FlatValue)
    | .error issue => reply (.error issue)
    | .ok root => do
      let lowered ← Claims.Record.lowerPayloadRoot recordClaims Limits.spec Quirks.none
        (destination.context inst) root .flat
      reply (lowered.mapError .lowerPayload)
  have routed : route start.host.nextTicket bindings name type [.int .i32 handle] =
      (admitGive inst selection >>= next) := by
    simp only [route, linked, giveFlat, admitGive, next, selection, Prog.bind_eq, Prog.bind_assoc]
    congr 1
    funext current
    congr 1
    funext store
    split
    · rfl
    · simp only [Prog.bind_assoc]
      congr 1
      funext choice
      cases choice with
      | error => rfl
      | ok root =>
        let lower : Session grow sig (Except Stored.Endpoints.RecordLower.Issue (List FlatValue)) :=
          Claims.Record.lowerPayloadRoot recordClaims Limits.spec Quirks.none (destination.context inst) root .flat
        change ((lower.bind fun result => pure (result.mapError .lowerPayload)).bind reply) = _
        exact Prog.bind_assoc lower _ _
  have checked : let entered := start.host.enter name type [.int .i32 handle]
      Plain.runBody selection start.store entered (some thread) = (start.store, entered, .ok (.ok tree)) := by
    let entered := start.host.enter name type [.int .i32 handle]
    change Plain.runBody selection start.store entered (some thread) = _
    simp only [selection, selectFlatDestination, Execution.Runtime.Value.int, Prog.bind_eq,
      read_store, destinationChecked, read_selection]
    rw [show Stored.Endpoints.Core.childFromHistory entered.writer.accepted handle = some tree from selected]
    simp [schema]
    rfl
  have actual := parked_give_prefix bindings name type _ start thread inst profile ready selection
    tree next parked calling caller mayLeave routed checked impl embedder
  simp only [next, reply, Prog.bind_eq, Prog.bind_assoc] at actual ⊢
  exact actual

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainScheduled
