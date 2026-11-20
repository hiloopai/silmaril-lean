module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Thms
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Sequence.Defs
public import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Width.Thms
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCursor.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCursor

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core (LocalIssue)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence

variable {grow : SingleThreaded.GrowOracle} {Host : Type}
  {profile : ProfileKind} {ready : HostReady Host}
  {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
  {before after : Machine.Config (core3 grow) Host} {trace : List (Label (core3 grow) Host)}

theorem check_width (destination : RecordDestination) (store : CStore (core3 grow))
    (checked : destination.check store = .ok ()) :
    (core3 grow).memAddrType? store.core destination.memory = some destination.width := by
  unfold RecordDestination.check at checked
  by_contra missing
  simp only [bne_iff_ne, ne_eq, missing, not_false_eq_true, ite_true] at checked
  contradiction

theorem memory_cursor (run : CoreGrowthSteps profile ready dispatch before trace after)
    (destination : RecordDestination) (inst : InstId) (checked : destination.check before.store = .ok ())
    (storeField : Nat → Field → Nat → P (core3 grow) Host Unit)
    (field : Field) (fields : List Field) (cursor index : Nat)
    (finish : Unit → P (core3 grow) Host (Ret (core3 grow))) {thread segments rest}
    (focused : after.ctl = ⟨thread, .prog (memorySequence (ptrType (destination.context inst))
      storeField (field :: fields) cursor index >>= finish), segments⟩ :: rest) :
    let area := layout destination.width field.type
    let ptr := alignTo cursor area.alignment
    CoreGrowthSteps profile ready dispatch after [.tau]
      { after with ctl := ⟨thread, .prog (do
          storeField index field ptr
          let result ← memorySequence (ptrType (destination.context inst)) storeField fields
            (ptr + area.size) (index + 1)
          finish result), segments⟩ :: rest } := by
  let next := fun width => do
    let area := layout width field.type
    let ptr := alignTo cursor area.alignment
    storeField index field ptr
    let result ← memorySequence (ptrType (destination.context inst)) storeField fields
      (ptr + area.size) (index + 1)
    finish result
  apply run.read_width (destination.context inst) rfl (check_width destination before.store checked) next
  simpa only [memorySequence, bind_assoc, next] using focused

theorem list_range_focus (cx : LiftLowerContext (core3 grow)) (area : Layout) (count : Nat)
    (finish : Nat → P (core3 grow) Host (Ret (core3 grow))) :
    (allocateListRange cx area count >>= finish) =
      .op (.call (.reallocate cx 0 0 area.alignment.bytes (count * area.size))) (listRangeResume cx area count finish) := by
  unfold allocateListRange allocate reallocate callNat callRet perform Prog.lift
  simp only [bind_assoc]
  apply congrArg (Prog.op (S := Eff (core3 grow) Host)
    (.call (.reallocate cx 0 0 area.alignment.bytes (count * area.size))))
  funext result
  cases result <;> rfl

theorem list_range_install (cx : LiftLowerContext (core3 grow)) (area : Layout) (count : Nat)
    (finish : Nat → P (core3 grow) Host (Ret (core3 grow))) {thread segments rest}
    (focused : after.ctl = ⟨thread, .prog (allocateListRange cx area count >>= finish),
      segments⟩ :: rest) :
    let request := Call.reallocate cx 0 0 area.alignment.bytes (count * area.size)
    Step profile ready dispatch after .tau { after with ctl :=
      ⟨thread, .prog (dispatch request), .prog (listRangeResume cx area count finish) :: segments⟩ :: rest } := by
  rw [list_range_focus] at focused
  exact Machine.Step.call focused

theorem list_range_body (destination : RecordDestination) (inst : InstId) (area : Layout)
    (count pointer : Nat) (store : CStore (core3 grow)) (host : Host) (thread : Option ThreadId) :
    Plain.runBody (validateListRange (destination.context inst) area count pointer) store host (some thread) =
      (store, host, if pointer ≠ alignTo pointer area.alignment then .error (.trapped .unalignedPointer)
        else match (core3 grow).memSize? store.core destination.memory with
        | none => .error (.trapped (.internal "dangling memory address"))
        | some size => if pointer + count * area.size ≤ size then .ok pointer
            else .error (.trapped .outOfBounds)) := by
  unfold validateListRange
  split
  · rename_i unaligned
    simp [trapIf, unaligned]
    rfl
  · rename_i aligned
    simp [trapIf, aligned]
    change Plain.runBody (.op .get (fun current =>
      (orTrap (.internal "dangling memory address") ((core3 grow).memSize? current.core destination.memory) >>=
        fun size => trapIf (decide (pointer + count * area.size > size)) .outOfBounds) >>=
        fun _ => pure pointer)) store host (some thread) = _
    rw [Plain.runBody]
    cases sized : (core3 grow).memSize? store.core destination.memory with
    | none => rfl
    | some size =>
      simp only [orTrap, pure_bind]
      by_cases bounds : pointer + count * area.size ≤ size
      · simp [trapIf, Nat.not_lt.mpr bounds, bounds]
        rfl
      · simp [trapIf, Nat.lt_of_not_ge bounds, bounds]
        rfl

theorem list_range_resume (destination : RecordDestination) (inst : InstId) (area : Layout)
    (count pointer : Nat) (finish : Nat → P (core3 grow) Host (Ret (core3 grow)))
    (resume : Ret (core3 grow) → P (core3 grow) Host (Ret (core3 grow)))
    (resumes : resume (.nat pointer) = (validateListRange (destination.context inst) area count pointer >>= finish))
    {thread segments rest}
    (returned : after.ctl = ⟨thread, .prog (.pure (.nat pointer)), .prog resume :: segments⟩ :: rest) :
    let body := validateListRange (destination.context inst) area count pointer
    match (Plain.runBody body after.store after.host (some thread)).2.2 with
    | .ok value => ∃ labels, (∀ label ∈ labels, label = .tau) ∧
        RetainsBelowTop profile ready dispatch after labels
          { after with ctl := ⟨thread, .prog (finish value), segments⟩ :: rest }
    | .error (.trapped reason) => ∃ count, Machine.Steps profile ready dispatch after
        (List.replicate count .tau ++ [.trap reason]) (Machine.StepDefs.trapCfg after)
    | .error _ => False := by
  let body : P (core3 grow) Host Nat := validateListRange (destination.context inst) area count pointer
  let reached := { after with ctl := ⟨thread, .prog (body >>= finish), segments⟩ :: rest }
  have pop : Machine.Step profile ready dispatch after .tau reached := by
    have step := Machine.Step.popProg (prof := profile) (hr := ready) (dispatch := dispatch) returned
    rw [resumes] at step
    exact step
  have readOnly := list_range_body destination inst area count pointer after.store after.host thread
  change Plain.runBody body after.store after.host (some thread) = _ at readOnly
  dsimp only
  generalize answer : (Plain.runBody body after.store after.host (some thread)).2.2 = verdict
  have evaluation : Plain.runBody body after.store after.host (some thread) = (after.store, after.host, verdict) := by
    rw [← answer, readOnly]
  cases verdict with
  | ok value =>
    obtain ⟨labels, silent, tail⟩ := Plain.runBody_thread_tracks body reached after.store after.host value
      finish thread segments rest profile ready dispatch rfl evaluation
    have returnedSlots : RetainsBelowTop profile ready dispatch after [.tau] reached := by
      simpa only [reached, resumes] using (Prefix.pop_return (profile := profile) (ready := ready) (dispatch := dispatch) returned)
    refine ⟨.tau :: labels, ?_, fun depth => (returnedSlots depth).append (tail depth)⟩
    intro label member
    rcases List.mem_cons.mp member with rfl | member
    · rfl
    · have tested := List.all_eq_true.mp silent label member
      cases label <;> first | rfl | contradiction
  | error issue =>
    cases issue with
    | trapped reason =>
      obtain ⟨count, tail⟩ := Plain.runBody_trap_steps body reached after.store after.host reason
        finish thread segments rest profile ready dispatch rfl evaluation
      exact ⟨count + 1, .cons pop tail⟩
    | _ =>
      rw [evaluation] at readOnly
      split at readOnly
      · cases readOnly
      · split at readOnly
        · cases readOnly
        · split at readOnly <;> cases readOnly

private theorem append_steps {first middle last : Machine.Config (core3 grow) Host} {front back}
    (prefixSteps : Machine.Steps profile ready dispatch first front middle)
    (suffixSteps : Machine.Steps profile ready dispatch middle back last) :
    Machine.Steps profile ready dispatch first (front ++ back) last := by
  induction prefixSteps with
  | refl => exact suffixSteps
  | cons step _ ih => exact .cons step (ih suffixSteps)

theorem list_range_recheck {sig : Stored.Signature} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (reached : Machine.Config (core3 grow) (HostState sig)) (destination : RecordDestination)
    (inst : InstId) (area : Layout) (count pointer : Nat) (plan : List Object)
    (finish : Nat → Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (resume : Ret (core3 grow) → Session grow sig (Ret (core3 grow)))
    (resumes : resume (.nat pointer) = (do
      let address ← validateListRange (destination.context inst) area count pointer
      let verdict ← (Stored.OwnedMemory.Claims.Record.authority recordClaims Limits.spec
        (destination.context inst)).prepare plan
      finish address verdict))
    {thread segments rest}
    (returned : reached.ctl = ⟨thread, .prog (.pure (.nat pointer)), .prog resume :: segments⟩ :: rest)
    (aligned : pointer = alignTo pointer area.alignment) {bytes : Nat}
    (sized : (core3 grow).memSize? reached.store.core destination.memory = some bytes)
    (bounds : pointer + count * area.size ≤ bytes) :
    ∃ labels, (∀ label ∈ labels, label = .tau) ∧
      RetainsBelowTop profile ready dispatch reached labels
        { reached with ctl := ⟨thread, .prog (finish pointer
          (Stored.OwnedMemory.Claims.Record.prepare reached.store reached.host.writer plan)),
          segments⟩ :: rest } := by
  let recheck := fun address => do
    let verdict ← (Stored.OwnedMemory.Claims.Record.authority recordClaims Limits.spec
      (destination.context inst)).prepare plan
    finish address verdict
  have checked := list_range_body destination inst area count pointer reached.store reached.host thread
  have unaligned : ¬ pointer ≠ alignTo pointer area.alignment := fun different => different aligned
  simp only [unaligned, ite_false, sized, bounds, ite_true] at checked
  have valid : (Plain.runBody (validateListRange (destination.context inst) area count pointer)
      reached.store reached.host (some thread)).2.2 = .ok pointer := congrArg (fun result => result.2.2) checked
  have resumed := list_range_resume (profile := profile) (ready := ready) (dispatch := dispatch)
    destination inst area count pointer recheck resume resumes returned
  dsimp only at resumed
  rw [valid] at resumed
  obtain ⟨labels, silent, tracks⟩ := resumed
  have reads : RetainsActiveSlots profile ready dispatch
      { reached with ctl := ⟨thread, .prog (recheck pointer), segments⟩ :: rest } [.tau, .tau]
      { reached with ctl := ⟨thread, .prog (finish pointer
        (Stored.OwnedMemory.Claims.Record.prepare reached.store reached.host.writer plan)),
        segments⟩ :: rest } :=
    fun _ => .step (.get rfl) rfl (.step (.hostGet rfl) rfl (.done _ _))
  refine ⟨labels ++ [.tau, .tau], ?_, ?_⟩
  · intro label member
    rcases List.mem_append.mp member with inPrefix | inReads
    · exact silent label inPrefix
    · simpa using inReads
  · exact fun depth => (tracks depth).append (reads depth)

theorem compiled_payload_start {sig : Stored.Signature} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (reached : Machine.Config (core3 grow) (HostState sig)) (destination : RecordDestination) (inst : InstId)
    (type : Stored.TypeOf) (payload : Stored.OwnedMemory.Payload type) (output : Stored.Lower.Output)
    (field : Field) (plan : List Object)
    (finish : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (compiled : Stored.OwnedMemory.Claims.Record.preflightValue (destination.context (grow := grow) inst) type
      payload output = .ok (field, plan))
    (destinationChecked : destination.check reached.store = .ok ()) {thread segments rest}
    (focused : reached.ctl = ⟨thread, .prog (Stored.OwnedMemory.Claims.Record.lowerValue recordClaims
      Limits.spec Quirks.none (destination.context inst) type payload output >>= finish), segments⟩ :: rest) :
    let cx := destination.context (grow := grow) inst
    let authority := Stored.OwnedMemory.Claims.Record.authority recordClaims Limits.spec cx
    field.value = payload.val.value ∧ field.LayoutMatches type ∧
    payload.val.owners = field.objects.filterMap Object.ownerReceipt ∧
    match Stored.OwnedMemory.Claims.Record.prepare reached.store reached.host.writer field.objects with
    | .error issue => Machine.Steps profile ready dispatch reached [.tau, .tau]
        { reached with ctl := ⟨thread, .prog (finish (.error issue)), segments⟩ :: rest }
    | .ok () => Machine.Steps profile ready dispatch reached [.tau, .tau, .tau]
        { reached with ctl := ⟨thread, .prog (
          if !Stored.Lower.fits Quirks.none destination.encoding destination.width type payload.val.value then
            finish (.error (.preflight (.abi .allocationPrecondition)))
          else Internal.emitValue Limits.spec Quirks.none cx authority destination.width type field output >>= finish),
          segments⟩ :: rest } := by
  let cx := destination.context (grow := grow) inst
  let authority := Stored.OwnedMemory.Claims.Record.authority (recordClaims (sig := sig)) Limits.spec cx
  have planIsField : plan = field.objects := by
    have compiledField := compiled
    simp only [Stored.OwnedMemory.Claims.Record.preflightValue, bind, Except.bind, Except.mapError] at compiledField
    split at compiledField <;> first | contradiction | exact compileValue_plan _ _ _ _ _ _ _ compiledField
  have owners := Stored.OwnedMemory.Claims.Record.preflightValue_receipts _ _ _ _ _ _ compiled
  rw [planIsField] at owners
  refine ⟨Stored.OwnedMemory.Claims.Record.preflightValue_value _ _ _ _ _ _ compiled,
    Stored.OwnedMemory.Claims.Record.preflightValue_layout _ _ _ _ _ _ compiled, owners, ?_⟩
  let proceed : AddrType → Session grow sig (Except Stored.Endpoints.RecordLower.Issue output.Result) := fun width =>
    if !Stored.Lower.fits Quirks.none cx.opts.encoding width type payload.val.value then
      pure (.error (.preflight (.abi .allocationPrecondition)))
    else Internal.emitValue Limits.spec Quirks.none cx authority width type field output
  let next : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)) := fun verdict =>
    (match verdict with
    | .error issue => pure (.error issue)
    | .ok () => ptrType cx >>= proceed) >>= finish
  simp only [Stored.OwnedMemory.Claims.Record.lowerValue, Internal.lowerWithPlan, compiled] at focused
  have read : reached.ctl = ⟨thread, .prog (.op .get (fun store => .op .hostGet fun current =>
      next (Stored.OwnedMemory.Claims.Record.prepare store current.writer field.objects))), segments⟩ :: rest := focused
  let middle := { reached with ctl := ⟨thread, .prog (next
    (Stored.OwnedMemory.Claims.Record.prepare reached.store reached.host.writer field.objects)), segments⟩ :: rest }
  have reads : Machine.Steps profile ready dispatch reached [.tau, .tau] middle :=
    .cons (.get read) (.cons (.hostGet rfl) (.refl _))
  cases verdict : Stored.OwnedMemory.Claims.Record.prepare reached.store reached.host.writer field.objects with
  | error issue =>
    simp only [middle, verdict] at reads
    exact reads
  | ok answer =>
    cases answer
    have width : ptrTypeIn reached.store cx = destination.width := by
      simp [ptrTypeIn, CanonOpts.ptrType, cx, RecordDestination.context, check_width _ _ destinationChecked]
    have readWidth : middle.ctl = ⟨thread, .prog (.op .get (fun store =>
      proceed (ptrTypeIn store cx) >>= finish)), segments⟩ :: rest := by
      simp only [middle, verdict, next, bind_assoc]
      rfl
    have step := Step.get (prof := profile) (hr := ready) (dispatch := dispatch) readWidth
    change Step profile ready dispatch middle .tau
      { reached with ctl := ⟨thread, .prog (proceed (ptrTypeIn reached.store cx) >>= finish), segments⟩ :: rest } at step
    rw [width] at step
    have tail := append_steps reads (.cons step (.refl _))
    by_cases fits : Stored.Lower.fits Quirks.none destination.encoding destination.width type payload.val.value = true
    · simp [proceed, cx, authority, RecordDestination.context, fits] at tail ⊢
      exact tail
    · have fails := Bool.eq_false_iff.mpr fits
      simpa [proceed, cx, RecordDestination.context, fails] using tail

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCursor
