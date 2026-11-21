module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadCursor.Thms
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadInstall.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Collection.Defs
public import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadInstall.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Collection.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Thms
import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Thms
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms
import Silmaril.Wasm.Component.Reference.ABI.Layout.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCollection

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence

variable {grow : SingleThreaded.GrowOracle} {Host : Type}
  {profile : ProfileKind} {ready : HostReady Host}
  {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}
  {before after : Machine.Config (core3 grow) Host} {trace : List (Label (core3 grow) Host)}

private theorem append_steps {first middle last : Machine.Config (core3 grow) Host} {front back}
    (prefixSteps : Machine.Steps profile ready dispatch first front middle)
    (suffixSteps : Machine.Steps profile ready dispatch middle back last) :
    Machine.Steps profile ready dispatch first (front ++ back) last := by
  induction prefixSteps with
  | refl => exact suffixSteps
  | cons step _ ih => exact .cons step (ih suffixSteps)

theorem canonical_dynamic_call (run : CoreGrowthSteps profile ready dispatch before trace after)
    (destination : RecordDestination) (inst : InstId) (checked : destination.check before.store = .ok ())
    (element : Stored.TypeOf) (entries : List Field) (output : Stored.Lower.Output)
    (storeEntry : AddrType → Field → Nat → P (core3 grow) Host Unit)
    (finish : output.Result → P (core3 grow) Host (Ret (core3 grow))) {thread segments rest}
    (focused : after.ctl = ⟨thread, .prog (canonicalDynamic (destination.context inst) destination.width
      element entries storeEntry output >>= finish), segments⟩ :: rest) :
    let cx := destination.context (grow := grow) inst
    let area := layout destination.width element
    let request := Call.reallocate cx 0 0 area.alignment.bytes (entries.length * area.size)
    ∃ resume : Ret (core3 grow) → P (core3 grow) Host (Ret (core3 grow)),
      (∀ pointer, resume (.nat pointer) = (do
        let ptr ← validateListRange cx area entries.length pointer
        elementSequence (fun _ => storeEntry destination.width) entries area.size ptr 0
        let result ← ListLower.publish cx destination.width ptr entries.length output
        finish result)) ∧
      Machine.Steps profile ready dispatch after [.tau, .tau]
        { after with ctl := ⟨thread, .prog (dispatch request), .prog resume :: segments⟩ :: rest } := by
  let cx := destination.context (grow := grow) inst
  let next := fun width =>
    let area := layout width element
    allocateListRange cx area entries.length >>= fun ptr => do
      elementSequence (fun _ => storeEntry width) entries area.size ptr 0
      let result ← ListLower.publish cx destination.width ptr entries.length output
      finish result
  have widthStep := run.read_width cx rfl (destination.check_width before.store checked) next
    (by simpa only [canonicalDynamic, bind_assoc, cx, next] using focused)
  let middle := { after with ctl := ⟨thread, .prog (next destination.width), segments⟩ :: rest }
  obtain ⟨resume, agreement, callStep⟩ := listRange_call (after := middle) (profile := profile)
    (ready := ready) (dispatch := dispatch) cx (layout destination.width element) entries.length
    (fun ptr => do
      elementSequence (fun _ => storeEntry destination.width) entries (layout destination.width element).size ptr 0
      let result ← ListLower.publish cx destination.width ptr entries.length output
      finish result) rfl
  exact ⟨resume, agreement, append_steps widthStep.steps (.cons callStep (.refl _))⟩

theorem checked_dynamic_call {sig : Stored.Signature} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (reached : Machine.Config (core3 grow) (HostState sig)) (destination : RecordDestination)
    (inst : InstId) (type element : Stored.TypeOf) (entries : List Field) (index : Nat) (output : Stored.Lower.Output)
    (finish : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (prepared : Record.prepare reached.store reached.host.writer (Field.listObjects entries) = .ok ())
    {thread segments rest}
    (focused : reached.ctl = ⟨thread, .prog (Internal.runField Limits.spec Quirks.none (destination.context inst)
      (Record.authority recordClaims Limits.spec (destination.context inst)) destination.width
      (.dynamic type element entries) index output >>= finish), segments⟩ :: rest) :
    let cx := destination.context (grow := grow) inst
    let authority := Record.authority recordClaims Limits.spec cx
    let area := layout destination.width element
    let request := Call.reallocate cx 0 0 area.alignment.bytes (entries.length * area.size)
    ∃ resume : Ret (core3 grow) → Session grow sig (Ret (core3 grow)),
      (∀ pointer, resume (.nat pointer) = (do
        let ptr ← validateListRange cx area entries.length pointer
        let verdict ← authority.prepare (Field.listObjects entries)
        let result ← checkedDynamicContinue Limits.spec Quirks.none cx authority destination.width
          element entries index output ptr verdict
        finish result)) ∧
      Machine.Steps profile ready dispatch reached [.tau, .tau, .tau]
        { reached with ctl := ⟨thread, .prog (dispatch request), .prog resume :: segments⟩ :: rest } := by
  let cx := destination.context (grow := grow) inst
  let authority := Record.authority (recordClaims (sig := sig)) Limits.spec cx
  let area := layout destination.width element
  let plan := Field.listObjects entries
  let onRange : Nat → Session grow sig (Ret (core3 grow)) := fun ptr => do
    let verdict ← authority.prepare plan
    let result ← checkedDynamicContinue Limits.spec Quirks.none cx authority destination.width
      element entries index output ptr verdict
    finish result
  let next : Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)) := fun verdict =>
    (match verdict with
    | .error (.preflight issue) => pure (.error (.field index (.beforeAllocation issue)))
    | .error issue => pure (.error (.nested index issue))
    | .ok () => do
      let ptr ← allocateListRange cx area entries.length
      let verdict ← authority.prepare plan
      checkedDynamicContinue Limits.spec Quirks.none cx authority destination.width element entries index
        output ptr verdict) >>= finish
  have read : reached.ctl = ⟨thread, .prog (.op .get fun store => .op .hostGet fun current =>
    next (Record.prepare store current.writer plan)), segments⟩ :: rest := by
    rw [checked_dynamic_canon_range] at focused
    exact focused
  let middle := { reached with ctl := ⟨thread, .prog (next
    (Record.prepare reached.store reached.host.writer plan)), segments⟩ :: rest }
  have reads : Machine.Steps profile ready dispatch reached [.tau, .tau] middle :=
    .cons (.get read) (.cons (.hostGet rfl) (.refl _))
  have allocating : middle.ctl = ⟨thread, .prog (allocateListRange cx area entries.length >>= onRange),
      segments⟩ :: rest := by
    simp only [middle, plan, prepared, next, onRange, bind_assoc]
  obtain ⟨resume, agreement, callStep⟩ := listRange_call cx area entries.length onRange allocating
  exact ⟨resume, agreement, append_steps reads (.cons callStep (.refl _))⟩

theorem paired_dynamic_call {sig : Stored.Signature} {ready : HostReady (HostState sig)}
    (bindings : List (Binding sig))
    {initial canonical checked : Machine.Config (core3 grow) (HostState sig)} {trace}
    (canonicalRun : CoreGrowthSteps profile ready (specDispatch ready (host bindings)) initial trace canonical)
    (destination : RecordDestination) (inst : InstId) (checkedDestination : destination.check initial.store = .ok ())
    (type element : Stored.TypeOf) (entries : List Field) (index : Nat) (output : Stored.Lower.Output)
    (storeEntry : AddrType → Field → Nat → Session grow sig Unit)
    (finishCanonical : output.Result → Session grow sig (Ret (core3 grow)))
    (finishChecked : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (prepared : Record.prepare checked.store checked.host.writer (Field.listObjects entries) = .ok ())
    {thread segments rest}
    (canonicalAt : canonical.ctl = ⟨thread, .prog (canonicalDynamic (destination.context inst) destination.width
      element entries storeEntry output >>= finishCanonical), segments⟩ :: rest)
    (checkedAt : checked.ctl = ⟨thread, .prog (Internal.runField Limits.spec Quirks.none (destination.context inst)
      (Record.authority recordClaims Limits.spec (destination.context inst)) destination.width
      (.dynamic type element entries) index output >>= finishChecked), segments⟩ :: rest)
    (same : { checked with ctl := canonical.ctl, host := canonical.host } = canonical) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    let cx := destination.context (grow := grow) inst
    let area := layout destination.width element
    let body := dispatch (.reallocate cx 0 0 area.alignment.bytes (entries.length * area.size))
    ∃ checkedResume canonicalResume : Machine.ReturnFrame.Continuation (core3 grow) (HostState sig),
      let checkedCall := { checked with ctl := ⟨thread, .prog body, .prog checkedResume :: segments⟩ :: rest }
      let canonicalCall := { canonical with ctl := ⟨thread, .prog body, .prog canonicalResume :: segments⟩ :: rest }
      (∀ pointer, checkedResume (.nat pointer) = (do
        let ptr ← validateListRange cx area entries.length pointer
        let authority := Record.authority recordClaims Limits.spec cx
        let verdict ← authority.prepare (Field.listObjects entries)
        let result ← checkedDynamicContinue Limits.spec Quirks.none cx authority destination.width
          element entries index output ptr verdict
        finishChecked result)) ∧
      (∀ pointer, canonicalResume (.nat pointer) = (do
        let ptr ← validateListRange cx area entries.length pointer
        elementSequence (fun _ => storeEntry destination.width) entries area.size ptr 0
        let result ← ListLower.publish cx destination.width ptr entries.length output
        finishCanonical result)) ∧
      Machine.Steps profile ready dispatch checked [.tau, .tau, .tau] checkedCall ∧
      Machine.Steps profile ready dispatch canonical [.tau, .tau] canonicalCall ∧
      Machine.HostFrame.Paired checkedResume canonicalResume checkedCall canonicalCall := by
  obtain ⟨checkedResume, checkedReturn, checkSteps⟩ := checked_dynamic_call (profile := profile)
    (ready := ready) (dispatch := specDispatch ready (host bindings)) checked destination inst type element entries
    index output finishChecked prepared checkedAt
  obtain ⟨canonicalResume, canonicalReturn, canonSteps⟩ := canonical_dynamic_call canonicalRun destination inst
    checkedDestination element entries output storeEntry finishCanonical canonicalAt
  refine ⟨checkedResume, canonicalResume, checkedReturn, canonicalReturn, checkSteps, canonSteps, ?_⟩
  unfold Machine.HostFrame.Paired
  conv => rhs; rw [← same]
  exact Machine.ReturnFrame.installed (Machine.HostFrame.replace checked canonical.host) thread _ segments rest

theorem paired_range_recheck {sig : Stored.Signature} {ready : HostReady (HostState sig)}
    {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {checked canonical : Machine.Config (core3 grow) (HostState sig)}
    {checkedResume canonicalResume : Machine.ReturnFrame.Continuation (core3 grow) (HostState sig)}
    {changes : Machine.ReturnFrame.Substitutions (core3 grow) (HostState sig)}
    (paired : Machine.HostFrame.Related.Paired changes checked canonical)
    (destination : RecordDestination) (inst : InstId) (area : Layout) (count pointer : Nat) (plan : List Object)
    (checkNext : Nat → Except Stored.Endpoints.RecordLower.Issue Unit → Session grow sig (Ret (core3 grow)))
    (canonNext : Nat → Session grow sig (Ret (core3 grow)))
    (checkedBody : checkedResume (.nat pointer) = (do
      let ptr ← validateListRange (destination.context inst) area count pointer
      let verdict ← (Record.authority recordClaims Limits.spec (destination.context inst)).prepare plan
      checkNext ptr verdict))
    (canonicalBody : canonicalResume (.nat pointer) = (validateListRange (destination.context inst) area count pointer >>= canonNext))
    {thread checkedFrames canonicalFrames checkedRest canonicalRest}
    (checkedAt : checked.ctl = ⟨thread, .prog (.pure (.nat pointer)), .prog checkedResume :: checkedFrames⟩ :: checkedRest)
    (canonicalAt : canonical.ctl = ⟨thread, .prog (.pure (.nat pointer)), .prog canonicalResume :: canonicalFrames⟩ :: canonicalRest)
    {bytes : Nat} (sized : (core3 grow).memSize? checked.store.core destination.memory = some bytes)
    (canonicalDispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))) :
    let trapped := fun reason =>
      (∃ steps, Machine.Steps profile ready dispatch checked (List.replicate steps .tau ++ [.trap reason])
        (Machine.StepDefs.trapCfg checked)) ∧
      (∃ steps, Machine.Steps profile ready canonicalDispatch canonical (List.replicate steps .tau ++ [.trap reason])
        (Machine.StepDefs.trapCfg canonical))
    if pointer ≠ alignTo pointer area.alignment then trapped .unalignedPointer
    else if pointer + count * area.size ≤ bytes then
      (∃ labels, (∀ label ∈ labels, label = .tau) ∧ RetainsBelowTop profile ready dispatch checked labels
        { checked with ctl := ⟨thread, .prog (checkNext pointer (Record.prepare checked.store checked.host.writer plan)),
          checkedFrames⟩ :: checkedRest }) ∧
      (∃ labels, (∀ label ∈ labels, label = .tau) ∧ RetainsBelowTop profile ready canonicalDispatch canonical labels
        { canonical with ctl := ⟨thread, .prog (canonNext pointer), canonicalFrames⟩ :: canonicalRest })
    else trapped .outOfBounds := by
  have canonSize : (core3 grow).memSize? canonical.store.core destination.memory = some bytes := by
    rw [← paired.data.1]
    exact sized
  have checkPrefix := destination.listRange_resume (after := checked) (profile := profile) (ready := ready)
    (dispatch := dispatch) inst area count pointer (fun ptr => do
      let verdict ← (Record.authority recordClaims Limits.spec (destination.context inst)).prepare plan
      checkNext ptr verdict) checkedResume checkedBody checkedAt
  have canonPrefix := destination.listRange_resume (after := canonical) (profile := profile) (ready := ready)
    (dispatch := canonicalDispatch) inst area count pointer canonNext canonicalResume canonicalBody canonicalAt
  dsimp only at checkPrefix canonPrefix
  rw [destination.listRange_body, sized] at checkPrefix
  rw [destination.listRange_body, canonSize] at canonPrefix
  by_cases alignment : pointer ≠ alignTo pointer area.alignment
  · simp only [ite_eq_left alignment] at checkPrefix canonPrefix ⊢
    exact ⟨checkPrefix, canonPrefix⟩
  by_cases bounds : pointer + count * area.size ≤ bytes
  · simp only [ite_eq_right alignment, ite_eq_left bounds] at canonPrefix ⊢
    exact ⟨destination.listRange_recheck checked inst area count pointer plan checkNext checkedResume
      checkedBody checkedAt (not_ne_iff.mp alignment) sized bounds, canonPrefix⟩
  · simp only [ite_eq_right alignment, ite_eq_right bounds] at checkPrefix canonPrefix ⊢
    exact ⟨checkPrefix, canonPrefix⟩

theorem linked_range_resume {sig : Stored.Signature} {ready : HostReady (HostState sig)}
    (bindings : List (Binding sig)) {initial reached : Machine.Config (core3 grow) (HostState sig)}
    {trace : List (Label (core3 grow) (HostState sig))}
    (run : Machine.Steps profile ready (specDispatch ready (host bindings)) initial trace reached)
    (growing : initial.CoreGrowing)
    (installs : ∀ {current next leading label},
      Machine.Steps profile ready (specDispatch ready (host bindings)) initial leading current →
      Step profile ready (specDispatch ready (host bindings)) current label next →
      LinkedPayloadInstall bindings current label ∨ CoreGrowthInstall (specDispatch ready (host bindings)) current label)
    (destination : RecordDestination) (inst : InstId) (checked : destination.check initial.store = .ok ())
    (start length initialBytes : Nat) (sized : (core3 grow).memSize? initial.store.core destination.memory = some initialBytes)
    (oldBounds : start + length ≤ initialBytes) (area : Layout) (count pointer : Nat)
    (finish : Nat → Session grow sig (Ret (core3 grow))) (resume : Ret (core3 grow) → Session grow sig (Ret (core3 grow)))
    (resumes : resume (.nat pointer) = (validateListRange (destination.context inst) area count pointer >>= finish))
    {thread segments rest}
    (returned : reached.ctl = ⟨thread, .prog (.pure (.nat pointer)), .prog resume :: segments⟩ :: rest) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    let trapped := fun reason => ∃ steps, Machine.Steps profile ready dispatch reached
      (List.replicate steps .tau ++ [.trap reason]) (Machine.StepDefs.trapCfg reached)
    ptrTypeIn reached.store (destination.context inst) = destination.width ∧
    ∃ bytes, (core3 grow).memSize? reached.store.core destination.memory = some bytes ∧
      initialBytes ≤ bytes ∧ start + length ≤ bytes ∧
      if pointer ≠ alignTo pointer area.alignment then trapped .unalignedPointer
      else if pointer + count * area.size ≤ bytes then
        ∃ labels, (∀ label ∈ labels, label = .tau) ∧
          Machine.Steps profile ready dispatch reached labels
            { reached with ctl := ⟨thread, .prog (finish pointer), segments⟩ :: rest }
      else trapped .outOfBounds := by
  obtain ⟨prefixSteps, _⟩ := linked_payload_prefix_growth run growing installs
  obtain ⟨_, width, bytes, memSize, monotone, valid⟩ := prefixSteps.linked_region
    (destination.context inst) rfl (destination.check_width initial.store checked) sized oldBounds
  refine ⟨width, bytes, memSize, monotone, valid, ?_⟩
  have next := destination.listRange_resume (after := reached) (profile := profile) (ready := ready)
    (dispatch := specDispatch ready (host bindings)) inst area count pointer finish resume resumes returned
  dsimp only at next
  rw [destination.listRange_body inst area count pointer reached.store reached.host thread, memSize] at next
  by_cases aligned : pointer ≠ alignTo pointer area.alignment
  · simpa [aligned] using next
  · by_cases fits : pointer + count * area.size ≤ bytes
    · simp only [ite_eq_right aligned, ite_eq_left fits] at next ⊢
      obtain ⟨labels, silent, tracked⟩ := next
      exact ⟨labels, silent, (prefix_survives (tracked 0)).1⟩
    · simpa [aligned, fits] using next

theorem linked_dynamic_refusal {sig : Stored.Signature} {ready : HostReady (HostState sig)}
    (bindings : List (Binding sig)) {initial reached : Machine.Config (core3 grow) (HostState sig)}
    {trace : List (Label (core3 grow) (HostState sig))}
    (run : Machine.Steps profile ready (specDispatch ready (host bindings)) initial trace reached)
    (growing : initial.CoreGrowing)
    (installs : ∀ {current next leading label},
      Machine.Steps profile ready (specDispatch ready (host bindings)) initial leading current →
      Step profile ready (specDispatch ready (host bindings)) current label next →
      LinkedPayloadInstall bindings current label ∨ CoreGrowthInstall (specDispatch ready (host bindings)) current label)
    (destination : RecordDestination) (inst : InstId) (checked : destination.check initial.store = .ok ())
    (start length initialBytes : Nat) (sized : (core3 grow).memSize? initial.store.core destination.memory = some initialBytes)
    (oldBounds : start + length ≤ initialBytes) (element : Stored.TypeOf) (entries : List Field)
    (index pointer : Nat) (output : Stored.Lower.Output)
    (finish : Except RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow)))
    (resume : Ret (core3 grow) → Session grow sig (Ret (core3 grow)))
    (resumes : resume (.nat pointer) = (do
      let cx := destination.context inst
      let authority := Record.authority recordClaims Limits.spec cx
      let ptr ← validateListRange cx (layout destination.width element) entries.length pointer
      let verdict ← authority.prepare (Field.listObjects entries)
      let result ← checkedDynamicContinue Limits.spec Quirks.none cx authority destination.width
        element entries index output ptr verdict
      finish result)) {thread segments rest}
    (returned : reached.ctl = ⟨thread, .prog (.pure (.nat pointer)), .prog resume :: segments⟩ :: rest)
    (issue : RecordLower.Issue)
    (refusal : Record.prepare reached.store reached.host.writer (Field.listObjects entries) = .error issue) :
    let dispatch := specDispatch ready (host (grow := grow) bindings)
    let trapped := fun reason => ∃ steps, Machine.Steps profile ready dispatch reached
      (List.replicate steps .tau ++ [.trap reason]) (Machine.StepDefs.trapCfg reached)
    let area := layout destination.width element
    let stopped := match issue with
      | .preflight bad => RecordLower.Issue.field index (.afterAllocation bad)
      | other => RecordLower.Issue.nested index other
    ptrTypeIn reached.store (destination.context inst) = destination.width ∧
    ∃ bytes, (core3 grow).memSize? reached.store.core destination.memory = some bytes ∧
      initialBytes ≤ bytes ∧ start + length ≤ bytes ∧
      if pointer ≠ alignTo pointer area.alignment then trapped .unalignedPointer
      else if pointer + entries.length * area.size ≤ bytes then
        ∃ labels, (∀ label ∈ labels, label = .tau) ∧
          Machine.Steps profile ready dispatch reached labels
            { reached with ctl := ⟨thread, .prog (finish (.error stopped)), segments⟩ :: rest }
      else trapped .outOfBounds := by
  let cx := destination.context (grow := grow) inst
  let authority := Record.authority (recordClaims (sig := sig)) Limits.spec cx
  let area := layout destination.width element
  let afterCheck := fun addr verdict => checkedDynamicContinue Limits.spec Quirks.none cx authority
    destination.width element entries index output addr verdict >>= finish
  let afterRange := fun addr => authority.prepare (Field.listObjects entries) >>= afterCheck addr
  have resumeRange : resume (.nat pointer) = (validateListRange cx area entries.length pointer >>= afterRange) :=
    resumes
  obtain ⟨width, bytes, memSize, monotone, valid, range⟩ := linked_range_resume bindings run growing installs destination inst
    checked start length initialBytes sized oldBounds area entries.length pointer afterRange resume resumeRange returned
  dsimp only
  refine ⟨width, bytes, memSize, monotone, valid, ?_⟩
  by_cases misaligned : pointer ≠ alignTo pointer (layout destination.width element).alignment
  · simpa [area, misaligned] using range
  · by_cases fits : pointer + entries.length * (layout destination.width element).size ≤ bytes
    · rw [ite_eq_right misaligned, ite_eq_left fits]
      have aligned : pointer = alignTo pointer (layout destination.width element).alignment := by omega
      have stops := destination.listRange_recheck (profile := profile) (ready := ready)
        (dispatch := specDispatch ready (host bindings)) reached inst area entries.length pointer
        (Field.listObjects entries) afterCheck resume resumes returned aligned memSize fits
      rw [refusal] at stops
      obtain ⟨labels, silent, tracked⟩ := stops
      refine ⟨labels, silent, ?_⟩
      cases issue <;> simpa only [afterCheck, checkedDynamicContinue, pure_bind] using (prefix_survives (tracked 0)).1
    · simpa [area, misaligned, fits] using range

theorem record_field_guard (run : CoreGrowthSteps profile ready dispatch before trace after)
    (destination : RecordDestination) (inst : InstId) (checked : destination.check before.store = .ok ())
    (fields : List Layout) (base index offset bytes : Nat) (field : Layout)
    (aligned : (recordAlignment fields).bytes ∣ base)
    (member : fields[index]? = some field) (placed : (fieldOffsets base fields)[index]? = some offset)
    (sized : (core3 grow).memSize? before.store.core destination.memory = some bytes)
    (bounds : base + (recordLayout fields).size ≤ bytes)
    (finish : P (core3 grow) Host (Ret (core3 grow))) {thread segments rest}
    (focused : after.ctl = ⟨thread, .prog (checkInBounds (destination.context inst) offset field.size >>= fun _ => finish),
      segments⟩ :: rest) :
    offset % field.alignment.bytes = 0 ∧
    CoreGrowthSteps profile ready dispatch after [.tau]
      { after with ctl := ⟨thread, .prog finish, segments⟩ :: rest } := by
  obtain ⟨_, placedAlign, placedBound⟩ := recordLayout_field_fits fields base index offset field aligned member placed
  obtain ⟨_, _, reachedBytes, reachedSize, _, fits⟩ := run.linked_region (destination.context inst) rfl
    (destination.check_width before.store checked) sized bounds
  let next := fun (current : CStore (core3 grow)) =>
    (orTrap (.internal "dangling memory address") ((core3 grow).memSize? current.core destination.memory) >>=
      fun size => trapIf (decide (offset + field.size > size)) .outOfBounds) >>= fun _ => finish
  have get : after.ctl = ⟨thread, .prog (.op .get next), segments⟩ :: rest := focused
  have safe : ¬ offset + field.size > reachedBytes := Nat.not_lt.mpr (Nat.le_trans placedBound fits)
  have completed : next after.store = finish := by
    simp [next, reachedSize, orTrap, trapIf, safe]
  have step := Step.get (prof := profile) (hr := ready) (dispatch := dispatch) get
  rw [completed] at step
  refine ⟨placedAlign, .cons ?_ step (.refl _)⟩
  simp only [CoreUpdateGrows, get]

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadCollection
