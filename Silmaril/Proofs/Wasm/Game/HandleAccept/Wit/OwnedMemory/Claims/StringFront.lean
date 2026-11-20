module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Defs
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
import Silmaril.Wasm.Component.Reference.Canon.Strings.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.StringFront

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix

variable {E : CoreEngine} {grow : SingleThreaded.GrowOracle} {Host Result : Type}

theorem factor (cx : LiftLowerContext E) (ptr : Nat) (steps : List StoreStep) :
    ((stringFront cx ptr steps : P E Host (StringFront steps.length)) >>= StringFront.remaining cx) = runStoreSteps cx ptr steps := by
  induction steps generalizing ptr with
  | nil => rfl
  | cons action rest ih =>
    have remaining (front : StringFront rest.length) :
        (StringFront.remaining (Host := Host) cx front.weaken) = front.remaining cx := by
      cases front <;> rfl
    have tail (next : Nat) : Prog.bind (stringFront cx next rest : P E Host (StringFront rest.length)) (StringFront.remaining cx) =
        runStoreSteps cx next rest := ih next
    cases action with
    | allocate | reallocate => rfl
    | _ => simp only [stringFront, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind', remaining, runStoreSteps_cons, tail]

private def LocalOp : Op (core3 grow) Host → Prop
  | .get | .trap _ => True
  | .modify update => ∀ store, Core3.Grows store.core (update store).core
  | _ => False

local notation "Closed" => Prog.Every (S := Eff (core3 grow) Host) LocalOp

private theorem closedGet : Closed (getStore : P (core3 grow) Host _) := .op trivial (fun _ => .pure _)

private theorem closedTrap (reason : TrapReason) : Closed (trap reason : P (core3 grow) Host Result) :=
  .op trivial (fun answer => nomatch answer)

private theorem closedOrTrap (reason : TrapReason) (value : Option Result) :
    Closed (orTrap reason value : P (core3 grow) Host Result) := by
  cases value
  · exact closedTrap reason
  · exact .pure _

private theorem closedRead (cx : LiftLowerContext (core3 grow)) (ptr size : Nat) :
    Closed (readMem cx ptr size : P (core3 grow) Host ByteArray) := by
  unfold readMem memAddr
  exact (closedOrTrap .noMemory cx.opts.memory).bind fun memory => closedGet.bind fun store =>
    closedOrTrap .outOfBounds ((core3 grow).memRead? store.core memory ptr size)

private theorem closedWrite (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (data : ByteArray) :
    Closed (writeMem cx ptr data : P (core3 grow) Host Unit) := by
  unfold writeMem memAddr
  refine (closedOrTrap .noMemory cx.opts.memory).bind fun memory => closedGet.bind fun store => ?_
  split
  · exact closedTrap _
  · exact .op (fun atStore => writeMemSt_grows atStore memory ptr data) (fun _ => .pure _)

private theorem closedTrapIf (condition : Bool) (reason : TrapReason) :
    Closed (trapIf condition reason : P (core3 grow) Host Unit) := by
  cases condition
  · exact .pure _
  · exact closedTrap reason

private theorem closedAction (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (action : StoreStep)
    (localAction : LocalStringStep action) : Closed (runStoreStep cx ptr action : P (core3 grow) Host Nat) := by
  cases action with
  | allocate | reallocate => cases localAction
  | trapIfMisaligned alignment =>
    exact (closedTrapIf (decide (ptr ≠ alignTo ptr alignment)) .unalignedPointer).bind (fun _ => .pure _)
  | trapIfOutOfBounds size =>
    unfold runStoreStep checkInBounds memLen memAddr
    simp only [Prog.bind_eq, Prog.bind_assoc]
    exact (closedOrTrap .noMemory cx.opts.memory).bind fun memory => closedGet.bind fun store =>
      (closedOrTrap (.internal "dangling memory address") ((core3 grow).memSize? store.core memory)).bind fun bytes =>
        (closedTrapIf (decide (ptr + size > bytes)) .outOfBounds).bind (fun _ => .pure _)
  | write offset data => exact (closedWrite cx (ptr + offset) data.toByteArray).bind (fun _ => .pure _)
  | inflateLatin1 size => exact (closedRead cx ptr (2 * size)).bind fun data =>
    (closedWrite cx ptr (memInflateLatin1 data.toList 0 size).toByteArray).bind (fun _ => .pure _)
  | deflateUtf16 size => exact (closedRead cx ptr (2 * size)).bind fun data =>
    (closedWrite cx ptr (memDeflateUtf16 data.toList 0 size).toByteArray).bind (fun _ => .pure _)

private theorem closedFront (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (steps : List StoreStep) :
    Closed (stringFront cx ptr steps : P (core3 grow) Host (StringFront steps.length)) := by
  induction steps generalizing ptr with
  | nil => exact .pure _
  | cons action rest ih =>
    have nextClosed (next : Nat) : Closed ((stringFront cx next rest : P _ Host _) >>= fun front => pure front.weaken) :=
      (ih next).bind (fun _ => .pure _)
    cases action with
    | allocate | reallocate => exact .pure _
    | trapIfMisaligned alignment => exact (closedAction cx ptr (.trapIfMisaligned alignment) trivial).bind nextClosed
    | trapIfOutOfBounds size => exact (closedAction cx ptr (.trapIfOutOfBounds size) trivial).bind nextClosed
    | write offset data => exact (closedAction cx ptr (.write offset data) trivial).bind nextClosed
    | inflateLatin1 size => exact (closedAction cx ptr (.inflateLatin1 size) trivial).bind nextClosed
    | deflateUtf16 size => exact (closedAction cx ptr (.deflateUtf16 size) trivial).bind nextClosed

private theorem closedTail (cx : LiftLowerContext (core3 grow)) (width : AddrType) (output : Stored.Lower.Output)
    (plan : StorePlan) (ptr : Nat) : Closed (stringPlanTail cx width output plan ptr : P (core3 grow) Host output.Result) := by
  cases output with
  | flat => exact .pure _
  | memory address =>
    have size : Closed (ptrSize cx : P (core3 grow) Host Nat) := closedGet.bind (fun _ => .pure _)
    exact size.bind fun bytes => (closedWrite cx address (strWordBytes bytes ptr)).bind fun _ =>
      closedWrite cx (address + bytes) (strWordBytes bytes plan.taggedCodeUnits)

variable {profile : ProfileKind} {ready : HostReady Host}
  {dispatch : Call (core3 grow) → P (core3 grow) Host (Ret (core3 grow))}

private theorem prepend {left right left' right' : Config (core3 grow) Host} {check canon}
    {checkNext canonNext : Result → P (core3 grow) Host (Ret (core3 grow))}
    (leftGrows : CoreUpdateGrows left) (rightGrows : CoreUpdateGrows right)
    (leftStep : Step profile ready dispatch left .tau left') (rightStep : Step profile ready dispatch right .tau right')
    (leftEdit : ReturnFrame.Occurrence.transitionEdit left .tau = .same)
    (rightEdit : ReturnFrame.Occurrence.transitionEdit right .tau = .same)
    (leftHost : left'.host = left.host) (rightHost : right'.host = right.host)
    (leftEnd : ∀ store outcome, localLeafEnd left' left.host store check.thread check.frames check.rest checkNext outcome =
      localLeafEnd left left.host store check.thread check.frames check.rest checkNext outcome)
    (rightEnd : ∀ store outcome, localLeafEnd right' right.host store canon.thread canon.frames canon.rest canonNext outcome =
      localLeafEnd right right.host store canon.thread canon.frames canon.rest canonNext outcome)
    (next : StringLocalCut profile ready dispatch left' right' check canon checkNext canonNext) :
    StringLocalCut profile ready dispatch left right check canon checkNext canonNext := by
  obtain ⟨store, outcome, labels, observed, lhs, rhs, tracks⟩ := next
  rw [leftHost, leftEnd] at lhs
  rw [rightHost, rightEnd] at rhs
  refine ⟨store, outcome, .tau :: labels, ?_, .cons leftGrows leftStep lhs, .cons rightGrows rightStep rhs, ?_⟩
  · cases outcome with
    | ok value => exact observed
    | error reason =>
      obtain ⟨count, rfl⟩ := observed
      exact ⟨count + 1, rfl⟩
  · intro value returned depth
    obtain ⟨keptLeft, keptRight⟩ := tracks value returned depth
    rw [leftHost, leftEnd] at keptLeft
    rw [rightHost, rightEnd] at keptRight
    exact ⟨.step leftStep (by rw [leftEdit]; rfl) keptLeft, .step rightStep (by rw [rightEdit]; rfl) keptRight⟩

private theorem closedCut {body : P (core3 grow) Host Result} (closed : Closed body)
    (left right : Config (core3 grow) Host) (check canon : Cursor (E := core3 grow) Host)
    (checkNext canonNext : Result → P (core3 grow) Host (Ret (core3 grow)))
    (same : left.store = right.store) (checkAt : left.ctl = check.control (body >>= checkNext))
    (canonAt : right.ctl = canon.control (body >>= canonNext)) :
    StringLocalCut profile ready dispatch left right check canon checkNext canonNext := by
  induction closed generalizing left right with
  | pure value =>
    have leftEnd : localLeafEnd left left.host right.store check.thread check.frames check.rest checkNext (.ok value) = left := by
      cases left
      simp_all [localLeafEnd, Cursor.control]
    have rightEnd : localLeafEnd right right.host right.store canon.thread canon.frames canon.rest canonNext (.ok value) = right := by
      cases right
      simp_all [localLeafEnd, Cursor.control]
    refine ⟨right.store, .ok value, [], rfl, leftEnd ▸ .refl _, rightEnd ▸ .refl _, ?_⟩
    intro _ _ depth
    rw [leftEnd, rightEnd]
    exact ⟨.done _ _, .done _ _⟩
  | @op effect continuation admitted _ ih =>
    cases effect with
    | get =>
      refine prepend (by simp [CoreUpdateGrows, checkAt, Cursor.control, Prog.bind])
        (by simp [CoreUpdateGrows, canonAt, Cursor.control, Prog.bind]) (.get checkAt) (.get canonAt) ?_ ?_ rfl rfl
        (fun _ result => by cases result <;> rfl) (fun _ result => by cases result <;> rfl) ?_
      · rw [ReturnFrame.Occurrence.transitionEdit, checkAt]; rfl
      · rw [ReturnFrame.Occurrence.transitionEdit, canonAt]; rfl
      · exact ih right.store _ _ same (congrArg (fun store => check.control (continuation store >>= checkNext)) same) rfl
    | modify update =>
      refine prepend (by simpa [CoreUpdateGrows, checkAt, Cursor.control, Prog.bind] using admitted left.store)
        (by simpa [CoreUpdateGrows, canonAt, Cursor.control, Prog.bind] using admitted right.store)
        (.modify checkAt) (.modify canonAt) ?_ ?_ rfl rfl (fun _ result => by cases result <;> rfl)
        (fun _ result => by cases result <;> rfl) (ih () _ _ (congrArg update same) rfl rfl)
      · rw [ReturnFrame.Occurrence.transitionEdit, checkAt]; rfl
      · rw [ReturnFrame.Occurrence.transitionEdit, canonAt]; rfl
    | trap reason =>
      refine ⟨right.store, .error reason, [.trap reason], ⟨0, rfl⟩, ?_, ?_, fun _ returned => by cases returned⟩
      · rw [← same]
        exact .cons (by simp [CoreUpdateGrows, checkAt, Cursor.control, Prog.bind]) (.trap checkAt) (.refl _)
      · exact .cons (by simp [CoreUpdateGrows, canonAt, Cursor.control, Prog.bind]) (.trap canonAt) (.refl _)
    | _ => contradiction

theorem cut (cx : LiftLowerContext (core3 grow)) (ptr : Nat) (steps : List StoreStep)
    (left right : Config (core3 grow) Host) (check canon : Cursor (E := core3 grow) Host)
    (checkNext canonNext : Nat → P (core3 grow) Host (Ret (core3 grow))) (same : left.store = right.store)
    (checkAt : left.ctl = check.control (runStoreSteps cx ptr steps >>= checkNext))
    (canonAt : right.ctl = canon.control (runStoreSteps cx ptr steps >>= canonNext)) :
    StringLocalCut profile ready dispatch left right check canon
      (fun front : StringFront steps.length => front.remaining cx >>= checkNext)
      (fun front : StringFront steps.length => front.remaining cx >>= canonNext) := by
  apply closedCut (closedFront cx ptr steps) left right check canon _ _ same
  · simpa only [Prog.bind_eq, Prog.bind_assoc] using checkAt.trans
      (congrArg (fun body => check.control (body >>= checkNext)) (factor (Host := Host) cx ptr steps).symm)
  · simpa only [Prog.bind_eq, Prog.bind_assoc] using canonAt.trans
      (congrArg (fun body => canon.control (body >>= canonNext)) (factor (Host := Host) cx ptr steps).symm)

theorem descriptor (cx : LiftLowerContext (core3 grow)) (width : AddrType) (output : Stored.Lower.Output)
    (plan : StorePlan) (ptr : Nat) (left right : Config (core3 grow) Host) (check canon : Cursor (E := core3 grow) Host)
    (checkNext canonNext : output.Result → P (core3 grow) Host (Ret (core3 grow))) (same : left.store = right.store)
    (checkAt : left.ctl = check.control (stringPlanTail cx width output plan ptr >>= checkNext))
    (canonAt : right.ctl = canon.control (stringPlanTail cx width output plan ptr >>= canonNext)) :
    StringLocalCut profile ready dispatch left right check canon checkNext canonNext :=
  closedCut (closedTail cx width output plan ptr) left right check canon checkNext canonNext same checkAt canonAt

theorem collectionDescriptor (cx : LiftLowerContext (core3 grow)) (width : AddrType) (output : Stored.Lower.Output)
    (ptr count : Nat) (left right : Config (core3 grow) Host) (check canon : Cursor (E := core3 grow) Host)
    (checkNext canonNext : output.Result → P (core3 grow) Host (Ret (core3 grow))) (same : left.store = right.store)
    (checkAt : left.ctl = check.control (ListLower.publish cx width ptr count output >>= checkNext))
    (canonAt : right.ctl = canon.control (ListLower.publish cx width ptr count output >>= canonNext)) :
    StringLocalCut profile ready dispatch left right check canon checkNext canonNext := by
  have localProgram : Closed (ListLower.publish cx width ptr count output : P (core3 grow) Host output.Result) := by
    cases output with
    | flat => exact .pure _
    | memory address =>
      have size : Closed (ptrSize cx : P (core3 grow) Host Nat) := closedGet.bind (fun _ => .pure _)
      exact size.bind fun bytes => (closedWrite cx address (intToLE bytes ptr)).bind fun _ =>
        closedWrite cx (address + bytes) (intToLE bytes count)
  exact closedCut localProgram left right check canon checkNext canonNext same checkAt canonAt

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.StringFront
