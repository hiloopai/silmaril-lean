module

import Silmaril.Containers.Machine.Thms
import Silmaril.Containers.TypedSyscall.Thms
import Silmaril.Process.TypedSyscall.Linux.Defs
import Silmaril.Semantics.Streams.Thms

namespace Silmaril.Containers.TypedSyscall

open Silmaril.Process (Memory Byte)
open Silmaril.Process.TypedSyscall
open Silmaril.Process.Syscall (Descriptor Event State)

private inductive Request where
  | getByte (address : Nat)
  | exit (status : Nat)

private def client : Signature := ⟨Request, fun
  | .getByte _ => Option Nat
  | .exit _ => Empty⟩

private def toLinux : client.Hom Linux.signature where
  request
    | .getByte address => .read 0 address 1
    | .exit status => .exit status
  response req reply := match req with
    | .getByte _ => match reply with | .ok count => some count | .error _ => none
    | .exit _ => reply

private inductive Stage where
  | ready
  | got (count : Option Nat)

private def cpu : Cpu client Nat Stage State Stop := fun address stage _ =>
  match stage with
  | .ready => .call (.getByte address) Stage.got
  | .got count => .call (.exit (if count = some 1 then 0 else 1)) (fun impossible => nomatch impossible)

private def memory : Memory := ⟨[⟨0x1000, 1, ⟨true, true, false⟩⟩], Memory.install ∅ 0x1000 [0]⟩
private def stdin : Descriptor := ⟨true, false, .ofList [0x41], 0, []⟩
private def initial : State := ⟨memory, fun fd => if fd = 0 then some stdin else none, none⟩
private def received : State := { initial.setDescriptor 0 { stdin with cursor := 1 } with
  memory := { memory with bytes := Memory.install memory.bytes 0x1000 [0x41] } }

private def isInput : Event → Bool
  | .read .. => true
  | _ => false

private def model : Mach.MachRuntime Nat (Nat × Stage × State) Event where
  load address := .ok (address, .ready, initial)
  machine := completedMachine isInput (Step (cpu.push toLinux) Linux.kernel (Scheduler.single Stage))

private def readEvent : Event := .read 0 [0x41]

private theorem readStep : model.machine.step (0x1000, .running .ready initial) (.ev readEvent)
    (0x1000, .running (.got (some 1)) received) := by
  refine ⟨rfl, ?_, some readEvent, rfl, ?_⟩
  · intro equal; cases equal
  refine ⟨readEvent, .returned (.ok 1) received, ?_, rfl, rfl⟩
  refine Silmaril.Process.Syscall.Step.readSome (descriptor := stdin) rfl rfl rfl ?_
    (by decide) (by decide) (by decide) (by decide) rfl
  intro index bound
  have zero : index = 0 := by simp at bound; omega
  subst index
  rfl

private theorem exitStep : model.machine.step (0x1000, .running (.got (some 1)) received) (.ev (.exit 0))
    (0x1000, .exited 0 { received with exited := some 0 }) := by
  refine ⟨rfl, ?_, some (.exit 0), rfl, ?_⟩
  · intro equal; cases equal
  exact ⟨.exit 0, .exited 0 _, Silmaril.Process.Syscall.Step.exit 0 rfl, rfl, rfl⟩

private def events : List Event := [readEvent, .exit 0]

example : model.toRuntime.beh 0x1000 (.done events (.exited 0)) := by
  apply (Mach.MachRuntime.beh_iff ..).mpr
  exact Or.inr ⟨_, rfl, _, .final rfl (.ev readStep (.ev exitStep (.refl _))) rfl, rfl⟩

example : model.toRuntime.beh 0x1000 =
    (model.withMachine
      (completedMachine isInput (Step cpu (Linux.kernel.pull toLinux) (Scheduler.single Stage)))
      Mach.seqPolicy).toRuntime.beh 0x1000 := by
  rw [← completedMachine_push toLinux cpu Linux.kernel (Scheduler.single Stage) isInput]
  rfl

private def observation : List (Check.Obs Event) := [.ev readEvent, .ev (.exit 0), .stop (.exited 0)]

example : Check.ObsPrefix (.done events (.exited 0)) observation := Or.inr ⟨_, _, rfl, rfl⟩

example : (Streams.Chunks.ofList [[.ev readEvent], [.ev (.exit 0), .stop (.exited 0)]]).limit =
    stoppedWord events (.exited 0) := Streams.Chunks.limit_ofList _

private def bytesIn : Event → List Byte
  | .read _ bytes => bytes
  | _ => []

example : (stoppedWord events (.exited 0)).map (relabel bytesIn) =
    .fin [.ev [0x41], .ev [], .stop (.exited 0)] := stoppedWord_map ..

example : (Check.vmonitor (fun _ : Event => true)).process true observation = true := rfl

private def stoppingMachine (reason : Stop) := completedMachine (fun _ : Event => false)
  (Step (fun (_ : Unit) (_ : Stage) (_ : State) => (.stop reason : Action client Stage State Stop))
    (Linux.kernel.pull toLinux) (Scheduler.single Stage))

example (reason : Stop) : (stoppingMachine reason).Run Mach.seqPolicy ((), .ready, initial)
    (.done [] reason) := by
  have edge : (stoppingMachine reason).step ((), .running .ready initial) .tau ((), .stopped reason) := by
    refine ⟨rfl, ?_, none, rfl, rfl, rfl⟩
    intro equal; cases equal
  exact .final rfl (.internal (a := .tau) trivial edge (.refl _)) rfl

example : (Check.vmonitor (fun _ : Event => true)).process true
    [.ev readEvent, .stop (.undefined .memory)] = false := rfl

#print axioms completedMachine_push
#print axioms stoppedWord_map
#print axioms relabel_vlang

end Silmaril.Containers.TypedSyscall
