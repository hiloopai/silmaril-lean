module

public import Silmaril.Process.LPS.Problems.Sha256Cli.Segments
public import Silmaril.Process.CLI.X86Linux.SilentTransport
public import Silmaril.Process.CLI.X86Linux.SyscallInversion
public import Silmaril.Process.CLI.Sha256Cli.FullBlockTail
public import Silmaril.Process.CLI.Sha256Cli.FullReadRepeat
public import Silmaril.Process.CLI.Sha256Cli.DriverMemory
public import Silmaril.Process.CLI.Sha256Cli.LoadedStartup
public import Silmaril.Process.CLI.Sha256Cli.EmptyCall

/-! # Segment `loop` of the `sha256` end-to-end proof

`loop_segment_proof : LoopSegment fun _ => True`: from every CLI launch of the pinned image,
under every read partition the reliable environment admits, every execution keeps `Ok`, can
always move, and reaches `LoopEnd` (the whole message consumed, at the loop-head `read` with
H the fold of the full blocks and the tail buffered, or, for the empty message, at the first
`read`).

Status: VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.CLI.Sha256Cli.LoopRuns

/-! ## Post-syscall silent segments (VERIFIED)

The chain's read lemmas (`BufferedTailFrame.Ready.read`, `first_read`,
`FullBlockIteration.first_full_read`) bundle the `read` step with the silent code after it, for a
`R11` value chosen by the caller. A `Leads` proof must instead follow the environment's own
choice of step, so these variants start just after the syscall, from the actual returned core
(any `R11`). Their bodies reuse the chain's instruction lemmas unchanged. `full_after` is new:
it covers a read that fills a *partially* filled buffer to 64 bytes (the chain covered only
64-byte reads into an empty buffer). -/

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 («Word»)
open Silmaril.Crypto.X86.Sha256O2 (stateOf)

set_option maxRecDepth 100000

/-- A positive buffered read below 64, after the syscall. -/
theorem short_after {initial : Memory} {stack : «Word»} {c : Core} {before after : Syscall.State}
    {tail : List Byte} {total : «Word»} {state : Silmaril.Crypto.SHA256.State}
    {event : Event} {amount : Nat}
    (ready : BufferedTailFrame.Ready initial stack c before tail total state)
    (positive : 0 < amount) (room : tail.length + amount < 64) (flags : «Word»)
    (effect : Syscall.Step before (.read 0 (0x401620 + tail.length) (64 - tail.length))
      event (.returned (.ok amount)) after) :
    ∃ (chunk : List Byte) (next : Core),
      chunk.length = amount ∧ event = .read 0 chunk ∧
      Proc.Runs X86Linux.isa Env.linux ⟨ShortReadFrame.returnedCore c (.ok amount) flags, after⟩ []
        ⟨next, after⟩ ∧
      BufferedTailFrame.Ready initial stack next after (tail ++ chunk)
        (total + BitVec.ofNat 64 amount) state := by
  obtain ⟨chunk, length, eventEq, running, stored⟩ := BufferedTailFrame.read_stored positive effect
  have nextFrame := ready.frame.trans (stored.writesWithin (by
    intro offset bound
    dsimp [DriverMemory.Above]
    omega))
  have headRead := (stored.readWith_disjoint .read 0x401620 tail.length (Or.inl (by omega))).trans ready.copied
  have tailRead : after.memory.readBytes (0x401620 + tail.length) chunk.length = some chunk :=
    stored.readWith_self (ready.frame.bss_permitted .read rfl _ _ (by omega) (by omega))
  have copied : after.memory.readBytes 0x401620 (tail ++ chunk).length = some (tail ++ chunk) := by
    simpa only [List.length_append] using Memory.readBytes_append headRead tailRead
  obtain ⟨bytes, observed, value⟩ := ready.hash
  have observed' : after.memory.readBytes 0x401660 32 = some bytes :=
    (stored.readWith_disjoint .read _ _ (Or.inr (by omega))).trans observed
  let returned := ShortReadFrame.returnedCore c (.ok amount) flags
  have rax : returned.read .rax = BitVec.ofNat 64 amount := by
    simp [returned, ShortReadFrame.returnedCore, resultWord, X86.State.read, X86.State.write,
      Machine.RegisterFile.write]
  have r8 : returned.read .r8 = BitVec.ofNat 64 tail.length := ready.registers.filled
  have rbp : returned.read .rbp = 64 := ready.registers.blockSize
  have body := ShortReadBranches.positive_loop_below64 returned after tail.length amount
    positive room running nextFrame.code rfl rax r8 rbp
  have registers := ShortRead.next_ready returned tail.length amount rbp
  have count : returned.read .rbx = total := ready.registers.total
  rw [count] at registers
  refine ⟨chunk, ShortRead.nextCore returned tail.length amount, length, eventEq, body, ?_⟩
  exact ⟨by simpa only [List.length_append, length] using room,
    by simpa only [List.length_append, length] using registers, running,
    (ShortRead.next_rsp _ _ _).trans ready.rsp, nextFrame, copied, bytes, observed', value⟩

private theorem positive_conditions {amount : Nat} (positive : 0 < amount) (bound : amount ≤ 64) :
    X86.Ext.Cond.eval (X86.Ext.logicFlagsN (BitVec.ofNat 64 amount)) .e = some false ∧
      X86.Ext.Cond.eval (X86.Ext.logicFlagsN (BitVec.ofNat 64 amount)) .s = some false := by
  have all : ∀ index : Fin 64,
      X86.Ext.Cond.eval (X86.Ext.logicFlagsN (BitVec.ofNat 64 (index.val + 1))) .e = some false ∧
        X86.Ext.Cond.eval (X86.Ext.logicFlagsN (BitVec.ofNat 64 (index.val + 1))) .s = some false := by
    decide
  have index : amount - 1 < 64 := by omega
  have restored : amount - 1 + 1 = amount := by omega
  simpa only [restored] using all ⟨amount - 1, index⟩

/-- TEST/JE/TEST/JS of any positive return up to 64, reaching the counter path at `0x400185`. -/
theorem positive_branch (c : Core) (s : Syscall.State) (amount : Nat)
    (positive : 0 < amount) (bound : amount ≤ 64)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400177) (rax : c.read .rax = BitVec.ofNat 64 amount) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
      ⟨{ c with rip := 0x400185, flags := X86.Ext.logicFlagsN (BitVec.ofNat 64 amount) }, s⟩ := by
  have conditions := positive_conditions positive bound
  let tested : Core := { c with
    rip := 0x40017a, flags := X86.Ext.logicFlagsN (BitVec.ofNat 64 amount) }
  have test : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [] ⟨tested, s⟩ := by
    apply Output.retire (entry := Binary.i_400177) (by simp [Binary.transcript]) intact running
      (by simp [pc, Binary.i_400177])
    simp [Entry.denote, X86Linux.execResult, Binary.i_400177, X86.Ext.exec,
      X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire, tested, pc, rax]
    dsimp (config := { instances := true }) only [X86.Ext.Sz.bits]
    simp only [BitVec.and_self]
  let checked : Core := { tested with rip := 0x40017c }
  have nonzero : Proc.Step X86Linux.isa Env.linux (⟨tested, s⟩ : Output.PS) [] ⟨checked, s⟩ := by
    apply Output.retire (entry := Binary.i_40017a) (by simp [Binary.transcript]) intact running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_40017a, X86.Ext.exec, checked, tested]
    erw [conditions.1]
  let signed : Core := { checked with
    rip := 0x40017f, flags := X86.Ext.logicFlagsN (BitVec.ofNat 64 amount) }
  have signTest : Proc.Step X86Linux.isa Env.linux (⟨checked, s⟩ : Output.PS) [] ⟨signed, s⟩ := by
    apply Output.retire (entry := Binary.i_40017c) (by simp [Binary.transcript]) intact running rfl
    have value : c.regs .rax = BitVec.ofNat 64 amount := rax
    simp [Entry.denote, X86Linux.execResult, Binary.i_40017c, X86.Ext.exec,
      X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire, signed, checked, tested,
      X86.State.read, value]
    dsimp (config := { instances := true }) only [X86.Ext.Sz.bits]
    simp only [BitVec.and_self]
  let positiveCore : Core := { signed with rip := 0x400185 }
  have signBranch : Proc.Step X86Linux.isa Env.linux (⟨signed, s⟩ : Output.PS) [] ⟨positiveCore, s⟩ := by
    apply Output.retire (entry := Binary.i_40017f) (by simp [Binary.transcript]) intact running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_40017f, X86.Ext.exec, positiveCore, signed]
    erw [conditions.2]
  simpa only [List.nil_append, positiveCore, signed, checked, tested] using
    (Silmaril.Machine.Trace.Runs.cons test (.cons nonzero (.cons signTest (.single signBranch))))

/-- A positive buffered read that fills the buffer to exactly 64 bytes (any previous fill),
after the syscall: the full-block compression and restart. -/
theorem full_after {initial : Memory} {top : Nat} {c : Core} {before after : Syscall.State}
    {tail : List Byte} {total : «Word»} {state : Silmaril.Crypto.SHA256.State}
    {event : Event} {amount : Nat}
    (ready : BufferedTailFrame.Ready initial (BitVec.ofNat 64 (top - 32)) c before tail total state)
    (positive : 0 < amount) (full : tail.length + amount = 64) (flags : «Word»)
    (effect : Syscall.Step before (.read 0 (0x401620 + tail.length) (64 - tail.length))
      event (.returned (.ok amount)) after)
    (geometry : CompressionStack.Geometry top) (stack : CompressionStack.Mapping initial top) :
    ∃ (chunk : List Byte) (next : Core) (memory : Memory),
      chunk.length = amount ∧ event = .read 0 chunk ∧
      Proc.Runs X86Linux.isa Env.linux ⟨ShortReadFrame.returnedCore c (.ok amount) flags, after⟩ []
        ⟨next, { after with memory := memory }⟩ ∧
      FullBlockIteration.Ready initial top next { after with memory := memory }
        (total + BitVec.ofNat 64 amount) (Driver.compressBlock state (tail ++ chunk)) := by
  obtain ⟨chunk, length, eventEq, running, stored⟩ := BufferedTailFrame.read_stored positive effect
  have nextFrame := ready.frame.trans (stored.writesWithin (by
    intro offset bound
    dsimp [DriverMemory.Above]
    omega))
  have headRead := (stored.readWith_disjoint .read 0x401620 tail.length (Or.inl (by omega))).trans ready.copied
  have tailRead : after.memory.readBytes (0x401620 + tail.length) chunk.length = some chunk :=
    stored.readWith_self (ready.frame.bss_permitted .read rfl _ _ (by omega) (by omega))
  have blockRead : after.memory.readBytes 0x401620 64 = some (tail ++ chunk) := by
    have joined := Memory.readBytes_append headRead tailRead
    rwa [length, full] at joined
  obtain ⟨stateBytes, stateRead, hash⟩ := ready.hash
  have stateRead' : after.memory.readBytes 0x401660 32 = some stateBytes :=
    (stored.readWith_disjoint .read _ _ (Or.inr (by omega))).trans stateRead
  let returned := ShortReadFrame.returnedCore c (.ok amount) flags
  have rax : returned.read .rax = BitVec.ofNat 64 amount := by
    simp [returned, ShortReadFrame.returnedCore, resultWord, X86.State.read, X86.State.write,
      Machine.RegisterFile.write]
  have toCounters := positive_branch returned after amount positive (by omega) running
    nextFrame.code rfl rax
  have advanced := FullRead.advance
    { returned with rip := 0x400185, flags := X86.Ext.logicFlagsN (BitVec.ofNat 64 amount) }
    after tail.length amount full running nextFrame.code rfl rax ready.registers.filled
    ready.registers.blockSize
  let call := FullRead.callCore
    { returned with rip := 0x400185, flags := X86.Ext.logicFlagsN (BitVec.ofNat 64 amount) }
    tail.length amount
  have callRsp : call.read .rsp = BitVec.ofNat 64 (top - 32) := by
    simpa [call, FullRead.callCore, ReadAdvance.countCore, returned, ShortReadFrame.returnedCore,
      X86.State.read, X86.State.write, Machine.RegisterFile.write] using ready.rsp
  have callTotal : call.read .rbx = total + BitVec.ofNat 64 amount := by
    simpa [call, FullRead.callCore, ReadAdvance.countCore, returned, ShortReadFrame.returnedCore,
      X86.State.read, X86.State.write, Machine.RegisterFile.write] using
        congrArg (· + BitVec.ofNat 64 amount) ready.registers.total
  have callSize : call.read .rbp = 64 := by
    simpa [call, FullRead.callCore, ReadAdvance.countCore, returned, ShortReadFrame.returnedCore,
      X86.State.read, X86.State.write, Machine.RegisterFile.write] using ready.registers.blockSize
  obtain ⟨next, memory, compressed, fresh⟩ := FullBlockIteration.compress_restart
    call after stateBytes (tail ++ chunk) (total + BitVec.ofNat 64 amount) running rfl callRsp
      rfl rfl callTotal callSize stateRead' blockRead nextFrame geometry stack
  rw [hash] at fresh
  exact ⟨chunk, next, memory, length, eventEq, by
    simpa only [List.append_nil] using (toCounters.append advanced).append compressed, fresh⟩

/-- The first positive read below 64, after the syscall (`BufferedTailFrame.first_read`). -/
theorem first_short_after {initial : Memory} {before after : Syscall.State}
    {stateBytes : List Byte} {amount : Nat} {event : Event}
    (c : Core) (flags : «Word») (positive : 0 < amount) (room : amount < 64)
    (frame : DriverMemory.Frame initial before.memory)
    (stateRead : before.memory.readBytes 0x401660 32 = some stateBytes)
    (effect : Syscall.Step before (.read 0 0x401620 64) event (.returned (.ok amount)) after) :
    ∃ (tail : List Byte) (next : Core),
      tail.length = amount ∧ event = .read 0 tail ∧
      Proc.Runs X86Linux.isa Env.linux ⟨ShortReadInit.returnedCore c amount flags, after⟩ []
        ⟨next, after⟩ ∧
      BufferedTailFrame.Ready initial (c.read .rsp) next after tail (BitVec.ofNat 64 amount)
        (stateOf stateBytes).toState := by
  obtain ⟨tail, length, eventEq, afterRunning, stored⟩ :=
    BufferedTailFrame.read_stored (fill := 0) positive effect
  have nextFrame := frame.trans (stored.writesWithin (by
    intro offset bound
    dsimp [DriverMemory.Above]
    omega))
  have copied : after.memory.readBytes 0x401620 tail.length = some tail :=
    stored.readWith_self (frame.bss_permitted .read rfl _ _ (by decide) (by omega))
  have observed : after.memory.readBytes 0x401660 32 = some stateBytes :=
    (stored.readWith_disjoint .read _ _ (Or.inr (by omega))).trans stateRead
  let returned := ShortReadInit.returnedCore c amount flags
  have rax : returned.read .rax = BitVec.ofNat 64 amount := by
    simp [returned, ShortReadInit.returnedCore, X86.State.read, X86.State.write,
      Machine.RegisterFile.write]
  have body := ShortReadBranches.first_positive_below64 returned after amount positive room
    afterRunning nextFrame.code rfl rax
  have registers : ShortRead.Ready (ShortReadBranches.firstNextCore returned amount) tail.length
      (BitVec.ofNat 64 amount) := by
    simpa [ShortReadBranches.firstNextCore, ShortReadBranches.initialCore, length,
      X86.State.read, X86.State.write, Machine.RegisterFile.write] using
        ShortRead.next_ready (ShortReadBranches.initialCore returned) 0 amount (by rfl)
  exact ⟨tail, ShortReadBranches.firstNextCore returned amount, length, eventEq, body,
    by omega, registers, afterRunning, by
      simp [ShortReadBranches.firstNextCore, ShortReadBranches.initialCore, returned,
        ShortReadInit.returnedCore, ShortRead.nextCore, X86.State.read, X86.State.write,
        Machine.RegisterFile.write], nextFrame, copied, stateBytes, observed, rfl⟩

/-- The first 64-byte read, after the syscall (`FullBlockIteration.first_full_read`). -/
theorem first_full_after {initial : Memory} {top : Nat} {before after : Syscall.State}
    {stateBytes : List Byte} {event : Event} (c : Core) (flags : «Word»)
    (rsp : c.read .rsp = BitVec.ofNat 64 (top - 32))
    (frame : DriverMemory.Frame initial before.memory)
    (stateRead : before.memory.readBytes 0x401660 32 = some stateBytes)
    (effect : Syscall.Step before (.read 0 0x401620 64) event (.returned (.ok 64)) after)
    (geometry : CompressionStack.Geometry top) (stack : CompressionStack.Mapping initial top) :
    ∃ (block : List Byte) (next : Core) (memory : Memory),
      block.length = 64 ∧ event = .read 0 block ∧
      Proc.Runs X86Linux.isa Env.linux ⟨ShortReadInit.returnedCore c 64 flags, after⟩ []
        ⟨next, { after with memory := memory }⟩ ∧
      FullBlockIteration.Ready initial top next { after with memory := memory } 64
        (Driver.compressBlock (stateOf stateBytes).toState block) := by
  obtain ⟨block, length, eventEq, afterRunning, stored⟩ := FullBlockIteration.full_read_stored effect
  have nextFrame : DriverMemory.Frame initial after.memory := frame.trans (stored.writesWithin (by
    intro offset bound
    dsimp [DriverMemory.Above]
    omega))
  have stateRead' : after.memory.readBytes 0x401660 32 = some stateBytes :=
    (stored.readWith_disjoint .read _ _ (Or.inr (by omega))).trans stateRead
  have blockRead : after.memory.readBytes 0x401620 64 = some block := by
    simpa only [Memory.readBytes, length] using stored.readWith_self
      (by rw [length]; exact frame.bss_permitted .read rfl _ _ (by decide) (by decide))
  let returned := ShortReadInit.returnedCore c 64 flags
  have toCall := FullRead.first_to_call returned after afterRunning nextFrame.code rfl rfl
  have callRsp : (FullRead.firstCallCore returned).read .rsp = BitVec.ofNat 64 (top - 32) := by
    simpa [FullRead.firstCallCore, FullRead.callCore, ReadAdvance.countCore,
      ShortReadBranches.initialCore, returned, ShortReadInit.returnedCore,
      X86.State.read, X86.State.write, Machine.RegisterFile.write] using rsp
  obtain ⟨next, memory, compressed, fresh⟩ := FullBlockIteration.compress_restart
    (FullRead.firstCallCore returned) after stateBytes block 64 afterRunning rfl callRsp
      rfl rfl rfl rfl stateRead' blockRead nextFrame geometry stack
  exact ⟨block, next, memory, length, eventEq, by
    simpa only [List.append_nil] using toCall.append compressed, fresh⟩

/-- The loop-head `read` traps. -/
theorem loop_trapped {initial : Memory} {stack : «Word»} {c : Core} {s : Syscall.State}
    {tail : List Byte} {total : «Word»} {state : Silmaril.Crypto.SHA256.State}
    (ready : BufferedTailFrame.Ready initial stack c s tail total state) :
    X86Linux.step c s.memory = .syscall { c with rip := 0x400177 } := by
  have actual := step_of_entry (core := c) (memory := s.memory) Binary.ok_400175.1
    (by simp [ready.registers.pc, Binary.i_400175]) (ready.frame.code _ (by simp [Binary.transcript]))
  simpa [Entry.denote, Binary.i_400175, ready.registers.pc] using actual

/-- The first `read` traps. -/
theorem first_trapped {initial : Memory} {c : Core} {s : Syscall.State}
    (frame : DriverMemory.Frame initial s.memory) (pc : c.rip = 0x400159) :
    X86Linux.step c s.memory = .syscall { c with rip := 0x40015b } := by
  have actual := step_of_entry (core := c) (memory := s.memory) Binary.ok_400159.1
    (by simp [pc, Binary.i_400159]) (frame.code _ (by simp [Binary.transcript]))
  simpa [Entry.denote, Binary.i_400159, pc] using actual

/-- Startup's footprint lies in the driver frame (`DriverMemory.launch_read`). -/
theorem frame_of_startup {input : ProcInput} {launchCore : Core} {initial current : Memory}
    (loaded : Loaded image input launchCore initial)
    (writes : Memory.WritesWithin initial current
      (LoadedStartup.Footprint (launchCore.read .rsp).toNat))
    (geometry : CompressionStack.Geometry (launchCore.read .rsp).toNat) :
    DriverMemory.Frame initial current := by
  refine ⟨loaded.1, writes.mono ?_⟩
  have := geometry.aboveGlobals
  intro address member
  rcases member with stack | state
  · dsimp [DriverMemory.Above]
    omega
  · dsimp [DriverMemory.Above, InitStores.stateAddress] at *
    omega

theorem first_pc (launchCore : Core) (top : Nat) :
    (LoadedStartup.readCore launchCore top).rip = 0x400159 := by
  simp [LoadedStartup.readCore, InitStores.readCore]

theorem initial_state : (stateOf EmptySupport.initialStateBytes).toState = Silmaril.Crypto.SHA256.H0 := by
  have same : EmptySupport.initialStateBytes = EmptyCall.initialHashBytes := rfl
  rw [same]
  exact EmptyCall.initialHashBytes_reference

end Silmaril.Process.CLI.Sha256Cli.LoopRuns

namespace Silmaril.Process.LPS.Problems.Sha256Cli.LoopProof

open Silmaril.Process.Syscall
open Silmaril.Process.CLI.X86Linux (Core)
open Silmaril.X86 («Word»)
open Silmaril.Crypto.X86.Sha256O2 (stateOf)

/-! ## Generic: silent segments and the event part of `Ok` -/

/-- The event part of `Ok`. -/
def EvOk (message : List Byte) (evs : List Syscall.Event) : Prop :=
  CLI.WritesOnlyTo [1] evs ∧ ReadsOnlyStdin evs ∧
    CLI.stdinRead evs <+: message ∧ CLI.stdout evs <+: CLI.Sha256.expected message ∧
    (CLI.stdout evs = [] ∨ (CLI.stdinRead evs = message ∧ CLI.SawEof 0 evs))

theorem ok_of {message : List Byte} {x : PS} {evs : List Syscall.Event}
    (running : x.sys.exited = none) (ev : EvOk message evs) (args : ReadArgs x) :
    Ok message x evs :=
  ⟨running, ev.1, ev.2.1, ev.2.2.1, ev.2.2.2.1, ev.2.2.2.2, args⟩

/-- A silent Linux run is a silent reliable run (retirements do not consult the environment's
syscall relation). -/
theorem silent_reliable {a b : CLI.PState CLI.X86Linux.isa CLI.Env.linux} {es : List Syscall.Event}
    (run : CLI.Proc.Runs CLI.X86Linux.isa CLI.Env.linux a es b) (silent : es = []) :
    CLI.Proc.Runs CLI.X86Linux.isa CLI.Env.reliable ⟨a.core, a.env⟩ [] ⟨b.core, b.env⟩ := by
  induction run with
  | refl => exact .refl _
  | cons step rest ih =>
    obtain ⟨first, second⟩ := List.append_eq_nil_iff.mp silent
    subst first
    cases step with
    | retire running retired =>
      exact .cons (events := []) (.retire running retired) (ih second)

/-- Prepend a silent reliable run to a `Leads` proof. -/
theorem leads_of_silent {message : List Byte} {Goal : PS → List Syscall.Event → Prop} {x y : PS}
    {evs : List Syscall.Event} (run : CLI.Proc.Runs CLI.X86Linux.isa CLI.Env.reliable x [] y)
    (running : x.sys.exited = none) (ev : EvOk message evs)
    (next : Leads CStep (Ok message) Goal y evs) : Leads CStep (Ok message) Goal x evs := by
  generalize empty : ([] : List Syscall.Event) = es at run
  induction run with
  | refl => exact next
  | cons step rest ih =>
    obtain ⟨first, second⟩ := List.append_eq_nil_iff.mp empty.symm
    subst first
    refine .step (ok_of running ev ?_) ⟨_, _, step⟩ fun e w other => ?_
    · cases step with
      | retire _ retired => exact readArgs_of_retired retired.symm
    obtain ⟨rfl, rfl⟩ := CLI.Proc.Step.unique_of_silent
      CLI.X86Linux.instruction_deterministic step other
    have running' : w.sys.exited = none := by
      cases step with
      | retire running _ => exact running
    simpa using ih running' next second.symm

/-- Prepend a silent Linux run (as produced by the chain's lemmas). -/
theorem leads_of_linux {message : List Byte} {Goal : PS → List Syscall.Event → Prop}
    {c c' : Core} {s s' : Syscall.State} {evs : List Syscall.Event}
    (run : CLI.Proc.Runs CLI.X86Linux.isa CLI.Env.linux ⟨c, s⟩ [] ⟨c', s'⟩)
    (running : s.exited = none) (ev : EvOk message evs)
    (next : Leads CStep (Ok message) Goal ⟨c', s'⟩ evs) :
    Leads CStep (Ok message) Goal ⟨c, s⟩ evs :=
  leads_of_silent (silent_reliable run rfl) running ev next

/-! ## Reads at a cut point -/

abbrev InputAt := CLI.Sha256Cli.ShortReadTransfer.InputAt

/-- Every reliable completed read of positive capacity, with input left, copies the next
`k > 0` message bytes. -/
theorem read_positive {s s' : Syscall.State} {message : List Byte} {p a n : Nat}
    {ev : Syscall.Event} {r : Result} (input : InputAt s message p) (more : p < message.length)
    (positive : 0 < n) (effect : Syscall.Step s (.read 0 a n) ev (.returned r) s') (reliable : ¬ ev.IsRefusal) :
    ∃ k, r = .ok k ∧ 0 < k ∧ k ≤ n ∧ p + k ≤ message.length ∧
      ev = .read 0 ((message.drop p).take k) ∧ InputAt s' message (p + k) ∧
      s'.exited = none ∧ s'.descriptors 1 = s.descriptors 1 := by
  obtain ⟨descriptor, opened, mode, stream, cursor⟩ := input
  cases effect with
  | @readSome _ _ _ other bytes memory running openedOther modeOther matched nonempty bounded transfer accessible copied =>
    have same := Option.some.inj (openedOther.symm.trans opened)
    subst same
    have matches' : (Syscall.InputStream.ofList message).Matches p bytes := by
      simpa only [stream, cursor] using matched
    obtain ⟨fits, exactBytes⟩ := matches'.ofList_slice (by omega)
    refine ⟨bytes.length, rfl, nonempty, bounded, by omega, congrArg (Syscall.Event.read 0) exactBytes,
      ?_, running, ?_⟩
    · refine ⟨{ other with cursor := other.cursor + bytes.length }, ?_, mode, stream, ?_⟩
      · simp [State.setDescriptor]
      · simp only [cursor]
    · simp [State.setDescriptor]
  | readEof running openedOther modeOther eof accessible =>
    have same := Option.some.inj (openedOther.symm.trans opened)
    subst same
    rw [stream, cursor, Syscall.InputStream.ofList_byteAt] at eof
    have := List.getElem?_eq_none_iff.mp eof
    omega
  | readZero => omega
  | readError => exact absurd trivial reliable
  | readBadDescriptor => exact absurd trivial reliable
  | readBadAddress => exact absurd trivial reliable

/-- At a read with input left, some step exists (a one-byte read). -/
theorem read_progress {c t : Core} {s : Syscall.State} {message : List Byte} {p a n : Nat}
    (trapped : CLI.X86Linux.step c s.memory = .syscall t)
    (request : CLI.X86Linux.request t = some (.read 0 a n))
    (input : InputAt s message p) (more : p < message.length) (running : s.exited = none)
    (positive : 0 < n) (accessible : s.memory.Permitted .write a n) :
    ∃ e y, CStep ⟨c, s⟩ e y := by
  obtain ⟨descriptor, opened, mode, stream, cursor⟩ := input
  have one : s.memory.Permitted .write a [message[p]].length :=
    X86.Ext.Memory.Permitted.sub accessible (by simp) (by omega) (by simp; omega)
  have written : s.memory.writeBytes a [message[p]] =
      some { s.memory with bytes := Silmaril.Process.Memory.install s.memory.bytes a [message[p]] } := by
    have one' : s.memory.checkSpan .write a [message[p]].length = true := one
    unfold Silmaril.Process.Memory.writeBytes
    simp only [one', ↓reduceIte]
  have matched : descriptor.input.Matches descriptor.cursor [message[p]] := by
    intro index bound
    simp only [List.length_singleton, Nat.lt_one_iff] at bound
    subst bound
    simp [stream, cursor]
  have effect := Syscall.Step.readSome running opened mode matched (by simp) (by simp; omega)
    (by simp [maxTransfer]) accessible written
  refine ⟨_, _, CLI.Proc.Step.call running trapped.symm request ⟨effect, ?_, ?_⟩ ⟨0, rfl⟩⟩
  · intro _ _ _ _ h
    cases h
  · exact id

/-- Every step at a `read` syscall is a completed, non-refused read. -/
theorem read_step_inv {c t : Core} {s : Syscall.State} {fd a n : Nat} {e : List Syscall.Event}
    {y : PS} (trapped : CLI.X86Linux.step c s.memory = .syscall t)
    (request : CLI.X86Linux.request t = some (.read fd a n)) (step : CStep ⟨c, s⟩ e y) :
    ∃ ev r, e = [ev] ∧ Syscall.Step s (.read fd a n) ev (.returned r) y.sys ∧ ¬ ev.IsRefusal ∧
      CLI.X86Linux.Resume t r y.cpu := by
  rcases (CLI.X86Linux.step_iff_of_syscall (E := CLI.Env.reliable) trapped request).mp step with
    ⟨_, ⟨ev, r, rfl, effect, resume⟩ | ⟨ev, status, rfl, effect, _⟩⟩
  · exact ⟨ev, r, rfl, effect.1, effect.2.2, resume⟩
  · cases effect.1

theorem evOk_nil (message : List Byte) : EvOk message [] :=
  ⟨by simp [CLI.WritesOnlyTo], by simp [ReadsOnlyStdin], by simp [CLI.stdinRead],
    by simp [CLI.stdout], .inl (by simp [CLI.stdout])⟩

theorem events_read (evs : List Syscall.Event) (chunk : List Byte) :
    CLI.stdinRead (evs ++ [.read 0 chunk]) = CLI.stdinRead evs ++ chunk ∧
    CLI.stdout (evs ++ [.read 0 chunk]) = CLI.stdout evs ∧
    (CLI.WritesOnlyTo [1] evs → CLI.WritesOnlyTo [1] (evs ++ [.read 0 chunk])) ∧
    (ReadsOnlyStdin evs → ReadsOnlyStdin (evs ++ [.read 0 chunk])) := by
  refine ⟨by simp [CLI.stdinRead, CLI.readOn_append, CLI.readOn],
    by simp [CLI.stdout, CLI.writtenOn_append, CLI.writtenOn], ?_, ?_⟩
  · intro only fd bytes member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with member | member
    · exact only fd bytes member
    · cases member
  · intro reads fd bytes member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with member | member
    · exact reads fd bytes member
    · cases member
      rfl

/-! ## The loop head -/

/-- The loop-head frame after `p` bytes: `AtLoopHead` with `message.take p` in place of the
message. -/
def HeadFrame (message : List Byte) (p : Nat) (x : PS) : Prop :=
  ∃ (initial : Silmaril.Process.Memory) (top : Nat) (blocks : List (List Byte)) (tail : List Byte),
    CLI.Sha256Cli.BufferedTailFrame.Ready initial (BitVec.ofNat 64 (top - 32)) x.cpu x.sys tail
        (BitVec.ofNat 64 p)
        (blocks.foldl CLI.Sha256Cli.Driver.compressBlock Silmaril.Crypto.SHA256.H0) ∧
      (∀ block ∈ blocks, block.length = 64) ∧ blocks.flatten ++ tail = message.take p ∧
      CLI.Sha256Cli.CompressionStack.Geometry top ∧ CLI.Sha256Cli.CompressionStack.Mapping initial top

/-- The loop invariant at the loop-head `read` after `p` bytes. -/
structure Head (input : CLI.ProcInput) (message : List Byte) (p : Nat) (x : PS)
    (evs : List Syscall.Event) : Prop where
  stdin : input.stdin = .ofList message
  frame : HeadFrame message p x
  input : InputAt x.sys message p
  output : ∃ d : Syscall.Descriptor, x.sys.descriptors 1 = some d ∧ d.writable = true
  read : CLI.stdinRead evs = message.take p
  silent : CLI.stdout evs = []
  only : CLI.WritesOnlyTo [1] evs
  reads : ReadsOnlyStdin evs

theorem Head.evOk {input : CLI.ProcInput} {message : List Byte} {p : Nat} {x : PS}
    {evs : List Syscall.Event} (head : Head input message p x evs) : EvOk message evs :=
  ⟨head.only, head.reads, head.read ▸ List.take_prefix _ _, head.silent ▸ List.nil_prefix,
    .inl head.silent⟩

/-- The events and descriptors after reading the next chunk. -/
theorem Head.make {input : CLI.ProcInput} {message : List Byte} {p k : Nat} {y : PS}
    {evs : List Syscall.Event} (stdin : input.stdin = .ofList message)
    (output : ∃ d : Syscall.Descriptor, y.sys.descriptors 1 = some d ∧ d.writable = true)
    (read : CLI.stdinRead evs = message.take p) (silent : CLI.stdout evs = [])
    (only : CLI.WritesOnlyTo [1] evs) (reads : ReadsOnlyStdin evs)
    (frame : HeadFrame message (p + k) y) (input' : InputAt y.sys message (p + k)) :
    Head input message (p + k) y (evs ++ [.read 0 ((message.drop p).take k)]) := by
  obtain ⟨read', write, only', reads'⟩ := events_read evs ((message.drop p).take k)
  exact ⟨stdin, frame, input', output,
    by rw [read', read, List.take_add], by rw [write, silent], only' only, reads' reads⟩

theorem Head.advance {input : CLI.ProcInput} {message : List Byte} {p k : Nat} {x y : PS}
    {evs : List Syscall.Event} (head : Head input message p x evs)
    (frame : HeadFrame message (p + k) y) (input' : InputAt y.sys message (p + k))
    (out : y.sys.descriptors 1 = x.sys.descriptors 1) :
    Head input message (p + k) y (evs ++ [.read 0 ((message.drop p).take k)]) :=
  Head.make head.stdin (out ▸ head.output) head.read head.silent head.only head.reads frame input'

theorem total_add (p k : Nat) :
    BitVec.ofNat 64 p + BitVec.ofNat 64 k = BitVec.ofNat 64 (p + k) :=
  BitVec.ofNat_add_ofNat p k

/-- **The loop.** From the loop head after `p` bytes, every execution keeps `Ok` and reaches
`LoopEnd`, by well-founded induction on the bytes left. -/
theorem head_leads (input : CLI.ProcInput) (message : List Byte) :
    ∀ n p (x : PS) (evs : List Syscall.Event), message.length - p = n → p ≤ message.length →
      Head input message p x evs → Leads CStep (Ok message) (LoopEnd input message) x evs := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p x evs distance bound head
  obtain ⟨initial, top, blocks, tail, ready, full, flat, geometry, mapping⟩ := head.frame
  by_cases finished : p = message.length
  · subst finished
    refine .done ⟨head.stdin, .inl ⟨initial, top, blocks, tail, ready, full, ?_, geometry, mapping⟩,
      ready.running, head.input, head.output, ?_, head.silent, head.only, head.reads⟩
    · simpa using flat
    · simpa using head.read
  have more : p < message.length := by omega
  obtain ⟨c, s⟩ := x
  have trapped := CLI.Sha256Cli.LoopRuns.loop_trapped ready
  have request := (ready.registers.request_below64 ready.room).1
  have room := ready.room
  have accessible : s.memory.Permitted .write (0x401620 + tail.length) (64 - tail.length) :=
    ready.frame.bss_permitted .write rfl _ _ (by omega) (by omega)
  refine .step (ok_of ready.running head.evOk (readArgs_of_read trapped request (by omega)))
    (read_progress trapped request head.input more ready.running (by omega) accessible) ?_
  intro e y step
  obtain ⟨ev, r, rfl, effect, reliable, flags, core⟩ := read_step_inv trapped request step
  obtain ⟨k, rfl, positive, bounded, fits, eventEq, input', running', out'⟩ :=
    read_positive head.input more (by omega) effect reliable
  obtain ⟨yc, ys⟩ := y
  change yc = _ at core
  subst core
  subst eventEq
  rcases Nat.lt_or_ge (tail.length + k) 64 with short | long
  · obtain ⟨chunk, next, length, chunkEq, run, ready'⟩ :=
      CLI.Sha256Cli.LoopRuns.short_after ready positive short flags effect
    cases (Syscall.Event.read.inj chunkEq).2
    rw [total_add] at ready'
    have head' := head.advance (k := k) (y := ⟨next, ys⟩)
      ⟨initial, top, blocks, tail ++ (message.drop p).take k, ready', full,
        by rw [← List.append_assoc, flat, List.take_add], geometry, mapping⟩ input' out'
    exact leads_of_linux run running' head'.evOk
      (ih (message.length - (p + k)) (by omega) (p + k) _ _ rfl fits head')
  · obtain ⟨chunk, next, memory, length, chunkEq, run, fullReady⟩ :=
      CLI.Sha256Cli.LoopRuns.full_after ready positive (by omega) flags effect geometry mapping
    cases (Syscall.Event.read.inj chunkEq).2
    have ready' := CLI.Sha256Cli.BufferedTailFrame.of_full fullReady
    rw [total_add] at ready'
    have head' := head.advance (k := k) (y := ⟨next, { ys with memory := memory }⟩)
      ⟨initial, top, blocks ++ [tail ++ (message.drop p).take k], [],
        by simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]; exact ready',
        by
          intro block member
          simp only [List.mem_append, List.mem_singleton] at member
          rcases member with member | rfl
          · exact full block member
          · simp only [List.length_append]
            omega,
        by simp only [List.flatten_append, List.flatten_singleton, List.append_nil]
           rw [← List.append_assoc, flat, List.take_add], geometry, mapping⟩ input' out'
    exact leads_of_linux run running' head'.evOk
      (ih (message.length - (p + k)) (by omega) (p + k) _ _ rfl fits head')

/-! ## The first read -/

/-- At the first `read` (`0x400159`) after startup, from a launch of `launchCore`/`initial`. -/
structure First (input : CLI.ProcInput) (message : List Byte) (launchCore : Core)
    (initial : Silmaril.Process.Memory) (x : PS) : Prop where
  stdin : input.stdin = .ofList message
  loaded : CLI.X86Linux.Loaded cliImage input launchCore initial
  core : x.cpu = CLI.Sha256Cli.LoadedStartup.readCore launchCore (launchCore.read .rsp).toNat
  state : x.sys.memory.readBytes CLI.Sha256Cli.InitStores.stateAddress 32 =
    some CLI.Sha256Cli.EmptySupport.initialStateBytes
  writes : Silmaril.Process.Memory.WritesWithin initial x.sys.memory
    (CLI.Sha256Cli.LoadedStartup.Footprint (launchCore.read .rsp).toNat)
  geometry : CLI.Sha256Cli.CompressionStack.Geometry (launchCore.read .rsp).toNat
  mapping : CLI.Sha256Cli.CompressionStack.Mapping initial (launchCore.read .rsp).toNat
  running : x.sys.exited = none
  input : InputAt x.sys message 0
  output : ∃ d : Syscall.Descriptor, x.sys.descriptors 1 = some d ∧ d.writable = true

theorem first_leads (input : CLI.ProcInput) (message : List Byte) (launchCore : Core)
    (initial : Silmaril.Process.Memory) (x : PS) (first : First input message launchCore initial x) :
    Leads CStep (Ok message) (LoopEnd input message) x [] := by
  by_cases empty : message = []
  · subst empty
    exact .done ⟨first.stdin, .inr ⟨rfl, launchCore, initial, first.loaded, first.core, first.state,
      first.writes, first.geometry, first.mapping⟩, first.running, by simpa using first.input,
      first.output, by simp [CLI.stdinRead], by simp [CLI.stdout], by simp [CLI.WritesOnlyTo],
      by simp [ReadsOnlyStdin]⟩
  have more : 0 < message.length := List.length_pos_iff.mpr empty
  obtain ⟨c, s⟩ := x
  have core : c = CLI.Sha256Cli.LoadedStartup.readCore launchCore (launchCore.read .rsp).toNat :=
    first.core
  have frame := CLI.Sha256Cli.LoopRuns.frame_of_startup first.loaded first.writes first.geometry
  have pc : c.rip = 0x400159 := by rw [core]; exact CLI.Sha256Cli.LoopRuns.first_pc _ _
  have trapped := CLI.Sha256Cli.LoopRuns.first_trapped (c := c) frame pc
  have request : CLI.X86Linux.request { c with rip := 0x40015b } = some (.read 0 0x401620 64) := by
    rw [core]
    exact CLI.Sha256Cli.LoadedStartup.read_request launchCore (launchCore.read .rsp).toNat
  have rsp : c.read .rsp = BitVec.ofNat 64 ((launchCore.read .rsp).toNat - 32) := by
    rw [core]
    exact (CLI.Sha256Cli.LoadedStartup.read_arguments _ _).2.2.2.2
  have stateRead : s.memory.readBytes 0x401660 32 = some CLI.Sha256Cli.EmptySupport.initialStateBytes :=
    first.state
  refine .step (ok_of first.running (evOk_nil message) (readArgs_of_read trapped request (by decide)))
    (read_progress trapped request first.input more first.running (by decide)
      (frame.bss_permitted .write rfl _ _ (by decide) (by decide))) ?_
  intro e y step
  obtain ⟨ev, r, rfl, effect, reliable, flags, yCore⟩ := read_step_inv trapped request step
  obtain ⟨k, rfl, positive, bounded, fits, eventEq, input', running', out'⟩ :=
    read_positive first.input more (by decide) effect reliable
  obtain ⟨yc, ys⟩ := y
  change yc = _ at yCore
  subst yCore
  subst eventEq
  have output : ∃ d : Syscall.Descriptor, ys.descriptors 1 = some d ∧ d.writable = true := by
    have out'' : ys.descriptors 1 = s.descriptors 1 := out'
    rw [out'']
    exact first.output
  rcases Nat.lt_or_ge k 64 with short | long
  · obtain ⟨tail, next, length, chunkEq, run, ready⟩ :=
      CLI.Sha256Cli.LoopRuns.first_short_after c flags positive short frame stateRead effect
    cases (Syscall.Event.read.inj chunkEq).2
    rw [rsp, CLI.Sha256Cli.LoopRuns.initial_state] at ready
    have head := Head.make (input := input) (p := 0) (k := k) (y := ⟨next, ys⟩) (evs := [])
      first.stdin output (by simp [CLI.stdinRead]) (by simp [CLI.stdout])
      (by simp [CLI.WritesOnlyTo]) (by simp [ReadsOnlyStdin])
      ⟨initial, _, [], (message.drop 0).take k,
        by simp only [Nat.zero_add, List.foldl_nil]; exact ready, by simp, by simp,
        first.geometry, first.mapping⟩ input'
    exact leads_of_linux run running' head.evOk
      (head_leads input message _ (0 + k) _ _ rfl fits head)
  · have k64 : k = 64 := by omega
    subst k64
    obtain ⟨block, next, memory, length, chunkEq, run, fullReady⟩ :=
      CLI.Sha256Cli.LoopRuns.first_full_after c flags rsp frame stateRead effect
        first.geometry first.mapping
    cases (Syscall.Event.read.inj chunkEq).2
    rw [CLI.Sha256Cli.LoopRuns.initial_state] at fullReady
    have ready := CLI.Sha256Cli.BufferedTailFrame.of_full fullReady
    have head := Head.make (input := input) (p := 0) (k := 64)
      (y := ⟨next, { ys with memory := memory }⟩) (evs := [])
      first.stdin output (by simp [CLI.stdinRead]) (by simp [CLI.stdout])
      (by simp [CLI.WritesOnlyTo]) (by simp [ReadsOnlyStdin])
      ⟨initial, _, [(message.drop 0).take 64], [],
        by simp only [Nat.zero_add, List.foldl_cons, List.foldl_nil]; exact ready,
        by simpa using length, by simp, first.geometry, first.mapping⟩ input'
    exact leads_of_linux run running' head.evOk
      (head_leads input message _ (0 + 64) _ _ rfl fits head)

/-! ## The segment -/

/-- **Segment `loop`** (VERIFIED). -/
theorem loop_segment_proof : LoopSegment fun _ => True := by
  intro message input x _ stdin _ launch
  obtain ⟨⟨m, loaded, memory, running, descriptors⟩, geometry, mapping⟩ := launch
  obtain ⟨c, s⟩ := x
  change s.memory = m at memory
  subst memory
  have apart : 0x4005c0 ≤ (c.read .rsp).toNat - 24 := by
    have : 0x401680 + 384 ≤ (c.read .rsp).toNat := geometry.aboveGlobals
    omega
  obtain ⟨after, run, initialized, writes, _⟩ :=
    CLI.Sha256Cli.LoadedStartup.of_loaded input c s loaded apart running
  refine leads_of_linux run running (evOk_nil message)
    (first_leads input message c s.memory _ ⟨stdin, loaded, rfl, initialized, writes, geometry,
      mapping, running, ⟨_, descriptors.1, rfl, stdin, rfl⟩, ⟨_, descriptors.2.1, rfl⟩⟩)

end Silmaril.Process.LPS.Problems.Sha256Cli.LoopProof



namespace Silmaril.Process.LPS.Problems.Sha256Cli

/-- The end-to-end target with the `loop` segment discharged: modulo `tail`, `output` and
`bridge` (WIP until those three are proved). -/
theorem totalGoal_of_remaining (tail : TailSegment fun _ => True)
    (output : OutputSegment fun _ => True) (bridge : BridgeSegment) : TotalGoal :=
  totalGoal_of_segments LoopProof.loop_segment_proof tail output bridge

end Silmaril.Process.LPS.Problems.Sha256Cli
