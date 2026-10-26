module

public import Silmaril.Process.LPS.Problems.Sha256Cli.Segments
public import Silmaril.Process.CLI.Sha256Cli.LongTailReadEofFrame
public import Silmaril.Process.CLI.Sha256Cli.TailReadEofFrame
public import Silmaril.Process.CLI.Sha256Cli.TailCompressionFrame
public import Silmaril.Process.CLI.Sha256Cli.TailPaddingReference
public import Silmaril.Process.CLI.Sha256Cli.EmptyReadUniversal
public import Silmaril.Process.CLI.Sha256Cli.EmptyPrepared
public import Silmaril.Process.CLI.Sha256Cli.LoadedStartup
public import Silmaril.Process.CLI.X86Linux.SilentTransport
public import Silmaril.Process.CLI.X86Linux.SyscallInversion

/-! # Segment `tail` of the `sha256` end-to-end proof

`tail_segment_proved : TailSegment fun _ => True`: from the cut point `LoopEnd` (the whole
message consumed, the machine at a `read` whose only reliable outcome is end of file), every
reliable CLI execution keeps `Ok` and reaches `OutReady` (the 65 answer bytes stored and the
write request prepared).

The segment has exactly one system call, the EOF `read`, followed by a silent (retire-only)
segment through padding, one or two compressions and the hex formatting. The proof is:

* `leads_of_silent`: a silent `Env.linux` run of the chain is a `Leads` in `Env.reliable`,
  because a retirement is the only transition of its source (`X86Linux` is functional).
* `leads_of_eof_read`: at a positive-capacity `read` with the stdin cursor at the end, every
  reliable reply is EOF (`EmptyReadUniversal.classify`; errors are refusals, which `reliable`
  excludes), and the resumed core is the trapped core with `rax = 0` and an arbitrary `R11`.
* The post-EOF silent runs are re-assembled from the chain's lemmas, but started *after* the
  syscall, for an arbitrary `R11` (`after_eof_short`, `after_eof_long`, `after_first_eof`):
  tails `0…55` (#3146/#3175), tails `56…63` (#3184–#3195) and the empty message's first
  read for an arbitrary launch (generalising the fixed-launch #3059 path).

Status: everything in this file is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.Sha256Cli.Tail

open Silmaril.Process.Syscall
open Silmaril.Process.CLI.X86Linux (Core)
open Silmaril.X86 («Word»)
open Silmaril.Crypto.X86.Sha256O2 (stateOf)

/-! ## Silent chain runs are `Leads` in the reliable environment -/

/-- States of the chain's `Env.linux` process. -/
abbrev LS := CLI.PState CLI.X86Linux.isa CLI.Env.linux

/-- The same state, in the reliable environment (identical state type). -/
def rel (x : LS) : PS := ⟨x.core, x.env⟩

theorem retire_reliable {x y : LS}
    (step : CLI.Proc.Step CLI.X86Linux.isa CLI.Env.linux x [] y) : CStep (rel x) [] (rel y) := by
  generalize empty : ([] : List Syscall.Event) = events at step
  cases step with
  | retire running retired => exact .retire running retired
  | call => cases empty
  | exit => cases empty

theorem silent_exited {x y : LS}
    (step : CLI.Proc.Step CLI.X86Linux.isa CLI.Env.linux x [] y) : y.env.exited = x.env.exited := by
  generalize empty : ([] : List Syscall.Event) = events at step
  cases step with
  | retire => rfl
  | call => cases empty
  | exit => cases empty

theorem silent_unique {x y : LS} {e : List Syscall.Event} {w : PS}
    (step : CLI.Proc.Step CLI.X86Linux.isa CLI.Env.linux x [] y) (other : CStep (rel x) e w) :
    e = [] ∧ w = rel y :=
  CLI.Proc.Step.unique_of_silent CLI.X86Linux.instruction_deterministic (retire_reliable step) other

theorem OkE.transfer {message : List Byte} {x y : PS} {evs : List Syscall.Event}
    (same : y.sys.exited = x.sys.exited) (ok : OkE message x evs) : OkE message y evs :=
  ⟨same.trans ok.1, ok.2⟩

/-- A silent `Env.linux` run, followed by a `Leads` from its end, is a `Leads` from its start. -/
theorem leads_of_silent {message : List Byte} {Goal : PS → List Syscall.Event → Prop} {x y : LS}
    {evs : List Syscall.Event} (run : CLI.Proc.Runs CLI.X86Linux.isa CLI.Env.linux x [] y)
    (ok : OkE message (rel x) evs) (k : Leads CStep (Ok message) Goal (rel y) evs) :
    Leads CStep (Ok message) Goal (rel x) evs := by
  generalize empty : ([] : List Syscall.Event) = events at run
  revert ok
  induction run with
  | refl => intro _; exact k
  | @cons a n b e1 e2 first rest ih =>
    intro ok
    obtain ⟨h1, h2⟩ := List.append_eq_nil_iff.mp empty.symm
    subst h1
    subst h2
    have okN : OkE message (rel n) evs := OkE.transfer (x := rel a) (silent_exited first) ok
    have args : ReadArgs (rel a) := by
      cases first with
      | retire _ retired => exact readArgs_of_retired retired.symm
    refine .step (ok_of_okE ok args) ⟨[], rel n, retire_reliable first⟩ fun e w s => ?_
    obtain ⟨rfl, rfl⟩ := silent_unique first s
    simpa only [List.append_nil] using ih k rfl okN

/-! ## The EOF `read` -/

/-- The kernel's return from a zero-byte `read`, with `R11 = flags`. -/
def resumed (trapped : Core) (flags : «Word») : Core :=
  ((trapped.write .rax (CLI.X86Linux.resultWord (.ok 0))).write .rcx trapped.rip).write .r11 flags

/-- At a positive-capacity stdin `read` with the cursor at the end of the message, the reliable
environment can answer, and every answer is EOF: an empty read event, the environment unchanged,
and the trapped core resumed with `rax = 0` and an arbitrary `R11`. -/
theorem leads_of_eof_read {message : List Byte} {Goal : PS → List Syscall.Event → Prop}
    {c trapped : Core} {s : Syscall.State} {evs : List Syscall.Event} {address count : Nat}
    (trappedStep : CLI.X86Linux.step c s.memory = .syscall trapped)
    (requested : CLI.X86Linux.request trapped = some (.read 0 address count))
    (positive : 0 < count) (accessible : s.memory.Permitted .write address count)
    (input : CLI.Sha256Cli.ShortReadTransfer.InputAt s message message.length)
    (ok : OkE message ⟨c, s⟩ evs)
    (next : ∀ flags, Leads CStep (Ok message) Goal ⟨resumed trapped flags, s⟩ (evs ++ [Syscall.Event.read 0 []])) :
    Leads CStep (Ok message) Goal ⟨c, s⟩ evs := by
  obtain ⟨descriptor, opened, readable, stream, cursor⟩ := input
  have eof : descriptor.input.byteAt descriptor.cursor = none := by
    rw [stream, cursor, InputStream.ofList_byteAt]
    simp
  have running : s.exited = none := ok.1
  have effect : Syscall.Step s (.read 0 address count) (.read 0 []) (.returned (.ok 0)) s :=
    .readEof running opened readable eof accessible
  have kept : CLI.Env.reliable.step s (.read 0 address count) (.read 0 []) (.returned (.ok 0)) s :=
    ⟨effect, fun _ _ _ _ _ => rfl, fun h => h⟩
  refine .step (ok_of_okE ok (readArgs_of_read trappedStep requested positive))
    ⟨[Syscall.Event.read 0 []], ⟨resumed trapped 0, s⟩,
    .call running trappedStep.symm requested kept ⟨0, rfl⟩⟩ ?_
  intro e w step
  rcases (CLI.X86Linux.step_iff_of_syscall (E := CLI.Env.reliable) trappedStep requested).mp step
    with ⟨_, returned | exited⟩
  · obtain ⟨event, result, rfl, effect', resume⟩ := returned
    rcases CLI.Sha256Cli.EmptyReadUniversal.classify positive opened readable eof effect'.1 with
      ⟨rfl, rfl, env⟩ | ⟨errno, _, rfl, _⟩
    · obtain ⟨flags, core⟩ := resume
      cases w with
      | mk wc ws =>
        change ws = s at env
        change wc = _ at core
        subst core
        subst env
        exact next flags
    · exact absurd trivial effect'.2.2
  · obtain ⟨event, status, rfl, effect', _⟩ := exited
    cases effect'.1

/-! ## Event bookkeeping across the EOF read -/

theorem ok_after_eof {input : CLI.ProcInput} {message : List Byte} {x : PS} {evs : List Syscall.Event}
    (h : LoopEnd input message x evs) {y : PS} (running : y.sys.exited = none) :
    OkE message y (evs ++ [Syscall.Event.read 0 []]) := by
  refine ⟨running, ?_, ?_, ?_, ?_, .inl ?_⟩
  · intro fd bytes member
    rcases List.mem_append.mp member with old | new
    · exact h.only fd bytes old
    · simp at new
  · intro fd bytes member
    rcases List.mem_append.mp member with old | new
    · exact h.reads fd bytes old
    · simp only [List.mem_singleton, Syscall.Event.read.injEq] at new
      exact new.1
  · have e : CLI.readOn 0 evs = message := h.read
    rw [CLI.stdinRead, CLI.readOn_append]
    simp [CLI.readOn, e]
  · have e : CLI.writtenOn 1 evs = [] := h.silent
    rw [CLI.stdout, CLI.writtenOn_append]
    simp [CLI.writtenOn, e]
  · have e : CLI.writtenOn 1 evs = [] := h.silent
    rw [CLI.stdout, CLI.writtenOn_append]
    simp [CLI.writtenOn, e]

theorem outReady_after_eof {input : CLI.ProcInput} {message : List Byte} {x : PS}
    {evs : List Syscall.Event} (h : LoopEnd input message x evs) {initial : Memory} {outCore : Core}
    {memory : Memory}
    (ready : CLI.Sha256Cli.HexOutputFrame.Ready initial outCore { x.sys with memory := memory } message) :
    OutReady input message ⟨outCore, { x.sys with memory := memory }⟩ (evs ++ [Syscall.Event.read 0 []]) := by
  have only : CLI.WritesOnlyTo [1] (evs ++ [Syscall.Event.read 0 []]) := (ok_after_eof h (y := x) h.running).2.1
  have reads : ReadsOnlyStdin (evs ++ [Syscall.Event.read 0 []]) := (ok_after_eof h (y := x) h.running).2.2.1
  refine ⟨h.stdin, ⟨initial, ready⟩, ?_, h.output, reads⟩
  apply CLI.Sha256Cli.Driver.OutputInv.start
  · have e : CLI.readOn 0 evs = message := h.read
    rw [CLI.stdinRead, CLI.readOn_append]
    simp [CLI.readOn, e]
  · exact List.mem_append_right _ (List.mem_singleton_self _)
  · exact only
  · have e : CLI.writtenOn 1 evs = [] := h.silent
    rw [CLI.stdout, CLI.writtenOn_append]
    simp [CLI.writtenOn, e]


theorem ok_at {input : CLI.ProcInput} {message : List Byte} {x : PS} {evs : List Syscall.Event}
    (h : LoopEnd input message x evs) : OkE message x evs :=
  ⟨h.running, h.only, h.reads, h.read ▸ List.prefix_refl _, h.silent ▸ List.nil_prefix,
    .inl h.silent⟩

/-! ## After the EOF read: the chain's silent segments, for an arbitrary `R11` -/

section AfterEof

open CLI.Sha256Cli

set_option maxRecDepth 100000

/-- Tails `0…55`: EOF branch, single padding block, one compression, hex and newline. -/
theorem after_eof_short {initial : Memory} {top : Nat} {c : Core} {s : Syscall.State}
    {tail : List Byte} {blocks : List (List Byte)}
    (ready : BufferedTailFrame.Ready initial (BitVec.ofNat 64 (top - 32)) c s tail
      (BitVec.ofNat 64 (blocks.flatten ++ tail).length)
      (blocks.foldl Driver.compressBlock Silmaril.Crypto.SHA256.H0))
    (short : tail.length < 56) (full : ∀ block ∈ blocks, block.length = 64)
    (geometry : CompressionStack.Geometry top) (stack : CompressionStack.Mapping initial top)
    (flags : «Word») :
    ∃ (outCore : Core) (memory : Memory),
      CLI.Proc.Runs CLI.X86Linux.isa CLI.Env.linux
        ⟨resumed { c with rip := 0x400177 } flags, s⟩ [] ⟨outCore, { s with memory := memory }⟩ ∧
      HexOutputFrame.Ready initial outCore { s with memory := memory } (blocks.flatten ++ tail) := by
  obtain ⟨stateBytes, stateRead, value⟩ := ready.hash
  let returned := ShortReadFrame.returnedCore c (.ok 0) flags
  rw [show resumed { c with rip := 0x400177 } flags = returned from rfl]
  have eof : CLI.Proc.Runs CLI.X86Linux.isa CLI.Env.linux ⟨returned, s⟩ []
      ⟨ShortReadFailure.paddingCore returned, s⟩ :=
    ShortReadFailure.eof_prefix returned s ready.running ready.frame.code rfl rfl
  let padding := ShortReadFailure.paddingCore returned
  have filled : padding.read .r8 = BitVec.ofNat 64 tail.length := ready.registers.filled
  have count : padding.read .rbx = BitVec.ofNat 64 (blocks.flatten ++ tail).length :=
    ready.registers.total
  obtain ⟨memory, body, _, padded⟩ := TailPaddingFrame.prepare padding s tail stateBytes _ short
    ready.running rfl filled count ready.copied stateRead ready.frame
  have stackEq : padding.read .rsp = BitVec.ofNat 64 (top - 32) := ready.rsp
  rw [stackEq] at padded
  obtain ⟨final, compressed, pc, _, finalFrame, bytes, digest, compression⟩ :=
    padded.compress geometry stack
  rw [value] at compression
  have value' := compression.trans (TailPaddingReference.fold_short blocks tail full short)
  obtain ⟨outCore, memory', formatted, answer⟩ := HexOutputFrame.prepare final.core
    { s with memory := final.memory } bytes (blocks.flatten ++ tail) ready.running finalFrame pc
      digest value'
  exact ⟨outCore, memory', by
    simpa only [List.append_nil] using (eof.append body).append (compressed.append formatted),
    answer⟩

/-- Tails `56…63`: EOF branch, extra padding block and its compression, second padding block
and the final compression, hex and newline. -/
theorem after_eof_long {initial : Memory} {top : Nat} {c : Core} {s : Syscall.State}
    {tail : List Byte} {blocks : List (List Byte)}
    (ready : BufferedTailFrame.Ready initial (BitVec.ofNat 64 (top - 32)) c s tail
      (BitVec.ofNat 64 (blocks.flatten ++ tail).length)
      (blocks.foldl Driver.compressBlock Silmaril.Crypto.SHA256.H0))
    (long : 56 ≤ tail.length) (full : ∀ block ∈ blocks, block.length = 64)
    (geometry : CompressionStack.Geometry top) (stack : CompressionStack.Mapping initial top)
    (flags : «Word») :
    ∃ (outCore : Core) (memory : Memory),
      CLI.Proc.Runs CLI.X86Linux.isa CLI.Env.linux
        ⟨resumed { c with rip := 0x400177 } flags, s⟩ [] ⟨outCore, { s with memory := memory }⟩ ∧
      HexOutputFrame.Ready initial outCore { s with memory := memory } (blocks.flatten ++ tail) := by
  obtain ⟨priorH, observed, value⟩ := ready.hash
  let returned := ShortReadFrame.returnedCore c (.ok 0) flags
  rw [show resumed { c with rip := 0x400177 } flags = returned from rfl]
  have eof : CLI.Proc.Runs CLI.X86Linux.isa CLI.Env.linux ⟨returned, s⟩ []
      ⟨ShortReadFailure.paddingCore returned, s⟩ :=
    ShortReadFailure.eof_prefix returned s ready.running ready.frame.code rfl rfl
  let padding := ShortReadFailure.paddingCore returned
  have filled : padding.read .r8 = BitVec.ofNat 64 tail.length := ready.registers.filled
  have count : padding.read .rbx = BitVec.ofNat 64 (blocks.flatten ++ tail).length :=
    ready.registers.total
  obtain ⟨memory, body, _, padded⟩ := ExtraPaddingFrame.prepare padding s tail priorH _
    ready.room long ready.running rfl filled count ready.copied observed ready.frame
  have stackEq : padding.read .rsp = BitVec.ofNat 64 (top - 32) := ready.rsp
  rw [stackEq] at padded
  obtain ⟨_, _, first, _, loopReady⟩ := ExtraPaddingContinuation.advance padded geometry stack
  obtain ⟨_, stores, _, finalReady⟩ := SecondPaddingFrame.prepare loopReady
  obtain ⟨_, _, second, _, returnedReady⟩ := LongTailOutputFrame.advance finalReady geometry stack
  obtain ⟨outCore, memory', formatted, answer⟩ :=
    returnedReady.canonical_output blocks full value rfl
  exact ⟨outCore, memory', by
    simpa only [List.append_nil] using
      ((((eof.append body).append first).append stores).append second).append formatted,
    answer⟩

/-- The empty message: EOF at the first `read`, the dedicated empty padding block, one
compression from H0, hex and newline, for an arbitrary launch stack. -/
theorem after_first_eof {initial : Memory} {launchCore : Core} {s : Syscall.State}
    (running : s.exited = none) (frame : DriverMemory.Frame initial s.memory)
    (state : s.memory.readBytes InitStores.stateAddress 32 = some EmptySupport.initialStateBytes)
    (geometry : CompressionStack.Geometry (launchCore.read .rsp).toNat)
    (stack : CompressionStack.Mapping initial (launchCore.read .rsp).toNat) (flags : «Word») :
    ∃ (outCore : Core) (memory : Memory),
      CLI.Proc.Runs CLI.X86Linux.isa CLI.Env.linux
        ⟨resumed { LoadedStartup.readCore launchCore (launchCore.read .rsp).toNat with
            rip := 0x40015b } flags, s⟩ [] ⟨outCore, { s with memory := memory }⟩ ∧
      HexOutputFrame.Ready initial outCore { s with memory := memory } [] := by
  let top := (launchCore.read .rsp).toNat
  let c' := resumed { LoadedStartup.readCore launchCore top with rip := 0x40015b } flags
  have prefixRun : CLI.Proc.Runs CLI.X86Linux.isa CLI.Env.linux ⟨c', s⟩ []
      ⟨EmptyReadUniversal.eofPaddingCore c', s⟩ :=
    EmptyReadUniversal.eof_prefix c' s running frame.code rfl rfl
  obtain ⟨m1, padRun, padded, padFrame, _⟩ :=
    Padding.empty_block (EmptyReadUniversal.eofPaddingCore c') s running frame.code rfl
      (frame.bss_permitted .write rfl _ _ (by decide) (by decide))
      (frame.bss_permitted .read rfl _ _ (by decide) (by decide))
  have rspLaunch : (LoadedStartup.readCore launchCore top).read .rsp = BitVec.ofNat 64 (top - 32) :=
    (LoadedStartup.read_arguments launchCore top).2.2.2.2
  have rspE : (EmptyReadUniversal.eofPaddingCore c').read .rsp = BitVec.ofNat 64 (top - 32) := by
    rw [EmptyReadUniversal.eofPaddingCore_rsp, ← rspLaunch]
    simp [c', resumed, X86.State.read, X86.State.write, Machine.RegisterFile.write]
  have stateM1 : m1.readBytes 0x401660 32 = some EmptySupport.initialStateBytes := by
    rw [padFrame.readBytes (by intro offset bound; dsimp [Padding.blockAddress]; omega)]
    exact state
  have emptyBlock : EmptySupport.emptyBlock =
      TailPaddingFrame.block [] (BitVec.ofNat 64 ((([] : List (List Byte)).flatten ++
        ([] : List Byte)).length)) := by decide
  have callReady : TailPaddingFrame.CallReady initial (BitVec.ofNat 64 (top - 32))
      (Padding.lengthCore (Padding.zeroFinished (Padding.loopCore
        (EmptyReadUniversal.eofPaddingCore c'))))
      { s with memory := m1 } [] EmptySupport.initialStateBytes
      (BitVec.ofNat 64 ((([] : List (List Byte)).flatten ++ ([] : List Byte)).length)) := by
    refine ⟨by decide, running, rfl, (Padding.lengthCore_args _).2.1,
      (Padding.lengthCore_args _).1, stateM1, emptyBlock ▸ padded, ?_, ?_⟩
    · simpa [Padding.lengthCore, Padding.zeroFinished, Padding.loopCore, X86.State.read,
        X86.State.write, Machine.RegisterFile.write] using rspE
    · exact frame.trans (padFrame.mono (by
        intro address inside
        dsimp [Padding.blockAddress, DriverMemory.Above] at *
        omega))
  obtain ⟨final, compressed, pc, _, finalFrame, bytes, digest, compression⟩ :=
    callReady.compress geometry stack
  have initialHash : (stateOf EmptySupport.initialStateBytes).toState =
      Silmaril.Crypto.SHA256.H0 := by
    rw [EmptySupport.initialStateBytes_state]
    rfl
  rw [initialHash] at compression
  have value := compression.trans
    (TailPaddingReference.fold_short [] [] (by simp) (by decide))
  obtain ⟨outCore, memory', formatted, answer⟩ := HexOutputFrame.prepare final.core
    { s with memory := final.memory } bytes [] running finalFrame pc digest
      (by simpa only [List.flatten_nil, List.append_nil] using value)
  exact ⟨outCore, memory', by
    simpa only [List.append_nil] using (prefixRun.append padRun).append (compressed.append formatted),
    answer⟩

end AfterEof

/-! ## The segment -/

section Segment

open CLI.Sha256Cli

set_option maxRecDepth 100000

/-- From the loop head after the last positive read. -/
theorem leads_of_loopHead {input : CLI.ProcInput} {message : List Byte} {x : PS}
    {evs : List Syscall.Event} (h : LoopEnd input message x evs) (head : AtLoopHead message x) :
    Leads CStep (Ok message) (OutReady input message) x evs := by
  obtain ⟨initial, top, blocks, tail, ready, full, flat, geometry, stack⟩ := head
  subst flat
  cases x with
  | mk c s =>
  change BufferedTailFrame.Ready initial _ c s tail _ _ at ready
  have trapped : CLI.X86Linux.step c s.memory = .syscall { c with rip := 0x400177 } := by
    have actual := CLI.X86Linux.step_of_entry (core := c) (memory := s.memory) Binary.ok_400175.1
      (by simp [ready.registers.pc, Binary.i_400175])
      (ready.frame.code _ (by simp [Binary.transcript]))
    simpa [CLI.X86Linux.Entry.denote, Binary.i_400175, ready.registers.pc] using actual
  have request := ready.registers.request_below64 ready.room
  have room := ready.room
  apply leads_of_eof_read trapped request.1 request.2
    (ready.frame.bss_permitted .write rfl _ _ (by omega) (by omega)) h.input (ok_at h)
  intro flags
  obtain ⟨outCore, memory, run, answer⟩ : ∃ (outCore : Core) (memory : Memory),
      CLI.Proc.Runs CLI.X86Linux.isa CLI.Env.linux
        ⟨resumed { c with rip := 0x400177 } flags, s⟩ [] ⟨outCore, { s with memory := memory }⟩ ∧
      HexOutputFrame.Ready initial outCore { s with memory := memory } (blocks.flatten ++ tail) := by
    by_cases short : tail.length < 56
    · exact after_eof_short ready short full geometry stack flags
    · exact after_eof_long ready (by omega) full geometry stack flags
  exact leads_of_silent (x := ⟨_, s⟩) (y := ⟨outCore, { s with memory := memory }⟩) run
    (ok_after_eof h h.running) (.done (outReady_after_eof h answer))

/-- From the first `read` of the empty message. -/
theorem leads_of_firstRead {input : CLI.ProcInput} {message : List Byte} {x : PS}
    {evs : List Syscall.Event} (h : LoopEnd input message x evs) (empty : message = [])
    (first : AtFirstRead input x) :
    Leads CStep (Ok message) (OutReady input message) x evs := by
  obtain ⟨launchCore, initial, loaded, core, state, writes, geometry, stack⟩ := first
  subst empty
  cases x with
  | mk c s =>
  change c = _ at core
  subst core
  change s.memory.readBytes _ 32 = _ at state
  have frame : DriverMemory.Frame initial s.memory := ⟨loaded.1, writes.mono (by
    intro address inside
    have above := geometry.aboveGlobals
    dsimp [LoadedStartup.Footprint, InitStores.stateAddress, DriverMemory.Above] at inside ⊢
    omega)⟩
  have trapped : CLI.X86Linux.step (LoadedStartup.readCore launchCore (launchCore.read .rsp).toNat)
      s.memory = .syscall { LoadedStartup.readCore launchCore (launchCore.read .rsp).toNat with
        rip := 0x40015b } := by
    have actual := CLI.X86Linux.step_of_entry
      (core := LoadedStartup.readCore launchCore (launchCore.read .rsp).toNat)
      (memory := s.memory) Binary.ok_400159.1 (by rfl)
      (frame.code _ (by simp [Binary.transcript]))
    have pc : (LoadedStartup.readCore launchCore (launchCore.read .rsp).toNat).rip = 0x400159 := rfl
    simpa [CLI.X86Linux.Entry.denote, Binary.i_400159, pc] using actual
  have requested : CLI.X86Linux.request
      { LoadedStartup.readCore launchCore (launchCore.read .rsp).toNat with rip := 0x40015b } =
        some (.read 0 0x401620 64) := by
    obtain ⟨rax, rdi, rsi, rdx, _⟩ :=
      LoadedStartup.read_arguments launchCore (launchCore.read .rsp).toNat
    simp only [X86.State.read] at rax rdi rsi rdx
    simp [CLI.X86Linux.request, X86.State.read, rax, rdi, rsi, rdx, CLI.X86Linux.readNumber]
  apply leads_of_eof_read trapped requested (by decide)
    (frame.bss_permitted .write rfl _ _ (by decide) (by decide)) h.input (ok_at h)
  intro flags
  obtain ⟨outCore, memory, run, answer⟩ :=
    after_first_eof (launchCore := launchCore) h.running frame state geometry stack flags
  exact leads_of_silent (x := ⟨_, s⟩) (y := ⟨outCore, { s with memory := memory }⟩) run
    (ok_after_eof h h.running) (.done (outReady_after_eof h answer))

/-- **Segment `tail`** (VERIFIED): the exact statement `TailSegment fun _ => True`. -/
theorem tail_segment_proved : TailSegment fun _ => True := by
  intro message input x evs _ h
  rcases h.frame with head | ⟨empty, first⟩
  · exact leads_of_loopHead h head
  · exact leads_of_firstRead h empty first

end Segment

/-! ## Non-vacuity (VERIFIED)

The hypothesis `LoopEnd` of the segment is satisfiable: from every CLI launch on the empty
stdin, the startup run reaches `LoopEnd` (the `AtFirstRead` arm), and such launches exist
(`launch_exists`). -/

section NonVacuity

open CLI.Sha256Cli

theorem loopEnd_of_launch_empty {input : CLI.ProcInput} {x : PS}
    (stdin : input.stdin = .ofList []) (launch : Launch input x) :
    ∃ y : PS, LoopEnd input [] y [] := by
  obtain ⟨⟨m, loaded, memory, exited, std⟩, geometry, mapping⟩ := launch
  cases x with
  | mk c s =>
  change s.memory = m at memory
  subst memory
  change s.exited = none at exited
  have above : 0x401680 + 384 ≤ (c.read .rsp).toNat := geometry.aboveGlobals
  obtain ⟨after, _, state, writes, _⟩ := LoadedStartup.of_loaded input c s loaded
    (by omega) exited
  refine ⟨⟨LoadedStartup.readCore c (c.read .rsp).toNat, { s with memory := after }⟩,
    ⟨stdin, .inr ⟨rfl, c, s.memory, loaded, rfl, state, writes, geometry, mapping⟩, exited,
      ⟨_, std.1, rfl, stdin, rfl⟩, ⟨_, std.2.1, rfl⟩, rfl, rfl, ?_, ?_⟩⟩
  · intro fd bytes member
    simp at member
  · intro fd bytes member
    simp at member

theorem loopEnd_exists : ∃ (input : CLI.ProcInput) (y : PS), LoopEnd input [] y [] := by
  obtain ⟨x, launch⟩ := launch_exists []
  obtain ⟨y, h⟩ := loopEnd_of_launch_empty (by rfl) launch
  exact ⟨_, y, h⟩

end NonVacuity

end Silmaril.Process.LPS.Problems.Sha256Cli.Tail
