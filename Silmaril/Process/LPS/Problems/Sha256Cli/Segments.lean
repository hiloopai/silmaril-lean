module

public import Silmaril.Process.LPS.Problems.Sha256Cli.Statement
public import Silmaril.Process.LPS.Problems.Sha256Cli.Leads
public import Silmaril.Process.CLI.Sha256Cli.Spec
public import Silmaril.Process.CLI.Sha256Cli.BlockSequenceOutput
public import Silmaril.Process.CLI.Sha256Cli.BufferedTailFrame
public import Silmaril.Process.CLI.Sha256Cli.HexOutputFinish
public import Silmaril.Process.CLI.Sha256Cli.ShortReadTransfer
public import Silmaril.Apps.Sha256sum.StdinRef

/-! # The `sha256` end-to-end proof in four segments

The target is `Sha256Cli.TotalGoal` (`Statement.lean`): LPS, native x86-64 launch of the
pinned ELF, every flag oracle, every refusal configuration, every finite stdin.

The proof is cut at three points of the actual binary, all expressed in the CLI process model
of the #3029 chain (`Process.CLI.X86Linux`, environment `Env.reliable`: short reads and
writes, no error returns, which is exactly what LPS allows on the standard channels):

```
Launch ──loop──▶ LoopEnd ──tail──▶ OutReady ──output──▶ Done      (CLI, Leads with Ok)
CliTotalOn ──bridge──▶ TotalOn                                    (CLI ⇒ LPS)
```

* `LoopSegment` (key `loop`): startup and the read loop. From every launch, every execution
  keeps `Ok` and reaches the loop head with the whole message consumed, the hash state equal
  to the fold of the full blocks and the tail in the buffer.
* `TailSegment` (key `tail`): EOF and padding for every tail length `0…63` (one or two final
  compressions) and the hex formatting, up to the write-ready cut point.
* `OutputSegment` (key `output`): the write loop under every write split, and exit 0.
* `BridgeSegment` (key `bridge`): a CLI `Leads` proof from every CLI launch transfers to the
  LPS statement for the pinned ELF.

`totalGoal_of_segments` (the glue) is proved; the four segments are stated `Prop`s here and
proved (or reduced) in downstream files, assembled in `EndToEnd.lean`.

Status: everything in this file is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.Sha256Cli

open Silmaril.Process.LPS.Machines

/-! ## The CLI side -/

/-- The chain's transcribed image of the same ELF. -/
abbrev cliImage : CLI.Image := CLI.Sha256Cli.image

/-- CLI process states and steps, in the reliable environment. -/
abbrev PS := CLI.PState CLI.X86Linux.isa CLI.Env.reliable
abbrev CStep : PS → List Syscall.Event → PS → Prop := CLI.Proc.Step CLI.X86Linux.isa CLI.Env.reliable

def PS.cpu (x : PS) : CLI.X86Linux.Core := x.core
def PS.sys (x : PS) : Syscall.State := x.env

/-- A CLI launch: the chain's loader relation plus the stack/global separation and stack
mapping that LPS's `ValidEntry` supplies and the bare CLI `Loaded` does not
(`Sha256Cli.LoadedIsolation` shows `Loaded` alone admits code aliasing). -/
def Launch (input : CLI.ProcInput) (x : PS) : Prop :=
  CLI.X86Linux.reliable.Init cliImage input x ∧
    CLI.Sha256Cli.CompressionStack.Geometry (x.cpu.read .rsp).toNat ∧
    CLI.Sha256Cli.CompressionStack.Mapping x.sys.memory (x.cpu.read .rsp).toNat

/-- Reads come only from descriptor 0. -/
def ReadsOnlyStdin (evs : List Syscall.Event) : Prop :=
  ∀ fd bytes, Syscall.Event.read fd bytes ∈ evs → fd = 0

/-- At a `read` trap the requested count is positive. The LPS `read` checks `access_ok` on the
buffer before it looks at the count, so a zero-count read at an arbitrary address would not
match the CLI; this register fact is what the bridge needs from the CLI run. -/
def ReadArgs (x : PS) : Prop :=
  ∀ t, CLI.X86Linux.step x.cpu x.sys.memory = .syscall t → (t.read .rax).toNat = 0 →
    0 < (t.read .rdx).toNat

theorem readArgs_of_retired {x : PS} {c : CLI.X86Linux.Core} {m : Silmaril.Process.Memory}
    (h : CLI.X86Linux.step x.cpu x.sys.memory = .retired c m) : ReadArgs x := by
  intro t ht; rw [h] at ht; cases ht

theorem readArgs_of_syscall {x : PS} {t : CLI.X86Linux.Core}
    (h : CLI.X86Linux.step x.cpu x.sys.memory = .syscall t)
    (args : (t.read .rax).toNat = 0 → 0 < (t.read .rdx).toNat) : ReadArgs x := by
  intro t' ht'; rw [h] at ht'; cases ht'; exact args

theorem request_read_count {t : CLI.X86Linux.Core} {fd a n : Nat}
    (request : CLI.X86Linux.request t = some (.read fd a n)) : (t.read .rdx).toNat = n := by
  unfold CLI.X86Linux.request at request
  simp only at request
  split_ifs at request <;> cases request
  rfl

theorem readArgs_of_read {x : PS} {t : CLI.X86Linux.Core} {fd a n : Nat}
    (h : CLI.X86Linux.step x.cpu x.sys.memory = .syscall t)
    (request : CLI.X86Linux.request t = some (.read fd a n)) (positive : 0 < n) : ReadArgs x :=
  readArgs_of_syscall h fun _ => by rw [request_read_count request]; exact positive

theorem readArgs_of_not_read {x : PS} {t : CLI.X86Linux.Core}
    (h : CLI.X86Linux.step x.cpu x.sys.memory = .syscall t)
    (request : ∀ fd a n, CLI.X86Linux.request t ≠ some (.read fd a n)) : ReadArgs x :=
  readArgs_of_syscall h fun zero => by
    exfalso
    apply request ((t.read .rdi).setWidth 32).toNat (t.read .rsi).toNat (t.read .rdx).toNat
    simp [CLI.X86Linux.request, CLI.X86Linux.readNumber, zero]

/-- The safety invariant of a running state: only stdin read, only stdout written, a prefix of
the message read, a prefix of the answer written, and nothing written before the whole message
and its end of file were read. -/
def Ok (message : List Byte) (x : PS) (evs : List Syscall.Event) : Prop :=
  x.sys.exited = none ∧ CLI.WritesOnlyTo [1] evs ∧ ReadsOnlyStdin evs ∧
    CLI.stdinRead evs <+: message ∧ CLI.stdout evs <+: CLI.Sha256.expected message ∧
    (CLI.stdout evs = [] ∨ (CLI.stdinRead evs = message ∧ CLI.SawEof 0 evs)) ∧ ReadArgs x

/-- `Ok` without the register part. -/
def OkE (message : List Byte) (x : PS) (evs : List Syscall.Event) : Prop :=
  x.sys.exited = none ∧ CLI.WritesOnlyTo [1] evs ∧ ReadsOnlyStdin evs ∧
    CLI.stdinRead evs <+: message ∧ CLI.stdout evs <+: CLI.Sha256.expected message ∧
    (CLI.stdout evs = [] ∨ (CLI.stdinRead evs = message ∧ CLI.SawEof 0 evs))

theorem ok_of_okE {message : List Byte} {x : PS} {evs : List Syscall.Event}
    (e : OkE message x evs) (args : ReadArgs x) : Ok message x evs :=
  ⟨e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2.1, e.2.2.2.2.2, args⟩

theorem Ok.okE {message : List Byte} {x : PS} {evs : List Syscall.Event}
    (o : Ok message x evs) : OkE message x evs :=
  ⟨o.1, o.2.1, o.2.2.1, o.2.2.2.1, o.2.2.2.2.1, o.2.2.2.2.2.1⟩

/-- The goal: exited 0 with the exact answer. -/
def Done (input : CLI.ProcInput) (_message : List Byte) (x : PS) (evs : List Syscall.Event) :
    Prop :=
  x.sys.exited = some 0 ∧ CLI.Sha256.Success input evs ∧ CLI.WritesOnlyTo [1] evs ∧
    ReadsOnlyStdin evs

/-- The machine is at the loop-head `read` (`0x400175`) after the last positive read: the
buffer holds the tail, the hash state is the fold of the full blocks, the modular total is the
message length, and the compressor's stack frame is available. -/
def AtLoopHead (message : List Byte) (x : PS) : Prop :=
  ∃ (initial : Silmaril.Process.Memory) (top : Nat) (blocks : List (List Byte)) (tail : List Byte),
    CLI.Sha256Cli.BufferedTailFrame.Ready initial (BitVec.ofNat 64 (top - 32)) x.cpu x.sys tail
        (BitVec.ofNat 64 message.length)
        (blocks.foldl CLI.Sha256Cli.Driver.compressBlock Silmaril.Crypto.SHA256.H0) ∧
      (∀ block ∈ blocks, block.length = 64) ∧ blocks.flatten ++ tail = message ∧
      CLI.Sha256Cli.CompressionStack.Geometry top ∧ CLI.Sha256Cli.CompressionStack.Mapping initial top

/-- The machine is at the first `read` (`0x400159`, before the loop) with H initialized: the
EOF point of the empty message, which never reaches the loop head. -/
def AtFirstRead (input : CLI.ProcInput) (x : PS) : Prop :=
  ∃ (launchCore : CLI.X86Linux.Core) (initial : Silmaril.Process.Memory),
    CLI.X86Linux.Loaded cliImage input launchCore initial ∧
    x.cpu = CLI.Sha256Cli.LoadedStartup.readCore launchCore (launchCore.read .rsp).toNat ∧
    x.sys.memory.readBytes CLI.Sha256Cli.InitStores.stateAddress 32 =
      some CLI.Sha256Cli.EmptySupport.initialStateBytes ∧
    Silmaril.Process.Memory.WritesWithin initial x.sys.memory
      (CLI.Sha256Cli.LoadedStartup.Footprint (launchCore.read .rsp).toNat) ∧
    CLI.Sha256Cli.CompressionStack.Geometry (launchCore.read .rsp).toNat ∧
    CLI.Sha256Cli.CompressionStack.Mapping initial (launchCore.read .rsp).toNat

/-- Cut point 1: the whole message has been read and the next `read` returns EOF; either at
the loop head, or (empty message only) at the first read. -/
structure LoopEnd (input : CLI.ProcInput) (message : List Byte) (x : PS)
    (evs : List Syscall.Event) : Prop where
  stdin : input.stdin = .ofList message
  frame : AtLoopHead message x ∨ (message = [] ∧ AtFirstRead input x)
  running : x.sys.exited = none
  input : CLI.Sha256Cli.ShortReadTransfer.InputAt x.sys message message.length
  output : ∃ d : Syscall.Descriptor, x.sys.descriptors 1 = some d ∧ d.writable = true
  read : CLI.stdinRead evs = message
  silent : CLI.stdout evs = []
  only : CLI.WritesOnlyTo [1] evs
  reads : ReadsOnlyStdin evs

/-- Cut point 2: the 65 answer bytes are in `out` and the write request is prepared. -/
structure OutReady (input : CLI.ProcInput) (message : List Byte) (x : PS)
    (evs : List Syscall.Event) : Prop where
  stdin : input.stdin = .ofList message
  ready : ∃ initial : Silmaril.Process.Memory, CLI.Sha256Cli.HexOutputFrame.Ready initial x.cpu x.sys message
  accounted : CLI.Sha256Cli.Driver.OutputInv message evs 0
  output : ∃ d : Syscall.Descriptor, x.sys.descriptors 1 = some d ∧ d.writable = true
  reads : ReadsOnlyStdin evs

/-! ## The four segments (stated) -/

/-- **Segment `loop`.** Startup, then the read loop under every read partition. -/
def LoopSegment (domain : List Byte → Prop) : Prop :=
  ∀ (message : List Byte) (input : CLI.ProcInput) (x : PS), domain message →
    input.stdin = .ofList message → input.Valid → Launch input x →
      Leads CStep (Ok message) (LoopEnd input message) x []

/-- **Segment `tail`.** EOF, padding of any tail, final compression(s) and hex formatting. -/
def TailSegment (domain : List Byte → Prop) : Prop :=
  ∀ (message : List Byte) (input : CLI.ProcInput) (x : PS) (evs : List Syscall.Event),
    domain message → LoopEnd input message x evs →
      Leads CStep (Ok message) (OutReady input message) x evs

/-- **Segment `output`.** The write loop under every write split, then `exit(0)`. -/
def OutputSegment (domain : List Byte → Prop) : Prop :=
  ∀ (message : List Byte) (input : CLI.ProcInput) (x : PS) (evs : List Syscall.Event),
    domain message → OutReady input message x evs →
      Leads CStep (Ok message) (Done input message) x evs

/-- The CLI-level end-to-end statement the bridge consumes. -/
def CliTotalOn (domain : List Byte → Prop) : Prop :=
  ∀ (message : List Byte) (input : CLI.ProcInput) (x : PS), domain message →
    input.stdin = .ofList message → input.Valid → Launch input x →
      Leads CStep (Ok message) (Done input message) x []

/-- **Segment `bridge`.** CLI total correctness from every CLI launch implies the LPS
statement for the pinned ELF. Its content: the LPS launch of `snapshot` is a CLI `Launch` of
`cliImage` (same segment bytes, SysV stack, 8 MiB stack mapping above the image); the LPS
instruction step of `x86WithFlagOracle` is the CLI `X86Linux.step` (both are `X86.Ext.fetch`/
`exec`; the oracle only completes the flags copied to R11, which `Resume` leaves unspecified);
LPS `read`/`write`/`exit` on the standard channels are CLI `readSome`/`readEof`/`writeSome`/
`exit` without refusals; LPS byte events are the flattening of CLI events (EOF reads are
silent); no lazy page is ever materialized, so `limit` is irrelevant. -/
def BridgeSegment : Prop := ∀ domain : List Byte → Prop, CliTotalOn domain → TotalOn domain

/-! ## Glue (VERIFIED) -/

/-- Goal states are final: an exited process takes no step. -/
theorem done_final (input : CLI.ProcInput) (message : List Byte) :
    ∀ z zs, Done input message z zs → ∀ e w, ¬ CStep z e w := by
  rintro ⟨c, s⟩ zs ⟨exited, -⟩ e w step
  change s.exited = some 0 at exited
  cases step with
  | retire running _ => exact absurd (running.symm.trans exited) (by simp)
  | call running _ _ _ _ => exact absurd (running.symm.trans exited) (by simp)
  | exit running _ _ _ => exact absurd (running.symm.trans exited) (by simp)

/-- The three CLI segments compose into the CLI end-to-end statement. -/
theorem cliTotalOn_of_segments {domain : List Byte → Prop} (loop : LoopSegment domain)
    (tail : TailSegment domain) (output : OutputSegment domain) : CliTotalOn domain :=
  fun message input x member stdin valid launch =>
    (loop message input x member stdin valid launch).trans fun y es atEnd =>
      (tail message input y es member atEnd).trans fun z zs ready =>
        output message input z zs member ready

/-- **Glue.** The four segments give the LPS target on any domain. -/
theorem totalOn_of_segments {domain : List Byte → Prop} (loop : LoopSegment domain)
    (tail : TailSegment domain) (output : OutputSegment domain) (bridge : BridgeSegment) :
    TotalOn domain :=
  bridge domain (cliTotalOn_of_segments loop tail output)

/-- **Glue**, full target. -/
theorem totalGoal_of_segments (loop : LoopSegment fun _ => True)
    (tail : TailSegment fun _ => True) (output : OutputSegment fun _ => True)
    (bridge : BridgeSegment) : TotalGoal :=
  totalOn_of_segments loop tail output bridge

/-- **Glue**, bounded tier: segments proved only for inputs of at most `n` bytes suffice. -/
theorem boundedGoal_of_segments (n : Nat) (loop : LoopSegment fun m => m.length ≤ n)
    (tail : TailSegment fun m => m.length ≤ n) (output : OutputSegment fun m => m.length ≤ n)
    (bridge : BridgeSegment) : BoundedGoal n :=
  totalOn_of_segments loop tail output bridge

/-- What a CLI `Leads` proof gives directly (used by the bridge): along every CLI run from a
launch the invariant or the goal holds, every non-final reachable state can move, and no run
is infinite. -/
theorem CliTotalOn.consequences {domain : List Byte → Prop} (h : CliTotalOn domain)
    {message : List Byte} {input : CLI.ProcInput} {x : PS} (member : domain message)
    (stdin : input.stdin = .ofList message) (valid : input.Valid) (launch : Launch input x) :
    (∀ es y, Machine.Trace.Runs CStep x es y → Ok message y es ∨ Done input message y es) ∧
      (∀ es y, Machine.Trace.Runs CStep x es y → ¬ Done input message y es → ∃ e w, CStep y e w) ∧
      ¬ Machine.Trace.Diverges CStep x := by
  have leads := h message input x member stdin valid launch
  refine ⟨fun es y run => ?_, fun es y run notDone => ?_, leads.not_diverges (done_final _ _)⟩
  · simpa using leads.runs (done_final _ _) run
  · exact leads.progress (done_final _ _) run (by simpa using notDone)

/-! ## Non-vacuity (VERIFIED)

The CLI launch predicate is inhabited on every stdin (the chain's concrete System V launch
`Sha256Cli.core₀`/`memory₀`), so `LoopSegment` and `CliTotalOn` are not vacuous. -/

set_option maxRecDepth 100000 in
theorem launch_exists (message : List Byte) :
    ∃ x : PS, Launch (CLI.Sha256Cli.inputOf message) x := by
  have rsp : (CLI.Sha256Cli.core₀.read .rsp).toNat = CLI.Sha256Cli.sp := by
    simp only [CLI.Sha256Cli.core₀, Silmaril.X86.State.read, Silmaril.X86.State.write]
    decide
  have loaded := CLI.Sha256Cli.loaded message
  refine ⟨⟨CLI.Sha256Cli.core₀, ⟨CLI.Sha256Cli.memory₀, fun fd =>
      if fd = 0 then some ⟨true, false, .ofList message, 0, []⟩
      else if fd = 1 ∨ fd = 2 then some ⟨false, true, .ofList [], 0, []⟩ else none, none⟩⟩,
    ⟨CLI.Sha256Cli.memory₀, loaded, rfl, rfl, by simp [CLI.StdDescriptors, CLI.Sha256Cli.inputOf]⟩,
    ?_, ?_⟩
  · exact CLI.Sha256Cli.CompressionStack.Geometry.of_loaded loaded (by
      change 0x401680 + 384 ≤ (CLI.Sha256Cli.core₀.read .rsp).toNat
      rw [rsp]; decide)
  · apply CLI.Sha256Cli.CompressionStack.Mapping.of_loaded loaded
    rw [rsp]
    exact Silmaril.X86.EntryState.permitted CLI.Sha256Cli.placements_wf
      (placement := ⟨⟨CLI.Sha256Cli.sp - CLI.X86Linux.stackRoom, CLI.X86Linux.stackRoom,
        ⟨true, true, false⟩⟩, none⟩)
      (by simp [CLI.Sha256Cli.placements]) rfl
      (by simp [CLI.Sha256Cli.sp, CLI.X86Linux.stackRoom])
      (by simp [CLI.Sha256Cli.sp, CLI.X86Linux.stackRoom])
      (by simp [CLI.Sha256Cli.sp, CLI.X86Linux.stackRoom])

/-! ## Relation to GNU `sha256sum` (VERIFIED)

On the stdin path `Apps.Sha256sum` (GNU coreutils 9.4) prints the same 64 digits followed by
`"  -\n"` instead of `"\n"`. -/

theorem hexDigit_agrees (n : Nat) (small : n < 16) :
    (Silmaril.Apps.Sha256sum.hexDigit n).toBitVec = CLI.Sha256.hexDigit n := by
  interval_cases n <;> decide

theorem gnu_stdout (message : List Byte) :
    (Silmaril.Apps.Sha256sum.Sys.stdinRecord (message.map UInt8.ofBitVec)).map UInt8.toBitVec =
      (CLI.Sha256.expected message).dropLast ++ [0x20, 0x20, 0x2d, 0x0a] := by
  have digits : ∀ bytes : List UInt8,
      (Silmaril.Apps.Sha256sum.hexLower bytes).map UInt8.toBitVec = bytes.flatMap CLI.Sha256.hexByte := by
    intro bytes
    induction bytes with
    | nil => rfl
    | cons b rest ih =>
      simp only [Silmaril.Apps.Sha256sum.hexLower, List.flatMap_cons, List.map_append] at ih ⊢
      rw [ih]
      simp only [List.map_cons, List.map_nil, CLI.Sha256.hexByte, List.cons_append, List.nil_append]
      have bound := b.toNat_lt
      rw [hexDigit_agrees _ (by omega), hexDigit_agrees _ (by omega)]
  have back : (message.map UInt8.ofBitVec).map UInt8.toBitVec = message := by
    simp [List.map_map, Function.comp_def]
  simp only [Silmaril.Apps.Sha256sum.Sys.stdinRecord, Silmaril.Apps.Sha256sum.hexDigest,
    List.map_append, digits, CLI.Sha256.expected, List.dropLast_concat]
  rfl

/-! The segment proofs are in `LoopSegment.lean`, `Tail.lean`, `OutputSegment.lean` and the
bridge files; `EndToEnd.lean` assembles them. -/

end Silmaril.Process.LPS.Problems.Sha256Cli
