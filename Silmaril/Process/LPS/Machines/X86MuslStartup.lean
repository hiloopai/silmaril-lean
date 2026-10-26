module

public import Silmaril.Process.LPS.Machines.X86MuslStartupBytes
public import Silmaril.Process.LPS.ELFImageX86
public import Silmaril.Process.LPS.Machines.X86WireFlagOracle
public import Silmaril.Process.LPS.RunHelpers

/-! # The pinned static-musl executable under the native x86 LPS launch

The checksum executable in `examples/verification-projects/x86-musl-startup`
is parsed from its exact 16,256 repository bytes by the checked ELF64 loader
(`ELFImage.loadX86`). The loaded snapshot is accepted by the Wire+REP STOSQ
option and its flag-oracle wrapper. A launch with the QEMU run's argv
(`checksum`) and empty environment satisfies the native launch guards, and its
first actual LPS transition (`xor %rbp,%rbp` at the ELF entry 0x401062) retires
under every syscall specification and refusal filter, for the deterministic
option and for the flag-oracle option under every oracle.

Scope: this module stops at the first transition and shows `main`'s bytes
(0x401030) fetchable in the launch memory. Reaching `main` is proved
downstream: `X86MuslRun.reaches_main` (`X86MuslRunMain`) gives a 542-transition
LPS run to `main`, through `arch_prctl(ARCH_SET_FS)` and `set_tid_address`, and
`X86MuslRun.every_execution` (`X86MuslRunUniversal`) shows every execution
enters `main` that way. (QEMU's instruction-attempt trace, under QEMU's own
launch, first reaches `main` at attempt 532; the two counts are not related
by any theorem.) The launch (`X86Launch.entryStack`) is a minimal
synthetic SysV profile, not Linux's `create_elf_tables`; see
`docs/LPSX86Parity.md`.

Proof method: `Std.ExtHashMap` lookups do not reduce in the kernel, and the
launch memory eagerly backs an 8 MiB stack. Image bytes are therefore read
through `segmentsView`, a plain list computation, using the loader's frame
rules (`initialMemory_below_stack_get`, `initialMemory_segments_get`), and
permission checks run on explicit regions.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Silmaril.Process.LPS.Machines.X86MuslStartup

open Silmaril.Formats
open Silmaril.Process.LPS.ELFImage

/-- `readelf -h` of the pinned file, field by field. -/
def header : ELF.Header :=
  ⟨0, 0, 2, 62, 1, 0x401062, 64, 15232, 0, 64, 56, 6, 64, 16, 15⟩

/-- The four `PT_LOAD`s, then `PT_GNU_STACK` and `PT_GNU_RELRO`. -/
def programHeaders : List ELF.ProgramHeader :=
  [ ⟨1, 4, 0, 0x400000, 0x400000, 0x190, 0x190, 0x1000⟩,
    ⟨1, 5, 0x1000, 0x401000, 0x401000, 0x874, 0x874, 0x1000⟩,
    ⟨1, 4, 0x2000, 0x402000, 0x402000, 0x54, 0x54, 0x1000⟩,
    ⟨1, 6, 0x2fd0, 0x403fd0, 0x403fd0, 0x44, 0x2a8, 0x1000⟩,
    ⟨0x6474e551, 6, 0, 0, 0, 0, 0, 0x10⟩,
    ⟨0x6474e552, 4, 0x2fd0, 0x403fd0, 0x403fd0, 0x30, 0x30, 1⟩ ]

def records : Records :=
  ⟨header, programHeaders, ⟨1, 4, 0, 0x400000, 0x400000, 0x190, 0x190, 0x1000⟩⟩

theorem file_size : file.size = 16256 := by decide +kernel

theorem parsed : parse x86Policy file = some records := by decide +kernel

def snapshot : X86Launch.Snapshot := records.x86Snapshot file

/-- `main`, from `checksum.disassembly.txt`; QEMU first attempts it at index 532. -/
def mainAddress : Nat := 0x401030

theorem entry_address : snapshot.image.initPc = 0x401062 := rfl

theorem segments_nowrap :
    ∀ segment ∈ snapshot.image.segments, segment.base + segment.bytes.length ≤ 2 ^ 64 := by
  decide +kernel

/-! ## Mapped regions

`String.contains` (used by segment permission letters) does not reduce in the
kernel, so the permission records are computed once by `simp` and the
remaining span checks run on explicit regions. -/

def imageRegions : List Silmaril.Process.Region :=
  [ ⟨0x400000, 0x190, ⟨true, false, false⟩⟩, ⟨0x401000, 0x874, ⟨true, false, true⟩⟩,
    ⟨0x402000, 0x54, ⟨true, false, false⟩⟩, ⟨0x403fd0, 0x2a8, ⟨true, true, false⟩⟩ ]

theorem image_regions : snapshot.image.segments.map segmentRegion = imageRegions := by
  simp [snapshot, Records.x86Snapshot, Records.image, records, programHeaders, loadHeaders,
    segment, segmentRegion, segmentPermissions, Segment.readable, Segment.writable,
    Segment.executable, permissions, imageRegions]

/-- Span checks depend only on the mapped regions. -/
theorem permitted_of_regions {memory : Silmaril.Process.Memory}
    {regions : List Silmaril.Process.Region} (same : memory.regions = regions)
    (access : Silmaril.Process.Access) (address length : Nat)
    (checked : (Silmaril.Process.Memory.mk regions ∅).checkSpan access address length = true) :
    memory.Permitted access address length := by
  unfold Silmaril.Process.Memory.Permitted Silmaril.Process.Memory.checkSpan
    Silmaril.Process.Memory.permits
  rw [same]
  exact checked

theorem initialMemory_regions (sp : Word) (stack : List Byte) :
    (initialMemory snapshot.image.segments sp stack).regions =
      imageRegions ++ [⟨sp.toNat - stackMaxSize.toNat,
        (pageRoundUp (uns sp + stack.length)).toNat - (sp.toNat - stackMaxSize.toNat),
        ⟨true, true, false⟩⟩] := by
  rw [← image_regions]
  rfl

/-! ## Entry and `main` bytes in the loaded image -/

/-- `xor %rbp,%rbp`, the first QEMU attempt (PC 0x401062). -/
def entryBytes : List Byte := [0x48, 0x31, 0xed]

/-- `endbr64`, the first instruction of `main`. -/
def mainBytes : List Byte := [0xf3, 0x0f, 0x1e, 0xfa]

theorem image_entry_fetched :
    (initialMemory snapshot.image.segments 0 []).fetchBytes 0x401062 3 = some entryBytes := by
  apply Silmaril.Process.Memory.readWith_eq _ .execute 0x401062 entryBytes
    (permitted_of_regions (initialMemory_regions 0 []) _ _ _ (by decide +kernel))
  intro index bound
  rw [initialMemory_segments_get _ _ segments_nowrap]
  revert index
  decide +kernel

theorem image_main_fetched :
    (initialMemory snapshot.image.segments 0 []).fetchBytes mainAddress 4 = some mainBytes := by
  apply Silmaril.Process.Memory.readWith_eq _ .execute mainAddress mainBytes
    (permitted_of_regions (initialMemory_regions 0 []) _ _ _ (by decide +kernel))
  intro index bound
  rw [initialMemory_segments_get _ _ segments_nowrap]
  revert index
  decide +kernel

def entryDecoded : Silmaril.X86.Ext.Wire.Decoded :=
  (Silmaril.X86.Ext.Wire.decode entryBytes).get (by decide +kernel)

theorem entry_decode : Silmaril.X86.Ext.Wire.decode entryBytes = some entryDecoded :=
  (Option.some_get _).symm

theorem entryDecoded_length : entryDecoded.length = 3 := by decide +kernel

/-! ## Byte-bound loading under the Wire+REP STOSQ options -/

theorem entry_fetchable (platform : Silmaril.X86.Ext.Wire.Platform) :
    (x86WireDf0RepStosq platform).entryFetchable snapshot.image.segments
      snapshot.image.initPc = true := by
  have fetched : Silmaril.X86.Ext.Wire.fetch (initialMemory snapshot.image.segments 0 [])
      snapshot.image.initPc = .decoded entryDecoded :=
    Silmaril.X86.Ext.Wire.fetch_eq_decoded_iff.mpr
      ⟨entryBytes, by rw [entryDecoded_length]; exact image_entry_fetched, entry_decode⟩
  simp only [x86WireDf0RepStosq, x86Wire, fetched, Bool.or_true]

theorem memoryRead_of_found {segments : List Segment} {address : Word} {length : Nat}
    {found : Segment} (located : findSegment segments (uns address) length = some found)
    (readable : found.readable = true) :
    memoryRead segments address length = (List.range length).mapM
      (fun offset => found.byteAt ((uns address - found.base).toNat + offset)) := by
  simp only [memoryRead, located, readable, ↓reduceIte]

/-- The first, read-only `PT_LOAD`, which holds the program-header table. -/
def firstSegment : Segment := segment file ⟨1, 4, 0, 0x400000, 0x400000, 0x190, 0x190, 0x1000⟩

theorem phdrs_readable : imagePhdrsReadable snapshot.image.segments snapshot.image.phdrs = true := by
  have readable : firstSegment.readable = true := by
    simp [firstSegment, segment, Segment.readable, permissions]
  have located : findSegment snapshot.image.segments (uns (zw snapshot.image.phdrs.addr))
      (snapshot.image.phdrs.num * snapshot.image.phdrs.ent) = some firstSegment := by
    decide +kernel
  unfold imagePhdrsReadable
  rw [memoryRead_of_found located readable]
  decide +kernel

theorem imageWf (platform : Silmaril.X86.Ext.Wire.Platform) :
    ImageWf (x86WireDf0RepStosq platform) snapshot.image :=
  ⟨entry_fetchable platform, phdrs_readable, by decide +kernel⟩

/-- The checked ELF64 loader accepts the exact pinned bytes. -/
theorem loaded (platform : Silmaril.X86.Ext.Wire.Platform) :
    loadX86 (x86WireDf0RepStosq platform) file = some snapshot := by
  rw [loadX86, parsed]
  change (if ImageWf (x86WireDf0RepStosq platform) snapshot.image then some snapshot
    else none) = _
  rw [ite_eq_left (imageWf platform)]

/-- The flag-oracle wrapper uses the same entry check, so loading agrees. -/
theorem loaded_oracle (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) :
    loadX86 (x86WireDf0RepStosqWithFlagOracle platform oracle) file = some snapshot := by
  rw [loadX86, parsed]
  change (if ImageWf (x86WireDf0RepStosqWithFlagOracle platform oracle) snapshot.image then
    some snapshot else none) = _
  rw [ite_eq_left (show ImageWf (x86WireDf0RepStosqWithFlagOracle platform oracle) snapshot.image
    from imageWf platform)]

/-! ## A guarded launch matching the QEMU run's argv and environment -/

/-- argv `["checksum"]`, empty environment and the shared minimal x86 profile. -/
def input : ProcInput where
  argv := [[99, 104, 101, 99, 107, 115, 117, 109]]
  envp := []
  imageFs := []
  stdin := InputStream.eof
  uid := 1000
  gid := 100
  groups := []
  net := netSilent
  nofile := 1024
  sigmask := 0
  hwcap := 0
  abortTerminal := false
  vaSize := .sv48
  urandom := InputStream.defaultUrandom
  tmp := []

/-- One concrete launch choice: page-aligned break just above `.bss`. -/
def entry : ExecEntry :=
  ⟨0x7fffffffe000, 0x405000, 0x40000000, ⟨0, fun _ => 0⟩⟩

theorem input_valid : X86Launch.ValidInput input := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [ValidArgv, input, totalArgBytes, pathHasSlash]
    · simp [ValidEnvp, input, totalArgBytes]
    · simp [input, ProcInput.fs, fsSeedTmp, Fs.ValidFs, Fs.sorted]
    · simp [input, Fs.KeysRelative]
    · unfold ValidCreds ValidId
      decide +kernel
    · unfold ValidNofile
      decide +kernel
    · unfold ValidSigmask
      decide +kernel
    · intro n
      rfl
  · rfl

theorem entry_valid (platform : Silmaril.X86.Ext.Wire.Platform) :
    X86Launch.ValidEntry (x86WireDf0RepStosq platform) snapshot entry input := by
  refine ⟨loadX86_validSnapshot (loaded platform), ?_⟩
  simp only [ValidBrk, entry]
  decide +kernel

theorem launch_nonempty (platform : Silmaril.X86.Ext.Wire.Platform) :
    ∃ configuration, X86Launch.Launched (x86WireDf0RepStosq platform) snapshot entry
      sourceAllocLimit input configuration :=
  (X86Launch.launch_exists_iff _ _ _ _ _).mpr ⟨input_valid, entry_valid platform⟩

theorem launch_nonempty_oracle (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) :
    ∃ configuration, X86Launch.Launched (x86WireDf0RepStosqWithFlagOracle platform oracle)
      snapshot entry sourceAllocLimit input configuration :=
  (X86Launch.launch_exists_iff _ _ _ _ _).mpr
    ⟨input_valid, loadX86_validSnapshot (loaded_oracle platform oracle), (entry_valid platform).2⟩

/-! ## The actual launch configuration -/

def initial (platform : Silmaril.X86.Ext.Wire.Platform) : Config (x86WireDf0RepStosq platform) :=
  X86Launch.init (x86WireDf0RepStosq platform) snapshot entry sourceAllocLimit input

theorem initial_rip (platform : Silmaril.X86.Ext.Wire.Platform) :
    (initial platform).ms.m.core.rip = 0x401062 := rfl

theorem initial_memory (platform : Silmaril.X86.Ext.Wire.Platform) :
    (initial platform).ms.m.memory =
      initialMemory snapshot.image.segments entry.sp (X86Launch.entryStack snapshot.image entry input) :=
  rfl

theorem stack_nowrap :
    entry.sp.toNat + (X86Launch.entryStack snapshot.image entry input).length ≤ 2 ^ 64 := by
  decide +kernel

/-- Image bytes below the 8 MiB stack reservation are the loaded segments'. -/
theorem initial_image_get (platform : Silmaril.X86.Ext.Wire.Platform) (address : Nat)
    (below : address < 0x7fffff7fe000) :
    (initial platform).ms.m.memory.bytes.get? address =
      segmentsView snapshot.image.segments address none := by
  rw [initial_memory, X86Launch.initialMemory_below_stack_get _ _ _ _ ?_ stack_nowrap,
    initialMemory_segments_get _ _ segments_nowrap]
  have lower : entry.sp.toNat - stackMaxSize.toNat = 0x7fffff7fe000 := by decide
  rw [lower]
  exact below

/-- The launch fetches `xor %rbp,%rbp` at its entry, from the real initialized
memory (with its symbolic stack reservation), not from a separate image. -/
theorem initial_entry_fetched (platform : Silmaril.X86.Ext.Wire.Platform) :
    (initial platform).ms.m.memory.fetchBytes 0x401062 3 = some entryBytes := by
  apply Silmaril.Process.Memory.readWith_eq _ .execute 0x401062 entryBytes
  · rw [initial_memory]
    exact permitted_of_regions (initialMemory_regions _ _) _ _ _ (by decide +kernel)
  · intro index bound
    rw [initial_image_get platform _ (by change index < 3 at bound; omega)]
    revert index
    decide +kernel

/-- `main`'s first instruction is executable in the same launch memory. -/
theorem initial_main_fetched (platform : Silmaril.X86.Ext.Wire.Platform) :
    (initial platform).ms.m.memory.fetchBytes mainAddress 4 = some mainBytes := by
  apply Silmaril.Process.Memory.readWith_eq _ .execute mainAddress mainBytes
  · rw [initial_memory]
    exact permitted_of_regions (initialMemory_regions _ _) _ _ _ (by decide +kernel)
  · intro index bound
    rw [initial_image_get platform _ (by change index < 4 at bound; change 0x401030 + index < _; omega)]
    revert index
    decide +kernel

/-! ## The first actual transition -/

/-- The entry instruction is not the SYSCALL spelling, so the flag oracle is
not consulted on the first step. -/
theorem initial_not_syscall (platform : Silmaril.X86.Ext.Wire.Platform) :
    (initial platform).ms.m.memory.fetchBytes
      (initial platform).ms.m.core.rip.toNat 2 ≠ some [0x0f, 0x05] := by
  have rip : (initial platform).ms.m.core.rip.toNat = 0x401062 := by
    rw [initial_rip]; rfl
  have three := initial_entry_fetched platform
  rw [← rip] at three
  have two : (initial platform).ms.m.memory.fetchBytes (initial platform).ms.m.core.rip.toNat 2 =
      some [0x48, 0x31] :=
    Silmaril.Process.Memory.readWith_sub_range three (offset := 0) (len := 2) (by decide) (by decide)
  rw [two]; decide

open Silmaril.X86 in
theorem first_machine_step (platform : Silmaril.X86.Ext.Wire.Platform) :
    ∃ next, X86RepStosq.step platform (initial platform).ms =
      .ok ⟨next, [((initial platform).ms.m.core.rip, 3)]⟩ ∧ next.m.core.rip = 0x401065 ∧
      next.m.memory = (initial platform).ms.m.memory ∧ next.pending = none := by
  have rip : (initial platform).ms.m.core.rip.toNat = 0x401062 := by
    rw [initial_rip]; rfl
  have three := initial_entry_fetched platform
  rw [← rip] at three
  have notRep : (initial platform).ms.m.memory.fetchBytes (initial platform).ms.m.core.rip.toNat 3 ≠
      some X86RepStosq.bytes := by
    rw [three]; decide
  have notSyscall := initial_not_syscall platform
  have fetched : Ext.Wire.fetch (initial platform).ms.m.memory (initial platform).ms.m.core.rip.toNat =
      .decoded entryDecoded :=
    Ext.Wire.fetch_eq_decoded_iff.mpr ⟨entryBytes, by rw [entryDecoded_length]; exact three, entry_decode⟩
  rw [X86RepStosq.step_eq_wire platform _ notRep]
  unfold x86WireStep
  rw [ite_eq_right notSyscall, fetched]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- The first actual LPS process transition of the launch: `xor %rbp,%rbp`
retires under any syscall specification and refusal filter. -/
theorem first_process_step (platform : Silmaril.X86.Ext.Wire.Platform)
    (spec : Sys SyscallEffect) (refused : RefusalFilter) :
    ∃ next : Config (x86WireDf0RepStosq platform),
      SStep snapshot.image.segments spec refused (initial platform) [] (.next next) ∧
        next.ms.m.core.rip = 0x401065 ∧ next.model = (initial platform).model := by
  obtain ⟨next, step, rip, -, -⟩ := first_machine_step platform
  exact ⟨⟨next, (initial platform).model⟩, SStep.instr rfl rfl
    (Progress.accountStep_of_noLazy _ _ _ _ rfl step), rip, rfl⟩

/-! ## The first transition under every flag oracle

The flag-oracle option consults its oracle only at SYSCALL, so the first step
is the same for every oracle and leaves the oracle counter at 0. -/

def initialOracle (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) :
    Config (x86WireDf0RepStosqWithFlagOracle platform oracle) :=
  X86Launch.init (x86WireDf0RepStosqWithFlagOracle platform oracle) snapshot entry
    sourceAllocLimit input

/-- The oracle launch wraps the deterministic launch state with counter 0. -/
theorem initialOracle_ms (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) :
    (initialOracle platform oracle).ms = ⟨(initial platform).ms, 0⟩ := rfl

/-- The first actual LPS process transition of the oracle launch, for every
oracle: `xor %rbp,%rbp` retires under any syscall specification and refusal
filter. -/
theorem first_process_step_oracle (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) (spec : Sys SyscallEffect) (refused : RefusalFilter) :
    ∃ next : Config (x86WireDf0RepStosqWithFlagOracle platform oracle),
      SStep snapshot.image.segments spec refused (initialOracle platform oracle) [] (.next next) ∧
        next.ms.native.m.core.rip = 0x401065 ∧ next.ms.counter = 0 ∧
        next.model = (initialOracle platform oracle).model := by
  obtain ⟨next, step, rip, -, -⟩ := first_machine_step platform
  have oracleStep : (x86WireDf0RepStosqWithFlagOracle platform oracle).step snapshot.image.segments
      (initialOracle platform oracle).ms =
        .ok ⟨⟨next, 0⟩, [((initial platform).ms.m.core.rip, 3)]⟩ := by
    rw [initialOracle_ms]
    change X86FlagOracle.stepUsing (X86RepStosq.step platform) oracle _ = _
    rw [X86FlagOracle.not_syscall (X86RepStosq.step platform) oracle ⟨(initial platform).ms, 0⟩
      (initial_not_syscall platform), step]
    rfl
  exact ⟨⟨⟨next, 0⟩, (initialOracle platform oracle).model⟩, SStep.instr rfl rfl
    (Progress.accountStep_of_noLazy _ _ _ _ rfl oracleStep), rip, rfl, rfl⟩

/-! ## Why the deterministic option cannot carry the QEMU path

By the disassembly, `test %eax,%eax` at 0x401744 is the last flag writer
before the `set_tid_address` SYSCALL at 0x401768 (the intervening instructions
are `js`, `jne`, `movb`, `movl`, `mov` and `lea`). Logic operations leave AF
undefined (`logicFlags_undefined`); given that, `syscall_unmodeled_of_adjust`
makes the deterministic Wire+REP option `unmodeled` at that SYSCALL. The
path-level fact (the launch reaches 0x401768 with AF undefined) is not proved
here. On that reading, reaching `main` needs the flag-oracle option. -/

theorem rflagsImage_adjust_none (flags : Silmaril.X86.Flags) (undefined : flags.adjust = none) :
    rflagsImage flags = none := by
  simp [rflagsImage, undefined]

theorem logicFlags_undefined {n : Nat} (result : BitVec n) :
    rflagsImage (Silmaril.X86.Ext.logicFlagsN result) = none :=
  rflagsImage_adjust_none _ rfl

/-- A fetched SYSCALL with undefined AF is a model gap for Wire+REP STOSQ. -/
theorem syscall_unmodeled_of_adjust (platform : Silmaril.X86.Ext.Wire.Platform)
    (state : X86State)
    (fetched : state.m.memory.fetchBytes state.m.core.rip.toNat 2 = some [0x0f, 0x05])
    (undefined : state.m.core.flags.adjust = none) :
    X86RepStosq.step platform state = .unmodeled := by
  rw [X86RepStosq.step_eq_wire platform state (X86FlagOracle.syscall_not_rep state fetched)]
  unfold x86WireStep
  rw [ite_eq_left fetched, rflagsImage_adjust_none _ undefined]

end Silmaril.Process.LPS.Machines.X86MuslStartup
