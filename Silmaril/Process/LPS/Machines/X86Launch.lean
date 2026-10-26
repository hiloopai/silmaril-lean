module

public import Silmaril.Process.LPS.Run
public import Silmaril.Process.LPS.Machines.X86
public import Silmaril.Process.LPS.Machines.ProcessMemorySupport
public import Silmaril.Formats.ELF.Basic

/-! # An opt-in static x86-64 SysV launch for the direct LPS port

The original RISC-V stack and `runWith` are unchanged. This option supplies
the entry block to `runWithStack`, and therefore to the actual LPS `SStep`,
budget, refusal and observation semantics. The syscall specification and
refusal filter remain explicit parameters, including their native ABI policy.

Scope: fixed-address, static ELF64 executables, no interpreter, initial FS base
zero (no preinstalled TLS), RDX zero (no dynamic-loader finalizer). The minimal
advertisement has HWCAP/HWCAP2 zero and AT_SYSINFO_EHDR zero: no vDSO code is
advertised or silently assumed executable. The platform string is `x86_64`.
Additional CPU features, vDSO contents, TLS setup, ET_DYN relocation and a
dynamic loader need separate launch options and contracts.

`Snapshot` is an ELF-header/program-header and loaded-image boundary. Its
checks reject wrong machines and inconsistent layout records, but do not
prove that a parser extracted these records from particular ELF bytes. A
byte-to-snapshot binding remains a separate loader obligation.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Machines.X86Launch

def AT_BASE : Word := 7
def AT_FLAGS : Word := 8
def AT_ENTRY : Word := 9
def AT_GID : Word := 13
def AT_EGID : Word := 14
def AT_PLATFORM : Word := 15
def AT_CLKTCK : Word := 17
def AT_HWCAP2 : Word := 26
def AT_EXECFN : Word := 31
def AT_SYSINFO_EHDR : Word := 33

def platformBytes : List Byte := [120, 56, 54, 95, 54, 52, 0]
def auxiliaryCount : Nat := 20
def auxiliarySize : Nat := 16 * auxiliaryCount

def structureSize (argv envp : List (List Byte)) : Nat :=
  8 + (argv.length + 1) * 8 + (envp.length + 1) * 8 + auxiliarySize

def platformOffset (argv envp : List (List Byte)) : Nat :=
  structureSize argv envp + (flattenStrings argv).length + (flattenStrings envp).length

def beforeRandomSize (argv envp : List (List Byte)) : Nat :=
  platformOffset argv envp + platformBytes.length

def randomPadding (argv envp : List (List Byte)) : Nat :=
  (16 - beforeRandomSize argv envp % 16) % 16

def randomPtr (sp : Word) (argv envp : List (List Byte)) : Word :=
  sp + natToWord (beforeRandomSize argv envp + randomPadding argv envp)

/-- The 20 conventional entries used by this minimal static profile. GID and
EGID retain the input's distinct group identity, and all optional hardware and
vDSO advertisements are zero. AT_EXECFN points at the NUL-terminated argv[0]. -/
def auxiliaryEntries (img : Image) (sp : Word) (inp : ProcInput) : List (Word × Word) :=
  [ (AT_PHDR, zw img.phdrs.addr), (AT_PHENT, zw img.phdrs.ent), (AT_PHNUM, zw img.phdrs.num),
    (AT_PAGESZ, 4096), (AT_BASE, 0), (AT_FLAGS, 0), (AT_ENTRY, natToWord img.initPc),
    (AT_UID, inp.uid), (AT_EUID, inp.uid), (AT_GID, inp.gid), (AT_EGID, inp.gid),
    (AT_PLATFORM, sp + natToWord (platformOffset inp.argv inp.envp)), (AT_HWCAP, inp.hwcap),
    (AT_CLKTCK, 100), (AT_SECURE, 0), (AT_RANDOM, randomPtr sp inp.argv inp.envp),
    (AT_HWCAP2, 0), (AT_EXECFN, sp + natToWord (structureSize inp.argv inp.envp)),
    (AT_SYSINFO_EHDR, 0), (AT_NULL, 0) ]

theorem auxiliaryEntries_length (img : Image) (sp : Word) (inp : ProcInput) :
    (auxiliaryEntries img sp inp).length = auxiliaryCount := rfl

theorem no_vdso_advertised (img : Image) (sp : Word) (inp : ProcInput) :
    (AT_SYSINFO_EHDR, 0) ∈ auxiliaryEntries img sp inp := by
  simp [auxiliaryEntries]

theorem no_hwcap2_advertised (img : Image) (sp : Word) (inp : ProcInput) :
    (AT_HWCAP2, 0) ∈ auxiliaryEntries img sp inp := by
  simp [auxiliaryEntries]

def stackBytes (img : Image) (en : ExecEntry) (inp : ProcInput) : List Byte :=
  let stringBase := en.sp + natToWord (structureSize inp.argv inp.envp)
  let a := stringAddrs stringBase inp.argv
  let e := stringAddrs a.2 inp.envp
  wordLe8 (lenWord inp.argv) ++ a.1.flatMap wordLe8 ++ wordLe8 0 ++
    e.1.flatMap wordLe8 ++ wordLe8 0 ++ buildAuxv (auxiliaryEntries img en.sp inp) ++
    flattenStrings inp.argv ++ flattenStrings inp.envp ++ platformBytes ++
    List.replicate (randomPadding inp.argv inp.envp) 0 ++ atRandomBytes en.draw.random

/-- As in LPS's existing launch, the drawn slack fills the remainder of the
last entry-block page. The ISA initializer separately installs the 8 MiB stack. -/
def entryStack : EntryStackBuilder := fun img en inp =>
  let bytes := stackBytes img en inp
  bytes ++ entrySlack en.sp bytes en.draw.slack

structure Snapshot where
  header : Silmaril.Formats.ELF.Header
  programHeaders : List Silmaril.Formats.ELF.ProgramHeader
  image : Image

/-- Fixed-address ET_EXEC, SysV/Linux ABI, ELF64 record sizes, no interpreter,
and matching entry/program-header facts. Endianness/class are the ELF64 reader's
separate byte-to-AST obligations, since Header does not retain e_ident. -/
def HeaderMatches (snapshot : Snapshot) : Prop :=
  snapshot.header.machine = 62 ∧ snapshot.header.fileType = 2 ∧ snapshot.header.version = 1 ∧
    (snapshot.header.osABI = 0 ∨ snapshot.header.osABI = 3) ∧ snapshot.header.abiVersion = 0 ∧
    snapshot.header.flags = 0 ∧ snapshot.header.headerSize = 64 ∧
    snapshot.header.programEntrySize = 56 ∧ snapshot.header.programCount > 0 ∧
    snapshot.header.programCount = snapshot.programHeaders.length ∧
    snapshot.header.entry = snapshot.image.initPc ∧
    snapshot.image.phdrs.ent = 56 ∧ snapshot.image.phdrs.num = snapshot.header.programCount ∧
    ∀ ph ∈ snapshot.programHeaders, ph.kind ≠ 3

def ProgramHeaderMatches (ph : Silmaril.Formats.ELF.ProgramHeader) (segment : Segment) : Prop :=
  ph.kind = 1 ∧ ph.virtualAddress = segment.base ∧ ph.memorySize = segment.size ∧
    ph.fileSize ≤ ph.memorySize ∧
    (ph.flags % 2 = 1 ↔ segment.executable = true) ∧
    (ph.flags / 2 % 2 = 1 ↔ segment.writable = true) ∧
    (ph.flags / 4 % 2 = 1 ↔ segment.readable = true)

/-- PT_LOAD records and loaded segments cover each other. The byte-loading,
BSS zeroing and program-header-table contents are separate extraction facts. -/
def LoadLayoutMatches (snapshot : Snapshot) : Prop :=
  (∀ segment ∈ snapshot.image.segments,
    ∃ ph ∈ snapshot.programHeaders, ProgramHeaderMatches ph segment) ∧
  (∀ ph ∈ snapshot.programHeaders, ph.kind = 1 →
    ∃ segment ∈ snapshot.image.segments, ProgramHeaderMatches ph segment)

def ValidSnapshot (isa : UserIsa) (snapshot : Snapshot) : Prop :=
  HeaderMatches snapshot ∧ LoadLayoutMatches snapshot ∧
    (∀ segment ∈ snapshot.image.segments,
      segment.bytes.length = segment.size ∧ 0 < segment.size ∧
        (segment.base : Int) + segment.size ≤ x86AddressSpace.taskSize) ∧
    snapshot.image.segments.Pairwise (fun first second =>
      first.base + first.size ≤ second.base ∨ second.base + second.size ≤ first.base) ∧
    isa.entryFetchable snapshot.image.segments snapshot.image.initPc = true ∧
    (memoryRead snapshot.image.segments (zw snapshot.image.phdrs.addr)
      (snapshot.image.phdrs.num * snapshot.image.phdrs.ent)).isSome = true

/-- The shared LPS data validity checks, with the minimal x86 feature scope.
vaSize is not reinterpreted as an x86 feature advertisement: the ISA carries
the x86 address-space profile independently. -/
def ValidInput (inp : ProcInput) : Prop := ValidInputCore inp ∧ inp.hwcap = 0

/-- An explicit launch envelope inside the fixed four-level x86 user space.
Images stay below the entire stack reservation. The stack, brk and mmap-base
windows contain every placement of Linux x86-64 v6.13-v6.18 ASLR, for every
`randomize_va_space` (`X86LaunchAslr.linuxEntry_valid`); the entry-block fit and
image placement are separate premises. -/
def ValidEntry (isa : UserIsa) (snapshot : Snapshot) (en : ExecEntry) (inp : ProcInput) : Prop :=
  ValidSnapshot isa snapshot ∧
    x86LaunchBounds.spWindowLo ≤ uns en.sp ∧ uns en.sp ≤ x86LaunchBounds.spWindowHi ∧
    uns en.sp % 16 = 0 ∧
    ValidBrk snapshot.image.segments en.brk ∧
    x86LaunchBounds.mmapBaseMin ≤ uns en.mmapBase ∧
    uns en.mmapBase ≤ x86LaunchBounds.mmapBaseMax ∧ uns en.mmapBase % pageSize = 0 ∧
    entryPageTop en.sp (stackBytes snapshot.image en inp) ≤ x86AddressSpace.taskSize ∧
    (∀ segment ∈ snapshot.image.segments,
      (segment.base : Int) + segment.size ≤ uns en.sp - stackMaxSize)

def init (isa : UserIsa) (snapshot : Snapshot) (en : ExecEntry) (limit : Int) (inp : ProcInput) :
    Config isa := initConfigWithStack isa entryStack snapshot.image en limit inp

/-- A symbolic projection avoids evaluating the eager 8 MiB backing map when
reasoning about a concrete launch's memory. -/
theorem init_native_memory (snapshot : Snapshot) (en : ExecEntry) (limit : Int) (inp : ProcInput) :
    (init x86ExtNative snapshot en limit inp).ms.m.memory =
      initialMemory snapshot.image.segments en.sp (entryStack snapshot.image en inp) := rfl

/-- The loader's eager stack backing does not overwrite lower image bytes.
The proof uses installer frame rules, rather than constructing an 8 MiB map.
This statement is independent of the instruction set and stack format. -/
theorem initialMemory_below_stack_get (segments : List Segment) (sp : Word)
    (stack : List Byte) (address : Nat) (below : address < sp.toNat - stackMaxSize.toNat)
    (nowrap : sp.toNat + stack.length ≤ 2 ^ 64) :
    (initialMemory segments sp stack).bytes.get? address =
      (initialMemory segments 0 []).bytes.get? address := by
  let low := sp.toNat - stackMaxSize.toNat
  change (installWrapping
    (installWrapping (segments.foldl (fun acc segment => installWrapping acc segment.base segment.bytes) ∅)
      low (List.replicate (sp.toNat - low) 0)) sp.toNat stack).get? address = _
  rw [installWrapping_outside _ _ _ _ nowrap (Or.inl (by omega))]
  rw [installWrapping_outside _ _ _ _ ?_ (Or.inl below)]
  · rfl
  · simp only [List.length_replicate]
    have bounded := sp.isLt
    dsimp [low]
    omega

/-- The actual LPS transition semantics initialized with this stack and the
chosen ISA profile. Native syscall dispatch/refusals are explicit arguments. -/
def runWith (isa : UserIsa) (spec : Sys SyscallEffect) (refused : RefusalFilter)
    (snapshot : Snapshot) (limit : Int) (en : ExecEntry) (inp : ProcInput) : Behavior :=
  runWithStack isa entryStack spec refused snapshot.image limit en inp

/-- A guarded launch cannot make a false safety claim by silently treating an
invalid ELF/header/entry as a process with no executions. -/
def Launched (isa : UserIsa) (snapshot : Snapshot) (en : ExecEntry) (limit : Int)
    (inp : ProcInput) (configuration : Config isa) : Prop :=
  ValidInput inp ∧ ValidEntry isa snapshot en inp ∧ configuration = init isa snapshot en limit inp

theorem launch_exists_iff (isa : UserIsa) (snapshot : Snapshot) (en : ExecEntry)
    (limit : Int) (inp : ProcInput) :
    (∃ configuration, Launched isa snapshot en limit inp configuration) ↔
      ValidInput inp ∧ ValidEntry isa snapshot en inp := by
  constructor
  · rintro ⟨_, validInput, validEntry, _⟩
    exact ⟨validInput, validEntry⟩
  · rintro ⟨validInput, validEntry⟩
    exact ⟨_, validInput, validEntry, rfl⟩

theorem wrong_machine_no_launch (isa : UserIsa) (snapshot : Snapshot) (en : ExecEntry)
    (limit : Int) (inp : ProcInput) (wrong : snapshot.header.machine ≠ 62) :
    ¬ ∃ configuration, Launched isa snapshot en limit inp configuration := by
  rintro ⟨_, _, valid, _⟩
  exact wrong valid.1.1.1

theorem misaligned_stack_no_launch (isa : UserIsa) (snapshot : Snapshot) (en : ExecEntry)
    (limit : Int) (inp : ProcInput) (misaligned : uns en.sp % 16 ≠ 0) :
    ¬ ∃ configuration, Launched isa snapshot en limit inp configuration := by
  rintro ⟨_, _, valid, _⟩
  exact misaligned valid.2.2.2.1

theorem runWith_empty_trace (isa : UserIsa) (spec : Sys SyscallEffect) (refused : RefusalFilter)
    (snapshot : Snapshot) (limit : Int) (en : ExecEntry) (inp : ProcInput) :
    (runWith isa spec refused snapshot limit en inp).traces [] :=
  ⟨[], init isa snapshot en limit inp, .refl _, ⟨[], rfl⟩⟩

/-- Without lazy reservations, reporting instruction accesses does not alter
or charge the process model. This is independent of instruction architecture. -/
theorem materializeModelAccesses_no_lazy (model : Model) (accesses : List (Word × Nat))
    (empty : model.vmLazy = []) :
    materializeModelAccesses model accesses = some model := by
  simp only [materializeModelAccesses, materializeAccesses, newlyMaterializedPages,
    empty, pageInRanges, List.any_nil, Bool.false_and, List.filter_false, Option.map_some]
  rw [← empty]
  rfl

end Silmaril.Process.LPS.Machines.X86Launch
