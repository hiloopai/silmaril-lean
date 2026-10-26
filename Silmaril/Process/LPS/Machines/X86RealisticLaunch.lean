module

public import Silmaril.Process.LPS.Machines.X86Launch

/-! # A realistic static x86-64 launch: the Linux `create_elf_tables` domain

`X86Launch` is a minimal launch: a fixed 20-entry auxiliary vector with
`AT_HWCAP2 = 0` and `AT_SYSINFO_EHDR = 0`, no `AT_MINSIGSTKSZ` and no rseq
entries, laid out in its own order (strings directly after the auxiliary
vector, then the platform string and `AT_RANDOM`). This file adds a second
launch variant, kept beside the old one, whose domain is the set of initial
stacks Linux x86-64 builds for a static ELF64 `ET_EXEC` (`fs/binfmt_elf.c`
`load_elf_binary`, `setup_arg_pages`, `create_elf_tables`; the auxiliary
vector code is unchanged from v6.3 through v6.18).

The auxiliary vector, in kernel order: `ARCH_DLINFO` (`AT_SYSINFO_EHDR` when a
vDSO is mapped, then `AT_MINSIGSTKSZ`), `AT_HWCAP`, `AT_PAGESZ`, `AT_CLKTCK`,
`AT_PHDR`, `AT_PHENT`, `AT_PHNUM`, `AT_BASE` (0, no interpreter), `AT_FLAGS`,
`AT_ENTRY`, `AT_UID`, `AT_EUID`, `AT_GID`, `AT_EGID`, `AT_SECURE`,
`AT_RANDOM`, `AT_HWCAP2`, `AT_EXECFN`, `AT_PLATFORM`, then
`AT_RSEQ_FEATURE_SIZE` and `AT_RSEQ_ALIGN` under `CONFIG_RSEQ`, then `AT_NULL`.

The stack, in ascending addresses from the entry RSP: `argc`, the argv
pointers and NULL, the envp pointers and NULL, the auxiliary vector, zero
padding (`STACK_ROUND`), the sixteen `AT_RANDOM` bytes, the `"x86_64"`
platform string, the zero gap left by `arch_align_stack` (random below 8 KiB,
then 16-byte rounding), the argv strings, the envp strings, the `execve`
filename (`AT_EXECFN`), and the eight zero bytes `bprm_mm_init` reserves under
the page-aligned, randomized stack top.

Quantified (`Choices`): the vDSO (absent, or present at a page-aligned
address), the legacy vsyscall page (absent or present), `AT_MINSIGSTKSZ` (a
multiple of 16 in a range that covers every XSAVE layout), `AT_HWCAP`
(CPUID.1:EDX, the input's `hwcap`, 32 bits) and `AT_HWCAP2` (`RING3MWAIT`,
`FSGSBASE`), the effective ids (the real ids, or set-id with `AT_SECURE = 1`),
`AT_SECURE`, the rseq entries, the `execve` filename (below `MAX_ARG_STRLEN`),
the stack top within the `STACK_RND_MASK` window below `STACK_TOP`, and the
`arch_align_stack` gap. The `AT_RANDOM` bytes are the entry draw's.

Soundness split (`Exact`): the vDSO image (and its `vvar` data pages) and the
vsyscall page are not modelled, and LPS starts every process with
`euid = uid`, `egid = gid`. A launch with a vDSO, a vsyscall page or set-id
credentials therefore has the chaos behaviour (`chaos`: every trace, possibly
erroring, unmodelled) in `runWith`, and has no `Launched` configuration; only
an `Exact` launch runs the actual LPS transitions. Statements quantified over
`Launched` configurations are therefore about `Exact` launches only. This is
coarse but sound; a finer variant would map the vDSO and vsyscall pages with
quantified bytes and make execution inside them unmodelled.

Relation to the old variant (`X86Launch`): both run the same LPS transition
system through `runWithStack`, differing only in the stack builder and in the
domain. The old variant is a separate lattice point, not a corollary of this
one: no behavioural refinement relates them in either direction, and the old
`reaches_main` is not implied by anything here. What is proved: the old input
domain is exactly the `hwcap = 0` slice of the realistic one
(`validInput_old_iff`); the old scalar advertisements are the realistic ones at
`AT_HWCAP2 = AT_SECURE = 0` with real effective ids (`scalar_agreement`); the
old auxiliary vector is never a realistic one (`old_auxv_not_realistic`); and
a recorded real launch is in the realistic domain but in no old launch
(`X86RealisticLaunchRecorded`).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Machines.X86RealisticLaunch

open X86Launch

def AT_RSEQ_FEATURE_SIZE : Word := 27
def AT_RSEQ_ALIGN : Word := 28
def AT_MINSIGSTKSZ : Word := 51

/-- The kernel's and the environment's choices at `execve` that `ExecEntry`
does not already carry. `alignedTop` is `arch_align_stack(bprm->p)`: the
16-byte aligned address just above the platform string. -/
structure Choices where
  vdso : Option Word
  minSigStkSz : Word
  hwcap2 : Word
  euid : Word
  egid : Word
  secure : Word
  rseq : Option (Word × Word)
  execfn : List Byte
  stackTop : Word
  alignedTop : Word
  /-- Whether the legacy vsyscall page at `0xffffffffff600000` is present
  (`vsyscall=xonly` or `emulate`); it is not in the auxiliary vector. -/
  vsyscall : Bool
  deriving DecidableEq

/-- The string area at the top of the stack: argv and envp strings, the
`execve` filename and the eight reserved zero bytes. -/
def stringArea (c : Choices) (inp : ProcInput) : List Byte :=
  flattenStrings inp.argv ++ flattenStrings inp.envp ++ flattenStrings [c.execfn] ++
    List.replicate 8 0

def stringBase (c : Choices) (inp : ProcInput) : Word :=
  c.stackTop - natToWord (stringArea c inp).length

def execfnPtr (c : Choices) : Word := c.stackTop - natToWord (c.execfn.length + 9)

def platformPtr (c : Choices) : Word := c.alignedTop - 7

def randomPtr (c : Choices) : Word := c.alignedTop - 23

/-- The auxiliary vector, in `create_elf_tables` order for x86-64. -/
def auxiliaryEntries (img : Image) (c : Choices) (inp : ProcInput) : List (Word × Word) :=
  (match c.vdso with | some address => [(AT_SYSINFO_EHDR, address)] | none => []) ++
  [ (AT_MINSIGSTKSZ, c.minSigStkSz), (AT_HWCAP, inp.hwcap), (AT_PAGESZ, 4096), (AT_CLKTCK, 100),
    (AT_PHDR, zw img.phdrs.addr), (AT_PHENT, zw img.phdrs.ent), (AT_PHNUM, zw img.phdrs.num),
    (AT_BASE, 0), (AT_FLAGS, 0), (AT_ENTRY, natToWord img.initPc),
    (AT_UID, inp.uid), (AT_EUID, c.euid), (AT_GID, inp.gid), (AT_EGID, c.egid),
    (AT_SECURE, c.secure), (AT_RANDOM, randomPtr c), (AT_HWCAP2, c.hwcap2),
    (AT_EXECFN, execfnPtr c), (AT_PLATFORM, platformPtr c) ] ++
  (match c.rseq with
    | some (size, align) => [(AT_RSEQ_FEATURE_SIZE, size), (AT_RSEQ_ALIGN, align)]
    | none => []) ++
  [(AT_NULL, 0)]

/-- Words below `AT_RANDOM`: auxiliary vector, argc, argv, envp and NULLs. -/
def tableWords (img : Image) (c : Choices) (inp : ProcInput) : Nat :=
  2 * (auxiliaryEntries img c inp).length + inp.argv.length + inp.envp.length + 3

def alignDown16 (w : Word) : Word := w &&& ~~~(15 : Word)

/-- `STACK_ROUND(sp, items)`: the entry RSP. -/
def entrySp (img : Image) (c : Choices) (inp : ProcInput) : Word :=
  alignDown16 (randomPtr c - natToWord (8 * tableWords img c inp))

/-- The bytes from the entry RSP to the stack top. -/
def stackBytes (img : Image) (c : Choices) (sp : Word) (random : BitVec 128) (inp : ProcInput) :
    List Byte :=
  let a := stringAddrs (stringBase c inp) inp.argv
  let e := stringAddrs a.2 inp.envp
  let table := wordLe8 (lenWord inp.argv) ++ a.1.flatMap wordLe8 ++ wordLe8 0 ++
    e.1.flatMap wordLe8 ++ wordLe8 0 ++ buildAuxv (auxiliaryEntries img c inp)
  table ++ List.replicate ((uns (randomPtr c) - uns sp).toNat - table.length) 0 ++
    atRandomBytes random ++ platformBytes ++
    List.replicate ((uns (stringBase c inp) - uns c.alignedTop).toNat) 0 ++ stringArea c inp

/-- The entry stack builder for one choice. When the block ends at the
page-aligned stack top, as in every valid launch, the slack is empty. -/
def entryStack (c : Choices) : EntryStackBuilder := fun img en inp =>
  let bytes := stackBytes img c en.sp en.draw.random inp
  bytes ++ entrySlack en.sp bytes en.draw.slack

/-! ## The domain -/

/-- `AT_HWCAP` is CPUID.1:EDX; `AT_HWCAP2` has two defined bits on x86;
`AT_MINSIGSTKSZ` is `get_sigframe_size()`, rounded to `FRAME_ALIGNMENT`,
between the legacy FXSAVE frame and a frame with every XSAVE component. -/
def ValidFeatures (inp : ProcInput) (c : Choices) : Prop :=
  uns inp.hwcap < 2 ^ 32 ∧ uns c.hwcap2 < 4 ∧
    512 ≤ uns c.minSigStkSz ∧ uns c.minSigStkSz ≤ 0x10000 ∧ uns c.minSigStkSz % 16 = 0

def ValidVdso : Option Word → Prop
  | none => True
  | some address =>
    uns address % pageSize = 0 ∧ 0 < uns address ∧ uns address < x86AddressSpace.taskSize

/-- `offsetof(struct rseq, end)` is at least the original 20 bytes. The
alignment is a power of two of at least 32: 32 through v6.18, and kernels that
tie it to the feature size may raise it. -/
def ValidRseq : Option (Word × Word) → Prop
  | none => True
  | some (size, align) =>
    20 ≤ uns size ∧ uns size ≤ 4096 ∧ 32 ≤ uns align ∧ align &&& (align - 1) = 0

instance (vdso : Option Word) : Decidable (ValidVdso vdso) := by
  cases vdso <;> unfold ValidVdso <;> infer_instance

instance (rseq : Option (Word × Word)) : Decidable (ValidRseq rseq) := by
  rcases rseq with _ | ⟨size, align⟩ <;> unfold ValidRseq <;> infer_instance

/-- `STACK_RND_MASK + 1` pages for 64-bit tasks. -/
def stackTopRandomPages : Int := 0x400000

/-- `STACK_TOP` for 64-bit tasks: `TASK_SIZE_LOW`, one page below 2^47. The
LPS x86 `taskSize` is already that value (`0x7ffffffff000`), so the stack top
is bounded by `STACK_TOP`, not by 2^47. -/
def stackTopMax : Int := x86AddressSpace.taskSize

theorem stackTopMax_eq : stackTopMax = 2 ^ 47 - pageSize := by decide

/-- `MAX_ARG_STRLEN`: `copy_string_kernel` bounds the `execve` filename,
terminating NUL included. `execveat` names (`/dev/fd/N/<path>`) can exceed
`PATH_MAX`, so `PATH_MAX` is not a bound. -/
def maxArgStrlen : Nat := 32 * 4096

/-- Effective ids: either the real ids, or a set-id launch, which the kernel
always marks `AT_SECURE`. -/
def ValidCreds (inp : ProcInput) (c : Choices) : Prop :=
  ValidId c.euid ∧ ValidId c.egid ∧ ((c.euid = inp.uid ∧ c.egid = inp.gid) ∨ c.secure = 1)

def ValidChoices (inp : ProcInput) (c : Choices) : Prop :=
  ValidVdso c.vdso ∧ ValidRseq c.rseq ∧ uns c.secure ≤ 1 ∧ ValidFeatures inp c ∧
    ValidCreds inp c ∧
    0 < c.execfn.length ∧ c.execfn.length < maxArgStrlen ∧ (0 : Byte) ∉ c.execfn ∧
    uns c.stackTop % pageSize = 0 ∧
    stackTopMax - stackTopRandomPages * pageSize ≤ uns c.stackTop ∧
    uns c.stackTop ≤ stackTopMax ∧
    ((stringArea c inp).length : Int) < uns c.stackTop ∧
    uns c.alignedTop % 16 = 0 ∧ uns (stringBase c inp) - 8206 ≤ uns c.alignedTop ∧
    uns c.alignedTop ≤ uns (stringBase c inp)

def ValidInput (inp : ProcInput) : Prop := ValidInputCore inp ∧ uns inp.hwcap < 2 ^ 32

def ValidEntry (isa : UserIsa) (snapshot : Snapshot) (c : Choices) (en : ExecEntry)
    (inp : ProcInput) : Prop :=
  ValidSnapshot isa snapshot ∧ ValidChoices inp c ∧
    en.sp = entrySp snapshot.image c inp ∧
    uns en.sp + 8 * tableWords snapshot.image c inp ≤ uns (randomPtr c) ∧
    23 + 8 * (tableWords snapshot.image c inp : Int) < uns c.alignedTop ∧
    ValidBrk snapshot.image.segments en.brk ∧
    x86LaunchBounds.mmapBaseMin ≤ uns en.mmapBase ∧
    uns en.mmapBase ≤ x86LaunchBounds.mmapBaseMax ∧ uns en.mmapBase % pageSize = 0 ∧
    entryPageTop en.sp (stackBytes snapshot.image c en.sp en.draw.random inp) ≤
      x86AddressSpace.taskSize ∧
    (∀ segment ∈ snapshot.image.segments,
      (segment.base : Int) + segment.size ≤ uns en.sp - stackMaxSize)

/-- The point of the realistic domain that the LPS transition system models
exactly: no vDSO and no vsyscall page (whose code is not modelled), and the
effective ids equal the real ids (LPS starts with `euid = uid`, `egid = gid`).
Everywhere else the realistic behaviour is `chaos`. -/
def Exact (inp : ProcInput) (c : Choices) : Prop :=
  c.vdso = none ∧ c.vsyscall = false ∧ c.euid = inp.uid ∧ c.egid = inp.gid

instance (inp : ProcInput) (c : Choices) : Decidable (Exact inp c) := by
  unfold Exact; infer_instance

/-- The LPS configuration built from the realistic stack. It is a faithful
initial state only at an `Exact` point: elsewhere the stack advertises a vDSO,
a vsyscall page or set-id credentials that the configuration does not model.
Use it through `Launched` or `runWith`, which carry that split. -/
def init (isa : UserIsa) (snapshot : Snapshot) (c : Choices) (en : ExecEntry) (limit : Int)
    (inp : ProcInput) : Config isa :=
  initConfigWithStack isa (entryStack c) snapshot.image en limit inp

/-- Everything is possible: the top of the behaviour order. -/
def chaos : Behavior := ⟨fun _ => True, True, False, True⟩

/-- The realistic run. At an `Exact` point it is the actual LPS semantics from
the realistic stack; with a vDSO or vsyscall page, whose code is not modelled,
or with set-id credentials, which LPS does not start with, it is `chaos`. -/
def runWith (isa : UserIsa) (spec : Sys SyscallEffect) (refused : RefusalFilter)
    (snapshot : Snapshot) (limit : Int) (c : Choices) (en : ExecEntry) (inp : ProcInput) :
    Behavior :=
  if Exact inp c then runWithStack isa (entryStack c) spec refused snapshot.image limit en inp
  else chaos

theorem runWith_exact (isa : UserIsa) (spec : Sys SyscallEffect) (refused : RefusalFilter)
    (snapshot : Snapshot) (limit : Int) (c : Choices) (en : ExecEntry) (inp : ProcInput)
    (exact : Exact inp c) :
    runWith isa spec refused snapshot limit c en inp =
      runWithStack isa (entryStack c) spec refused snapshot.image limit en inp := by
  simp [runWith, exact]

theorem runWith_not_exact (isa : UserIsa) (spec : Sys SyscallEffect) (refused : RefusalFilter)
    (snapshot : Snapshot) (limit : Int) (c : Choices) (en : ExecEntry) (inp : ProcInput)
    (inexact : ¬ Exact inp c) : runWith isa spec refused snapshot limit c en inp = chaos := by
  simp [runWith, inexact]

theorem runWith_vdso_unmodeled (isa : UserIsa) (spec : Sys SyscallEffect)
    (refused : RefusalFilter) (snapshot : Snapshot) (limit : Int) (c : Choices) (en : ExecEntry)
    (inp : ProcInput) (address : Word) (present : c.vdso = some address) :
    (runWith isa spec refused snapshot limit c en inp).unmodeled ∧
      ∀ trace, (runWith isa spec refused snapshot limit c en inp).traces trace := by
  rw [runWith_not_exact _ _ _ _ _ _ _ _ (by simp [Exact, present])]
  simp [chaos]

theorem runWith_vsyscall_unmodeled (isa : UserIsa) (spec : Sys SyscallEffect)
    (refused : RefusalFilter) (snapshot : Snapshot) (limit : Int) (c : Choices) (en : ExecEntry)
    (inp : ProcInput) (present : c.vsyscall = true) :
    (runWith isa spec refused snapshot limit c en inp).unmodeled ∧
      ∀ trace, (runWith isa spec refused snapshot limit c en inp).traces trace := by
  rw [runWith_not_exact _ _ _ _ _ _ _ _ (by simp [Exact, present])]
  simp [chaos]

/-- Every behaviour is below chaos. -/
theorem le_chaos (behaviour : Behavior) :
    (∀ trace, behaviour.traces trace → chaos.traces trace) ∧ (behaviour.errors → chaos.errors) ∧
      (chaos.allErrors → behaviour.allErrors) ∧ (behaviour.unmodeled → chaos.unmodeled) :=
  ⟨fun _ _ => trivial, fun _ => trivial, False.elim, fun _ => trivial⟩

/-- A realistic launch that is in the whole domain (`ValidInput`,
`ValidEntry`), including vDSO, vsyscall and set-id launches. Its behaviour is
`runWith`; there is no exact LPS configuration for it in general. -/
def InDomain (isa : UserIsa) (snapshot : Snapshot) (c : Choices) (en : ExecEntry)
    (inp : ProcInput) : Prop :=
  ValidInput inp ∧ ValidEntry isa snapshot c en inp

/-- The exactly modelled launches: an `Exact` point of the domain and its LPS
configuration. Statements quantified over `Launched` configurations (such as a
transferred `reaches_main` or a statement profile) are sound only for these
launches; the rest of the domain is covered by `runWith`, which is `chaos`
there. -/
def Launched (isa : UserIsa) (snapshot : Snapshot) (c : Choices) (en : ExecEntry) (limit : Int)
    (inp : ProcInput) (configuration : Config isa) : Prop :=
  InDomain isa snapshot c en inp ∧ Exact inp c ∧ configuration = init isa snapshot c en limit inp

theorem launch_exists_iff (isa : UserIsa) (snapshot : Snapshot) (c : Choices) (en : ExecEntry)
    (limit : Int) (inp : ProcInput) :
    (∃ configuration, Launched isa snapshot c en limit inp configuration) ↔
      ValidInput inp ∧ ValidEntry isa snapshot c en inp ∧ Exact inp c := by
  constructor
  · rintro ⟨_, ⟨validInput, validEntry⟩, exact, _⟩
    exact ⟨validInput, validEntry, exact⟩
  · rintro ⟨validInput, validEntry, exact⟩
    exact ⟨_, ⟨validInput, validEntry⟩, exact, rfl⟩

/-- A launch that is not `Exact` has no LPS configuration. -/
theorem not_exact_no_launch (isa : UserIsa) (snapshot : Snapshot) (c : Choices)
    (en : ExecEntry) (limit : Int) (inp : ProcInput) (inexact : ¬ Exact inp c) :
    ¬ ∃ configuration, Launched isa snapshot c en limit inp configuration := by
  rintro ⟨_, _, exact, _⟩
  exact inexact exact

/-- On `Launched` configurations `runWith` is the LPS run from them. -/
theorem launched_run (isa : UserIsa) (spec : Sys SyscallEffect) (refused : RefusalFilter)
    (snapshot : Snapshot) (limit : Int) (c : Choices) (en : ExecEntry) (inp : ProcInput)
    (configuration : Config isa) (launched : Launched isa snapshot c en limit inp configuration) :
    runWith isa spec refused snapshot limit c en inp =
      runWithStack isa (entryStack c) spec refused snapshot.image limit en inp :=
  runWith_exact _ _ _ _ _ _ _ _ launched.2.1

theorem misaligned_stack_no_launch (isa : UserIsa) (snapshot : Snapshot) (c : Choices)
    (en : ExecEntry) (limit : Int) (inp : ProcInput)
    (misaligned : en.sp ≠ entrySp snapshot.image c inp) :
    ¬ ∃ configuration, Launched isa snapshot c en limit inp configuration := by
  rintro ⟨_, ⟨_, valid⟩, _, _⟩
  exact misaligned valid.2.2.1

/-- The old launch's input domain is exactly the `hwcap = 0` slice of the
realistic one. This relates inputs only: the two variants' stacks are
disjoint (`old_auxv_not_realistic`) and no behavioural refinement is claimed. -/
theorem validInput_old_iff (inp : ProcInput) :
    X86Launch.ValidInput inp ↔ ValidInput inp ∧ inp.hwcap = 0 :=
  ⟨fun old => ⟨⟨old.1, by rw [old.2]; decide⟩, old.2⟩, fun ⟨valid, zero⟩ => ⟨valid.1, zero⟩⟩

theorem validInput_of_old (inp : ProcInput) (old : X86Launch.ValidInput inp) : ValidInput inp :=
  ((validInput_old_iff inp).mp old).1

/-! ## The realistic auxiliary vector -/

theorem minsigstksz_advertised (img : Image) (c : Choices) (inp : ProcInput) :
    (AT_MINSIGSTKSZ, c.minSigStkSz) ∈ auxiliaryEntries img c inp := by
  simp [auxiliaryEntries]

theorem hwcap2_advertised (img : Image) (c : Choices) (inp : ProcInput) :
    (AT_HWCAP2, c.hwcap2) ∈ auxiliaryEntries img c inp := by
  simp [auxiliaryEntries]

theorem vdso_advertised (img : Image) (c : Choices) (inp : ProcInput) (address : Word)
    (present : c.vdso = some address) :
    (AT_SYSINFO_EHDR, address) ∈ auxiliaryEntries img c inp := by
  simp [auxiliaryEntries, present]

theorem no_vdso_key (img : Image) (c : Choices) (inp : ProcInput) (absent : c.vdso = none) :
    AT_SYSINFO_EHDR ∉ (auxiliaryEntries img c inp).map Prod.fst := by
  cases rseq : c.rseq <;>
    simp [auxiliaryEntries, absent, rseq, AT_SYSINFO_EHDR, AT_MINSIGSTKSZ, AT_HWCAP, AT_PAGESZ,
      AT_CLKTCK, AT_PHDR, AT_PHENT, AT_PHNUM, AT_BASE, AT_FLAGS, AT_ENTRY, AT_UID, AT_EUID,
      AT_GID, AT_EGID, AT_SECURE, AT_RANDOM, AT_HWCAP2, AT_EXECFN, AT_PLATFORM,
      AT_RSEQ_FEATURE_SIZE, AT_RSEQ_ALIGN, AT_NULL]

theorem old_no_minsigstksz (img : Image) (sp : Word) (inp : ProcInput) :
    AT_MINSIGSTKSZ ∉ (X86Launch.auxiliaryEntries img sp inp).map Prod.fst := by
  simp [X86Launch.auxiliaryEntries, AT_SYSINFO_EHDR, AT_MINSIGSTKSZ, AT_HWCAP, AT_PAGESZ,
    AT_CLKTCK, AT_PHDR, AT_PHENT, AT_PHNUM, AT_BASE, AT_FLAGS, AT_ENTRY, AT_UID, AT_EUID,
    AT_GID, AT_EGID, AT_SECURE, AT_RANDOM, AT_HWCAP2, AT_EXECFN, AT_PLATFORM, AT_NULL]

/-- No old auxiliary vector is a realistic one: the old launch never
advertises `AT_MINSIGSTKSZ`, which Linux x86-64 always does. -/
theorem old_auxv_not_realistic (img img' : Image) (sp : Word) (inp inp' : ProcInput)
    (c : Choices) : X86Launch.auxiliaryEntries img sp inp ≠ auxiliaryEntries img' c inp' := by
  intro same
  apply old_no_minsigstksz img sp inp
  rw [same]
  exact List.mem_map_of_mem (f := Prod.fst) (minsigstksz_advertised img' c inp')

/-- The entries whose values do not depend on the stack layout or on the
realistic domain's extra choices, at `AT_HWCAP2 = AT_SECURE = 0` and real
effective ids. -/
def scalarEntries (img : Image) (inp : ProcInput) : List (Word × Word) :=
  [ (AT_PHDR, zw img.phdrs.addr), (AT_PHENT, zw img.phdrs.ent), (AT_PHNUM, zw img.phdrs.num),
    (AT_PAGESZ, 4096), (AT_BASE, 0), (AT_FLAGS, 0), (AT_ENTRY, natToWord img.initPc),
    (AT_UID, inp.uid), (AT_EUID, inp.uid), (AT_GID, inp.gid), (AT_EGID, inp.gid),
    (AT_HWCAP, inp.hwcap), (AT_CLKTCK, 100), (AT_SECURE, 0), (AT_HWCAP2, 0), (AT_NULL, 0) ]

/-- The precise relation of the two variants' advertisements: at the point
`AT_HWCAP2 = AT_SECURE = 0` the old and the realistic auxiliary vectors both
carry every scalar entry (the realistic one in kernel order). They differ in
the pointer entries (`AT_RANDOM`, `AT_EXECFN`, `AT_PLATFORM`, by layout), in
`AT_SYSINFO_EHDR` (old: an explicit 0; realistic: absent or the vDSO), and in
the realistic `AT_MINSIGSTKSZ` and rseq entries. -/
theorem scalar_agreement (img : Image) (sp : Word) (inp : ProcInput) (c : Choices)
    (hwcap2 : c.hwcap2 = 0) (secure : c.secure = 0) (euid : c.euid = inp.uid)
    (egid : c.egid = inp.gid) :
    ∀ entry ∈ scalarEntries img inp,
      entry ∈ X86Launch.auxiliaryEntries img sp inp ∧ entry ∈ auxiliaryEntries img c inp := by
  intro entry member
  simp only [scalarEntries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [X86Launch.auxiliaryEntries, auxiliaryEntries, hwcap2, secure, euid, egid]

/-! ## Telling the variants apart on recorded bytes -/

/-- Two byte strings agree on their common prefix. -/
def PrefixAgree (first second : List Byte) : Prop := first <+: second ∨ second <+: first

theorem prefixAgree_getElem? {first second : List Byte} (agree : PrefixAgree first second)
    (index : Nat) (inFirst : index < first.length) (inSecond : index < second.length) :
    first[index]? = second[index]? := by
  rcases agree with isPrefix | isPrefix
  · rw [List.getElem?_eq_getElem inFirst, List.getElem?_eq_getElem inSecond,
      isPrefix.getElem inFirst]
  · rw [List.getElem?_eq_getElem inFirst, List.getElem?_eq_getElem inSecond,
      isPrefix.getElem inSecond]

theorem wordLe8_length (value : Word) : (wordLe8 value).length = 8 := by simp [wordLe8]

theorem byte8_of (first second : Word) (rest : List Byte) :
    (wordLe8 first ++ (wordLe8 second ++ rest))[8]? = some (second.extractLsb' 0 8) := by
  rw [List.getElem?_append_right (by rw [wordLe8_length]), wordLe8_length, Nat.sub_self,
    List.getElem?_append_left (by rw [wordLe8_length]; decide)]
  simp [wordLe8]

theorem old_entryStack_long (img : Image) (en : ExecEntry) (inp : ProcInput) :
    8 < (X86Launch.entryStack img en inp).length := by
  unfold X86Launch.entryStack X86Launch.stackBytes
  simp only [List.length_append, wordLe8_length]
  omega

/-- Byte 8 of an old entry stack without arguments: the argv NULL. -/
theorem old_entryStack_byte8_nil (img : Image) (en : ExecEntry) (inp : ProcInput)
    (argv : inp.argv = []) :
    (X86Launch.entryStack img en inp)[8]? = some 0 := by
  unfold X86Launch.entryStack X86Launch.stackBytes
  rw [argv]
  simp only [stringAddrs, List.flatMap_nil, List.append_assoc, List.nil_append]
  exact byte8_of _ _ _

/-- Byte 8 of an old entry stack: the low byte of argv[0]'s pointer, which the
old layout places at an 8-byte aligned offset from RSP. -/
theorem old_entryStack_byte8_cons (img : Image) (en : ExecEntry) (inp : ProcInput)
    (first : List Byte) (rest : List (List Byte)) (argv : inp.argv = first :: rest) :
    (X86Launch.entryStack img en inp)[8]? =
      some ((en.sp + natToWord (structureSize inp.argv inp.envp)).extractLsb' 0 8) := by
  unfold X86Launch.entryStack X86Launch.stackBytes
  rw [argv]
  simp only [stringAddrs, List.flatMap_cons, List.append_assoc]
  exact byte8_of _ _ _

theorem natToWord_toNat (n : Nat) : (natToWord n).toNat = n % 2 ^ 64 := by
  simp [natToWord, zw]

/-- No old entry stack agrees with a byte string whose byte 8 is nonzero and
not congruent to RSP modulo 8. Linux packs the strings at the top of the
stack, unaligned, so argv[0]'s pointer is usually such a byte. -/
theorem old_excludes_unaligned_argv (img : Image) (en : ExecEntry) (inp : ProcInput)
    (recorded : List Byte) (byte : Byte) (at8 : recorded[8]? = some byte)
    (nonzero : byte ≠ 0) (unaligned : byte.toNat % 8 ≠ en.sp.toNat % 8) :
    ¬ PrefixAgree (X86Launch.entryStack img en inp) recorded := by
  intro agree
  have inRecorded : 8 < recorded.length := by
    rcases Nat.lt_or_ge 8 recorded.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at at8
      cases at8
  have same := prefixAgree_getElem? agree 8 (old_entryStack_long img en inp) inRecorded
  rw [at8] at same
  rcases argv : inp.argv with _ | ⟨first, rest⟩
  · rw [old_entryStack_byte8_nil img en inp argv, Option.some.injEq] at same
    exact nonzero same.symm
  · rw [old_entryStack_byte8_cons img en inp first rest argv, Option.some.injEq] at same
    apply unaligned
    rw [← same]
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_add, natToWord_toNat,
      structureSize, auxiliarySize, auxiliaryCount]
    omega

end Silmaril.Process.LPS.Machines.X86RealisticLaunch
