module

public import Silmaril.Process.LPS.Machines.X86RealisticLaunchData
public import Silmaril.Process.LPS.Machines.X86MuslStartup

/-! # Reality check: recorded Linux launches are realistic, and not old launches

`X86RealisticLaunchData` holds two real launches of the pinned static-musl
checksum ELF, recorded by a ptrace tracer at the post-`execve` stop under
bubblewrap (`tools/verification-projects/x86_launch_probe.py`): one with
`ADDR_NO_RANDOMIZE`, one with full randomization. For each recording this file
proves, by evaluation on the concrete data:

* the recorded launch is in the realistic domain: a valid realistic input,
  choices and entry for the checked musl snapshot whose entry RSP is the
  recorded RSP and whose entry stack is exactly the recorded bytes from RSP to
  the top of `[stack]` (`inRealisticDomain`); the parsed auxiliary vector is the
  realistic one (`auxv_realistic`), and the realistic launch's entry registers
  are the recorded RSP and RIP;
* the recorded launch is in no old launch: no `X86Launch` entry stack with the
  recorded RSP agrees with the recorded bytes even on their common prefix, for
  any image, entry or input (`notInOldDomain`); in particular not in the old
  domain (`notInOldValidDomain`).

Both recordings also record the initial program break (`start_brk`), which is
checked against `ValidBrk`; the mmap base is not observable at the exec stop
(a static `ET_EXEC` has no mmap-region mapping yet), so the entries use a fixed
valid mmap base.

Both recordings map a vDSO and the vsyscall page, so they are not `Exact`
points: their realistic behaviour is `chaos` and they have no `Launched`
configuration (`recorded_not_launched`, `recorded_run_chaos`). The inhabited
exactly modelled launch of the musl ELF (`launch_nonempty`) is the
`ADDR_NO_RANDOMIZE` recording with the vDSO and vsyscall page removed, whose
behaviour is the actual LPS run.

The recordings were made on the host kernel named in the data module; the
auxiliary-vector and stack-layout code they exercise is the same in v6.13-v6.18.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Silmaril.Process.LPS.Machines.X86RealisticLaunch.Recorded

open Silmaril.Process.LPS.Machines.X86MuslStartup (snapshot loaded loaded_oracle)

/-- The recorded launch is a realistic launch of `snapshot`. -/
def InRealisticDomain (isa : UserIsa) (rsp : Word) (bytes : List Byte) : Prop :=
  ∃ c en inp, ValidInput inp ∧ ValidEntry isa snapshot c en inp ∧ en.sp = rsp ∧
    entryStack c snapshot.image en inp = bytes

/-- The recorded launch is an old launch of `snapshot`. -/
def InOldDomain (isa : UserIsa) (rsp : Word) (bytes : List Byte) : Prop :=
  ∃ en inp, X86Launch.ValidInput inp ∧ X86Launch.ValidEntry isa snapshot en inp ∧ en.sp = rsp ∧
    PrefixAgree (X86Launch.entryStack snapshot.image en inp) bytes

def inputWith (hwcap uid gid : Word) : ProcInput where
  argv := [[99, 104, 101, 99, 107, 115, 117, 109]]
  envp := []
  imageFs := []
  stdin := InputStream.eof
  uid := uid
  gid := gid
  groups := []
  net := netSilent
  nofile := 1024
  sigmask := 0
  hwcap := hwcap
  abortTerminal := false
  vaSize := .sv48
  urandom := InputStream.defaultUrandom
  tmp := []

theorem inputWith_valid (hwcap uid gid : Word) (small : uns hwcap < 2 ^ 32)
    (uidValid : ValidId uid) (gidValid : ValidId gid) : ValidInput (inputWith hwcap uid gid) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ⟨uidValid, gidValid⟩, ?_, ?_, ?_⟩, small⟩
  · simp [ValidArgv, inputWith, totalArgBytes, pathHasSlash]
  · simp [ValidEnvp, inputWith, totalArgBytes]
  · simp [inputWith, ProcInput.fs, fsSeedTmp, Fs.ValidFs, Fs.sorted]
  · simp [inputWith, Fs.KeysRelative]
  · change uns (1024 : Word) ≤ 2 ^ 31 - 64
    decide
  · change (0 : Word) &&& sigKernelOnlyMask = 0
    decide
  · intro n
    rfl

namespace norandom

def input : ProcInput := inputWith hwcap uid gid

/-- The recorded RSP, break and random bytes; the mmap base is not recorded. -/
def entry : ExecEntry := ⟨rsp, brk, 0x40000000, ⟨random, fun _ => 0⟩⟩

theorem input_valid : ValidInput input :=
  inputWith_valid _ _ _ (by decide) (by unfold ValidId; decide) (by unfold ValidId; decide)

theorem auxv_realistic : auxv = auxiliaryEntries snapshot.image choices input := by
  decide +kernel

theorem auxv_in_bytes : (bytes.drop 32).take (16 * auxv.length) = buildAuxv auxv := by
  decide +kernel

theorem sp_eq : entrySp snapshot.image choices input = rsp := by decide +kernel

theorem stack_eq : entryStack choices snapshot.image entry input = bytes := by decide +kernel

/-- The valid-entry lemma for the realistic domain at this launch. -/
theorem entry_valid (isa : UserIsa) (validSnapshot : X86Launch.ValidSnapshot isa snapshot) :
    ValidEntry isa snapshot choices entry input := by
  refine ⟨validSnapshot, ?_, sp_eq.symm, ?_⟩
  · unfold ValidChoices ValidFeatures ValidCreds ValidId
    decide +kernel
  · simp only [ValidBrk]
    decide +kernel

theorem inRealisticDomain (isa : UserIsa) (validSnapshot : X86Launch.ValidSnapshot isa snapshot) :
    InRealisticDomain isa rsp bytes :=
  ⟨choices, entry, input, input_valid, entry_valid isa validSnapshot, rfl, stack_eq⟩

theorem notInOldDomain (img : Image) (en : ExecEntry) (inp : ProcInput) (sp : en.sp = rsp) :
    ¬ PrefixAgree (X86Launch.entryStack img en inp) bytes :=
  old_excludes_unaligned_argv img en inp bytes 0xe5 (by decide +kernel) (by decide)
    (by rw [sp]; decide)

theorem notInOldValidDomain (isa : UserIsa) : ¬ InOldDomain isa rsp bytes := by
  rintro ⟨en, inp, -, -, sp, agree⟩
  exact notInOldDomain _ en inp sp agree

/-- The recording maps a vDSO and the vsyscall page: it is not an `Exact`
point, so it has no `Launched` configuration. -/
theorem recorded_not_launched (isa : UserIsa) (limit : Int) :
    ¬ ∃ configuration, Launched isa snapshot choices entry limit input configuration :=
  not_exact_no_launch _ _ _ _ _ _ (by decide)

/-- Its realistic behaviour is `chaos`. -/
theorem recorded_run_chaos (isa : UserIsa) (spec : Sys SyscallEffect) (refused : RefusalFilter)
    (limit : Int) : runWith isa spec refused snapshot limit choices entry input = chaos :=
  runWith_not_exact _ _ _ _ _ _ _ _ (by decide)

theorem initial_rsp (platform : Silmaril.X86.Ext.Wire.Platform) :
    (init (x86WireDf0RepStosq platform) snapshot choices entry sourceAllocLimit input).ms.m.core.read
      .rsp = rsp := rfl

theorem initial_rip (platform : Silmaril.X86.Ext.Wire.Platform) :
    (init (x86WireDf0RepStosq platform) snapshot choices entry sourceAllocLimit input).ms.m.core.rip =
      rip := rfl

/-- The same recording without the vDSO and the vsyscall page: an `Exact`
realistic launch whose behaviour is the actual LPS run. Its stack differs from
the recorded one only by the removed `AT_SYSINFO_EHDR` entry. -/
def choicesExact : Choices := { choices with vdso := none, vsyscall := false }

def entryExact : ExecEntry :=
  { entry with sp := entrySp snapshot.image choicesExact input }

theorem exact : Exact input choicesExact := by decide

/-- An inhabited, exactly modelled realistic launch of the musl ELF under the
Wire+REP STOSQ flag-oracle ISA that carries `X86MuslRun.reaches_main`. -/
theorem launch_nonempty (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) :
    ∃ configuration, Launched (x86WireDf0RepStosqWithFlagOracle platform oracle) snapshot
      choicesExact entryExact sourceAllocLimit input configuration := by
  refine (launch_exists_iff _ _ _ _ _ _).mpr ⟨input_valid,
    ⟨ELFImage.loadX86_validSnapshot (loaded_oracle platform oracle), ?_, rfl, ?_⟩, exact⟩
  · unfold ValidChoices ValidFeatures ValidCreds ValidId
    decide +kernel
  · simp only [ValidBrk]
    decide +kernel

theorem run_exact (isa : UserIsa) (spec : Sys SyscallEffect) (refused : RefusalFilter)
    (limit : Int) :
    runWith isa spec refused snapshot limit choicesExact entryExact input =
      runWithStack isa (entryStack choicesExact) spec refused snapshot.image limit entryExact
        input :=
  runWith_exact _ _ _ _ _ _ _ _ exact

end norandom

namespace randomized

def input : ProcInput := inputWith hwcap uid gid

def entry : ExecEntry := ⟨rsp, brk, 0x40000000, ⟨random, fun _ => 0⟩⟩

theorem input_valid : ValidInput input :=
  inputWith_valid _ _ _ (by decide) (by unfold ValidId; decide) (by unfold ValidId; decide)

theorem auxv_realistic : auxv = auxiliaryEntries snapshot.image choices input := by
  decide +kernel

theorem sp_eq : entrySp snapshot.image choices input = rsp := by decide +kernel

theorem stack_eq : entryStack choices snapshot.image entry input = bytes := by decide +kernel

theorem entry_valid (isa : UserIsa) (validSnapshot : X86Launch.ValidSnapshot isa snapshot) :
    ValidEntry isa snapshot choices entry input := by
  refine ⟨validSnapshot, ?_, sp_eq.symm, ?_⟩
  · unfold ValidChoices ValidFeatures ValidCreds ValidId
    decide +kernel
  · simp only [ValidBrk]
    decide +kernel

theorem inRealisticDomain (isa : UserIsa) (validSnapshot : X86Launch.ValidSnapshot isa snapshot) :
    InRealisticDomain isa rsp bytes :=
  ⟨choices, entry, input, input_valid, entry_valid isa validSnapshot, rfl, stack_eq⟩

theorem notInOldDomain (img : Image) (en : ExecEntry) (inp : ProcInput) (sp : en.sp = rsp) :
    ¬ PrefixAgree (X86Launch.entryStack img en inp) bytes :=
  old_excludes_unaligned_argv img en inp bytes 0xe5 (by decide +kernel) (by decide)
    (by rw [sp]; decide)

theorem notInOldValidDomain (isa : UserIsa) : ¬ InOldDomain isa rsp bytes := by
  rintro ⟨en, inp, -, -, sp, agree⟩
  exact notInOldDomain _ en inp sp agree

/-- The randomized RSP lies in the x86 launch stack window, which reaches 2 GiB below the
lowest randomized x86-64 stack top (`x86LaunchBounds`); the riscv64-derived window it
replaced excluded this recording. -/
theorem inside_x86_window : x86LaunchBounds.spWindowLo ≤ uns rsp := by decide

end randomized

/-- Both recordings, for the ISA of `X86MuslRun.reaches_main`. -/
theorem recorded_realistic_not_old (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) :
    let isa := x86WireDf0RepStosqWithFlagOracle platform oracle
    (InRealisticDomain isa norandom.rsp norandom.bytes ∧ ¬ InOldDomain isa norandom.rsp norandom.bytes) ∧
      (InRealisticDomain isa randomized.rsp randomized.bytes ∧
        ¬ InOldDomain isa randomized.rsp randomized.bytes) :=
  have valid := ELFImage.loadX86_validSnapshot (loaded_oracle platform oracle)
  ⟨⟨norandom.inRealisticDomain _ valid, norandom.notInOldValidDomain _⟩,
    ⟨randomized.inRealisticDomain _ valid, randomized.notInOldValidDomain _⟩⟩

end Silmaril.Process.LPS.Machines.X86RealisticLaunch.Recorded
