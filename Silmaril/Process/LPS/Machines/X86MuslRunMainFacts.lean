module

public import Silmaril.Process.LPS.Machines.X86MuslRunMain

/-! # The state in which the pinned static-musl executable enters `main`

`reaches_main_facts` strengthens `X86MuslRun.reaches_main` with the calling
state musl's `libc_start_main_stage2` builds for `main(argc, argv, envp)`:

* `rdi = 1` (argc), `rsi = 0x7fffffffe008` (argv, the launch `rsp + 8`),
  `rdx = 0x7fffffffe018` (envp, `argv + 8·(argc + 1)`);
* `rsp ≡ 8 (mod 16)`, as required at a System V function entry after `call`,
  and the 8 bytes at `rsp` are the return address `0x40145f` back into
  `libc_start_main_stage2`;
* in the reached memory `argv[0]` points to the NUL-terminated string
  `"checksum"`, `argv[1] = NULL` and `envp[0] = NULL` (the empty environment);
* the FS base is `0x404138`, the thread pointer installed by
  `arch_prctl(ARCH_SET_FS)` during `__init_tp`.

As for `reaches_main`, the statement is for every CPUID platform, every flag
oracle and every spurious-refusal configuration, and the trace is empty.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 100000

namespace Silmaril.Process.LPS.Machines.X86MuslRun

open Silmaril.Process (Memory ByteMemory Region)
open Silmaril.Process.LPS.Machines.X86MuslStartup

/-- `argv[0]` of the launch, `"checksum"` with its terminating NUL. -/
def argv0Bytes : List Byte := [0x63, 0x68, 0x65, 0x63, 0x6b, 0x73, 0x75, 0x6d, 0x00]

/-- Little-endian bytes of a 64-bit value. -/
def wordBytes (n : Nat) : List Byte := (List.range 8).map fun i => natByte n i

theorem launch_rsp : c0.read .rsp = 0x7fffffffe000 := rfl

/-- The launch stack holds `argc = 1` at the initial `rsp`. -/
theorem launch_argc : Memory.readWith ⟨R, M0⟩ .read 0x7fffffffe000 8 = some (wordBytes 1) := by
  rw [readWith_eq realizes0]
  decide +kernel

/-- The state musl's `libc_start_main_stage2` builds for `main(argc, argv, envp)`,
for the thread id `tid`: the next instruction is `main`'s, nothing is pending,
the process runs, `rdi`/`rsi`/`rdx` are argc, argv and envp, the stack is
aligned for a function entry with the return address on top, `argv` and
`envp` are as launched, FS holds the thread pointer, and `td->tid` and the
model hold `tid`. -/
def MainFacts {platform : Silmaril.X86.Ext.Wire.Platform} {oracle : Nat → X86FlagChoices.Choice}
    (tid : Silmaril.X86.Word) (final : Config (x86WireDf0RepStosqWithFlagOracle platform oracle)) :
    Prop :=
  final.ms.native.m.core.rip.toNat = mainAddress ∧ final.ms.native.pending = none ∧
    final.model.halted = none ∧
    final.ms.native.m.core.read .rdi = 1 ∧
    final.ms.native.m.core.read .rsi = 0x7fffffffe008 ∧
    final.ms.native.m.core.read .rdx = 0x7fffffffe018 ∧
    (final.ms.native.m.core.read .rsp).toNat % 16 = 8 ∧
    final.ms.native.m.core.fsBase = 0x404138 ∧
    final.ms.native.m.memory.readWith .read 0x7fffffffdfc8 8 = some (wordBytes 0x40145f) ∧
    final.ms.native.m.memory.readWith .read 0x7fffffffe008 8 =
      some (wordBytes 0x7fffffffe160) ∧
    final.ms.native.m.memory.readWith .read 0x7fffffffe010 8 = some (wordBytes 0) ∧
    final.ms.native.m.memory.readWith .read 0x7fffffffe018 8 = some (wordBytes 0) ∧
    final.ms.native.m.memory.readWith .read 0x7fffffffe160 9 = some argv0Bytes ∧
    final.ms.native.m.memory.readWith .read tidAddress 4 = some (tidBytes tid) ∧
    final.model.tid = some tid

/-- Reads of the main-entry memory away from `td->tid` are reads of the
recorded view `V104`. -/
theorem main_read (tid : Silmaril.X86.Word) (a n : Nat) (apart : a + n ≤ tidAddress ∨ tidAddress + 4 ≤ a) :
    Memory.readWith ⟨R, M104 tid⟩ .read a n = readWithV R V104 .read a n := by
  rw [readWith_eq (realizesT104 tid), readWithV_overlay _ _ _ _ _ _ _ _ apart]

/-- `mainCfg … tid b` has the main-entry facts for its thread id. -/
theorem mainCfg_facts (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) (tid : Silmaril.X86.Word) (b : Bool) :
    MainFacts tid (mainCfg platform oracle tid b) := by
  refine ⟨by cases b <;> rfl, rfl, initial_halted platform oracle, by cases b <;> rfl,
    by cases b <;> rfl, by cases b <;> rfl,
    by cases b <;> exact (by decide : (0x7fffffffdfc8 : BitVec 64).toNat % 16 = 8),
    by cases b <;> rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  rotate_right
  · change Memory.readWith ⟨R, M104 tid⟩ _ _ _ = _
    rw [readWith_eq (realizesT104 tid)]
    rfl
  all_goals
    change Memory.readWith ⟨R, M104 tid⟩ _ _ _ = _
    rw [main_read tid _ _ (by decide)]
    decide +kernel

/-- For every thread id `set_tid_address` may return, the launch-to-`main`
run, with the register and memory state at `main`'s entry. -/
theorem reaches_main_facts_tid (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) {refused : RefusalFilter}
    (notRefused : StartupNotRefused refused) (tid : Silmaril.X86.Word) (valid : ValidTid tid) :
    ∃ final : Config (x86WireDf0RepStosqWithFlagOracle platform oracle),
      Star snapshot.image.segments NativeX86.extendedSyscallSpec refused
          (initialOracle platform oracle) [] final ∧ MainFacts tid final :=
  ⟨_, star_main platform oracle notRefused tid valid, mainCfg_facts platform oracle tid _⟩

/-- The launch-to-`main` run, with the register and memory state at `main`'s entry. -/
theorem reaches_main_facts (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) (cfgRefusal : SpuriousCfg) :
    ∃ final : Config (x86WireDf0RepStosqWithFlagOracle platform oracle),
      Star snapshot.image.segments NativeX86.extendedSyscallSpec
          (NativeX86.defaultRefusalFilter cfgRefusal) (initialOracle platform oracle) [] final ∧
        final.ms.native.m.core.rip.toNat = mainAddress ∧ final.ms.native.pending = none ∧
        final.model.halted = none ∧
        final.ms.native.m.core.read .rdi = 1 ∧
        final.ms.native.m.core.read .rsi = 0x7fffffffe008 ∧
        final.ms.native.m.core.read .rdx = 0x7fffffffe018 ∧
        (final.ms.native.m.core.read .rsp).toNat % 16 = 8 ∧
        final.ms.native.m.core.fsBase = 0x404138 ∧
        final.ms.native.m.memory.readWith .read 0x7fffffffdfc8 8 = some (wordBytes 0x40145f) ∧
        final.ms.native.m.memory.readWith .read 0x7fffffffe008 8 =
          some (wordBytes 0x7fffffffe160) ∧
        final.ms.native.m.memory.readWith .read 0x7fffffffe010 8 = some (wordBytes 0) ∧
        final.ms.native.m.memory.readWith .read 0x7fffffffe018 8 = some (wordBytes 0) ∧
        final.ms.native.m.memory.readWith .read 0x7fffffffe160 9 = some argv0Bytes := by
  obtain ⟨final, run, rip, pending, halted, rdi, rsi, rdx, rsp, fs, ret, argv0, argv1, envp0,
    string, _⟩ := reaches_main_facts_tid platform oracle (startupNotRefused_default cfgRefusal) 7
      validTid_seven
  exact ⟨final, run, rip, pending, halted, rdi, rsi, rdx, rsp, fs, ret, argv0, argv1, envp0,
    string⟩

end Silmaril.Process.LPS.Machines.X86MuslRun
