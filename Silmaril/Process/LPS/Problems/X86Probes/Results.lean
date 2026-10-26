module

public import Silmaril.Process.LPS.Problems.X86Probes.Corpus
public import Silmaril.Process.LPS.Problems.X86Probes.Launch.Errors
public import Silmaril.Process.LPS.Problems.X86Probes.Launch.Split
public import Silmaril.Process.LPS.Problems.X86Probes.Launch.Pairs
public import Silmaril.Process.LPS.Problems.X86Probes.Launch.Arch
public import Silmaril.Process.LPS.Problems.X86Probes.Launch.Opens
public import Silmaril.Process.LPS.Problems.X86Probes.Launch.ReadBadfd0
public import Silmaril.Process.LPS.Problems.X86Probes.Launch.ReadEcho
public import Silmaril.Process.LPS.Probes.Getrandom
public import Silmaril.Process.LPS.Probes.ArchPrctl

/-! # The x86 probe corpus: proofs and refutations

Every `proved` or `refuted` statement of the catalogue
(`tools/verification-projects/problems/x86-probes.json`, generated into
`Problems.X86Probes.Corpus`), settled:

* **Proved** (`haltsMayFail` and the extended `haltsMayFailWith`): the probe's universal
  theorem at every native launch (`Launch.Exit`, `Launch.Errors`, `Launch.Split`), lifted
  by `Probes.haltsMayFail_of_exec` and `Probes.haltsMayFailWith_of_exec`.
* **Refuted**, by the reason the catalogue records (`refutedBy`):
  - `modelCoverage`: the model lacks the call, so the run reaches an error (chaos) at the
    probe's own launch (`unknown_syscall`, `getrandom_badflags`, `arch_getfs`:
    `Probes.not_haltsMayFail_of_error`). A reachable error refutes `haltsMayFail` for every
    exit set, so these say nothing about Linux's status (218, 234, 120); they are blocked on
    table coverage.
  - `faultInjection`: an `ENOMEM` that `Env.mayFail` injects (`open_legacy`, `open_create`,
    `open_create_ko`, `Launch.Opens`).
  - `launchInput`: another valid launch input (`open_missing`, with `nofile` in the file system).
  - `shortWrite`: LPS may cut a channel write short (`write_hello_split`'s short first write
    prints `hlo\n`, which is not a prefix of `hello\n`: `Probes.not_haltsMayFailWith_of_run`).
    Linux prints `hello\n` for this probe; the refutation measures the model's short-write
    semantics, not a Linux-observable difference.
* **Refuted agreements** (`Launch.Pairs`): `exit42` against `exit43` (`program`: the exit
  statuses differ), and `write_hello` against `write_hello_split` (`shortWrite`: the split
  probe's short first write).

`results` lists them as `Settled` entries, so each proof's type is its entry's statement
under its entry's status; `x86_probe_problems.py check` compares the list with the
catalogue.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Problems.X86Probes.Results

open Silmaril.Process.LPS Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Probes
open Silmaril.Process.LPS.Problems Silmaril.Process.LPS.Problems.X86Probes

/-! ## Exit statuses -/

theorem negStatus_mem {k : Nat} (positive : 0 < k) (atMost : k ≤ 6) :
    negStatus k ∈ ([250, 251, 252, 253, 254, 255] : List Word) := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;> first | omega | decide

theorem countStatus_one {k : Nat} (positive : 0 < k) (atMost : k ≤ 1) :
    countStatus k ∈ ([1] : List Word) := by
  rcases k with _ | _ | k <;> first | omega | decide

/-! ## Deterministic probes -/

theorem exit42_halts : Corpus.Exit42.plain_halts_may_fail :=
  haltsMayFail_of_exec Data.Exit42.probe (fun en inp launch => exit42_exec en inp _ launch)
    (ExitOnly.exitsIn (by decide))

theorem exit42_silent : Corpus.Exit42.plain_halts_may_fail_silent :=
  haltsMayFailWith_of_exec Data.Exit42.probe (fun en inp launch => exit42_exec en inp _ launch)
    fun trace outcome post => ⟨ExitOnly.exitsIn (by decide) trace outcome post, ExitOnly.silent trace outcome post⟩

theorem exit43_halts : Corpus.Exit43.plain_halts_may_fail :=
  haltsMayFail_of_exec Data.Exit43.probe (fun en inp launch => exit43_exec en inp _ launch)
    (ExitOnly.exitsIn (by decide))

theorem exit43_silent : Corpus.Exit43.plain_halts_may_fail_silent :=
  haltsMayFailWith_of_exec Data.Exit43.probe (fun en inp launch => exit43_exec en inp _ launch)
    fun trace outcome post => ⟨ExitOnly.exitsIn (by decide) trace outcome post, ExitOnly.silent trace outcome post⟩

theorem closeTwice_halts : Corpus.CloseTwice.plain_halts_may_fail :=
  haltsMayFail_of_exec Data.CloseTwice.probe closeTwice_exec (Emits.exitsIn rfl (by decide))

theorem closeTwice_silent : Corpus.CloseTwice.plain_halts_may_fail_silent :=
  haltsMayFailWith_of_exec Data.CloseTwice.probe closeTwice_exec fun trace outcome post =>
    ⟨Emits.exitsIn rfl (by decide) trace outcome post, Emits.silent rfl rfl rfl trace outcome post⟩

theorem closeTwice1_halts : Corpus.CloseTwice1.plain_halts_may_fail :=
  haltsMayFail_of_exec Data.CloseTwice1.probe closeTwice1_exec (Emits.exitsIn rfl (by decide))

theorem closeTwice1_silent : Corpus.CloseTwice1.plain_halts_may_fail_silent :=
  haltsMayFailWith_of_exec Data.CloseTwice1.probe closeTwice1_exec fun trace outcome post =>
    ⟨Emits.exitsIn rfl (by decide) trace outcome post, Emits.silent rfl rfl rfl trace outcome post⟩

theorem readBadfd_halts : Corpus.ReadBadfd.plain_halts_may_fail :=
  haltsMayFail_of_exec Data.ReadBadfd.probe readBadfd_exec (Emits.exitsIn rfl (by decide))

theorem readBadfd_silent : Corpus.ReadBadfd.plain_halts_may_fail_silent :=
  haltsMayFailWith_of_exec Data.ReadBadfd.probe readBadfd_exec fun trace outcome post =>
    ⟨Emits.exitsIn rfl (by decide) trace outcome post, Emits.silent rfl rfl rfl trace outcome post⟩

theorem unknownExitGroup_halts : Corpus.UnknownExitGroup.plain_halts_may_fail :=
  haltsMayFail_of_exec Data.UnknownExitGroup.probe unknownExitGroup_exec (Emits.exitsIn rfl (by decide))

theorem unknownExitGroup_silent : Corpus.UnknownExitGroup.plain_halts_may_fail_silent :=
  haltsMayFailWith_of_exec Data.UnknownExitGroup.probe unknownExitGroup_exec fun trace outcome post =>
    ⟨Emits.exitsIn rfl (by decide) trace outcome post, Emits.silent rfl rfl rfl trace outcome post⟩

theorem writeClosed_halts : Corpus.WriteClosed.plain_halts_may_fail :=
  haltsMayFail_of_exec Data.WriteClosed.probe writeClosed_exec (Emits.exitsIn rfl (by decide))

theorem writeClosed_silent : Corpus.WriteClosed.plain_halts_may_fail_silent :=
  haltsMayFailWith_of_exec Data.WriteClosed.probe writeClosed_exec fun trace outcome post =>
    ⟨Emits.exitsIn rfl (by decide) trace outcome post, Emits.silent rfl rfl rfl trace outcome post⟩

theorem writeEfault_halts : Corpus.WriteEfault.plain_halts_may_fail :=
  haltsMayFail_of_exec Data.WriteEfault.probe writeEfault_exec (Emits.exitsIn rfl (by decide))

theorem writeEfault_silent : Corpus.WriteEfault.plain_halts_may_fail_silent :=
  haltsMayFailWith_of_exec Data.WriteEfault.probe writeEfault_exec fun trace outcome post =>
    ⟨Emits.exitsIn rfl (by decide) trace outcome post, Emits.silent rfl rfl rfl trace outcome post⟩

theorem writeZero_halts : Corpus.WriteZero.plain_halts_may_fail :=
  haltsMayFail_of_exec Data.WriteZero.probe writeZero_exec (Emits.exitsIn rfl (by decide))

theorem writeZero_silent : Corpus.WriteZero.plain_halts_may_fail_silent :=
  haltsMayFailWith_of_exec Data.WriteZero.probe writeZero_exec fun trace outcome post =>
    ⟨Emits.exitsIn rfl (by decide) trace outcome post, Emits.silent rfl rfl rfl trace outcome post⟩

/-! ## `arch_prctl`, identities and echoes -/

theorem archFs_halts : Corpus.ArchFs.plain_halts_may_fail :=
  haltsMayFail_of_exec Data.ArchFs.probe archFs_exec (Emits.exitsIn rfl (by decide))

theorem archFs_silent : Corpus.ArchFs.plain_halts_may_fail_silent :=
  haltsMayFailWith_of_exec Data.ArchFs.probe archFs_exec fun trace outcome post =>
    ⟨Emits.exitsIn rfl (by decide) trace outcome post, Emits.silent rfl rfl rfl trace outcome post⟩

theorem archFs1_halts : Corpus.ArchFs1.plain_halts_may_fail :=
  haltsMayFail_of_exec Data.ArchFs1.probe archFs1_exec (Emits.exitsIn rfl (by decide))

theorem archFs1_silent : Corpus.ArchFs1.plain_halts_may_fail_silent :=
  haltsMayFailWith_of_exec Data.ArchFs1.probe archFs1_exec fun trace outcome post =>
    ⟨Emits.exitsIn rfl (by decide) trace outcome post, Emits.silent rfl rfl rfl trace outcome post⟩

theorem archGetfsExit_halts : Corpus.ArchGetfsExit.plain_halts_may_fail :=
  haltsMayFail_of_exec Data.ArchGetfsExit.probe archGetfsExit_exec (Emits.exitsIn rfl (by decide))

theorem archGetfsExit_silent : Corpus.ArchGetfsExit.plain_halts_may_fail_silent :=
  haltsMayFailWith_of_exec Data.ArchGetfsExit.probe archGetfsExit_exec fun trace outcome post =>
    ⟨Emits.exitsIn rfl (by decide) trace outcome post, Emits.silent rfl rfl rfl trace outcome post⟩

theorem readBadfd0_halts : Corpus.ReadBadfd0.plain_halts_may_fail :=
  haltsMayFail_of_exec Data.ReadBadfd0.probe readBadfd0_exec ReadThenNeg.exitsIn

theorem readBadfd0_silent : Corpus.ReadBadfd0.plain_halts_may_fail_silent :=
  haltsMayFailWith_of_exec Data.ReadBadfd0.probe readBadfd0_exec fun trace outcome post =>
    ⟨ReadThenNeg.exitsIn trace outcome post, ReadThenNeg.silent trace outcome post⟩

theorem readEcho_halts : Corpus.ReadEcho.plain_halts_may_fail :=
  haltsMayFail_of_exec Data.ReadEcho.probe readEcho_exec_some EchoSome.exitsIn

theorem readEcho_echo : Corpus.ReadEcho.plain_halts_may_fail_echo :=
  haltsMayFailWith_of_exec Data.ReadEcho.probe readEcho_exec_some fun trace outcome post =>
    ⟨EchoSome.exitsIn trace outcome post, EchoSome.echo trace outcome post⟩

theorem readEcho2_halts : Corpus.ReadEcho2.plain_halts_may_fail :=
  haltsMayFail_of_exec Data.ReadEcho2.probe readEcho2_exec_some EchoSome.exitsIn

theorem readEcho2_echo : Corpus.ReadEcho2.plain_halts_may_fail_echo :=
  haltsMayFailWith_of_exec Data.ReadEcho2.probe readEcho2_exec_some fun trace outcome post =>
    ⟨EchoSome.exitsIn trace outcome post, EchoSome.echo trace outcome post⟩

/-! ## Opening probes -/

theorem openEfault_halts : Corpus.OpenEfault.plain_halts_may_fail :=
  haltsMayFail_of_exec Data.OpenEfault.probe openEfault_exec (Emits.exitsIn rfl (by decide))

theorem openEfault_silent : Corpus.OpenEfault.plain_halts_may_fail_silent :=
  haltsMayFailWith_of_exec Data.OpenEfault.probe openEfault_exec fun trace outcome post =>
    ⟨Emits.exitsIn rfl (by decide) trace outcome post, Emits.silent rfl rfl rfl trace outcome post⟩

/-- An injected `ENOMEM` on the legacy `open`: exit 244, not 3. -/
theorem openLegacy_refuted : ¬ Corpus.OpenLegacy.plain_halts_may_fail := by
  obtain ⟨_, _, _, run, halted⟩ := openLegacy_enomem
  exact not_haltsMayFail_of_exit Data.OpenLegacy.probe (nativeLaunch_self _ rfl) run.star halted (by decide)

/-- An injected `ENOMEM` on `openat(O_CREAT)`: exit 247, not 2. -/
theorem openCreate_refuted : ¬ Corpus.OpenCreate.plain_halts_may_fail := by
  obtain ⟨_, _, _, run, halted⟩ := openCreate_enomem
  exact not_haltsMayFail_of_exit Data.OpenCreate.probe (nativeLaunch_self _ rfl) run.star halted (by decide)

theorem openCreateKo_refuted : ¬ Corpus.OpenCreateKo.plain_halts_may_fail := by
  obtain ⟨_, _, _, run, halted⟩ := openCreateKo_enomem
  exact not_haltsMayFail_of_exit Data.OpenCreateKo.probe (nativeLaunch_self _ rfl) run.star halted (by decide)

/-- At a launch whose file system holds `nofile`: exit 253, not 2. -/
theorem openMissing_refuted : ¬ Corpus.OpenMissing.plain_halts_may_fail := by
  obtain ⟨_, _, _, run, halted⟩ := OpenMissing.present_opens
  exact not_haltsMayFail_of_exit Data.OpenMissing.probe
    (NativeLaunch.transfer (P := OpenMissing.present) rfl (nativeLaunch_self _ rfl)) run.star halted (by decide)

/-! ## Channel writes, with the short-write alternatives -/

theorem writeHello_halts : Corpus.WriteHello.plain_halts_may_fail :=
  haltsMayFail_of_exec Data.WriteHello.probe (fun en inp launch => writeHello_exec en inp _ launch)
    WriteThenExit.exitsIn

theorem writeHello_stdout : Corpus.WriteHello.plain_halts_may_fail_stdout :=
  haltsMayFailWith_of_exec Data.WriteHello.probe (fun en inp launch => writeHello_exec en inp _ launch)
    fun trace outcome post =>
      ⟨WriteThenExit.exitsIn trace outcome post,
        WriteThenExit.stdoutNonemptyPrefix (List.cons_ne_nil _ _) trace outcome post⟩

theorem writeHello5_halts : Corpus.WriteHello5.plain_halts_may_fail :=
  haltsMayFail_of_exec Data.WriteHello5.probe (fun en inp launch => writeHello5_exec en inp _ launch)
    WriteThenExit.exitsIn

theorem writeHello5_stdout : Corpus.WriteHello5.plain_halts_may_fail_stdout :=
  haltsMayFailWith_of_exec Data.WriteHello5.probe (fun en inp launch => writeHello5_exec en inp _ launch)
    fun trace outcome post =>
      ⟨WriteThenExit.exitsIn trace outcome post,
        WriteThenExit.stdoutNonemptyPrefix (List.cons_ne_nil _ _) trace outcome post⟩

theorem writeZero1_halts : Corpus.WriteZero1.plain_halts_may_fail :=
  haltsMayFail_of_exec Data.WriteZero1.probe writeZero1_exec
    (WroteThenExit.exitsIn (bs := Data.WriteZero1.observed.stdout)
      fun _ positive atMost => countStatus_one positive atMost)

theorem writeZero1_stdout : Corpus.WriteZero1.plain_halts_may_fail_stdout :=
  haltsMayFailWith_of_exec Data.WriteZero1.probe writeZero1_exec fun trace outcome post =>
    ⟨WroteThenExit.exitsIn (bs := Data.WriteZero1.observed.stdout)
      (fun _ positive atMost => countStatus_one positive atMost) trace outcome post,
      WroteThenExit.stdoutNonemptyPrefix trace outcome post⟩

theorem writeClosed2_halts : Corpus.WriteClosed2.plain_halts_may_fail :=
  haltsMayFail_of_exec Data.WriteClosed2.probe writeClosed2_exec
    (WroteThenExit.exitsIn (bs := Data.WriteClosed2.observed.stdout)
      fun _ positive atMost => negStatus_mem positive atMost)

theorem writeClosed2_stdout : Corpus.WriteClosed2.plain_halts_may_fail_stdout :=
  haltsMayFailWith_of_exec Data.WriteClosed2.probe writeClosed2_exec fun trace outcome post =>
    ⟨WroteThenExit.exitsIn (bs := Data.WriteClosed2.observed.stdout)
      (fun _ positive atMost => negStatus_mem positive atMost) trace outcome post,
      WroteThenExit.stdoutNonemptyPrefix trace outcome post⟩

theorem writeEfaultOk_halts : Corpus.WriteEfaultOk.plain_halts_may_fail :=
  haltsMayFail_of_exec Data.WriteEfaultOk.probe writeEfaultOk_exec
    (WroteThenExit.exitsIn (bs := Data.WriteEfaultOk.observed.stdout)
      fun _ positive atMost => negStatus_mem positive atMost)

theorem writeEfaultOk_stdout : Corpus.WriteEfaultOk.plain_halts_may_fail_stdout :=
  haltsMayFailWith_of_exec Data.WriteEfaultOk.probe writeEfaultOk_exec fun trace outcome post =>
    ⟨WroteThenExit.exitsIn (bs := Data.WriteEfaultOk.observed.stdout)
      (fun _ positive atMost => negStatus_mem positive atMost) trace outcome post,
      WroteThenExit.stdoutNonemptyPrefix trace outcome post⟩

theorem writeHelloSplit_halts : Corpus.WriteHelloSplit.plain_halts_may_fail :=
  haltsMayFail_of_exec Data.WriteHelloSplit.probe writeHelloSplit_exec TwoWritesThenExit.exitsIn

theorem writeHelloSplit_pieces : Corpus.WriteHelloSplit.plain_halts_may_fail_pieces :=
  haltsMayFailWith_of_exec Data.WriteHelloSplit.probe writeHelloSplit_exec fun trace outcome post =>
    ⟨TwoWritesThenExit.exitsIn trace outcome post, TwoWritesThenExit.pieces trace outcome post⟩

/-- `write_hello_split` may print `hlo\n` (its first write cut short to `h`), which is not a
prefix of `hello\n`. -/
theorem writeHelloSplit_stdout_refuted : ¬ Corpus.WriteHelloSplit.plain_halts_may_fail_stdout := by
  obtain ⟨_, fs, _, run⟩ := WriteHelloSplit.admits_short sourceAllocLimit
  refine not_haltsMayFailWith_of_run Data.WriteHelloSplit.probe
    (nativeLaunch_self Data.WriteHelloSplit.probe rfl) run ?_
  rintro ⟨_, printed, _⟩
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, written] at printed
  revert printed
  decide

/-! ## Unmodeled calls at the probe's own launch -/

theorem unknownSyscall_refuted : ¬ Corpus.UnknownSyscall.plain_halts_may_fail :=
  not_haltsMayFail_of_error Data.UnknownSyscall.probe (nativeLaunch_self _ rfl) unknownSyscall_errors

theorem getrandomBadflags_refuted : ¬ Corpus.GetrandomBadflags.plain_halts_may_fail :=
  not_haltsMayFail_of_error Data.GetrandomBadflags.probe
    (NativeLaunch.transfer (P := GetrandomBadflags.linuxProbe) rfl (nativeLaunch_self _ rfl))
    (Probe.unmodeled_reachesError (GetrandomBadflags.unmodeled noFilter))

theorem archGetfs_refuted : ¬ Corpus.ArchGetfs.plain_halts_may_fail :=
  not_haltsMayFail_of_error Data.ArchGetfs.probe (nativeLaunch_self _ rfl)
    (Probe.unmodeled_reachesError ArchGetfs.unmodeled)

/-! ## The settled entries -/

/-- Every settled statement of the corpus, with its proof or refutation. -/
def results : List Settled :=
  [⟨Corpus.ArchFs.plain_halts_may_fail_entry, archFs_halts⟩,
   ⟨Corpus.ArchFs.plain_halts_may_fail_silent_entry, archFs_silent⟩,
   ⟨Corpus.ArchFs1.plain_halts_may_fail_entry, archFs1_halts⟩,
   ⟨Corpus.ArchFs1.plain_halts_may_fail_silent_entry, archFs1_silent⟩,
   ⟨Corpus.ArchGetfs.plain_halts_may_fail_entry, archGetfs_refuted⟩,
   ⟨Corpus.ArchGetfsExit.plain_halts_may_fail_entry, archGetfsExit_halts⟩,
   ⟨Corpus.ArchGetfsExit.plain_halts_may_fail_silent_entry, archGetfsExit_silent⟩,
   ⟨Corpus.CloseTwice.plain_halts_may_fail_entry, closeTwice_halts⟩,
   ⟨Corpus.CloseTwice.plain_halts_may_fail_silent_entry, closeTwice_silent⟩,
   ⟨Corpus.CloseTwice1.plain_halts_may_fail_entry, closeTwice1_halts⟩,
   ⟨Corpus.CloseTwice1.plain_halts_may_fail_silent_entry, closeTwice1_silent⟩,
   ⟨Corpus.Exit42.plain_halts_may_fail_entry, exit42_halts⟩,
   ⟨Corpus.Exit42.plain_halts_may_fail_silent_entry, exit42_silent⟩,
   ⟨Corpus.Exit43.plain_halts_may_fail_entry, exit43_halts⟩,
   ⟨Corpus.Exit43.plain_halts_may_fail_silent_entry, exit43_silent⟩,
   ⟨Corpus.GetrandomBadflags.plain_halts_may_fail_entry, getrandomBadflags_refuted⟩,
   ⟨Corpus.OpenCreate.plain_halts_may_fail_entry, openCreate_refuted⟩,
   ⟨Corpus.OpenCreateKo.plain_halts_may_fail_entry, openCreateKo_refuted⟩,
   ⟨Corpus.OpenEfault.plain_halts_may_fail_entry, openEfault_halts⟩,
   ⟨Corpus.OpenEfault.plain_halts_may_fail_silent_entry, openEfault_silent⟩,
   ⟨Corpus.OpenLegacy.plain_halts_may_fail_entry, openLegacy_refuted⟩,
   ⟨Corpus.OpenMissing.plain_halts_may_fail_entry, openMissing_refuted⟩,
   ⟨Corpus.ReadBadfd.plain_halts_may_fail_entry, readBadfd_halts⟩,
   ⟨Corpus.ReadBadfd.plain_halts_may_fail_silent_entry, readBadfd_silent⟩,
   ⟨Corpus.ReadBadfd0.plain_halts_may_fail_entry, readBadfd0_halts⟩,
   ⟨Corpus.ReadBadfd0.plain_halts_may_fail_silent_entry, readBadfd0_silent⟩,
   ⟨Corpus.ReadEcho.plain_halts_may_fail_entry, readEcho_halts⟩,
   ⟨Corpus.ReadEcho.plain_halts_may_fail_echo_entry, readEcho_echo⟩,
   ⟨Corpus.ReadEcho2.plain_halts_may_fail_entry, readEcho2_halts⟩,
   ⟨Corpus.ReadEcho2.plain_halts_may_fail_echo_entry, readEcho2_echo⟩,
   ⟨Corpus.UnknownExitGroup.plain_halts_may_fail_entry, unknownExitGroup_halts⟩,
   ⟨Corpus.UnknownExitGroup.plain_halts_may_fail_silent_entry, unknownExitGroup_silent⟩,
   ⟨Corpus.UnknownSyscall.plain_halts_may_fail_entry, unknownSyscall_refuted⟩,
   ⟨Corpus.WriteClosed.plain_halts_may_fail_entry, writeClosed_halts⟩,
   ⟨Corpus.WriteClosed.plain_halts_may_fail_silent_entry, writeClosed_silent⟩,
   ⟨Corpus.WriteClosed2.plain_halts_may_fail_entry, writeClosed2_halts⟩,
   ⟨Corpus.WriteClosed2.plain_halts_may_fail_stdout_entry, writeClosed2_stdout⟩,
   ⟨Corpus.WriteEfault.plain_halts_may_fail_entry, writeEfault_halts⟩,
   ⟨Corpus.WriteEfault.plain_halts_may_fail_silent_entry, writeEfault_silent⟩,
   ⟨Corpus.WriteEfaultOk.plain_halts_may_fail_entry, writeEfaultOk_halts⟩,
   ⟨Corpus.WriteEfaultOk.plain_halts_may_fail_stdout_entry, writeEfaultOk_stdout⟩,
   ⟨Corpus.WriteHello.plain_halts_may_fail_entry, writeHello_halts⟩,
   ⟨Corpus.WriteHello.plain_halts_may_fail_stdout_entry, writeHello_stdout⟩,
   ⟨Corpus.WriteHello5.plain_halts_may_fail_entry, writeHello5_halts⟩,
   ⟨Corpus.WriteHello5.plain_halts_may_fail_stdout_entry, writeHello5_stdout⟩,
   ⟨Corpus.WriteHelloSplit.plain_halts_may_fail_entry, writeHelloSplit_halts⟩,
   ⟨Corpus.WriteHelloSplit.plain_halts_may_fail_pieces_entry, writeHelloSplit_pieces⟩,
   ⟨Corpus.WriteHelloSplit.plain_halts_may_fail_stdout_entry, writeHelloSplit_stdout_refuted⟩,
   ⟨Corpus.WriteZero.plain_halts_may_fail_entry, writeZero_halts⟩,
   ⟨Corpus.WriteZero.plain_halts_may_fail_silent_entry, writeZero_silent⟩,
   ⟨Corpus.WriteZero1.plain_halts_may_fail_entry, writeZero1_halts⟩,
   ⟨Corpus.WriteZero1.plain_halts_may_fail_stdout_entry, writeZero1_stdout⟩,
   ⟨Corpus.Pairs.exit42_vs_exit43_entry, exit42_vs_exit43_refuted⟩,
   ⟨Corpus.Pairs.write_hello_vs_split_entry, writeHello_vs_split_refuted⟩]

/-- The settled entries are exactly the corpus's proved and refuted entries, in order. -/
theorem results_settle :
    results.map (fun s => s.entry.key) =
      ((Corpus.entries.filter (fun e => e.status.settled)).map Entry.key) := by
  decide

end Silmaril.Process.LPS.Problems.X86Probes.Results
