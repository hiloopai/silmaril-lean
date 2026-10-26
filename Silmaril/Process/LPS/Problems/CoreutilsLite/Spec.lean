module

public import Silmaril.Process.LPS.Probes.Oracle

/-! # Core utilities, simplified: the statement shape (VERIFIED definitions and checks)

The freestanding programs of `examples/coreutils-lite/` (GCC 13.3 `-O2`, no libc, syscall
wrappers in `sys.h`, linked by the probe harness into one R+X `PT_LOAD`) are stated against LPS
in one shape, `Total snapshot spec`:

* **Machine.** `Machines.x86WithFlagOracle oracle`, for **every** oracle: GCC zeroes registers
  with `xor`, which leaves AF undefined, and the deterministic adapter `x86ExtNative` declines
  every `syscall` with an undefined flag (so under it the GCC build of `true` is unmodelled at
  its only system call). This is the machine of the `sha256` end-to-end problems.
* **Launch.** Every valid launch (`X86Launch.ValidInput`, `X86Launch.ValidEntry`): any argv,
  environment, stdin, file system, stack pointer, brk and mmap base the launch envelope
  allows, and every allocation limit; only the inputs in `spec.domain`.
* **Semantics.** The LPS reference semantics without refusals (`noFilter`, LPS's `run`), with
  the native x86-64 syscall table. LPS `read` returns any non-empty prefix of the rest of
  stdin and `write` accepts any non-empty prefix, so every read and write chunking is covered.
  By `Omni.Exec.sound_any` the safety half extends to every refusal filter (`Total.sound_any`).
* **Claim** (`TotalAt`): every maximal execution is finite (no divergence), error free (no
  fault, nothing unmodelled, no stall) and ends with a normal exit whose events and status
  `spec.allowed` accepts (`Ends`), and the ideal trace `spec.ideal` is observable (`complete`,
  which rules out a program that never does the right thing).

A mutant is refuted by the same statement about its own bytes: `¬ Total mutant spec`
(`@[refutes]`).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.CoreutilsLite

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Probes

/-- The user machine. -/
abbrev machine (oracle : Nat → X86FlagChoices.Choice) : UserIsa := x86WithFlagOracle oracle

/-- The postcondition: a normal exit (no signal) whose events and status are allowed. -/
def Ends {isa : UserIsa} (allowed : List Event → Word → Prop) : Omni.Post isa :=
  fun trace outcome => ∃ final, outcome = .halt final ∧ final.model.killedBy = none ∧
    ∃ code, final.model.halted = some code ∧ allowed trace code

/-- What a program must do: the inputs it is specified on, the complete traces and statuses it
may end with, and the ideal trace that must be observable. -/
structure Spec where
  domain : ProcInput → Prop
  allowed : ProcInput → List Event → Word → Prop
  ideal : ProcInput → List Event

/-- A valid launch. -/
def Admissible (oracle : Nat → X86FlagChoices.Choice) (snapshot : X86Launch.Snapshot)
    (en : ExecEntry) (inp : ProcInput) : Prop :=
  X86Launch.ValidInput inp ∧ X86Launch.ValidEntry (machine oracle) snapshot en inp

/-- Total correctness of one launch. -/
structure TotalAt (oracle : Nat → X86FlagChoices.Choice) (snapshot : X86Launch.Snapshot)
    (limit : Int) (en : ExecEntry) (inp : ProcInput) (spec : Spec) : Prop where
  exec : Omni.Exec snapshot.image.segments Probes.spec noFilter
    (X86Launch.init (machine oracle) snapshot en limit inp) (Ends (spec.allowed inp))
  complete : (X86Launch.runWith (machine oracle) Probes.spec noFilter snapshot limit en inp).traces
    (spec.ideal inp)

/-- **The statement**: total correctness on every admissible launch with an input in the
domain, for every flag oracle and allocation limit. -/
def Total (snapshot : X86Launch.Snapshot) (spec : Spec) : Prop :=
  ∀ (oracle : Nat → X86FlagChoices.Choice) (limit : Int) (en : ExecEntry) (inp : ProcInput),
    spec.domain inp → Admissible oracle snapshot en inp → TotalAt oracle snapshot limit en inp spec

/-! ## Consequences (VERIFIED) -/

/-- Every finite execution under any refusal filter ends allowed. -/
theorem TotalAt.sound_any {oracle : Nat → X86FlagChoices.Choice} {snapshot : X86Launch.Snapshot}
    {limit : Int} {en : ExecEntry} {inp : ProcInput} {spec : Spec}
    (total : TotalAt oracle snapshot limit en inp spec) {refused : RefusalFilter}
    {trace : List Event} {outcome : Omni.Outcome (machine oracle)}
    (finite : Omni.FiniteExec snapshot.image.segments Probes.spec refused
      (X86Launch.init (machine oracle) snapshot en limit inp) trace outcome) :
    Ends (spec.allowed inp) trace outcome :=
  Omni.Exec.sound_any total.exec finite

/-- No execution errors, under any refusal filter. -/
theorem TotalAt.no_error {oracle : Nat → X86FlagChoices.Choice} {snapshot : X86Launch.Snapshot}
    {limit : Int} {en : ExecEntry} {inp : ProcInput} {spec : Spec}
    (total : TotalAt oracle snapshot limit en inp spec) (refused : RefusalFilter) :
    ¬ (X86Launch.runWith (machine oracle) Probes.spec refused snapshot limit en inp).errors :=
  Omni.Exec.no_error total.exec (fun _ _ ⟨_, impossible, _⟩ => by cases impossible)

/-- Nothing unmodelled is reachable, under any refusal filter. -/
theorem TotalAt.no_unmodeled {oracle : Nat → X86FlagChoices.Choice}
    {snapshot : X86Launch.Snapshot} {limit : Int} {en : ExecEntry} {inp : ProcInput} {spec : Spec}
    (total : TotalAt oracle snapshot limit en inp spec) (refused : RefusalFilter) :
    ¬ (X86Launch.runWith (machine oracle) Probes.spec refused snapshot limit en inp).unmodeled :=
  fun reaches => total.no_error refused (Probe.unmodeled_reachesError reaches)

/-- Every execution exits normally with a status in `S` when `allowed` forces it
(`MustExitInAt`, LPS `must_exit_in_at`). -/
theorem TotalAt.mustExit {oracle : Nat → X86FlagChoices.Choice} {snapshot : X86Launch.Snapshot}
    {limit : Int} {en : ExecEntry} {inp : ProcInput} {spec : Spec}
    (total : TotalAt oracle snapshot limit en inp spec) (S : List Word)
    (status : ∀ trace code, spec.allowed inp trace code → code ∈ S) :
    MustExitInAt snapshot.image.segments Probes.spec noFilter S
      (X86Launch.init (machine oracle) snapshot en limit inp) :=
  (Omni.mustExitInAt_iff_exec S _).mpr (total.exec.consequence fun _ outcome post => by
    obtain ⟨final, rfl, unkilled, code, halted, allowed⟩ := post
    exact ⟨code, halted, status _ _ allowed, unkilled⟩)

/-- A mutant whose every execution ends in a way the spec forbids, on one admissible launch
in the domain, does not meet the spec. -/
theorem not_total_of_exec {snapshot : X86Launch.Snapshot} {spec : Spec}
    {oracle : Nat → X86FlagChoices.Choice} {limit : Int} {en : ExecEntry} {inp : ProcInput}
    (domain : spec.domain inp) (admissible : Admissible oracle snapshot en inp)
    {post : Omni.Post (machine oracle)}
    (run : Omni.Exec snapshot.image.segments Probes.spec noFilter
      (X86Launch.init (machine oracle) snapshot en limit inp) post)
    (forbidden : ∀ trace outcome, post trace outcome → ¬ Ends (spec.allowed inp) trace outcome) :
    ¬ Total snapshot spec := by
  intro total
  obtain ⟨trace, outcome, finite, satisfied⟩ := run.realizes
  exact forbidden trace outcome satisfied
    ((total oracle limit en inp domain admissible).exec.sound finite)

/-! ## Launches exist (VERIFIED)

The kit's harness launch (`argv = ["./probe"]`, empty environment and stdin) of a checked probe
is admissible for every oracle, so `Total` is not vacuous for it. -/

theorem admissible_harness (P : Probe) [checked : Probe.Checked P]
    (oracle : Nat → X86FlagChoices.Choice) : Admissible oracle P.snapshot P.entry P.input :=
  ⟨checked.launched.1, checked.launched.2⟩

/-- The default flag choice (all clear), for refutations. -/
def clearChoice : X86FlagChoices.Choice := ⟨false, false, false, false, false, false⟩

end Silmaril.Process.LPS.Problems.CoreutilsLite
