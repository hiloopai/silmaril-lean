module

public import Silmaril.Machine.Process.LibMiniClient.Thms
public import Silmaril.Machine.Process.Lps9.Thms

/-!
# Ladder rung 12 as an LPS process on the `Ext9` machine (`x86WithFlagOracle9`)

PROVED (standard axioms; short proofs inline; names in
`Silmaril.Machine.Process.LibMiniClient.Rel`):

* `startRunR`: from every valid launch of the rung-12 image, `∀ n, SafeNR L9 ExitAt n` on the
  launch state, where `L9 = loosen Open9.isa ⊤`. From `startRun_holds` (on `Open.step`) via
  `safeNR_open9_of_open`.
* `rung12_processSafeR`: **for every relational `A` above `ofFun Open9.step`**, a demonic safe
  run of `A` from the launch state to `ExitAt` makes every launch process-safe on
  `x86WithFlagOracle9` for `exitAllowed inp.fs` (`psafe_of_safeNR`, `agrees_open9`,
  `psafeF_exit`).
* **`rung12_processSafe9`**: unconditionally, every valid launch of the rung-12 executable is
  process-safe on `x86WithFlagOracle9` (every oracle, refusal configuration and budget).
* **`rung12_mustExit9`**: every valid launch must exit with status 6 on `x86WithFlagOracle9`
  (`mustExit9_of_launchR` from `Must L9`, from `startRun_total`).

**What this is not.** The plan asked for this "from `len1_composedR`". It is not: the process
proof needs `_start` and `cmain`, which are composed with `len1` in the deterministic
`logicOn Open.step` (`rung12_link`, `cmain_safeB`), and there is no relational call rule
(P5's note) through which `cmain` could consume `len1`'s relational contract. So the
relational content enters at the *whole-run* level (`rung12_processSafeR` takes any
`SafeNR A` run), and the instance discharges it from the existing `Open.step` proof, lifted
to `loosen Open9.isa ⊤`. `len1_composedR` (the `len1` function contract on every
`C ≤ loosen Open9.isa ⊤`) is not used.
-/

@[expose] public section

namespace Silmaril.Machine.Process.LibMiniClient.Rel

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Machine.X86
open Silmaril.Machine.X86.RelIsa (Le Must SafeNR ofFun loosen)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.Lps9
open Silmaril.Machine.Process.LibMiniClient
open Silmaril.Proofs.Machine.Process.LpsBridge
open Silmaril.Proofs.Machine.Process.Lps9

/-- The everywhere-loosened `Ext9` open machine. -/
abbrev L9 : RelIsa MState := loosen Open9.isa (fun _ => True)

/-- **The `_start` run, relationally**: demonic safety on `loosen Open9.isa ⊤`. -/
theorem startRunR (snapshot : X86Launch.Snapshot) (en : ExecEntry) (inp : ProcInput)
    (himg : snapshot.image = image) (hv : X86Launch.ValidEntry x86ExtNative snapshot en inp) :
    ∀ n, SafeNR L9 ExitAt n (launchState snapshot en inp) :=
  safeNR_open9_of_open
    (Silmaril.Proofs.Machine.Process.LibMiniClient.startRun_holds snapshot en inp himg hv)

/-- **Rung 12 on `x86WithFlagOracle9`, from any relational `_start` run.** -/
theorem rung12_processSafeR {A : RelIsa MState} (hle : Le (ofFun Open9.step) A)
    (snapshot : X86Launch.Snapshot) (refusals : SpuriousCfg) (limit : Int) (en : ExecEntry)
    (inp : ProcInput) (hrun : ∀ n, SafeNR A ExitAt n (launchState snapshot en inp)) :
    ProcessSafeF x86NativeStep9 snapshot refusals limit en inp (exitAllowed inp.fs) := by
  refine processSafe9_of_launchR (Q := ExitAt) hle (.inl rfl) hrun ?_
  intro oracle c m al hm ⟨ht, hrax, hrdi⟩
  refine psafeF_exit agrees_open9 al ht (.inl hrax) (.inl rfl) ?_
  rw [hrdi, hm]
  exact .inr rfl

/-- **Ladder rung 12 as a process on `x86WithFlagOracle9`**: every valid launch is
process-safe for `exitAllowed inp.fs` (traces `[]` or `[exit 6]`, no error), for every flag
oracle, refusal configuration and budget. -/
theorem rung12_processSafe9 (snapshot : X86Launch.Snapshot) (refusals : SpuriousCfg)
    (limit : Int) (en : ExecEntry) (inp : ProcInput) (himg : snapshot.image = image)
    (hv : X86Launch.ValidEntry x86ExtNative snapshot en inp) :
    ProcessSafeF x86NativeStep9 snapshot refusals limit en inp (exitAllowed inp.fs) :=
  rung12_processSafeR le_open9 snapshot refusals limit en inp (startRunR snapshot en inp himg hv)

/-- **Ladder rung 12 must exit with status 6 on `x86WithFlagOracle9`.** -/
theorem rung12_mustExit9 (snapshot : X86Launch.Snapshot) (refusals : SpuriousCfg) (limit : Int)
    (en : ExecEntry) (inp : ProcInput) (himg : snapshot.image = image)
    (hv : X86Launch.ValidEntry x86ExtNative snapshot en inp) (oracle : Oracle) :
    MustExitInAt snapshot.image.segments spec (NativeX86.defaultRefusalFilter refusals) [6]
      (X86Launch.init (x86WithFlagOracle9 oracle) snapshot en limit inp) := by
  obtain ⟨k, m', hr, ht, hrax, hrdi⟩ :=
    Silmaril.Proofs.Machine.Process.LibMiniClient.startRun_total snapshot en inp himg hv
  exact mustExit9_of_launchR le_open9
    (must_open9_of_run (Q := fun m' => ExitReq m' ∧ m'.core.read .rdi &&& 255 = 6) hr
      ⟨⟨ht, .inl hrax⟩, hrdi⟩) oracle _

/-! ## Non-vacuity and a mutation probe -/

open Silmaril.Proofs.Machine.Process.LibMiniClient.Launch in
/-- **Non-vacuity**: some launch of the rung-12 image is valid, and for it both conclusions
hold. `MustExitInAt` is not vacuous: its `running` case demands an LPS step. -/
theorem rung12_nonvacuous9 : ∃ (snapshot : X86Launch.Snapshot) (en : ExecEntry)
    (inp : ProcInput), snapshot.image = image ∧
      X86Launch.ValidEntry x86ExtNative snapshot en inp ∧
      (∀ refusals limit,
        ProcessSafeF x86NativeStep9 snapshot refusals limit en inp (exitAllowed inp.fs)) ∧
      ∀ refusals limit oracle,
        MustExitInAt snapshot.image.segments spec (NativeX86.defaultRefusalFilter refusals) [6]
          (X86Launch.init (x86WithFlagOracle9 oracle) snapshot en limit inp) := by
  obtain ⟨snapshot, en, inp, himg, hv⟩ := launch_nonvacuous
  exact ⟨snapshot, en, inp, himg, hv,
    fun refusals limit => rung12_processSafe9 snapshot refusals limit en inp himg hv,
    fun refusals limit oracle => rung12_mustExit9 snapshot refusals limit en inp himg hv oracle⟩

open Silmaril.Proofs.Machine.Process.LibMiniClient.Launch in
/-- **Mutation probe for `Agrees`**: a machine that steps at a `syscall` (here the identity)
agrees with no native step; the rung-12 `exit` state is a `syscall` state. -/
theorem not_agrees_id (nstep : NStep) : ¬ Agrees nstep (fun m => some m) := by
  intro h
  obtain ⟨snapshot, en, inp, himg, hv⟩ := launch_nonvacuous
  obtain ⟨k, m', -, ht, -⟩ :=
    Silmaril.Proofs.Machine.Process.LibMiniClient.startRun_total snapshot en inp himg hv
  cases h.stuck ht

end Silmaril.Machine.Process.LibMiniClient.Rel
