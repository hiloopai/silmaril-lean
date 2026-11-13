module

public import Silmaril.Proofs.Machine.Process.IoSpec.Rules
public import Silmaril.Machine.Process.LibMiniClient.Rel.Thms
public import Silmaril.Machine.Process.Lps9.Str.Thms
public import Silmaril.Machine.X86.Str9.Thms

/-!
# Regression: ladder rung 12 through `IoSpec`

acceptance. Rung 12's process safety, re-derived through `IoSafeN` and the sound
`lpsEnv` (`ioSafe_psafeLps`) instead of the direct `psafe_exit` argument, on three LPS user
machines. Names in `Silmaril.Proofs.Machine.Process.IoSpec`.

* `rung12_ioSafe`: for any deterministic step `c` that every `Open.step` step is a step of,
  the rung-12 launch state is `IoSafeN c (lpsEnv segs) ⊥ n` for every `n`, with remainder
  `exitAllowed inp.fs` (from `startRun_holds` by `ioSafe_of_safeN` and `ioSafe_exit`).
* **`rung12_processSafe_io`** (`x86WithFlagOracle8`, `c = Open.step`, `agrees_open8`),
  **`rung12_processSafe9_io`** (`x86WithFlagOracle9`, `c = Open9.step`, `agrees_open9`),
  **`rung12_processSafeStr`** (`x86WithFlagOracle9Str`, `c = Str9.step`, `agrees_str9`):
  every valid launch is process-safe for `exitAllowed inp.fs`.
* **`rung12_complete_io`**: the statement of `rung12_complete`, with the safety half from
  `rung12_processSafe_io`. The must-exit half is still `rung12_mustExit` (`IoSpec` has no total
  variant yet).
* `rung12_nonvacuousStr`: some valid launch exists, and for it the `Str9` conclusion holds.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Process.IoSpec

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Machine.X86
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.Machine.Process.LibMiniClient
open Silmaril.Machine.Process.Lps9.Str
open Silmaril.Proofs.Machine.Process.LpsBridge

/-- **The rung-12 launch state is `IoSafe`** on every machine extending `Open.step`. -/
theorem rung12_ioSafe {c : MState → Option MState} (hc : Safe.Refines Open.step c)
    (segs : List Segment) (snapshot : X86Launch.Snapshot) (en : ExecEntry) (inp : ProcInput)
    (himg : snapshot.image = image) (hv : X86Launch.ValidEntry x86ExtNative snapshot en inp)
    (e : (lpsEnv segs).Model) (hfs : e.fs = inp.fs) :
    ∀ n, IoSafeN c (lpsEnv segs) (fun _ _ _ => False) n (launchState snapshot en inp) e
      (exitAllowed inp.fs) := by
  have hrun := Silmaril.Proofs.Machine.Process.LibMiniClient.startRun_holds snapshot en inp himg hv
  intro n
  refine ioSafe_of_safeN (.inl rfl) (fun m' ⟨ht, hrax, hrdi⟩ => ?_) n
    (fun k => Safe.safeN_of_refines hc (hrun k))
  refine ioSafe_exit ht (.inl hrax) (.inl rfl) ?_
  rw [hrdi, hfs]
  exact .inr rfl

/-- **Rung 12 on `x86WithFlagOracle8` through `IoSpec`.** -/
theorem rung12_processSafe_io (snapshot : X86Launch.Snapshot) (refusals : SpuriousCfg)
    (limit : Int) (en : ExecEntry) (inp : ProcInput) (himg : snapshot.image = image)
    (hv : X86Launch.ValidEntry x86ExtNative snapshot en inp) :
    ProcessSafe snapshot refusals limit en inp (exitAllowed inp.fs) := fun oracle =>
  (psafeF_iff (oracle := oracle)).1 <| ioSafe_psafeLps agrees_open8
    (fun _ _ _ _ _ _ h => h.elim) (initF_aligned oracle x86NativeStep8 snapshot en limit inp)
    (rung12_ioSafe (fun h => h) _ snapshot en inp himg hv _ rfl)

/-- **Rung 12 on `x86WithFlagOracle9` through `IoSpec`.** -/
theorem rung12_processSafe9_io (snapshot : X86Launch.Snapshot) (refusals : SpuriousCfg)
    (limit : Int) (en : ExecEntry) (inp : ProcInput) (himg : snapshot.image = image)
    (hv : X86Launch.ValidEntry x86ExtNative snapshot en inp) :
    ProcessSafeF Silmaril.Machine.Process.Lps9.x86NativeStep9 snapshot refusals limit en inp
      (exitAllowed inp.fs) := fun oracle =>
  ioSafe_psafeLps Silmaril.Proofs.Machine.Process.Lps9.agrees_open9
    (fun _ _ _ _ _ _ h => h.elim)
    (initF_aligned oracle Silmaril.Machine.Process.Lps9.x86NativeStep9 snapshot en limit inp)
    (rung12_ioSafe (fun h => Open9.step_of_open h) _ snapshot en inp himg hv _ rfl)

/-- **Rung 12 on `x86WithFlagOracle9Str` (`Ext9` + string forms) through `IoSpec`.** -/
theorem rung12_processSafeStr (snapshot : X86Launch.Snapshot) (refusals : SpuriousCfg)
    (limit : Int) (en : ExecEntry) (inp : ProcInput) (himg : snapshot.image = image)
    (hv : X86Launch.ValidEntry x86ExtNative snapshot en inp) :
    ProcessSafeF x86NativeStep9Str snapshot refusals limit en inp (exitAllowed inp.fs) :=
  fun oracle =>
  ioSafe_psafeLps Silmaril.Proofs.Machine.Process.Lps9.Str.agrees_str9
    (fun _ _ _ _ _ _ h => h.elim)
    (initF_aligned oracle x86NativeStep9Str snapshot en limit inp)
    (rung12_ioSafe (fun h => Str9.step_of_open9 (Open9.step_of_open h)) _ snapshot en inp
      himg hv _ rfl)

/-- **Ladder rung 12, end to end, with the safety half through `IoSpec`.** Same statement
as `rung12_complete`. -/
theorem rung12_complete_io (snapshot : X86Launch.Snapshot) (refusals : SpuriousCfg)
    (limit : Int) (en : ExecEntry) (inp : ProcInput) (himg : snapshot.image = image)
    (hv : X86Launch.ValidEntry x86ExtNative snapshot en inp) :
    ProcessSafe snapshot refusals limit en inp (exitAllowed inp.fs) ∧
      ∀ oracle : Oracle, MustExitInAt snapshot.image.segments spec
        (NativeX86.defaultRefusalFilter refusals) [6]
        (X86Launch.init (machine oracle) snapshot en limit inp) :=
  ⟨rung12_processSafe_io snapshot refusals limit en inp himg hv,
    Silmaril.Proofs.Machine.Process.LibMiniClient.rung12_mustExit snapshot refusals limit en inp
      himg hv⟩

open Silmaril.Proofs.Machine.Process.LibMiniClient.Launch in
/-- **Non-vacuity** on the string machine: some launch of the rung-12 image is valid, and
for it the `x86WithFlagOracle9Str` conclusion holds. -/
theorem rung12_nonvacuousStr : ∃ (snapshot : X86Launch.Snapshot) (en : ExecEntry)
    (inp : ProcInput), snapshot.image = image ∧
      X86Launch.ValidEntry x86ExtNative snapshot en inp ∧
      ∀ refusals limit,
        ProcessSafeF x86NativeStep9Str snapshot refusals limit en inp (exitAllowed inp.fs) := by
  obtain ⟨snapshot, en, inp, himg, hv⟩ := launch_nonvacuous
  exact ⟨snapshot, en, inp, himg, hv,
    fun refusals limit => rung12_processSafeStr snapshot refusals limit en inp himg hv⟩

end Silmaril.Proofs.Machine.Process.IoSpec
