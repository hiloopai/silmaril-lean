module

public import Silmaril.X86.Concurrency.Bridge.Crit.Defs
public import Silmaril.X86.Concurrency.Bridge.Thms
public import Silmaril.X86.Concurrency.Cir.Mutex.Thms
public import Silmaril.X86.Concurrency.Cir.Robust.Thms
import Silmaril.Proofs.X86.Concurrency.Bridge.Crit

/-!
# A compiled caller of the mutex, validated through its call sites: what is proved

PROVED with the standard axioms (kernel checks in
`Silmaril/Proofs/X86/Concurrency/Bridge/Crit.lean`):

* `ltv_ok`: the caller checker `Bridge.ltv` accepts `crit_add2` in the pinned image (every
  image with these bytes, at any base): its two call sites, its body, and the callees
  `mutex_lock`, `mutex_unlock` against the certificates;
* `cert_body`: the linked CIR program is `critCir` with **`spinMutex` code** for the two
  callees, so the callee parts are the implementation behind the mutex interface;
* `crit_real`: every real run of `crit_add2` on `Atomic9.step` (an `LRun` of the image: the
  segments, the calls, the callee bodies and the returns, with interference) is a run of that
  CIR program, step by step (`Bridge.ltv_real`);
* `crit_tso`, `crit_finishes`: two threads running the validated program linked with the
  mutex (loop bound 2) end with the counter at `4` in every finished, drained state of CIR's
  native TSO machine, and such a state is reached (the explorer, `tsoCheck_sound`,
  `witness_of_any`);
* `ltv_rejects`: the checker rejects swapped callees, a retargeted call and a changed body;
* `lrun_nonvacuous`, `mini_real`: `LRun` is not vacuous: a concrete real run
  through a `call` and a `ret` of the image `call +0 ; ret`, accepted by `ltv`;
* `racy_lost`: **negative example**: with both callee bodies removed (no lock), a finished,
  drained TSO state has the counter at `2` (a lost update).

What is not claimed: the two-thread facts are about CIR's TSO machine `OReach .tso`, not a
concurrent run of the bytes (gap 1, `Bridge.Task.tsoRunCir`, is proved only for
straight-line litmus threads, `Bridge.cellsB`; this code has calls and loops); they are per
instance (two threads, loop bound 2); `crit_real` assumes, at each `ret`, that the return
address is still in its stack slot (`LRun`).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Bridge.Crit

open Silmaril.X86 (State)
open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.TvCfg
open Silmaril.X86.Concurrency.Cir.Tv (XThread)

/-- **The caller checker accepts `crit_add2`** in every image with the pinned bytes. -/
theorem ltv_ok {t : XThread} (h : t.code = Code.image) : ltv t Code.critOff cert = true := by
  rw [ltv_code (t' := Prim.thr Code.image) h]
  exact Silmaril.Proofs.X86.Concurrency.Bridge.Crit.ltv_thr

/-- **The checker rejects mutants**: the callees swapped in the certificate; the first call
retargeted to `mutex_unlock` (its displacement byte `0x41` set to `0xeb`); the body's `add eax, 2`
changed to `add eax, 1`. -/
theorem ltv_rejects :
    ltv (Prim.thr Code.image) Code.critOff swapped = false ∧
    ltv (Prim.thr (Code.image.set 0x41 0xeb)) Code.critOff cert = false ∧
    ltv (Prim.thr (Code.image.set 0x49 0x01)) Code.critOff cert = false :=
  Silmaril.Proofs.X86.Concurrency.Bridge.Crit.rejects

/-- **The callees are the mutex**: the linked program of `crit_add2` is `critCir` with the
code of `Mutex.spinMutex` (`mutex_lock`, `mutex_unlock`). -/
theorem cert_body (L : Nat) :
    cert.body L = critCir L (Mutex.spinMutex.lockCode L) (Mutex.spinMutex.unlockCode L) := rfl

/-- **Every real run of the compiled `crit_add2` is a CIR run** of the linked program with the
mutex code, step for step, ending with the same registers. -/
theorem crit_real {t : XThread} (h : t.code = Code.image) {s : State} {obs : List LObs}
    {s' : State} (hr : LRun t Code.critOff cert.parts cert.lastLen cert.lastCert s obs s')
    (h0 : s.rip = t.base + BitVec.ofNat 64 Code.critOff) {L : Nat} (hL : obs.length ≤ L) :
    ∃ rs, ∃ los : List (Option Lab),
      TRun (critCir L (Mutex.spinMutex.lockCode L) (Mutex.spinMutex.unlockCode L)) (regsOf s)
        (los.filterMap id) .skip rs ∧
      List.Forall₂ LObs.Ok obs los ∧ regsOf s' = rs :=
  ltv_real (ltv_ok h) hr h0 hL

/-- **Two validated critical sections add up** (positive example): two threads running the
validated `crit_add2` with the mutex end with the counter at `4` in every finished, drained
state of CIR's TSO machine. -/
theorem crit_tso {C : OCfg} (hr : OReach .tso 2 critC.cfg.toO C) (hd : C.Drained)
    (hf : ∀ t < 2, (C.ts t).1 = .skip) : C.mem x = some 4 := by
  obtain ⟨d, hp, rfl⟩ := Robust.tsoCheck_sound
    Silmaril.Proofs.X86.Concurrency.Bridge.Crit.crit_four hr hd hf
  simpa [xIs, Robust.CSt.ocfg] using hp

/-- **Non-vacuity**: such a finished, drained state is reached. -/
theorem crit_finishes : ∃ C : OCfg, OReach .tso 2 critC.cfg.toO C ∧ C.Drained ∧
    (∀ t < 2, (C.ts t).1 = .skip) ∧ C.mem x = some 4 := by
  obtain ⟨d, hr, hd, hf, hp⟩ := Robust.witness_of_any (N := 2) (c0 := critC) rfl rfl
    Silmaril.Proofs.X86.Concurrency.Bridge.Crit.crit_fin
  exact ⟨d.ocfg, hr, hd, hf, by simpa [xIs, Robust.CSt.ocfg] using hp⟩

/-- **Without the lock an update is lost** (negative example): with both callee bodies removed,
a finished, drained TSO state has the counter at `2`. -/
theorem racy_lost : ∃ C : OCfg, OReach .tso 2 racyC.cfg.toO C ∧ C.Drained ∧
    (∀ t < 2, (C.ts t).1 = .skip) ∧ C.mem x = some 2 := by
  obtain ⟨d, hr, hd, hf, hp⟩ := Robust.witness_of_any (N := 2) (c0 := racyC) rfl rfl
    Silmaril.Proofs.X86.Concurrency.Bridge.Crit.racy_two
  exact ⟨d.ocfg, hr, hd, hf, by simpa [xIs, Robust.CSt.ocfg] using hp⟩

/-- **`LRun` is not vacuous**: the image `call +0 ; ret` (`miniT`) is accepted by
the caller checker, and it has a concrete real run on `Atomic9.step` through a `call` and a `ret`
(`miniObs`), whose `ret` reads the return address the `call` wrote (no interference: the `ret`'s
memory is the `call`'s result). So `ltv_real`'s hypotheses, including the stack-slot hypothesis,
hold together on a real run with a call. (Not a run of `crit_add2`: that would run the lock
loop concretely.) -/
theorem lrun_nonvacuous :
    ltv miniT 0 miniCert = true ∧
      LRun miniT 0 miniCert.parts miniCert.lastLen miniCert.lastCert miniS0 miniObs miniS2 ∧
      miniS0.rip = miniT.base + BitVec.ofNat 64 0 ∧ miniObs.length = 2 :=
  ⟨Silmaril.Proofs.X86.Concurrency.Bridge.Crit.mini_ltv,
    Silmaril.Proofs.X86.Concurrency.Bridge.Crit.mini_run, by decide +kernel, rfl⟩

/-- `ltv_real` applied to the concrete run: a CIR run of the linked program. -/
theorem mini_real : ∃ rs, ∃ los : List (Option Lab),
    TRun (miniCert.body 2) (regsOf miniS0) (los.filterMap id) .skip rs ∧
      List.Forall₂ LObs.Ok miniObs los ∧ regsOf miniS2 = rs :=
  ltv_real lrun_nonvacuous.1 lrun_nonvacuous.2.1 lrun_nonvacuous.2.2.1 (by decide)

end Silmaril.X86.Concurrency.Bridge.Crit
