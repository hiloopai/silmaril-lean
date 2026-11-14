module

public import Silmaril.X86.Concurrency.Cir.Rc.Tv.Defs
public import Silmaril.Proofs.X86.Concurrency.Cir.Rc.Tv

/-!
# Translation validation of the refcount idioms: what is proved

PROVED (standard axioms; proofs in `Silmaril/Proofs/X86/Concurrency/Cir/Rc/Tv.lean`):

* `rcTv_sound`: **trace refinement with a clobber set and exit edges.** If the checker accepts
  a certificate, then every finite x86 run of the code from its start (any core with
  `rip = base`, any values returned by reads) is a run of the certificate's CIR program
  `c.body slow` (the small steps), for every cold path `slow`:
  * step by step, each x86 step's memory actions are those of at most one CIR label, so a
    locked instruction stays one atomic CIR label;
  * the registers outside the clobber set agree;
  * if the run reached the function's `ret`, the CIR program has finished;
  * if the run left the code forwards (the `je` to the cold block), the CIR program is at the
    cold path `slow`.
* `rcTv_flat`: the flattened form (equal memory actions of the whole runs).
* `rcTv_code`: the checker reads only the code bytes.
* `tv_ok`: the four pinned functions (`rc_clone`, `rc_drop`, `rc_publish`, `rc_share2`,
  gcc 13.3.0 `-O2`) check, each with its cold block beyond its `ret`;
* `bodies`: their CIR programs are exactly `rcInc`, `rcDrop` and their compositions;
* `tv_rejects`: a `jne` for the `je`, a `lock add` for the `lock sub`, an unlocked `add`, and a
  `je` back into the code are all rejected.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Rc.Tv

open Silmaril.X86 (State)
open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.TvCfg (XRun TRun regsOf)
open Silmaril.X86.MemoryModel.Litmus (XAct)
open Silmaril.X86.Concurrency.Cir.Tv (XThread)

/-- **The refcount checker is sound**: every x86 run of accepted code is a CIR run of the
certificate's program, step by step, equal outside the clobber set; at the `ret` the CIR
program has finished, and beyond the code it is at the cold path. -/
theorem rcTv_sound {t : XThread} {c : RCert} {ex : List Nat} (h : rcTv t c = some ex)
    (slow : Stmt) {s0 s : State} (h0 : s0.rip = t.base) {acc : List (List XAct)}
    (hr : XRun t s0 acc s) :
    ∃ σ rs, ∃ los : List (Option Lab), TRun (c.body slow) (regsOf s0) (los.filterMap id) σ rs ∧
      List.Forall₂ (fun acts o => acts = o.toList.flatMap Lab.acts) acc los ∧
      (∀ r, r ∉ c.K → regsOf s r = rs r) ∧ (s.rip = t.endRip → σ = .skip) ∧
      (∀ p, p < 2 ^ 64 → t.code.length < p → s.rip = t.base + BitVec.ofNat 64 p →
        σ = slow ∨ ∃ k, σ = .seq slow k) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Rc.TvP.rcTv_sound h slow h0 hr

/-- The flattened form: the whole run's memory actions are the CIR labels' actions. -/
theorem rcTv_flat {t : XThread} {c : RCert} {ex : List Nat} (h : rcTv t c = some ex)
    (slow : Stmt) {s0 s : State} (h0 : s0.rip = t.base) {acc : List (List XAct)}
    (hr : XRun t s0 acc s) :
    ∃ σ rs labs, TRun (c.body slow) (regsOf s0) labs σ rs ∧
      acc.flatten = labs.flatMap Lab.acts ∧ (∀ r, r ∉ c.K → regsOf s r = rs r) ∧
      (s.rip = t.endRip → σ = .skip) := by
  obtain ⟨σ, rs, los, hrun, hfa, hR, hend, -⟩ := rcTv_sound h slow h0 hr
  exact ⟨σ, rs, _, hrun, Silmaril.Proofs.X86.Concurrency.Cir.Rc.TvP.flatten_of_forall₂ hfa, hR,
    hend⟩

/-- The checker reads only the code bytes. -/
theorem rcTv_code {t t' : XThread} (h : t.code = t'.code) (c : RCert) : rcTv t c = rcTv t' c :=
  Silmaril.Proofs.X86.Concurrency.Cir.Rc.TvP.rcTv_code h c

/-- **The four pinned functions check**, each with one cold-path exit (none for `rc_clone`). -/
theorem tv_ok :
    rcTv (thr Code.rcClone) cloneCert = some [] ∧ rcTv (thr Code.rcDrop) dropCert = some [16] ∧
      rcTv (thr Code.rcPublish) publishCert = some [16] ∧
      rcTv (thr Code.rcShare2) share2Cert = some [16] := by
  decide +kernel

/-- **The validated programs are the derived ops.** -/
theorem bodies (slow : Stmt) :
    cloneCert.body slow = rcInc scratch (atRdi 0) ∧
      dropCert.body slow = rcDrop scratch (atRdi 0) slow ∧
      publishCert.body slow = .seq (.load .rax .rlx 4 .wb (atRdi 4))
        (.seq (.store .na 4 .wb (.bin .add (.bin .add (.reg .rsi) (.lit 0)) (.lit 0)) (.reg .rax))
          (rcDrop scratch (atRdi 0) slow)) ∧
      share2Cert.body slow = .seq (rcInc scratch (atRdi 0))
        (.seq (rcInc scratch (atRdi 0)) (rcDrop scratch (atRdi 0) slow)) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Mutants are rejected**: `je` → `jne`, `lock sub` → `lock add`, an unlocked `add`, and a
`je` back into the code. -/
theorem tv_rejects :
    rcTv (thr dropJne) dropCert = none ∧ rcTv (thr dropAdd) dropCert = none ∧
      rcTv (thr cloneUnlocked) cloneCert = none ∧ rcTv (thr dropBack) dropCert = none := by
  decide +kernel

/-- **More mutants are rejected**: an increment by `2`, a drop on the wrong
address, a drop without its `je`. -/
theorem tv_rejects_more :
    rcTv (thr cloneBy2) cloneCert = none ∧ rcTv (thr dropRsi) dropCert = none ∧
      rcTv (thr dropNoJe) dropCert = none := by
  decide +kernel

/-- **`rc_drop`'s bytes are `rcDrop`**: every x86 run of the pinned `rc_drop` (any thread with
those bytes) is a run of `rcDrop r11 [rdi] slow`, for every cold path `slow`, equal outside
`r11`, finished at the `ret`, at `slow` past it. -/
theorem drop_refines {t : XThread} (htc : t.code = Code.rcDrop) (slow : Stmt) {s0 s : State}
    (h0 : s0.rip = t.base) {acc : List (List XAct)} (hr : XRun t s0 acc s) :
    ∃ σ rs, ∃ los : List (Option Lab),
      TRun (rcDrop scratch (atRdi 0) slow) (regsOf s0) (los.filterMap id) σ rs ∧
      List.Forall₂ (fun acts o => acts = o.toList.flatMap Lab.acts) acc los ∧
      (∀ r, r ≠ scratch → regsOf s r = rs r) ∧ (s.rip = t.endRip → σ = .skip) ∧
      (∀ p, p < 2 ^ 64 → t.code.length < p → s.rip = t.base + BitVec.ofNat 64 p →
        σ = slow ∨ ∃ k, σ = .seq slow k) := by
  have h := tv_ok.2.1
  rw [rcTv_code (t' := t) (by simp [thr, htc])] at h
  obtain ⟨σ, rs, los, hrun, hfa, hR, hend, hex⟩ := rcTv_sound h slow h0 hr
  exact ⟨σ, rs, los, (bodies slow).2.1 ▸ hrun, hfa,
    fun r hr' => hR r (by simp [dropCert, hr']), hend, hex⟩

/-- **`rc_clone`'s bytes are `rcInc`.** -/
theorem clone_refines {t : XThread} (htc : t.code = Code.rcClone) {s0 s : State}
    (h0 : s0.rip = t.base) {acc : List (List XAct)} (hr : XRun t s0 acc s) :
    ∃ σ rs, ∃ los : List (Option Lab),
      TRun (rcInc scratch (atRdi 0)) (regsOf s0) (los.filterMap id) σ rs ∧
      List.Forall₂ (fun acts o => acts = o.toList.flatMap Lab.acts) acc los ∧
      (∀ r, r ≠ scratch → regsOf s r = rs r) ∧ (s.rip = t.endRip → σ = .skip) := by
  have h := tv_ok.1
  rw [rcTv_code (t' := t) (by simp [thr, htc])] at h
  obtain ⟨σ, rs, los, hrun, hfa, hR, hend, -⟩ := rcTv_sound h .skip h0 hr
  exact ⟨σ, rs, los, (bodies .skip).1 ▸ hrun, hfa,
    fun r hr' => hR r (by simp [cloneCert, hr']), hend⟩

end Silmaril.X86.Concurrency.Cir.Rc.Tv
