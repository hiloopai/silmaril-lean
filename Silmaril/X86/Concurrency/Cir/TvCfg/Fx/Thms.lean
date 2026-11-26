module

public import Silmaril.X86.Concurrency.Cir.TvCfg.Fx.Defs
import Silmaril.Proofs.X86.Concurrency.Cir.TvCfg.FxSound

/-!
# Translation validation of futex code: what is proved

All statements are PROVED with the standard axioms (proofs in
`Silmaril/Proofs/X86/Concurrency/Cir/TvCfg/Fx{X86,Sound}.lean`). The x86 side is `XStep`
(`stepSym`) extended by the **futex system-call convention** `SysStep`, which is an
assumption about Linux (`TvCfg.Fx.SysStep`).

* `tvFx_steps`: **trace refinement for futex code.** If the checker accepts a certificate, then
  every finite x86 run of the code (any start core with `rip = base`, any values returned by
  reads, any futex outcomes, `k` steps) is a run of the certificate's CIR program `c.body L`
  (the small steps `Csl.TStep`) for every loop bound `L ≥ k`, from the same registers:
  - each x86 step's actions are those of at most one CIR label, so a locked instruction or a
    futex call is one atomic CIR label;
  - the final registers agree **outside `rax`, `rcx` and `r11`**, the registers `syscall`
    clobbers;
  - if the x86 run has returned (`rip` at the end of the code or at another `ret`), the CIR run
    has finished (`skip`).
* `tvFx_sound`: the same with the actions flattened.
* `tvFx_code`: the checker reads only the code bytes.
* `tvFx_reach`: every core a run from the start reaches has `rip` at a certificate entry
  (exported for the real-machine bridge, `Bridge.tvFxDefined_holds`).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.TvCfg.Fx

open Silmaril.X86 (State)
open Silmaril.X86.Concurrency.Cir.Tv (XThread)
open Silmaril.X86.MemoryModel.Litmus (XAct)

/-- **The futex-code checker is sound, step by step.** -/
theorem tvFx_steps {t : XThread} {c : FCert} (hc : tvFx t c = true) {s0 s : State}
    (h0 : s0.rip = t.base) {acc : List (List XAct)} (hr : FRun t s0 acc s) {L : Nat}
    (hL : acc.length ≤ L) :
    ∃ σ rs, ∃ los : List (Option Lab), TRun (c.body L) (regsOf s0) (los.filterMap id) σ rs ∧
      List.Forall₂ (fun acts o => acts = o.toList.flatMap Lab.acts) acc los ∧
      (∀ r, r ∉ clob → regsOf s r = rs r) ∧ (Returned t s → σ = .skip) :=
  Silmaril.Proofs.X86.Concurrency.Cir.TvCfg.tvFx_steps hc h0 hr hL

/-- **The futex-code checker is sound**: every x86 run is a CIR run with the same memory actions. -/
theorem tvFx_sound {t : XThread} {c : FCert} (hc : tvFx t c = true) {s0 s : State}
    (h0 : s0.rip = t.base) {acc : List (List XAct)} (hr : FRun t s0 acc s) {L : Nat}
    (hL : acc.length ≤ L) :
    ∃ σ rs labs, TRun (c.body L) (regsOf s0) labs σ rs ∧ acc.flatten = labs.flatMap Lab.acts ∧
      (∀ r, r ∉ clob → regsOf s r = rs r) ∧ (Returned t s → σ = .skip) := by
  obtain ⟨σ, rs, los, hrun, h2, hregs, hend⟩ := tvFx_steps hc h0 hr hL
  exact ⟨σ, rs, _, hrun, Silmaril.Proofs.X86.Concurrency.Cir.TvCfg.flatten_of_forall₂ h2,
    hregs, hend⟩

/-- **The cores a futex-code run reaches sit at entries**. -/
theorem tvFx_reach {t : XThread} {c : FCert} (hc : tvFx t c = true) {s0 s : State}
    (h0 : s0.rip = t.base) {acc : List (List XAct)} (hr : FRun t s0 acc s) :
    ∃ e ∈ c.entries, s.rip = t.base + BitVec.ofNat 64 e.off :=
  Silmaril.Proofs.X86.Concurrency.Cir.TvCfg.tvFx_reach hc h0 hr

/-- The checker reads only the code bytes. -/
theorem tvFx_code {t t' : XThread} (h : t.code = t'.code) (c : FCert) :
    tvFx t c = tvFx t' c := by
  obtain ⟨b, code, r, i⟩ := t
  obtain ⟨b', code', r', i'⟩ := t'
  simp only at h
  subst h
  rfl

end Silmaril.X86.Concurrency.Cir.TvCfg.Fx
