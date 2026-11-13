module

public import Silmaril.X86.Concurrency.Cir.Tv.Spin.Defs
public import Silmaril.X86.Concurrency.Cir.Refute.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.TvSpin

/-!
# Translation validation of spin loops: what is proved

PROVED with the standard axioms (proofs in
`Silmaril/Proofs/X86/Concurrency/Cir/TvSpin.lean`):

* `spin_sound`-based `stvRun_sound`: **trace refinement per thread**, for every spin bound `n`:
  every x86 trace of the pieces (`pexplore`, spins retrying at most `n` times) is a run of the
  CIR thread `c.body n` over the same domain, with the same memory actions up to `normActs` and
  the same final registers outside the clobber set. The spin's x86 meaning comes from the
  symbolic steps of the actual bytes (load, `test`/`cmp`, `jcc`), not from a convention.
* `STest.refines`: every x86 behaviour of a test (under any model `M`) is a CIR behaviour with
  the same witness value;
* `STest.safe`: a passing `safeOk` proves the test's condition for every x86 behaviour with
  spin bound `0`, under SC, TSO and XL;
* `STest.cir_witness`: a passing `witnessOk` gives a CIR behaviour (spin bound `0`) satisfying
  the condition, under SC, TSO and XL.

Not proved: that `pexplore` (the pieces one after the other) is the whole function's
behaviour; see `Cir.Tv.Spin.Defs`.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Tv

open Silmaril.X86.Litmus (Trace)
open Silmaril.X86.MemoryModel.Litmus (Model Final Cond)

/-- **A spin-validated thread is sound** (trace refinement, every spin bound). -/
theorem stvRun_sound {th : SThread} {c : SCert} {K : List Reg} (h : stvRun th c = some K)
    {dom : List Nat} (hdom : ∀ v ∈ dom, v < 2 ^ 32) {fuel n : Nat} {trs : List Trace}
    (hx : pexplore th dom fuel n 0 c.pieces th.init = some trs) :
    ∀ tr ∈ trs, ∃ p ∈ run dom (c.body n) Regs.zero,
      p.1.flatMap Lab.acts = normActs tr.acts ∧ ∀ q, q ∉ K → tr.final.read q = p.2 q :=
  Silmaril.Proofs.X86.Concurrency.Cir.TvSpin.stvRun_sound h hdom hx

/-- **Refinement of a spin-validated test**, every spin bound. -/
theorem STest.refines {c : STest} (h : c.tvOk = true) (hd : c.domOk = true) {n : Nat}
    {M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop} {f : Final} (hf : c.XBehav n M f) :
    ∃ f', BehavIn (c.prog n) c.dom M f' ∧ c.test.witness.eval f' = c.test.witness.eval f :=
  Silmaril.Proofs.X86.Concurrency.Cir.TvSpin.STest.refines h hd hf

/-- The condition is the negated witness of a `forall` test. -/
theorem cond_of_witness {t : Silmaril.X86.MemoryModel.Litmus.Test}
    (hq : t.quant = .forall_) {f f' : Final} (h : t.witness.eval f' = t.witness.eval f) :
    t.cond.eval f' = t.cond.eval f := by
  simp only [Silmaril.X86.MemoryModel.Litmus.Test.witness, hq, Cond.eval] at h
  simpa using h

/-- **Safety for the bytes**: a passing `safeOk` proves the condition of a `forall` test for
every x86 behaviour with spin bound `0`, under SC, TSO and XL. -/
theorem STest.safe {c : STest} (h : c.safeOk = true) (hq : c.test.quant = .forall_) (M : Model)
    {f : Final} (hf : c.XBehav 0 M.Holds f) : c.test.cond.eval f = true := by
  simp only [STest.safeOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨htv, hd⟩, _⟩, hs⟩ := h
  obtain ⟨f', hf', hw⟩ := STest.refines htv hd hf
  rw [← cond_of_witness hq hw]
  exact Refute.behavIn_safe hs M hf'

/-- **A CIR witness**: a passing `witnessOk` gives a behaviour of the validated CIR program
(spin bound `0`) satisfying the condition, under SC, TSO and XL. -/
theorem STest.cir_witness {c : STest} {ks : List Nat} (h : c.witnessOk ks = true) (M : Model) :
    ∃ f, BehavIn (c.prog 0) c.dom M.Holds f ∧ c.test.cond.eval f = true := by
  simp only [STest.witnessOk, Bool.and_eq_true] at h
  exact Refute.witnessAuto_model h.2 M

/-- The x86 traces exist (no unsupported instruction, fault or exhausted straight-line fuel). -/
theorem STest.xtraces_some {c : STest} (h : c.safeOk = true) : (c.xtraces 0).isSome = true := by
  simp only [STest.safeOk, Bool.and_eq_true] at h
  exact h.1.2

end Silmaril.X86.Concurrency.Cir.Tv
