module

public import Silmaril.X86.Concurrency.Cir.TvCfg.Defs
public import Silmaril.X86.Litmus.Extract.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.TvCfg.Sound

/-!
# Translation validation of x86 code with loops into CIR: what is proved

All statements are PROVED with the standard axioms (proofs in
`Silmaril/Proofs/X86/Concurrency/Cir/TvCfg/`).

* `tvCfg_sound`: **trace refinement for code with loops.** If the checker accepts a certificate,
  then every finite x86 run of the code from its start (any core with `rip = base`, any values
  returned by reads, `k` steps) is a run of the certificate's CIR program `c.body L` (the small
  steps `Csl.TStep`) for every loop bound `L ≥ k`, from the same registers. The memory actions
  are equal (`acts.flatten = labs.flatMap Lab.acts`), the final registers are equal, and if the
  x86 run has reached the end of the code (the function's `ret`), the CIR run has reached
  `skip`.
* `tvCfg_steps`: the same, step by step: each x86 step's actions are those of at
  most one CIR label, so atomicity is kept (the flattened form of `tvCfg_sound` alone would allow
  an `xchg` to be matched by a separate load and store).
* `tvCfg_reach`: every core a run from the start reaches has `rip` at a certificate
  entry (exported for the real-machine bridge, `Bridge.tvCfgDefined_holds`).
* `sbeq_eq`: the Boolean statement equality the checker uses is equality.
* `tvCfg_code`: the checker reads only the code, so the result holds for every thread (base,
  regions, initial core) with those bytes.
* `XStep.replays`: each x86 step of the semantics used here replays on the sequential machine
  `Atomic9.step` on every memory that has the thread's regions and code and answers the step's
  reads (`stepSym_sound`), so other threads may change memory between steps.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.TvCfg

open Silmaril.X86 (State)
open Silmaril.X86.Concurrency.Cir.Tv (XThread)
open Silmaril.X86.MemoryModel.Litmus (XAct)

/-- **The CFG checker is sound**: every x86 run of `k` steps from the code's start is a CIR run
of `c.body L` for every `L ≥ k`, with the same memory actions and final registers; at the end
of the code the CIR program has finished. -/
theorem tvCfg_sound {t : XThread} {c : GCert} (hc : tvCfg t c = true) {s0 s : State}
    (h0 : s0.rip = t.base) {acc : List (List XAct)} (hr : XRun t s0 acc s) {L : Nat}
    (hL : acc.length ≤ L) :
    ∃ σ rs labs, TRun (c.body L) (regsOf s0) labs σ rs ∧ acc.flatten = labs.flatMap Lab.acts ∧
      regsOf s = rs ∧ (s.rip = t.endRip → σ = .skip) :=
  Silmaril.Proofs.X86.Concurrency.Cir.TvCfg.tvCfg_sound hc h0 hr hL

/-- **The CFG checker is sound, step by step**: as `tvCfg_sound`, and moreover the actions of
each x86 step are the actions of at most one CIR label (`List.Forall₂`), so a locked instruction
is one atomic CIR label, never split into a read and a write. -/
theorem tvCfg_steps {t : XThread} {c : GCert} (hc : tvCfg t c = true) {s0 s : State}
    (h0 : s0.rip = t.base) {acc : List (List XAct)} (hr : XRun t s0 acc s) {L : Nat}
    (hL : acc.length ≤ L) :
    ∃ σ rs, ∃ los : List (Option Lab), TRun (c.body L) (regsOf s0) (los.filterMap id) σ rs ∧
      List.Forall₂ (fun acts o => acts = o.toList.flatMap Lab.acts) acc los ∧
      regsOf s = rs ∧ (s.rip = t.endRip → σ = .skip) :=
  Silmaril.Proofs.X86.Concurrency.Cir.TvCfg.tvCfg_steps hc h0 hr hL

/-- **The cores a run reaches sit at entries**: every core an x86 run from the
code's start reaches has `rip` at the offset of some certificate entry (the `rip` field of the
simulation invariant). -/
theorem tvCfg_reach {t : XThread} {c : GCert} (hc : tvCfg t c = true) {s0 s : State}
    (h0 : s0.rip = t.base) {acc : List (List XAct)} (hr : XRun t s0 acc s) :
    ∃ e ∈ c.entries, s.rip = t.base + BitVec.ofNat 64 e.off :=
  Silmaril.Proofs.X86.Concurrency.Cir.TvCfg.tvCfg_reach hc h0 hr

/-- The Boolean statement equality is equality. -/
theorem sbeq_eq {s t : Stmt} (h : sbeq s t = true) : s = t :=
  Silmaril.Proofs.X86.Concurrency.Cir.TvCfg.sbeq_eq h

/-- The checker reads only the code bytes. -/
theorem tvCfg_code {t t' : XThread} (h : t.code = t'.code) (c : GCert) :
    tvCfg t c = tvCfg t' c := by
  obtain ⟨b, code, r, i⟩ := t
  obtain ⟨b', code', r', i'⟩ := t'
  simp only at h
  subst h
  rfl

/-- **Each x86 step replays on `Atomic9.step`** on every memory with the thread's regions and
code that answers the step's reads (`stepSym_sound`). -/
theorem XStep.replays {t : XThread} {s : State} {acts : List XAct} {s' : State}
    (h : XStep t s acts s') (m : Silmaril.Process.Memory) (hR : m.regions = t.regions)
    (hl : Silmaril.X86.Ext.Loaded m t.base t.code)
    (hans : Silmaril.X86.Litmus.Answers m acts) :
    ∃ m', Silmaril.X86.Atomic9.step ⟨s, m⟩ = some ⟨s', m'⟩ ∧
      Silmaril.X86.Litmus.applyWrites m acts = some m' := by
  obtain ⟨dom, outs, hs, ho⟩ := h
  exact Silmaril.X86.Litmus.stepSym_sound hs ho m hR hl hans

end Silmaril.X86.Concurrency.Cir.TvCfg
