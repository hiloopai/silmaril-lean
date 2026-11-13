module

public import Silmaril.X86.Litmus.Domain.Defs
public import Silmaril.X86.Litmus.Extract.Thms
import Silmaril.Proofs.X86.Litmus.Domain

/-!
# How extracted traces depend on the value domain: what is proved

PROVED (standard axioms; proofs in `Silmaril/Proofs/X86/Litmus/Domain.lean`), for any two
value domains `D` and `D'` over which extraction of a thread succeeds:

* `extract_restrict`: a trace over `D'` whose reads all lie in `D` is a trace over `D`;
* `extract_prefix`: the first `k` steps of a trace over `D'`, if their reads lie in a nonempty
  `D`, are the first `k` steps of some trace over `D`;
* `extract_ne_nil`: over a nonempty domain the trace set is nonempty;
* `straight_events`, `stepSym_post` (exported): a straight-line form's events depend only on
  `rip`, and every branch of its symbolic step falls through;
* `extract_skel`: on **straight-line code** (`Thread.skel` succeeds) every trace over every
  domain has the code's skeleton: step by step, its events are the skeleton's.
-/

@[expose] public section

namespace Silmaril.X86.Litmus

/-- **Restriction to a smaller domain.** -/
theorem extract_restrict {t : Thread} {D D' : List Nat} {fuel : Nat} {trs trs' : List Trace}
    (h : extract t D fuel = some trs) (h' : extract t D' fuel = some trs') {tr : Trace}
    (htr : tr ∈ trs') (hr : ∀ r ∈ tr.steps, r.ReadsIn D) : tr ∈ trs :=
  Silmaril.Proofs.X86.Litmus.explore_restrict fuel h h' htr hr

/-- **Prefix extension into a smaller domain.** -/
theorem extract_prefix {t : Thread} {D D' : List Nat} (hD : D ≠ []) {fuel : Nat}
    {trs trs' : List Trace} (h : extract t D fuel = some trs) (h' : extract t D' fuel = some trs')
    {tr : Trace} (htr : tr ∈ trs') (k : Nat) (hr : ∀ r ∈ tr.steps.take k, r.ReadsIn D) :
    ∃ tr₂ ∈ trs, tr₂.steps.take k = tr.steps.take k :=
  Silmaril.Proofs.X86.Litmus.explore_prefix hD fuel h h' htr k hr

/-- Over a nonempty domain the trace set is nonempty. -/
theorem extract_ne_nil {t : Thread} {D : List Nat} (hD : D ≠ []) {fuel : Nat}
    {trs : List Trace} (h : extract t D fuel = some trs) : trs ≠ [] :=
  Silmaril.Proofs.X86.Litmus.explore_ne_nil hD fuel h

/-- **On straight-line code every trace has the skeleton.** -/
theorem extract_skel {t : Thread} {D : List Nat} {fuel f : Nat} {trs : List Trace}
    {S : List (List MemEvent.Event)} (h : extract t D fuel = some trs) (hS : t.skel f = some S) :
    ∀ tr ∈ trs, tr.steps.map (fun r => r.acts.map Act.ev) = S :=
  Silmaril.Proofs.X86.Litmus.explore_skel fuel h hS

/-- The events of a straight-line form depend only on `rip` (exported). -/
theorem straight_events {i : Atomic9.Instr} (hi : straightForm i = true)
    {s s' : Silmaril.X86.State} (hs : s.rip = s'.rip) (n : Nat) :
    MemEvent.atomic9Accesses i s n = MemEvent.atomic9Accesses i s' n :=
  Silmaril.Proofs.X86.Litmus.straight_events hi hs n

/-- Every branch of the symbolic step of a straight-line form falls through (exported). -/
theorem stepSym_post {t : Thread} {D : List Nat} {s : Silmaril.X86.State}
    {outs : List (List Act × Silmaril.X86.State)} (h : stepSym t D s = some outs)
    {i : Atomic9.Instr} {n : Nat} (hf : t.fetch s = some (i, n)) (hi : straightForm i = true)
    {o : List Act × Silmaril.X86.State} (ho : o ∈ outs) : o.2.rip = s.rip + BitVec.ofNat 64 n :=
  Silmaril.Proofs.X86.Litmus.stepSym_post h hf hi ho

end Silmaril.X86.Litmus
