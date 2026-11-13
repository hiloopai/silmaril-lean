module

public import Silmaril.X86.Litmus.WeakExtract.Defs
public import Silmaril.X86.Litmus.Extract.Thms
public import Silmaril.X86.Weak9.Thms
import Silmaril.Proofs.X86.Litmus.WeakExtract

/-!
# Litmus event extraction over `Weak9`: what is proved

PROVED (standard axioms; proofs in `Silmaril/Proofs/X86/Litmus/WeakExtract.lean`):

* `wextract_sound`: **every trace extracted over `Weak9` replays** on `Weak9.step`
  (`WReplay`): at each step, on every memory with the thread's regions and code that answers
  the step's reads, one `Weak9` step reaches the trace's next core and writes exactly the
  trace's bytes. This covers `movnti` (non-temporal stores), `rep stosb`, and `Str9`'s
  `movsb`/`rep movsq`/`rep stosq`, one `rep` element per step.
* `wstepSym_sound`: the one-step form.

The flavours (`nonTemporal` for `movnti`, `string` for the string forms) are attached by the
extractor from the decoded form; they have no sequential meaning and are read only by the
axiomatic models (`annOf`).
-/

@[expose] public section

namespace Silmaril.X86.Litmus

open Silmaril.X86 (State)
open Silmaril.Process (Memory)

/-- **Extraction over `Weak9` is sound.** -/
theorem wextract_sound {t : Thread} {dom : List Nat} {fuel : Nat} {trs : List Trace}
    (h : wextract t dom fuel = some trs) : ∀ tr ∈ trs, WReplay t t.init tr.steps tr.final :=
  Silmaril.Proofs.X86.Litmus.wextract_sound h

/-- **One symbolic step over `Weak9` is sound.** -/
theorem wstepSym_sound {t : Thread} {dom : List Nat} {s : State}
    {outs : List (List Act × State)} (h : wstepSym t dom s = some outs) {o : List Act × State}
    (ho : o ∈ outs) (m : Memory) (hR : m.regions = t.regions)
    (hl : Silmaril.X86.Ext.Loaded m t.base t.code) (hans : Answers m o.1) :
    ∃ m', Weak9.step ⟨s, m⟩ = some ⟨o.2, m'⟩ ∧ applyWrites m o.1 = some m' :=
  Silmaril.Proofs.X86.Litmus.wstepSym_sound h ho m hR hl hans

end Silmaril.X86.Litmus
