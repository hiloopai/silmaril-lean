module

public import Silmaril.X86.RelIsa.Loosen.Defs
public import Silmaril.X86.RelIsa.Thms
import Silmaril.Proofs.X86.RelIsa.Loosen

/-!
# Loosening: what is proved

Proofs of more than a few lines are in `Silmaril/Proofs/X86/RelIsa/Loosen.lean`.

* `loosen_step_iff`, `loosen_toViews`, `loosen_step_of_step`: the steps of `loosen I P`; where
  `P` holds and `I` steps, exactly that step (so the loose machine is not `⊤` there);
* `le_loosen`: **the machine refines its loosening**;
* `loosen_mono`: loosening is antitone in the predicate;
* `must_loosen_of_runsIn`, `must_loosen_of_reaches`: **every terminating run of `I` is a
  `Must` run of its loosening** (the free bridge from deterministic to demonic proofs);
* `loosen_le_of_refines`: a conservative extension refines after loosening (the order
  flips); `loosen_open9_le_open`: every proof on the loosened `Ext8` open machine transfers
  to the loosened `Ext9` one, by `Must.of_le`.
-/

@[expose] public section

namespace Silmaril.X86.RelIsa

open Silmaril.X86 (MState)
open Silmaril.X86.SegVC (Isa)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.X86.FnContract (RunsIn)

variable {σ : Type} {I J : Isa σ} {P P' R Q : σ → Prop} {s : σ}

theorem loosen_step_iff {r : Res σ} :
    (loosen I P).step s r ↔
      (∀ t, P s → I.step s = some t → r = .ok t) ∧ ∀ t, r = .ok t → I.live t := Iff.rfl

@[simp] theorem loosen_toViews : (loosen I P).toViews = Views.ofIsa I := rfl

/-- **Where `P` holds and `I` steps, the loosening is exactly that step** (non-vacuity: the
loose machine is not `⊤` there; in particular it cannot stop). -/
theorem loosen_step_of_step {t : σ} {r : Res σ} (hp : P s) (he : I.step s = some t)
    (hl : I.live s) : (loosen I P).step s r ↔ r = .ok t :=
  Proofs.X86.RelIsa.Loosen.loosen_step_of_step hp he hl

/-- **The machine refines its loosening.** -/
theorem le_loosen : Le (ofIsa I) (loosen I P) :=
  Proofs.X86.RelIsa.Loosen.le_loosen

/-- **Loosening is antitone in the predicate**: constraining more states gives fewer
behaviours. -/
theorem loosen_mono (h : ∀ s, P s → P' s) : Le (loosen I P') (loosen I P) :=
  ⟨rfl, fun _ hs => ⟨fun t hp he => hs.1 t (h _ hp) he, hs.2⟩⟩

/-- **The free bridge.** A terminating run of `I` whose every step is taken from a state
satisfying `R` and `P` is a `Must` run of `loosen I P`: along it, `loosen I P` has exactly
the step the run took. -/
theorem must_loosen_of_runsIn {t : σ} (h : RunsIn I (fun m => R m ∧ P m) s t) (hq : Q t) :
    Must (loosen I P) R Q s :=
  Proofs.X86.RelIsa.Loosen.must_loosen_of_runsIn h hq

/-- A reachable state is a `Must` target of the everywhere-loosened machine. -/
theorem must_loosen_of_reaches {t : σ} (h : Reaches I.step s t) (hq : Q t) :
    Must (loosen I (fun _ => True)) (fun _ => True) Q s :=
  Proofs.X86.RelIsa.Loosen.must_loosen_of_reaches h hq

/-- **Conservative extensions refine after loosening.** If every `I` step is a `J` step
(and the views agree), `loosen J P` has fewer behaviours than `loosen I P`. -/
theorem loosen_le_of_refines (hv : Views.ofIsa I = Views.ofIsa J)
    (h : ∀ {s t}, I.step s = some t → J.step s = some t) : Le (loosen J P) (loosen I P) :=
  Proofs.X86.RelIsa.Loosen.loosen_le_of_refines hv h

/-- The views of `Open.isa` are the `MState` views. -/
theorem views_ofIsa_open : Views.ofIsa Silmaril.X86.Open.isa = Views.mstate := rfl

/-- **Every proof on the loosened `Ext8` open machine transfers to the loosened `Ext9` one**
(and so to `JumpTable.isa = Open9.isa`), by `Must.of_le`. -/
theorem loosen_open9_le_open {P : MState → Prop} :
    Le (loosen Silmaril.X86.Open9.isa P) (loosen Silmaril.X86.Open.isa P) :=
  loosen_le_of_refines rfl Silmaril.X86.Open9.step_of_open

end Silmaril.X86.RelIsa
