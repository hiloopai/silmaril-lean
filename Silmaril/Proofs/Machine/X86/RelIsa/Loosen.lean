module

public import Silmaril.Proofs.Machine.X86.RelIsa.Must

/-!
# Proofs: loosening a deterministic machine (the free bridge)

Names are in `Silmaril.Machine.X86.RelIsa`, so that the header `RelIsa/Thms.lean` exports them.

* `le_loosen`: the machine refines its loosening (non-vacuity witness);
* `loosen_mono`: loosening is antitone in the predicate;
* `must_loosen_of_runsIn`, `must_loosen_of_reaches`: **every terminating run of `I` is a
  `Must` run of its loosening** (determinism is used only in that `I.step s` is a function);
* `loosen_le_of_refines`, `loosen_le_of_safeRefines`: a conservative extension refines after
  loosening (the demonic reading of `Safe.ExtendsOpen`; the order flips).
-/

@[expose] public section

namespace Silmaril.Machine.X86.RelIsa

open Silmaril.X86 (MState)
open Silmaril.X86.SegVC (Isa)
open Silmaril.Machine.Execution (run Reaches)
open Silmaril.Machine.X86.FnContract (RunsIn)

variable {σ : Type} {I J : Isa σ} {P P' R Q : σ → Prop} {s : σ}

theorem loosen_step_iff {r : Res σ} :
    (loosen I P).step s r ↔
      (∀ t, P s → I.step s = some t → r = .ok t) ∧ ∀ t, r = .ok t → I.live t := Iff.rfl

@[simp] theorem loosen_toViews : (loosen I P).toViews = Views.ofIsa I := rfl
@[simp] theorem ofIsa_toViews : (ofIsa I).toViews = Views.ofIsa I := rfl

/-- **Where `P` holds and `I` steps, the loosening is exactly that step** (non-vacuity: the
loose machine is not `⊤` there; in particular it cannot stop). -/
theorem loosen_step_of_step {t : σ} {r : Res σ} (hp : P s) (he : I.step s = some t)
    (hl : I.live s) : (loosen I P).step s r ↔ r = .ok t := by
  constructor
  · intro hs; exact hs.1 t hp he
  · rintro rfl; exact ⟨fun u _ hu => by rw [he] at hu; cases hu; rfl,
      fun u e => by cases e; exact I.live_step hl he⟩

/-- **The machine refines its loosening.** -/
theorem le_loosen : Le (ofIsa I) (loosen I P) := by
  refine ⟨rfl, fun {s r} hl hs => ⟨fun t _ he => ?_, fun t e => ?_⟩⟩
  · cases r with
    | ok u => rw [ofIsa_step_ok, he] at hs; cases hs; rfl
    | stop => rw [ofIsa_step_stop, he] at hs; cases hs
  · subst e
    exact I.live_step hl (ofIsa_step_ok.1 hs)

/-- **Loosening is antitone in the predicate**: constraining more states gives fewer
behaviours. -/
theorem loosen_mono (h : ∀ s, P s → P' s) : Le (loosen I P') (loosen I P) :=
  ⟨rfl, fun _ hs => ⟨fun t hp he => hs.1 t (h _ hp) he, hs.2⟩⟩

/-- **The free bridge.** A terminating run of `I` whose every step is taken from a state
satisfying `R` and `P` is a `Must` run of `loosen I P`: along it, `loosen I P` has exactly
the step the run took. -/
theorem must_loosen_of_runsIn {t : σ} (h : RunsIn I (fun m => R m ∧ P m) s t) (hq : Q t) :
    Must (loosen I P) R Q s := by
  induction h with
  | refl => exact .done hq
  | step hrp he _ ih =>
    refine .step hrp.1 (fun hs => ?_) (fun u hu => ?_)
    · cases hs.1 _ hrp.2 he
    · cases hu.1 _ hrp.2 he; exact ih hq

/-- A reachable state is a `Must` target of the everywhere-loosened machine. -/
theorem must_loosen_of_reaches {t : σ} (h : Reaches I.step s t) (hq : Q t) :
    Must (loosen I (fun _ => True)) (fun _ => True) Q s := by
  obtain ⟨n, hn⟩ := h
  induction n generalizing s with
  | zero => cases hn; exact .done hq
  | succ n ih =>
    rw [run] at hn
    cases e : I.step s with
    | none => rw [e] at hn; cases hn
    | some u =>
      rw [e] at hn
      refine .step trivial (fun hs => ?_) (fun v hv => ?_)
      · cases hs.1 _ trivial e
      · cases hv.1 _ trivial e; exact ih hn

/-- **Conservative extensions refine after loosening.** If every `I` step is a `J` step
(and the views agree), `loosen J P` has fewer behaviours than `loosen I P`. -/
theorem loosen_le_of_refines (hv : Views.ofIsa I = Views.ofIsa J)
    (h : ∀ {s t}, I.step s = some t → J.step s = some t) : Le (loosen J P) (loosen I P) := by
  have hlive : I.live = J.live := congrArg Views.live hv
  refine ⟨hv.symm, fun _ hs => ⟨fun t hp he => hs.1 t hp (h he), fun t e => ?_⟩⟩
  rw [hlive]; exact hs.2 t e

/-- `loosen_le_of_refines` for `MState` machines related by `Safe.Refines`. -/
theorem loosen_le_of_safeRefines {I J : Isa MState} {P : MState → Prop}
    (hv : Views.ofIsa I = Views.ofIsa J) (h : Safe.Refines I.step J.step) :
    Le (loosen J P) (loosen I P) :=
  loosen_le_of_refines hv h

end Silmaril.Machine.X86.RelIsa
