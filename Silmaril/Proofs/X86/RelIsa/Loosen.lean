module

public import Silmaril.X86.RelIsa.Loosen.Defs
public import Silmaril.X86.RelIsa.Thms

/-!
# Proofs: loosening a deterministic machine (the free bridge)

* `le_loosen`: the machine refines its loosening (non-vacuity witness);
* `loosen_mono`: loosening is antitone in the predicate;
* `must_loosen_of_runsIn`, `must_loosen_of_reaches`: **every terminating run of `I` is a
  `Must` run of its loosening** (determinism is used only in that `I.step s` is a function);
* `loosen_le_of_refines`: a conservative extension refines after loosening (the order flips).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.RelIsa.Loosen

open Silmaril.X86.RelIsa
open Silmaril.X86.SegVC (Isa)
open Silmaril.Machine.Execution (run Reaches)
open Silmaril.X86.FnContract (RunsIn)

variable {σ : Type} {I J : Isa σ} {P P' R Q : σ → Prop} {s : σ}

theorem loosen_step_of_step {t : σ} {r : Res σ} (hp : P s) (he : I.step s = some t)
    (hl : I.live s) : (loosen I P).step s r ↔ r = .ok t := by
  constructor
  · intro hs; exact hs.1 t hp he
  · rintro rfl; exact ⟨fun u _ hu => by rw [he] at hu; cases hu; rfl,
      fun u e => by cases e; exact I.live_step hl he⟩

theorem le_loosen : Le (ofIsa I) (loosen I P) := by
  refine ⟨rfl, fun {s r} hl hs => ⟨fun t _ he => ?_, fun t e => ?_⟩⟩
  · cases r with
    | ok u => rw [ofIsa_step_ok, he] at hs; cases hs; rfl
    | stop => rw [ofIsa_step_stop, he] at hs; cases hs
  · subst e
    exact I.live_step hl (ofIsa_step_ok.1 hs)

theorem must_loosen_of_runsIn {t : σ} (h : RunsIn I (fun m => R m ∧ P m) s t) (hq : Q t) :
    Must (loosen I P) R Q s := by
  induction h with
  | refl => exact .done hq
  | step hrp he _ ih =>
    refine .step hrp.1 (fun hs => ?_) (fun u hu => ?_)
    · cases hs.1 _ hrp.2 he
    · cases hu.1 _ hrp.2 he; exact ih hq

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

theorem loosen_le_of_refines (hv : Views.ofIsa I = Views.ofIsa J)
    (h : ∀ {s t}, I.step s = some t → J.step s = some t) : Le (loosen J P) (loosen I P) := by
  have hlive : I.live = J.live := congrArg Views.live hv
  refine ⟨hv.symm, fun _ hs => ⟨fun t hp he => hs.1 t hp (h he), fun t e => ?_⟩⟩
  rw [hlive]; exact hs.2 t e

end Silmaril.Proofs.X86.RelIsa.Loosen
