module

public import Silmaril.Machine.X86.FnContract.Defs

/-!
# First-return contracts: generic proofs

Generic over the segment-VC machine `I`:

* `runsIn_mono`, `runsIn_trans`, `runsIn_reaches`, `runsIn_live`, `runsIn_map`: runs inside a
  predicate;
* `totalIn_mono`, `TotalIn.total`: a `TotalIn` proof gives `Spec.Total`;
* `returned_of_result`: a call result is a returned state;
* `strict_of_totalIn`: a `TotalIn` whose run predicate excludes returned states is strict;
* `Strict.firstReturn`: a strict spec's result is the first return;
* `firstReturn_unique`: on any machine (`Isa.step` is a function) the first return is unique;
* `not_returned_of_below`, `not_returned_of_inCode`: the two ways a run predicate excludes
  the entry's return (stack depth; code region with the return address outside).
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.X86.FnContract

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.SegVC (Isa)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.Machine.X86
open Silmaril.Machine.X86.FnContract

variable {σ : Type} {I : Isa σ}

theorem runsIn_mono {P Q : σ → Prop} (h : ∀ m, P m → Q m) {s t : σ} (r : RunsIn I P s t) :
    RunsIn I Q s t := by
  induction r with
  | refl m => exact .refl m
  | step hp hs _ ih => exact .step (h _ hp) hs ih

theorem runsIn_trans {P : σ → Prop} {s t u : σ} (r₁ : RunsIn I P s t) (r₂ : RunsIn I P t u) :
    RunsIn I P s u := by
  induction r₁ with
  | refl _ => exact r₂
  | step hp hs _ ih => exact .step hp hs (ih r₂)

theorem runsIn_reaches {P : σ → Prop} {s t : σ} (r : RunsIn I P s t) : Reaches I.step s t := by
  induction r with
  | refl m => exact Reaches.refl _ m
  | step _ hs _ ih => exact (Silmaril.X86.SegVC.reaches_head (I := I) hs).trans ih

theorem runsIn_live {P : σ → Prop} {s t : σ} (r : RunsIn I P s t) (h : I.live s) : I.live t := by
  induction r with
  | refl _ => exact h
  | step _ hs _ ih => exact ih (I.live_step h hs)

/-- Every run of `n` steps is a run inside the trivial predicate. -/
theorem runsIn_of_run : ∀ (n : Nat) {s t : σ},
    Silmaril.Machine.Execution.run I.step n s = some t → RunsIn I (fun _ => True) s t
  | 0, s, t, h => by
    simp only [Silmaril.Machine.Execution.run, Option.some.injEq] at h
    subst h; exact .refl _
  | n + 1, s, t, h => by
    simp only [Silmaril.Machine.Execution.run] at h
    cases hs : I.step s with
    | none => rw [hs] at h; cases h
    | some s' =>
      rw [hs] at h
      exact .step trivial hs (runsIn_of_run n h)

/-- Runs carry over to a machine with more steps (same states). -/
theorem runsIn_map {J : Isa σ} (hJ : ∀ {s s'}, I.step s = some s' → J.step s = some s')
    {P : σ → Prop} {s t : σ} (r : RunsIn I P s t) : RunsIn J P s t := by
  induction r with
  | refl m => exact .refl m
  | step hp hs _ ih => exact .step hp (hJ hs) ih

/-- On a deterministic machine, two runs that stop at the first state outside `P` agree. -/
theorem runsIn_unique {P : σ → Prop} {s t t' : σ} (r : RunsIn I P s t) (ht : ¬ P t)
    (r' : RunsIn I P s t') (ht' : ¬ P t') : t = t' := by
  induction r generalizing t' with
  | refl m =>
    cases r' with
    | refl => rfl
    | step hp _ _ => exact absurd hp ht
  | step hp hs _ ih =>
    cases r' with
    | refl => exact absurd hp ht'
    | step _ hs' r'' =>
      rw [hs] at hs'
      cases hs'
      exact ih ht r'' ht'

theorem firstReturn_unique {s t t' : σ} (h : FirstReturn I s t) (h' : FirstReturn I s t') :
    t = t' :=
  runsIn_unique h.1 (not_not_intro h.2) h'.1 (not_not_intro h'.2)

theorem totalIn_mono {S : Spec σ} {P Q : σ → σ → Prop} (h : ∀ s m, P s m → Q s m)
    (hP : S.TotalIn I P) : S.TotalIn I Q := fun s hl ha he => by
  obtain ⟨t, r, res⟩ := hP s hl ha he
  exact ⟨t, runsIn_mono (h s) r, res⟩

theorem TotalIn.total {S : Spec σ} {P : σ → σ → Prop} (h : S.TotalIn I P) : S.Total I :=
  fun s hl ha he => by
    obtain ⟨t, r, res⟩ := h s hl ha he
    exact ⟨t, runsIn_reaches r, res⟩

theorem returned_of_result {S : Spec σ} {s t : σ} (h : S.Result I s t) : Returned I s t :=
  ⟨h.abi.pc, h.abi.stack⟩

theorem strict_of_totalIn {S : Spec σ} {P : σ → σ → Prop}
    (hP : ∀ s m, P s m → ¬ Returned I s m) (h : S.TotalIn I P) : S.Strict I :=
  totalIn_mono hP h

theorem Strict.firstReturn {S : Spec σ} (h : S.Strict I) {s : σ} (hl : I.live s)
    (ha : AbiEntry (I.core s) (I.mem s)) (he : S.entry s) :
    ∃ t, FirstReturn I s t ∧ S.Result I s t := by
  obtain ⟨t, r, res⟩ := h s hl ha he
  exact ⟨t, ⟨r, returned_of_result res⟩, res⟩

theorem not_returned_of_below {s m : σ} (hb : Below I s m)
    (hw : ((I.core s).read .rsp).toNat + 8 < 2 ^ 64) : ¬ Returned I s m := by
  rintro ⟨-, hsp⟩
  unfold Below at hb
  rw [hsp, BitVec.toNat_add] at hb
  simp only [BitVec.toNat_ofNat] at hb
  omega

theorem not_returned_of_inCode {base : Word} {len : Nat} {s m : σ}
    (hout : RetOutside I base len s) (hin : InCode I base len m) : ¬ Returned I s m := by
  rintro ⟨hrip, -⟩
  obtain ⟨o, ho, hm⟩ := hin
  exact hout o ho (hrip.symm.trans hm)

end Silmaril.Proofs.Machine.X86.FnContract
