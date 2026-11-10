module

public import Silmaril.X86.FnContract.Defs
public import Silmaril.X86.Extends.Thms

/-!
# First-return contracts: proofs

Proofs behind the first-return part of `Silmaril.X86.FnContract.Thms`, generic over the
segment-VC machine `I`:

* `runsIn_mono`, `runsIn_trans`, `runsIn_reaches`, `runsIn_live`, `runsIn_of_run`,
  `runsIn_map`: runs inside a predicate;
* `runsIn_unique`, `firstReturn_unique`: the machine is a function, so the first exit from a
  predicate is unique;
* `totalIn_mono`, `totalIn_total`, `returned_of_result`, `strict_of_totalIn`,
  `strict_firstReturn`, `not_returned_of_below`, `not_returned_of_inCode`;
* along an extension `E : I.Extends J`: `runsIn_lift`, `result_lift`, `totalIn_lift`, and
  `returned_iff`, `below_iff` (both read only the core and memory, which are the view's).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.FnContract

open Silmaril.X86 (State Word)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.FnContract
open Silmaril.Machine.Execution (Reaches)

variable {σ τ : Type} {I : Isa σ}

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

theorem totalIn_total {S : Spec σ} {P : σ → σ → Prop} (h : S.TotalIn I P) : S.Total I :=
  fun s hl ha he => by
    obtain ⟨t, r, res⟩ := h s hl ha he
    exact ⟨t, runsIn_reaches r, res⟩

theorem total_totalIn {S : Spec σ} (h : S.Total I) : S.TotalIn I fun _ _ => True :=
  fun s hl ha he => by
    obtain ⟨t, ⟨n, hn⟩, res⟩ := h s hl ha he
    exact ⟨t, runsIn_of_run n hn, res⟩

theorem returned_of_result {S : Spec σ} {s t : σ} (h : S.Result I s t) : Returned I s t :=
  ⟨h.abi.pc, h.abi.stack⟩

theorem strict_of_totalIn {S : Spec σ} {P : σ → σ → Prop}
    (hP : ∀ s m, P s m → ¬ Returned I s m) (h : S.TotalIn I P) : S.Strict I :=
  totalIn_mono hP h

theorem strict_firstReturn {S : Spec σ} (h : S.Strict I) {s : σ} (hl : I.live s)
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

/-! ## Along a machine extension -/

theorem runsIn_lift {J : Isa τ} (E : I.Extends J) {P : σ → Prop} {s t : σ}
    (r : RunsIn I P s t) : ∀ x, E.view x = s → RunsIn J (fun y => P (E.view y)) x (E.put x t) := by
  induction r with
  | refl m =>
    intro x hx
    subst hx
    rw [E.put_view]
    exact .refl x
  | @step _ s' _ hp hs _ ih =>
    intro x hx
    subst hx
    have h := ih (E.put x s') (E.view_put _ _)
    rw [E.put_put] at h
    exact .step hp (E.step hs) h

theorem returned_iff {J : Isa τ} (E : I.Extends J) (x y : τ) :
    Returned J x y ↔ Returned I (E.view x) (E.view y) := by
  simp only [Returned, E.core, E.mem]

theorem below_iff {J : Isa τ} (E : I.Extends J) (x y : τ) :
    Below J x y ↔ Below I (E.view x) (E.view y) := by
  simp only [Below, E.core]

theorem result_lift {J : Isa τ} (E : I.Extends J) {S : Spec σ} {x : τ} {t : σ}
    (res : S.Result I (E.view x) t) : (S.comap E.view).Result J x (E.put x t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [E.upd, E.core, E.mem, E.view_put, res.silent]
  · rw [E.core, E.mem, E.core, E.view_put]; exact res.abi
  · rw [E.mem, E.mem, E.view_put]; exact res.frame
  · show S.post (E.view x) (E.view (E.put x t)); rw [E.view_put]; exact res.post

theorem totalIn_lift {J : Isa τ} (E : I.Extends J) {S : Spec σ} {P : σ → σ → Prop}
    (h : S.TotalIn I P) :
    (S.comap E.view).TotalIn J fun x y => P (E.view x) (E.view y) := by
  intro x hl ha he
  rw [E.core, E.mem] at ha
  obtain ⟨t, r, res⟩ := h (E.view x) (E.live x hl) ha he
  exact ⟨E.put x t, runsIn_lift E r x rfl, result_lift E res⟩

end Silmaril.Proofs.X86.FnContract
