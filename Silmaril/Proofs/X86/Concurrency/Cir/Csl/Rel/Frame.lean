module

public import Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.Buf

/-!
# CSL with release stores: the frame rule and the pending flag before a draining label

`safeR_frame`: a thread safe on `h` stays safe next to a disjoint frame it never
touches. `safeR_flag`: code whose first labelled step drains (`DF`) is safe whatever its starting
flag, since the draining step ends any pending window.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel

open Silmaril.X86.Concurrency.Cir (Stmt Regs Expr Lab truthy)
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Rel

section F
variable {I : GProp} {Q : Bool → Regs → Heap → Heap → Prop}

theorem updH_union (h F : Heap) (l : Lab) :
    l.updH (Heap.union h F) = Heap.union (l.updH h) F := by
  funext a; simp only [updH_apply, union_apply, Option.or_assoc]

theorem oblig_mono {e : Ent} {hR gR H G H' G' : Heap} (dH : Dom H H') (dG : Dom G G')
    (ob : Oblig I e hR gR H G) : Oblig I e hR gR H' G' :=
  fun hI gI i d1 d2 => ob hI gI i (disj_of_dom d1 dH (dom_refl _)) (disj_of_dom d2 dG (dom_refl _))

/-- **The frame rule**: a frame `hF` disjoint from the thread's heap is never touched and is
still there at the end. -/
theorem safeR_frame {p : Bool} {s : Stmt} {rs : Regs} {h g hF : Heap}
    (H : SafeR I Q p s rs h g) (hd : Heap.Disjoint h hF) :
    SafeR I (fun p rs h' g' => ∃ h1, Q p rs h1 g' ∧ Heap.Disjoint h1 hF ∧
      h' = Heap.union h1 hF) p s rs (Heap.union h hF) g := by
  refine safeR_coind (fun p s rs H g => ∃ h, SafeR I Q p s rs h g ∧ Heap.Disjoint h hF ∧
    H = Heap.union h hF) ?_ ⟨h, H, hd, rfl⟩
  rintro p s rs _ g ⟨h, H, hd, rfl⟩
  have S := safeR_unfold H
  refine ⟨fun e => ⟨h, S.1 e, hd, rfl⟩, fun s' rs' st => Or.inl ⟨h, S.2.1 _ _ st, hd, rfl⟩,
    fun l s' rs' st => ?_⟩
  obtain ⟨hm, H⟩ := S.2.2 l s' rs' st
  refine ⟨hm, ?_⟩
  rcases H with ⟨tc, k⟩ | ⟨ena, pc, sh⟩ |
    ⟨m, fl, a, sz, v, rfl, hmn, h', hR, g', gR, d1, eh, d2, eg, k, ob⟩
  · -- local
    refine Or.inl ⟨fun a ta => dom_union_left _ _ a (tc a ta), fun ok => ?_⟩
    have ok' : l.okH h := by
      intro q hq
      have := ok q hq
      rw [union_apply] at this
      obtain ⟨u, eu⟩ := Option.isSome_iff_exists.mp (tc _ (reads_touch hq))
      rw [eu] at this ⊢; exact this
    refine Or.inl ⟨l.updH h, k ok', ?_, updH_union h hF l⟩
    refine disj_of_dom hd (fun a e => ?_) (dom_refl _)
    rw [updH_apply, or_isSome] at e
    cases ew : (l.wval a).isSome
    · rw [ew, Bool.false_or] at e; exact e
    · exact tc a (wval_touch ew)
  · -- shared
    refine Or.inr (Or.inl ⟨ena, pc, fun hI gI hIi dI dgI => ?_⟩)
    have dhI : Heap.Disjoint h hI := disj_of_dom dI (dom_union_left _ _) (dom_refl _)
    have dFI : Heap.Disjoint hF hI := disj_of_dom dI (dom_union_right _ _) (dom_refl _)
    obtain ⟨c1, c2, c3⟩ := sh hI gI hIi dhI dgI
    refine ⟨fun a ta => ?_, fun ed a ew => dom_union_left _ _ a (c2 ed a ew), fun ok => ?_⟩
    · have := c1 a ta
      rw [union_isSome] at this ⊢; rw [union_isSome]
      cases e1 : (h a).isSome <;> cases e2 : (hI a).isSome <;> simp_all
    · have ok' : l.okH (Heap.union h hI) := by
        intro q hq
        have t := c1 _ (reads_touch hq)
        have := ok q hq
        rw [union_apply, union_apply] at this; rw [union_apply]
        rw [union_isSome] at t
        cases e1 : h q.1 with
        | some w => rw [e1] at this; simpa using this
        | none =>
          simp only [e1, Option.isSome_none, Bool.false_or] at t
          simp only [e1, Option.none_or, disj_none (disjoint_symm dFI) t] at this
          simpa using this
      obtain ⟨h', hI', g', gI', y1, y2, y3, y4, y5, y6, y7⟩ := c3 ok'
      have pt : ∀ a, (h' a).or (hI' a) = (l.wval a).or ((h a).or (hI a)) := fun a => by
        have := congrFun y2 a; rw [union_apply, updH_apply, union_apply] at this; exact this
      have tw : ∀ a, (l.wval a).isSome → ((h a).or (hI a)).isSome := fun a e => by
        have := c1 a (wval_touch e); rw [union_apply] at this; exact this
      have outF : ∀ a, (hF a).isSome → h' a = none ∧ hI' a = none ∧ l.wval a = none ∧
          h a = none ∧ hI a = none := fun a ea => by
        have e4 : h a = none := none_of_disj hd ea
        have e5 : hI a = none := disj_none dFI ea
        have e6 : l.wval a = none := by
          cases e : l.wval a with
          | none => rfl
          | some _ => have := tw a (by rw [e]; rfl); rw [e4, e5] at this; cases this
        have p := pt a; rw [e4, e5, e6] at p
        cases e1 : h' a <;> cases e2 : hI' a <;> simp_all
      have dF' : Heap.Disjoint h' hF := fun a => by
        cases e3 : hF a with
        | none => exact Or.inr rfl
        | some _ => exact Or.inl (outF a (by rw [e3]; rfl)).1
      refine ⟨Heap.union h' hF, hI', g', gI', fun a => ?_, ?_, y3, y4, y5,
        Or.inl ⟨h', y6, dF', rfl⟩, fun ed a ea => ?_⟩
      · rw [union_apply]
        cases e3 : hF a with
        | none => rw [Option.or_none]; exact y1 a
        | some _ => exact Or.inr (outF a (by rw [e3]; rfl)).2.1
      · funext a
        rw [union_apply, union_apply, updH_apply, union_apply, union_apply]
        cases e3 : hF a with
        | none =>
          simp only [Option.or_none]; exact pt a
        | some _ =>
          obtain ⟨e1, e2, e6, e4, e5⟩ := outF a (by rw [e3]; rfl)
          simp [e4, e5, e1, e2, e6]
      · rw [union_isSome] at ea ⊢
        cases e3 : (hF a).isSome
        · simp only [e3, Bool.or_false] at ea ⊢; exact y7 ed a ea
        · simp
  · -- release
    have dRF : Heap.Disjoint hR hF := disj_of_dom hd (by rw [eh]; exact dom_union_right _ _)
      (dom_refl _)
    have dh'F : Heap.Disjoint h' hF := disj_of_dom hd (by rw [eh]; exact dom_union_left _ _)
      (dom_refl _)
    refine Or.inr (Or.inr ⟨m, fl, a, sz, v, rfl, hmn, Heap.union h' hF, hR, g', gR,
      disj_union_left d1 (disjoint_symm dRF), ?_, d2, eg, Or.inl ⟨h', k, dh'F, rfl⟩,
      oblig_mono (dom_union_left _ _) (dom_refl _) ob⟩)
    rw [eh]
    funext x
    simp only [union_apply]
    rcases dRF x with e | e <;> simp [e]

end F

/-! ## The pending flag before a draining label -/

theorem labOkR_drains {I : GProp} {K : Bool → Heap → Heap → Prop} {l : Lab} {h g : Heap}
    (hd : l.drains = true) (H : LabOkR I K false l h g) (p : Bool) : LabOkR I K p l h g := by
  obtain ⟨hm, H⟩ := H
  refine ⟨hm, ?_⟩
  rcases H with ⟨a1, a2⟩ | ⟨b1, -, b3⟩ | ⟨m, fl, a, sz, v, rfl, -⟩
  · refine Or.inl ⟨a1, fun ok => ?_⟩
    have := a2 ok
    simp only [hd, Bool.not_true, Bool.and_false] at this ⊢
    exact this
  · exact Or.inr (Or.inl ⟨b1, Or.inr hd, b3⟩)
  · cases hd

/-- **Code that drains first is safe from any flag.** -/
theorem safeR_flag {I : GProp} {Q : Bool → Regs → Heap → Heap → Prop} {s : Stmt} {rs : Regs}
    (hdf : DF s rs) {h g : Heap} (H : SafeR I Q false s rs h g) (p : Bool) :
    SafeR I Q p s rs h g := by
  induction hdf generalizing h g with
  | @intro s rs hs hl ht ih =>
    have S := safeR_unfold H
    refine safeR_fold ⟨fun e => absurd e hs, fun s' rs' st => ?_, fun l s' rs' st => ?_⟩
    · exact ih s' rs' st (S.2.1 s' rs' st)
    · exact labOkR_drains (hl l s' rs' st) (S.2.2 l s' rs' st) p

theorem df_seq_skip {s : Stmt} {rs : Regs} (h : DF s rs) : DF (.seq .skip s) rs := by
  refine DF.intro (by intro e; cases e) (fun l s' rs' st => ?_) (fun s' rs' st => ?_)
  · rcases tstep_seq st with ⟨s'', st', -⟩ | ⟨-, e, -⟩
    · cases st'
    · cases e
  · rcases tstep_seq st with ⟨s'', st', -⟩ | ⟨-, -, rfl, rfl⟩
    · cases st'
    · exact h

/-- An assignment, then code that drains first. -/
theorem df_seq_assign {d : Silmaril.X86.Concurrency.Cir.Reg} {e : Expr} {s : Stmt} {rs : Regs}
    (h : ∀ rs', DF s rs') : DF (.seq (.assign d e) s) rs := by
  refine DF.intro (by intro e; cases e) (fun l s' rs' st => ?_) (fun s' rs' st => ?_)
  · rcases tstep_seq st with ⟨s'', st', -⟩ | ⟨e, -⟩
    · cases st'
    · cases e
  · rcases tstep_seq st with ⟨s'', st', rfl⟩ | ⟨e, -⟩
    · cases st'; exact df_seq_skip (h _)
    · cases e

/-- A read-modify-write first. -/
theorem df_seq_rmw {d : Silmaril.X86.Concurrency.Cir.Reg} {m : Silmaril.X86.Concurrency.Cir.Mode}
    {sz : Nat} {op : Silmaril.X86.Concurrency.Cir.RmwOp} {a arg : Expr} {t : Stmt} {rs : Regs} :
    DF (.seq (.rmw d m sz op a arg) t) rs := by
  refine DF.intro (by intro e; cases e) (fun l s' rs' st => ?_) (fun s' rs' st => ?_)
  · rcases tstep_seq st with ⟨s'', st', -⟩ | ⟨e, -⟩
    · cases st'; rfl
    · cases e
  · rcases tstep_seq st with ⟨s'', st', -⟩ | ⟨e, -⟩
    · cases st'
    · cases e

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel
