module

public import Silmaril.X86.Concurrency.Cir.Csl.Rel.Defs

/-!
# CSL with release stores: heap lemmas, the fixed point, structural rules, lifting base proofs

The heap lemmas restate the few of the base CSL proofs module that are needed here (that
module belongs to another topic). Stated in `Silmaril.X86.Concurrency.Cir.Csl.Rel.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel

open Silmaril.X86.Concurrency.Cir (Stmt Regs Expr Lab truthy)
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Rel
open Silmaril.X86.Sep.BI (SepAlg)

/-! ## Heaps, pointwise -/

theorem union_apply (h₁ h₂ : Heap) (a : Nat) : Heap.union h₁ h₂ a = (h₁ a).or (h₂ a) := by
  simp only [Heap.union, SepAlg.pmapUnion]; cases h₁ a <;> rfl

theorem updH_apply (H : Heap) (l : Lab) (a : Nat) : l.updH H a = (l.wval a).or (H a) := rfl

theorem empty_apply (a : Nat) : Heap.empty a = none := rfl

theorem single_apply (a v x : Nat) : Heap.single a v x = if x = a then some v else none := rfl

theorem or_isSome {α : Type} (x y : Option α) : (x.or y).isSome = (x.isSome || y.isSome) := by
  cases x <;> cases y <;> rfl

theorem union_isSome (h₁ h₂ : Heap) (a : Nat) :
    (Heap.union h₁ h₂ a).isSome = ((h₁ a).isSome || (h₂ a).isSome) := by
  rw [union_apply, or_isSome]

theorem disj_apply {h₁ h₂ : Heap} (d : Heap.Disjoint h₁ h₂) (a : Nat) :
    h₁ a = none ∨ h₂ a = none := d a

theorem union_empty (h : Heap) : Heap.union Heap.empty h = h := by
  funext x; rw [union_apply]; rfl

theorem union_empty_right (h : Heap) : Heap.union h Heap.empty = h := by
  funext x; rw [union_apply, empty_apply, Option.or_none]

theorem disjoint_empty (h : Heap) : Heap.Disjoint Heap.empty h := fun _ => Or.inl rfl

theorem disjoint_empty_right (h : Heap) : Heap.Disjoint h Heap.empty := fun _ => Or.inr rfl

theorem disjoint_symm {h₁ h₂ : Heap} (d : Heap.Disjoint h₁ h₂) : Heap.Disjoint h₂ h₁ :=
  fun a => (d a).symm

theorem wval_touch {l : Lab} {a : Nat} (e : (l.wval a).isSome) : l.Touches a := Or.inr e

theorem reads_touch {l : Lab} {p : Nat × Nat} (hp : p ∈ l.reads) : l.Touches p.1 :=
  Or.inl ⟨p.2, hp⟩

/-- Agreement on the touched cells transfers `okH`. -/
theorem okH_congr {A M : Heap} {l : Lab} (he : ∀ a, l.Touches a → A a = M a) (hok : l.okH A) :
    l.okH M := by
  intro p hp; rw [← he _ (reads_touch hp)]; exact hok p hp

/-- The view through a buffer is the buffer applied to memory, oldest first. -/
theorem view_cons (mem : Heap) (e : Ent) (b : List Ent) :
    view mem (e :: b) = view (e.apply mem) b := by
  funext a
  simp only [view, newest]
  cases e with
  | st c v w =>
    simp only [Ent.apply, Ent.val]
    by_cases h : c = a
    · subst h; simp
    · simp [h, Ne.symm h]
  | bar => simp [Ent.apply, Ent.val]

theorem view_nil (mem : Heap) : view mem [] = mem := by
  funext a; rfl

theorem view_apply (mem : Heap) (b : List Ent) (a : Nat) :
    view mem b a = (newest b a).or (mem a) := rfl

theorem newest_append (b c : List Ent) (a : Nat) :
    newest (b ++ c) a = (newest c a).or (newest b a) := by
  induction b with
  | nil => simp [newest]
  | cons e b ih => simp only [List.cons_append, newest, ih, Option.or_assoc]

theorem newest_cellLast (outs : List (Nat × Nat × Nat)) (a : Nat) :
    newest (outs.map fun c => Ent.st c.1 c.2.2 false) a =
      Silmaril.X86.Concurrency.Cir.cellLast outs a := by
  induction outs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, newest, ih, Silmaril.X86.Concurrency.Cir.cellLast, Ent.val]

theorem newest_ents {l : Lab} (hd : l.drains = false) (a : Nat) : newest l.ents a = l.wval a := by
  cases l with
  | wr m fl a0 sz v => simp [Lab.ents, newest, Ent.val, Lab.wval]
  | blk n ins outs rvs => exact newest_cellLast outs a
  | fence k => cases k <;> simp_all [Lab.ents, newest, Ent.val, Lab.wval, Lab.drains]
  | _ => simp_all [Lab.ents, newest, Lab.wval, Lab.drains]

/-- The view after appending a label's entries. -/
theorem view_ents {l : Lab} (hd : l.drains = false) (mem : Heap) (b : List Ent) (a : Nat) :
    view mem (b ++ l.ents) a = (l.wval a).or (view mem b a) := by
  simp only [view, newest_append, newest_ents hd, Option.or_assoc]

/-! ## The fixed point -/

section Fix
variable {I : GProp} {Q Q' : Bool → Regs → Heap → Heap → Prop}

theorem labOkR_mono {K K' : Bool → Heap → Heap → Prop} (hK : ∀ p h g, K p h g → K' p h g)
    {p : Bool} {l : Lab} {h g : Heap} (H : LabOkR I K p l h g) : LabOkR I K' p l h g := by
  obtain ⟨hm, H⟩ := H
  refine ⟨hm, ?_⟩
  rcases H with ⟨a1, a2⟩ | ⟨b1, b2, b3⟩ | ⟨m, fl, a, sz, v, e, hmn, h', hR, g', gR, c1, c2, c3, c4,
    c6, c7⟩
  · exact Or.inl ⟨a1, fun ok => hK _ _ _ (a2 ok)⟩
  · refine Or.inr (Or.inl ⟨b1, b2, fun hI gI i d1 d2 => ?_⟩)
    obtain ⟨x1, x2, x3⟩ := b3 hI gI i d1 d2
    refine ⟨x1, x2, fun ok => ?_⟩
    obtain ⟨h', hI', g', gI', y1, y2, y3, y4, y5, y6, y7⟩ := x3 ok
    exact ⟨h', hI', g', gI', y1, y2, y3, y4, y5, hK _ _ _ y6, y7⟩
  · exact Or.inr (Or.inr ⟨m, fl, a, sz, v, e, hmn, h', hR, g', gR, c1, c2, c3, c4,
      hK _ _ _ c6, c7⟩)

theorem safeFR_mono {R R' : Bool → Stmt → Regs → Heap → Heap → Prop}
    (hQ : ∀ p rs h g, Q p rs h g → Q' p rs h g)
    (hR : ∀ p s rs h g, R p s rs h g → R' p s rs h g) {p : Bool} {s : Stmt} {rs : Regs}
    {h g : Heap} (H : SafeFR I Q R p s rs h g) : SafeFR I Q' R' p s rs h g :=
  ⟨fun e => hQ _ _ _ _ (H.1 e), fun s' rs' st => hR _ _ _ _ _ (H.2.1 s' rs' st),
    fun l s' rs' st => labOkR_mono (fun _ _ _ x => hR _ _ _ _ _ x) (H.2.2 l s' rs' st)⟩

theorem safeR_unfold {p : Bool} {s : Stmt} {rs : Regs} {h g : Heap}
    (H : SafeR I Q p s rs h g) : SafeFR I Q (SafeR I Q) p s rs h g := by
  obtain ⟨R, hR, hpost⟩ := H
  exact safeFR_mono (fun _ _ _ _ x => x) (fun p s rs h g hr => ⟨R, hr, hpost⟩)
    (hpost _ _ _ _ _ hR)

/-- **Coinduction up to `SafeR`.** -/
theorem safeR_coind (R : Bool → Stmt → Regs → Heap → Heap → Prop)
    (hR : ∀ p s rs h g, R p s rs h g →
      SafeFR I Q (fun p s rs h g => R p s rs h g ∨ SafeR I Q p s rs h g) p s rs h g)
    {p : Bool} {s : Stmt} {rs : Regs} {h g : Heap} (H : R p s rs h g) : SafeR I Q p s rs h g := by
  refine ⟨fun p s rs h g => R p s rs h g ∨ SafeR I Q p s rs h g, Or.inl H,
    fun p s rs h g hx => ?_⟩
  rcases hx with hx | hx
  · exact hR _ _ _ _ _ hx
  · exact safeFR_mono (fun _ _ _ _ x => x) (fun _ _ _ _ _ x => Or.inr x) (safeR_unfold hx)

theorem safeR_fold {p : Bool} {s : Stmt} {rs : Regs} {h g : Heap}
    (H : SafeFR I Q (SafeR I Q) p s rs h g) : SafeR I Q p s rs h g :=
  safeR_coind (fun p' s' rs' h' g' => p' = p ∧ s' = s ∧ rs' = rs ∧ h' = h ∧ g' = g)
    (fun _ _ _ _ _ ⟨e0, e1, e2, e3, e4⟩ => by
      subst e0 e1 e2 e3 e4
      exact safeFR_mono (fun _ _ _ _ x => x) (fun _ _ _ _ _ x => Or.inr x) H)
    ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem safeR_conseq (hQ : ∀ p rs h g, Q p rs h g → Q' p rs h g) {p : Bool} {s : Stmt}
    {rs : Regs} {h g : Heap} (H : SafeR I Q p s rs h g) : SafeR I Q' p s rs h g :=
  safeR_coind (SafeR I Q) (fun _ _ _ _ _ hx =>
    safeFR_mono hQ (fun _ _ _ _ _ x => Or.inl x) (safeR_unfold hx)) H

end Fix

/-! ## Thread-step inversions -/

theorem tstep_skip {rs : Regs} {l : Option Lab} {s' : Stmt} {rs' : Regs} :
    ¬ TStep .skip rs l s' rs' := by
  intro h; cases h

theorem tstep_seq {s t : Stmt} {rs : Regs} {l : Option Lab} {s0 : Stmt} {rs' : Regs}
    (h : TStep (.seq s t) rs l s0 rs') :
    (∃ s', TStep s rs l s' rs' ∧ s0 = .seq s' t) ∨ (s = .skip ∧ l = none ∧ s0 = t ∧ rs' = rs) := by
  cases h with
  | seq h => exact Or.inl ⟨_, h, rfl⟩
  | seqSkip => exact Or.inr ⟨rfl, rfl, rfl, rfl⟩

theorem tstep_ite {c : Expr} {s t : Stmt} {rs : Regs} {l : Option Lab} {s0 : Stmt} {rs' : Regs}
    (h : TStep (.ite c s t) rs l s0 rs') :
    l = none ∧ rs' = rs ∧ ((truthy (c.eval rs) = true ∧ s0 = s) ∨
      (truthy (c.eval rs) = false ∧ s0 = t)) := by
  cases h with
  | iteT h => exact ⟨rfl, rfl, Or.inl ⟨h, rfl⟩⟩
  | iteF h => exact ⟨rfl, rfl, Or.inr ⟨h, rfl⟩⟩

theorem tstep_loop {n : Nat} {c : Expr} {b : Stmt} {rs : Regs} {l : Option Lab} {s0 : Stmt}
    {rs' : Regs} (h : TStep (.loop n c b) rs l s0 rs') :
    l = none ∧ rs' = rs ∧
      ((truthy (c.eval rs) = true ∧ ∃ k, n = k + 1 ∧ s0 = .seq b (.loop k c b)) ∨
      (truthy (c.eval rs) = false ∧ s0 = .skip)) := by
  cases h with
  | loopT h => exact ⟨rfl, rfl, Or.inl ⟨h, _, rfl, rfl⟩⟩
  | loopF h => exact ⟨rfl, rfl, Or.inr ⟨h, rfl⟩⟩

/-! ## Structural rules -/

section Rules
variable {I : GProp} {Q : Bool → Regs → Heap → Heap → Prop}

theorem safeR_skip {p : Bool} {rs : Regs} {h g : Heap} (hq : Q p rs h g) :
    SafeR I Q p .skip rs h g :=
  safeR_fold ⟨fun _ => hq, fun _ _ st => absurd st tstep_skip,
    fun _ _ _ st => absurd st tstep_skip⟩

theorem safeR_skip_inv {p : Bool} {rs : Regs} {h g : Heap} (H : SafeR I Q p .skip rs h g) :
    Q p rs h g :=
  (safeR_unfold H).1 rfl

/-- **Sequential composition** (the flag flows from `s` into `t`). -/
theorem safeR_seq {p : Bool} {s t : Stmt} {rs : Regs} {h g : Heap}
    (H : SafeR I (fun p rs h g => SafeR I Q p t rs h g) p s rs h g) :
    SafeR I Q p (.seq s t) rs h g := by
  refine safeR_coind
    (fun p s0 rs h g => ∃ s, s0 = .seq s t ∧
      SafeR I (fun p rs h g => SafeR I Q p t rs h g) p s rs h g)
    ?_ ⟨s, rfl, H⟩
  rintro p _ rs h g ⟨s, rfl, H⟩
  have F := safeR_unfold H
  refine ⟨(fun e => nomatch e), fun s0 rs' st => ?_, fun l s0 rs' st => ?_⟩
  · rcases tstep_seq st with ⟨s', st', rfl⟩ | ⟨rfl, -, rfl, rfl⟩
    · exact Or.inl ⟨s', rfl, F.2.1 _ _ st'⟩
    · exact Or.inr (F.1 rfl)
  · rcases tstep_seq st with ⟨s', st', rfl⟩ | ⟨-, e, -⟩
    · exact labOkR_mono (fun _ _ _ hx => Or.inl ⟨s', rfl, hx⟩) (F.2.2 l s' rs' st')
    · cases e

/-- **Conditionals.** -/
theorem safeR_ite {p : Bool} {c : Expr} {s t : Stmt} {rs : Regs} {h g : Heap}
    (hs : truthy (c.eval rs) = true → SafeR I Q p s rs h g)
    (ht : truthy (c.eval rs) = false → SafeR I Q p t rs h g) :
    SafeR I Q p (.ite c s t) rs h g := by
  refine safeR_fold ⟨(fun e => nomatch e), fun s0 rs' st => ?_, fun l s0 rs' st => ?_⟩
  · obtain ⟨-, rfl, (⟨e, rfl⟩ | ⟨e, rfl⟩)⟩ := tstep_ite st
    · exact hs e
    · exact ht e
  · cases (tstep_ite st).1

/-- **Bounded loops**, with an invariant indexed by the remaining bound. -/
theorem safeR_loop {c : Expr} {b : Stmt} (J : Nat → Bool → Regs → Heap → Heap → Prop)
    (hexit : ∀ k p rs h g, J k p rs h g → truthy (c.eval rs) = false → Q p rs h g)
    (hbody : ∀ k p rs h g, J (k + 1) p rs h g → truthy (c.eval rs) = true →
      SafeR I (J k) p b rs h g)
    {n : Nat} {p : Bool} {rs : Regs} {h g : Heap} (hJ : J n p rs h g) :
    SafeR I Q p (.loop n c b) rs h g := by
  induction n generalizing p rs h g with
  | zero =>
    refine safeR_fold ⟨(fun e => nomatch e), fun s0 rs' st => ?_, fun l s0 rs' st => ?_⟩
    · obtain ⟨-, rfl, (⟨-, k', e, -⟩ | ⟨e, rfl⟩)⟩ := tstep_loop st
      · cases e
      · exact safeR_skip (hexit _ _ _ _ _ hJ e)
    · cases (tstep_loop st).1
  | succ k ih =>
    refine safeR_fold ⟨(fun e => nomatch e), fun s0 rs' st => ?_, fun l s0 rs' st => ?_⟩
    · obtain ⟨-, rfl, (⟨e, k', ek, rfl⟩ | ⟨e, rfl⟩)⟩ := tstep_loop st
      · cases ek
        exact safeR_seq (safeR_conseq (fun _ _ _ _ hj => ih hj) (hbody k _ _ _ _ hJ e))
      · exact safeR_skip (hexit _ _ _ _ _ hJ e)
    · cases (tstep_loop st).1

/-- **A silent register assignment.** -/
theorem safeR_assign {p : Bool} {d : Silmaril.X86.Concurrency.Cir.Reg} {e : Expr} {rs : Regs}
    {h g : Heap} (hq : Q p (rs.set d (e.eval rs)) h g) : SafeR I Q p (.assign d e) rs h g := by
  refine safeR_fold ⟨(fun e => by cases e), (fun s' rs' hs => ?_), (fun l s' rs' hs => by cases hs)⟩
  cases hs
  exact safeR_skip hq

/-- **One labelled step to `skip`**, meeting `LabOkR` with the postcondition. -/
theorem safeR_atomic {p : Bool} {s : Stmt} {rs : Regs} {h g : Heap}
    (hs : s ≠ .skip) (hτ : ∀ s' rs', ¬ TStep s rs none s' rs')
    (hl : ∀ l s' rs', TStep s rs (some l) s' rs' →
      s' = .skip ∧ LabOkR I (fun p' h' g' => Q p' rs' h' g') p l h g) :
    SafeR I Q p s rs h g := by
  refine safeR_fold ⟨fun e => absurd e hs, fun s' rs' st => absurd st (hτ s' rs'),
    fun l s' rs' st => ?_⟩
  obtain ⟨rfl, H⟩ := hl l s' rs' st
  exact labOkR_mono (fun _ _ _ q => safeR_skip q) H

end Rules

/-! ## Lifting base proofs -/

/-- **Base CSL proofs are `SafeR` proofs.** A thread safe in the base logic under `I0` stays safe
under any `I` whose states split into an `I0` part and a part the thread never touches (an
invariant frame),
with its ghost heap unchanged and its flag clear. -/
theorem safeR_lift {I0 : HProp} {Q0 : Regs → HProp} {I : GProp} {g : Heap}
    (split : ∀ hI gI, I hI gI → ∃ hA hB, Heap.Disjoint hA hB ∧ hI = Heap.union hA hB ∧ I0 hA ∧
      ∀ hA', I0 hA' → Heap.Disjoint hA' hB → I (Heap.union hA' hB) gI)
    {s : Stmt} {rs : Regs} {h : Heap} (H : Safe I0 Q0 s rs h) :
    SafeR I (fun p rs h' g' => p = false ∧ Q0 rs h' ∧ g' = g) false s rs h g := by
  refine safeR_coind (fun p s rs h g' => p = false ∧ g' = g ∧ Safe I0 Q0 s rs h) ?_
    ⟨rfl, rfl, H⟩
  rintro p s rs h g' ⟨rfl, hg, H⟩
  obtain ⟨R, hR, hpost⟩ := H
  have S := hpost _ _ _ hR
  refine ⟨fun e => ⟨rfl, S.1 e, hg⟩, fun s' rs' st => Or.inl ⟨rfl, hg, R, S.2.1 _ _ st, hpost⟩,
    fun l s' rs' st => ?_⟩
  obtain ⟨hm, hna, hat⟩ := S.2.2 l s' rs' st
  refine ⟨hm, ?_⟩
  cases ena : l.na with
  | true =>
    obtain ⟨hc, hk⟩ := hna ena
    refine Or.inl ⟨hc, fun ok => Or.inl ⟨by simp, hg, R, hk ok, hpost⟩⟩
  | false =>
    refine Or.inr (Or.inl ⟨rfl, Or.inl rfl, fun hI gI hIi hd hdg => ?_⟩)
    obtain ⟨hA, hB, dAB, rfl, iA, back⟩ := split hI gI hIi
    have dhA : Heap.Disjoint h hA := fun a => by
      have := hd a; rw [union_apply] at this
      cases e1 : h a <;> cases e2 : hA a <;> simp_all
    have dhB : Heap.Disjoint h hB := fun a => by
      have := hd a; rw [union_apply] at this
      cases e1 : h a <;> cases e2 : hA a <;> cases e3 : hB a <;> simp_all
    obtain ⟨c1, c2, c3⟩ := hat ena hA iA dhA
    refine ⟨fun a ta => ?_, c2, fun ok => ?_⟩
    · have := c1 a ta; rw [union_isSome] at this ⊢; rw [union_isSome]
      cases e1 : (h a).isSome <;> cases e2 : (hA a).isSome <;> simp_all
    · have ok' : l.okH (Heap.union h hA) := by
        intro q hq
        have t := c1 _ (reads_touch hq)
        have := ok q hq
        rw [union_apply, union_apply] at this; rw [union_apply]
        rw [union_isSome] at t
        cases e1 : h q.1 <;> cases e2 : hA q.1 <;> simp_all
      obtain ⟨h', hA', d', eq', iA', k', sur⟩ := c3 ok'
      have pt : ∀ a, (h' a).or (hA' a) = (l.wval a).or ((h a).or (hA a)) := fun a => by
        have := congrFun eq' a; rw [union_apply, updH_apply, union_apply] at this; exact this
      have tw : ∀ a, (l.wval a).isSome → ((h a).or (hA a)).isSome := fun a e => by
        have := c1 a (wval_touch e); rw [union_apply] at this; exact this
      have outB : ∀ a, (hB a).isSome → h' a = none ∧ hA' a = none ∧ l.wval a = none ∧
          h a = none ∧ hA a = none := fun a ea => by
        have e4 : h a = none := by
          rcases dhB a with e | e
          · exact e
          · rw [e] at ea; cases ea
        have e5 : hA a = none := by
          rcases dAB a with e | e
          · exact e
          · rw [e] at ea; cases ea
        have e6 : l.wval a = none := by
          cases e : l.wval a with
          | none => rfl
          | some _ => have := tw a (by rw [e]; rfl); rw [e4, e5] at this; cases this
        have p := pt a; rw [e4, e5, e6] at p
        cases e1 : h' a <;> cases e2 : hA' a <;> simp_all
      refine ⟨h', Heap.union hA' hB, g', gI, fun a => ?_, ?_, hdg, rfl,
        back hA' iA' (fun a => ?_), Or.inl ⟨rfl, hg, R, k', hpost⟩, sur⟩
      · rw [union_apply]
        cases e3 : hB a with
        | none => rw [Option.or_none]; exact d' a
        | some _ => exact Or.inl (outB a (by rw [e3]; rfl)).1
      · funext a
        rw [union_apply, union_apply, updH_apply, union_apply, union_apply]
        cases e3 : hB a with
        | none =>
          simp only [Option.or_none]
          have := pt a
          cases e1 : h' a <;> cases e2 : hA' a <;> cases e4 : l.wval a <;> cases e5 : h a <;>
            cases e6 : hA a <;> simp_all
        | some _ =>
          obtain ⟨e1, e2, e6, e4, e5⟩ := outB a (by rw [e3]; rfl)
          simp [e4, e5, e1, e2, e6]
      · cases e3 : hB a with
        | none => exact Or.inr rfl
        | some _ => exact Or.inl (outB a (by rw [e3]; rfl)).2.1

end Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel
