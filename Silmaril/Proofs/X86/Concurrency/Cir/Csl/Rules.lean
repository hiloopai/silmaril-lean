module

public import Silmaril.X86.Concurrency.Cir.Csl.Defs

/-!
# CSL over CIR: heap lemmas, the fixed point, and the thread-local proof rules

Stated in `Silmaril.X86.Concurrency.Cir.Csl.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl

open Silmaril.X86.Concurrency.Cir (Stmt Regs Expr Lab truthy cellVals cellLast)
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Sep.BI (SepAlg)

/-! ## Heaps, pointwise -/

theorem union_apply (h₁ h₂ : Heap) (a : Nat) : Heap.union h₁ h₂ a = (h₁ a).or (h₂ a) := by
  simp only [Heap.union, SepAlg.pmapUnion]; cases h₁ a <;> rfl

theorem updH_apply (H : Heap) (l : Lab) (a : Nat) : l.updH H a = (l.wval a).or (H a) := rfl

theorem or_isSome {α : Type} (x y : Option α) : (x.or y).isSome = (x.isSome || y.isSome) := by
  cases x <;> cases y <;> rfl

theorem union_isSome (h₁ h₂ : Heap) (a : Nat) :
    (Heap.union h₁ h₂ a).isSome = ((h₁ a).isSome || (h₂ a).isSome) := by
  rw [union_apply, or_isSome]

theorem updH_union (h F : Heap) (l : Lab) :
    l.updH (Heap.union h F) = Heap.union (l.updH h) F := by
  funext a; simp only [updH_apply, union_apply, Option.or_assoc]

theorem le_union_left (h F : Heap) : Heap.Le h (Heap.union h F) := by
  intro a v e; rw [union_apply, e]; rfl

theorem le_union_right {h F : Heap} (hd : Heap.Disjoint h F) : Heap.Le F (Heap.union h F) := by
  intro a v e; rw [union_apply]
  rcases hd a with e' | e'
  · rw [e', e]; rfl
  · rw [e'] at e; cases e

theorem union_le {h F M : Heap} (h₁ : Heap.Le h M) (h₂ : Heap.Le F M) :
    Heap.Le (Heap.union h F) M := by
  intro a v e; rw [union_apply] at e
  cases e' : h a with
  | none => rw [e'] at e; exact h₂ a v e
  | some w => rw [e'] at e; cases e; exact h₁ a _ e'

theorem le_trans {a b c : Heap} (h₁ : Heap.Le a b) (h₂ : Heap.Le b c) : Heap.Le a c :=
  fun x v e => h₂ x v (h₁ x v e)

theorem updH_le {A M : Heap} (l : Lab) (h : Heap.Le A M) : Heap.Le (l.updH A) (l.updH M) := by
  intro a v e; rw [updH_apply] at e ⊢
  cases e' : l.wval a with
  | none => rw [e', Option.none_or] at e; rw [Option.none_or]; exact h a v e
  | some w => rw [e'] at e; exact e

theorem isSome_of_le {A M : Heap} (h : Heap.Le A M) {a : Nat} (e : (A a).isSome) :
    (M a).isSome := by
  cases e' : A a with
  | none => rw [e'] at e; cases e
  | some v => rw [h a v e']; rfl

theorem eq_of_le {A M : Heap} (h : Heap.Le A M) {a : Nat} (e : (A a).isSome) : A a = M a := by
  cases e' : A a with
  | none => rw [e'] at e; cases e
  | some v => rw [h a v e']

theorem isSome_iff_ne_none {α : Type} {x : Option α} : x.isSome = false ↔ x = none := by
  cases x <;> simp

theorem disjoint_none_left {h F : Heap} (hd : Heap.Disjoint h F) {a : Nat} (e : (F a).isSome) :
    h a = none := by
  rcases hd a with e' | e'
  · exact e'
  · rw [e'] at e; cases e

theorem disjoint_none_right {h F : Heap} (hd : Heap.Disjoint h F) {a : Nat} (e : (h a).isSome) :
    F a = none := by
  rcases hd a with e' | e'
  · rw [e'] at e; cases e
  · exact e'

theorem reads_touch {l : Lab} {p : Nat × Nat} (hp : p ∈ l.reads) : l.Touches p.1 :=
  Or.inl ⟨p.2, hp⟩

theorem wval_touch {l : Lab} {a : Nat} (e : (l.wval a).isSome) : l.Touches a := Or.inr e

/-- Reads agree with a sub-heap containing the read cells. -/
theorem okH_of_le {A M : Heap} {l : Lab} (hc : ∀ a, l.Touches a → (A a).isSome)
    (hle : Heap.Le A M) (hok : l.okH M) : l.okH A := by
  intro p hp
  rw [eq_of_le hle (hc _ (reads_touch hp))]; exact hok p hp

theorem okH_mono {A M : Heap} {l : Lab} (hle : Heap.Le A M) (hok : l.okH A) : l.okH M :=
  fun p hp => hle _ _ (hok p hp)

/-- Agreement on the touched cells transfers `okH`. -/
theorem okH_congr {A M : Heap} {l : Lab} (he : ∀ a, l.Touches a → A a = M a) (hok : l.okH A) :
    l.okH M := by
  intro p hp; rw [← he _ (reads_touch hp)]; exact hok p hp

theorem updH_isSome (H : Heap) (l : Lab) (a : Nat) :
    (l.updH H a).isSome = ((l.wval a).isSome || (H a).isSome) := by
  rw [updH_apply, or_isSome]

/-- If the written cells are in `H`, the domain does not change. -/
theorem updH_dom {H : Heap} {l : Lab} (hw : ∀ a, l.Touches a → (H a).isSome) (a : Nat) :
    (l.updH H a).isSome = (H a).isSome := by
  rw [updH_isSome]
  cases e : (l.wval a).isSome
  · rfl
  · rw [hw a (wval_touch e)]; rfl

theorem updH_of_not {H : Heap} {l : Lab} {a : Nat} (e : l.wval a = none) : l.updH H a = H a := by
  rw [updH_apply, e, Option.none_or]

/-! ## The fixed point -/

theorem labOk_mono {I : HProp} {K K' : Heap → Prop} (hK : ∀ h, K h → K' h) {l : Lab} {h : Heap}
    (H : LabOk I K l h) : LabOk I K' l h := by
  obtain ⟨hm, hna, hat⟩ := H
  refine ⟨hm, fun e => ⟨(hna e).1, fun ok => hK _ ((hna e).2 ok)⟩, fun e hI hIh hd => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hat e hI hIh hd
  refine ⟨h1, h2, fun ok => ?_⟩
  obtain ⟨h', hI', a1, a2, a3, a4, a5⟩ := h3 ok
  exact ⟨h', hI', a1, a2, a3, hK _ a4, a5⟩

theorem safeF_mono {I : HProp} {Q Q' : Regs → HProp} {R R' : Stmt → Regs → Heap → Prop}
    (hQ : ∀ rs h, Q rs h → Q' rs h) (hR : ∀ s rs h, R s rs h → R' s rs h) {s : Stmt}
    {rs : Regs} {h : Heap} (H : SafeF I Q R s rs h) : SafeF I Q' R' s rs h :=
  ⟨fun e => hQ _ _ (H.1 e), fun s' rs' st => hR _ _ _ (H.2.1 s' rs' st),
    fun l s' rs' st => labOk_mono (hR _ _) (H.2.2 l s' rs' st)⟩

theorem safe_unfold {I : HProp} {Q : Regs → HProp} {s : Stmt} {rs : Regs} {h : Heap}
    (H : Safe I Q s rs h) : SafeF I Q (Safe I Q) s rs h := by
  obtain ⟨R, hR, hpost⟩ := H
  exact safeF_mono (fun _ _ x => x) (fun s rs h hr => ⟨R, hr, hpost⟩) (hpost _ _ _ hR)

/-- **Coinduction up to `Safe`.** -/
theorem safe_coind {I : HProp} {Q : Regs → HProp} (R : Stmt → Regs → Heap → Prop)
    (hR : ∀ s rs h, R s rs h → SafeF I Q (fun s rs h => R s rs h ∨ Safe I Q s rs h) s rs h)
    {s : Stmt} {rs : Regs} {h : Heap} (H : R s rs h) : Safe I Q s rs h := by
  refine ⟨fun s rs h => R s rs h ∨ Safe I Q s rs h, Or.inl H, fun s rs h hx => ?_⟩
  rcases hx with hx | hx
  · exact hR _ _ _ hx
  · exact safeF_mono (fun _ _ x => x) (fun _ _ _ x => Or.inr x) (safe_unfold hx)

theorem safe_fold {I : HProp} {Q : Regs → HProp} {s : Stmt} {rs : Regs} {h : Heap}
    (H : SafeF I Q (Safe I Q) s rs h) : Safe I Q s rs h :=
  safe_coind (fun s' rs' h' => s' = s ∧ rs' = rs ∧ h' = h)
    (fun _ _ _ ⟨e1, e2, e3⟩ => by
      subst e1 e2 e3; exact safeF_mono (fun _ _ x => x) (fun _ _ _ x => Or.inr x) H)
    ⟨rfl, rfl, rfl⟩

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

theorem safe_skip {I : HProp} {Q : Regs → HProp} {rs : Regs} {h : Heap} (hq : Q rs h) :
    Safe I Q .skip rs h :=
  safe_fold ⟨fun _ => hq, fun _ _ st => absurd st tstep_skip,
    fun _ _ _ st => absurd st tstep_skip⟩

theorem safe_skip_inv {I : HProp} {Q : Regs → HProp} {rs : Regs} {h : Heap}
    (H : Safe I Q .skip rs h) : Q rs h :=
  (safe_unfold H).1 rfl

theorem safe_conseq {I : HProp} {Q Q' : Regs → HProp} (hQ : ∀ rs h, Q rs h → Q' rs h)
    {s : Stmt} {rs : Regs} {h : Heap} (H : Safe I Q s rs h) : Safe I Q' s rs h :=
  safe_coind (Safe I Q) (fun _ _ _ hx =>
    safeF_mono hQ (fun _ _ _ x => Or.inl x) (safe_unfold hx)) H

/-- **Sequential composition.** -/
theorem safe_seq {I : HProp} {Q : Regs → HProp} {s t : Stmt} {rs : Regs} {h : Heap}
    (H : Safe I (fun rs h => Safe I Q t rs h) s rs h) : Safe I Q (.seq s t) rs h := by
  refine safe_coind
    (fun s0 rs h => ∃ s, s0 = .seq s t ∧ Safe I (fun rs h => Safe I Q t rs h) s rs h)
    ?_ ⟨s, rfl, H⟩
  rintro _ rs h ⟨s, rfl, H⟩
  have F := safe_unfold H
  refine ⟨(fun e => nomatch e), fun s0 rs' st => ?_, fun l s0 rs' st => ?_⟩
  · rcases tstep_seq st with ⟨s', st', rfl⟩ | ⟨rfl, -, rfl, rfl⟩
    · exact Or.inl ⟨s', rfl, F.2.1 _ _ st'⟩
    · exact Or.inr (F.1 rfl)
  · rcases tstep_seq st with ⟨s', st', rfl⟩ | ⟨-, e, -⟩
    · exact labOk_mono (fun h' hx => Or.inl ⟨s', rfl, hx⟩) (F.2.2 l s' rs' st')
    · cases e

/-- **Conditionals.** -/
theorem safe_ite {I : HProp} {Q : Regs → HProp} {c : Expr} {s t : Stmt} {rs : Regs} {h : Heap}
    (hs : truthy (c.eval rs) = true → Safe I Q s rs h)
    (ht : truthy (c.eval rs) = false → Safe I Q t rs h) : Safe I Q (.ite c s t) rs h := by
  refine safe_fold ⟨(fun e => nomatch e), fun s0 rs' st => ?_, fun l s0 rs' st => ?_⟩
  · obtain ⟨-, rfl, (⟨e, rfl⟩ | ⟨e, rfl⟩)⟩ := tstep_ite st
    · exact hs e
    · exact ht e
  · cases (tstep_ite st).1

/-- **Bounded loops** with an invariant `J k` indexed by the remaining bound. A run that
exhausts the bound has no step (assume semantics), so it is vacuously safe. -/
theorem safe_loop {I : HProp} {Q : Regs → HProp} {c : Expr} {b : Stmt}
    (J : Nat → Regs → Heap → Prop)
    (hexit : ∀ k rs h, J k rs h → truthy (c.eval rs) = false → Q rs h)
    (hbody : ∀ k rs h, J (k + 1) rs h → truthy (c.eval rs) = true → Safe I (J k) b rs h)
    {n : Nat} {rs : Regs} {h : Heap} (hJ : J n rs h) : Safe I Q (.loop n c b) rs h := by
  induction n generalizing rs h with
  | zero =>
    refine safe_fold ⟨(fun e => nomatch e), fun s0 rs' st => ?_, fun l s0 rs' st => ?_⟩
    · obtain ⟨-, rfl, (⟨-, k', e, -⟩ | ⟨e, rfl⟩)⟩ := tstep_loop st
      · cases e
      · exact safe_skip (hexit _ _ _ hJ e)
    · cases (tstep_loop st).1
  | succ k ih =>
    refine safe_fold ⟨(fun e => nomatch e), fun s0 rs' st => ?_, fun l s0 rs' st => ?_⟩
    · obtain ⟨-, rfl, (⟨e, k', ek, rfl⟩ | ⟨e, rfl⟩)⟩ := tstep_loop st
      · cases ek
        exact safe_seq (safe_conseq (fun rs h hj => ih hj) (hbody k _ _ hJ e))
      · exact safe_skip (hexit _ _ _ hJ e)
    · cases (tstep_loop st).1

/-! ## The frame rule -/

/-- **Frame rule**: a thread safe on `h` stays safe on `h` next to any disjoint frame `F`,
which it never touches and which holds again at the end. -/
theorem safe_frame {I : HProp} {Q : Regs → HProp} {F : HProp} {s : Stmt} {rs : Regs}
    {h hF : Heap} (H : Safe I Q s rs h) (hd : Heap.Disjoint h hF) (hf : F hF) :
    Safe I (fun rs => Q rs ∗ F) s rs (Heap.union h hF) := by
  refine safe_coind (fun s rs H => ∃ h hF, Safe I Q s rs h ∧ Heap.Disjoint h hF ∧ F hF ∧
    H = Heap.union h hF) ?_ ⟨h, hF, H, hd, hf, rfl⟩
  rintro s rs _ ⟨h, hF, H, hd, hf, rfl⟩
  have S := safe_unfold H
  refine ⟨fun e => ⟨h, hF, hd, rfl, S.1 e, hf⟩,
    fun s' rs' st => Or.inl ⟨h, hF, S.2.1 _ _ st, hd, hf, rfl⟩, fun l s' rs' st => ?_⟩
  obtain ⟨hm, hna, hat⟩ := S.2.2 l s' rs' st
  refine ⟨hm, fun e => ?_, fun e hI hIi hdI => ?_⟩
  · obtain ⟨hc, hk⟩ := hna e
    refine ⟨fun a ta => ?_, fun ok => ?_⟩
    · rw [union_isSome, hc a ta]; rfl
    · refine Or.inl ⟨l.updH h, hF, hk (okH_of_le hc (le_union_left h hF) ok), fun a => ?_, hf,
        updH_union h hF l⟩
      have ha := hd a
      have hw : (l.wval a).isSome → (h a).isSome := fun e => hc a (wval_touch e)
      rw [updH_apply]
      cases e1 : l.wval a <;> cases e2 : h a <;> cases e3 : hF a <;> simp_all
  · have hdh : Heap.Disjoint h hI := fun a => by
      have := hdI a; rw [union_apply] at this
      cases e1 : h a <;> cases e2 : hI a <;> simp_all
    obtain ⟨c1, c2, c3⟩ := hat e hI hIi hdh
    refine ⟨fun a ta => ?_, fun ed a ew => ?_, fun ok => ?_⟩
    · have := c1 a ta; have h2 := hdI a
      rw [union_apply, union_apply] at *
      cases e1 : h a <;> cases e2 : hI a <;> cases e3 : hF a <;> simp_all
    · have := c2 ed a ew; rw [union_isSome, this]; rfl
    · have le : Heap.Le (Heap.union h hI) (Heap.union (Heap.union h hF) hI) := by
        intro a v ev; have h2 := hdI a
        rw [union_apply] at ev ⊢; rw [union_apply] at h2 ⊢
        cases e1 : h a <;> cases e2 : hI a <;> cases e3 : hF a <;> simp_all
      obtain ⟨h', hI', d', eq', iI', k', sur⟩ := c3 (okH_of_le c1 le ok)
      have pt : ∀ a, (h' a).or (hI' a) = (l.wval a).or ((h a).or (hI a)) := fun a => by
        have := congrFun eq' a; rw [union_apply, updH_apply, union_apply] at this; exact this
      have tw : ∀ a, (l.wval a).isSome → ((h a).or (hI a)).isSome := fun a e => by
        have := c1 a (wval_touch e); rw [union_apply] at this; exact this
      have out : ∀ a, (hF a).isSome → h a = none ∧ hI a = none ∧ h' a = none ∧ hI' a = none ∧
          l.wval a = none :=
        fun a ea => by
          have e4 : h a = none := disjoint_none_left hd ea
          have e5 : hI a = none := by
            have := hdI a; rw [union_apply, e4, Option.none_or] at this
            rcases this with e | e
            · rw [e] at ea; cases ea
            · exact e
          have e6 : l.wval a = none := by
            cases e : l.wval a with
            | none => rfl
            | some _ => have := tw a (by rw [e]; rfl); rw [e4, e5] at this; cases this
          have p := pt a; rw [e4, e5, e6] at p
          cases e1 : h' a <;> cases e2 : hI' a <;> simp_all
      have dF : Heap.Disjoint h' hF := fun a => by
        cases e3 : hF a with
        | none => exact Or.inr rfl
        | some _ => exact Or.inl (out a (by rw [e3]; rfl)).2.2.1
      refine ⟨Heap.union h' hF, hI', fun a => ?_, ?_, iI', Or.inl ⟨h', hF, k', dF, hf, rfl⟩,
        fun ed a ea => ?_⟩
      · rw [union_apply]
        cases e3 : hF a with
        | none => rw [Option.or_none]; exact d' a
        | some _ => exact Or.inr (out a (by rw [e3]; rfl)).2.2.2.1
      · funext a
        rw [union_apply, union_apply, updH_apply, union_apply, union_apply]
        cases e3 : hF a with
        | none => simp only [Option.or_none]; exact pt a
        | some _ =>
          obtain ⟨e4, e5, e1, e2, e6⟩ := out a (by rw [e3]; rfl)
          simp [e4, e5, e1, e2, e6]
      · have := sur ed a; rw [union_isSome] at ea ⊢
        cases e1 : h a <;> cases e3 : hF a <;> simp_all

/-! ## Atomic steps -/

/-- **Atomic invariant access** (the generic one-step rule): a statement that takes no silent
step and whose every label step ends at `skip` is safe when each of its labels meets
`LabOk` with the postcondition. For an atomic label `LabOk` opens the invariant `I` for the
duration of the step, and may move cells between the thread and `I`. -/
theorem safe_atomic {I : HProp} {Q : Regs → HProp} {s : Stmt} {rs : Regs} {h : Heap}
    (hs : s ≠ .skip) (hτ : ∀ s' rs', ¬ TStep s rs none s' rs')
    (hl : ∀ l s' rs', TStep s rs (some l) s' rs' → s' = .skip ∧ LabOk I (Q rs') l h) :
    Safe I Q s rs h := by
  refine safe_fold ⟨fun e => absurd e hs, fun s' rs' st => absurd st (hτ s' rs'),
    fun l s' rs' st => ?_⟩
  obtain ⟨rfl, H⟩ := hl l s' rs' st
  exact labOk_mono (fun _ q => safe_skip q) H

theorem touches_rd {m : Silmaril.X86.Concurrency.Cir.Mode}
    {fl : Silmaril.X86.Concurrency.Cir.Flav}
    {a sz v x : Nat} : Lab.Touches (.rd m fl a sz v) x ↔ x = a := by
  simp [Lab.Touches, Lab.reads, Lab.wval]

theorem touches_wr {m : Silmaril.X86.Concurrency.Cir.Mode}
    {fl : Silmaril.X86.Concurrency.Cir.Flav}
    {a sz v x : Nat} : Lab.Touches (.wr m fl a sz v) x ↔ x = a := by
  by_cases h : a = x <;> simp [Lab.Touches, Lab.reads, Lab.wval, h] ; omega

/-- **Owned non-atomic load.** -/
theorem safe_load_na {I : HProp} {Q : Regs → HProp} {d : Silmaril.X86.Reg} {sz : Nat}
    {fl : Silmaril.X86.Concurrency.Cir.Flav} {a : Expr} {rs : Regs} {h : Heap} {v : Nat}
    (hv : h (a.eval rs).toNat = some v) (hq : Q (rs.set d (BitVec.ofNat 64 v)) h) :
    Safe I Q (.load d .na sz fl a) rs h := by
  refine safe_atomic (fun e => nomatch e) (fun _ _ st => nomatch st) fun l s' rs' st => ?_
  cases st with
  | load hv' =>
    refine ⟨rfl, rfl, fun _ => ⟨fun x tx => ?_, fun ok => ?_⟩, fun e => nomatch e⟩
    · rw [touches_rd.mp tx, hv]; rfl
    · have := ok _ (List.mem_singleton_self _); rw [hv] at this; cases this; exact hq

/-- **Owned non-atomic store.** -/
theorem safe_store_na {I : HProp} {Q : Regs → HProp} {sz : Nat}
    {fl : Silmaril.X86.Concurrency.Cir.Flav} {a v : Expr} {rs : Regs} {h : Heap}
    (ha : (h (a.eval rs).toNat).isSome)
    (hq : Q rs
      ((.wr .na fl (a.eval rs).toNat sz ((v.eval rs).toNat % 2 ^ (8 * sz)) : Lab).updH h)) :
    Safe I Q (.store .na sz fl a v) rs h := by
  refine safe_atomic (fun e => nomatch e) (fun _ _ st => nomatch st) fun l s' rs' st => ?_
  cases st with
  | store =>
    refine ⟨rfl, rfl, fun _ => ⟨fun x tx => ?_, fun _ => hq⟩, fun e => nomatch e⟩
    rw [touches_wr.mp tx]; exact ha

/-! ## Lifting sequential contracts: `local` blocks -/

theorem mem_cellVals {cs : List (Nat × Nat)} {vs : List Nat} {c : Nat × Nat × Nat}
    (h : c ∈ cellVals cs vs) : (c.1, c.2.1) ∈ cs := by
  induction cs generalizing vs with
  | nil => cases vs <;> simp [cellVals] at h
  | cons x cs ih =>
    cases vs with
    | nil => simp [cellVals] at h
    | cons v vs =>
      simp only [cellVals, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

theorem cellLast_isSome {cs : List (Nat × Nat × Nat)} {a : Nat} (h : (cellLast cs a).isSome) :
    ∃ c ∈ cs, c.1 = a := by
  induction cs with
  | nil => simp [cellLast] at h
  | cons c cs ih =>
    simp only [cellLast, or_isSome, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨c', hc, e⟩ := ih h; exact ⟨c', List.mem_cons_of_mem _ hc, e⟩
    · by_cases e : c.1 = a
      · exact ⟨c, List.mem_cons_self, e⟩
      · simp [e] at h

/-- **Lifting a sequential contract (`lift_sequential`).** A `local b` block whose input and
output cells are owned is a valid CSL step whatever the other threads do: its only proof
obligation is its own contract `b.spec` (the sequential summary), with the inputs read from
the owned heap. Nothing about the block's code is re-proved. -/
theorem safe_local {I : HProp} {Q : Regs → HProp} {b : Silmaril.X86.Concurrency.Cir.Block}
    {rs : Regs} {h : Heap}
    (hin : ∀ c ∈ b.ins, (h c.1).isSome) (hout : ∀ c ∈ b.outs, (h c.1).isSome)
    (hq : ∀ ivs rvs ovs, ivs.length = b.ins.length → rvs.length = b.rout.length →
      ovs.length = b.outs.length →
      b.spec (b.rin.map (fun r => (rs r).toNat) ++ ivs) (rvs ++ ovs) →
      (∀ c ∈ cellVals b.ins ivs, h c.1 = some c.2.2) →
      Q (rs.setMany b.rout rvs)
        ((.blk b.name (cellVals b.ins ivs) (cellVals b.outs ovs) rvs : Lab).updH h)) :
    Safe I Q (.local b) rs h := by
  refine safe_atomic (fun e => nomatch e) (fun _ _ st => nomatch st) fun l s' rs' st => ?_
  cases st with
  | blk hspec hi hr ho =>
    refine ⟨rfl, rfl, fun _ => ⟨fun x tx => ?_, fun ok => ?_⟩, fun e => nomatch e⟩
    · rcases tx with ⟨v, hv⟩ | hw
      · simp only [Lab.reads, List.mem_map] at hv
        obtain ⟨c, hc, e⟩ := hv
        cases e; exact hin _ (mem_cellVals hc)
      · obtain ⟨c, hc, rfl⟩ := cellLast_isSome hw
        exact hout _ (mem_cellVals hc)
    · refine hq _ _ _ hi hr ho hspec fun c hc => ?_
      exact ok (c.1, c.2.2) (List.mem_map.mpr ⟨c, hc, rfl⟩)

end Silmaril.Proofs.X86.Concurrency.Cir.Csl
