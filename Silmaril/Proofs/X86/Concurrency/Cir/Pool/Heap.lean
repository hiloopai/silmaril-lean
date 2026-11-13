module

public import Silmaril.X86.Concurrency.Cir.Csl.Thms
public import Silmaril.X86.Concurrency.Cir.Pool.Defs

/-!
# Proofs: heap, ownership and counting lemmas for the worker pool

* the fixed-point helpers and heap lemmas, **restated** from `Proofs/…/Mutex/Frame.lean`
  (another topic's proofs module, not imported);
* the pool's heaps: footprints and `owner`, `jobH` under a state update, the queue cells;
* `doneCount` under a state update.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Pool

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Pool
open Silmaril.X86.Sep.BI.SepAlg (pmapUnion pmapDisjoint)

/-! ## The fixed point, restated -/

theorem labOk_mono {I : HProp} {K K' : Heap → Prop} (hK : ∀ h, K h → K' h) {l : Lab} {h : Heap}
    (H : LabOk I K l h) : LabOk I K' l h := by
  obtain ⟨hm, hna, hat⟩ := H
  refine ⟨hm, fun hn => ⟨(hna hn).1, fun hok => hK _ ((hna hn).2 hok)⟩, fun hn hI hIi hd => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hat hn hI hIi hd
  refine ⟨h1, h2, fun hok => ?_⟩
  obtain ⟨h', hI', a, b, c, d, e⟩ := h3 hok
  exact ⟨h', hI', a, b, c, hK _ d, e⟩

theorem safeF_mono {I : HProp} {Q : Regs → HProp} {R R' : Stmt → Regs → Heap → Prop}
    (hR : ∀ s rs h, R s rs h → R' s rs h) {s : Stmt} {rs : Regs} {h : Heap}
    (H : SafeF I Q R s rs h) : SafeF I Q R' s rs h :=
  ⟨H.1, fun s' rs' hs => hR _ _ _ (H.2.1 s' rs' hs),
    fun l s' rs' hs => labOk_mono (hR _ _) (H.2.2 l s' rs' hs)⟩

theorem safe_post {I : HProp} {Q : Regs → HProp} {s : Stmt} {rs : Regs} {h : Heap}
    (H : Csl.Safe I Q s rs h) : SafeF I Q (Csl.Safe I Q) s rs h := by
  obtain ⟨R, hR, hpost⟩ := H
  exact safeF_mono (fun s rs h hr => ⟨R, hr, hpost⟩) (hpost _ _ _ hR)

theorem safe_intro {I : HProp} {Q : Regs → HProp} {s : Stmt} {rs : Regs} {h : Heap}
    (H : SafeF I Q (Csl.Safe I Q) s rs h) : Csl.Safe I Q s rs h := by
  refine ⟨fun s' rs' h' => (s' = s ∧ rs' = rs ∧ h' = h) ∨ Csl.Safe I Q s' rs' h',
    Or.inl ⟨rfl, rfl, rfl⟩, ?_⟩
  rintro s' rs' h' (⟨rfl, rfl, rfl⟩ | hs)
  · exact safeF_mono (fun _ _ _ x => Or.inr x) H
  · exact safeF_mono (fun _ _ _ x => Or.inr x) (safe_post hs)

/-- A silent register assignment. -/
theorem safe_assign {I : HProp} {Q : Regs → HProp} {d : Reg} {e : Expr} {rs : Regs} {h : Heap}
    (hq : Q (rs.set d (e.eval rs)) h) : Csl.Safe I Q (.assign d e) rs h := by
  refine safe_intro ⟨(fun e => by cases e), (fun s' rs' hs => ?_), (fun l s' rs' hs => by cases hs)⟩
  cases hs
  exact safe_skip hq

/-! ## Heaps, restated -/

theorem union_apply (h₁ h₂ : Heap) (a : Nat) :
    Heap.union h₁ h₂ a = match h₁ a with | some v => some v | none => h₂ a := by
  simp only [Heap.union, pmapUnion]; cases h₁ a <;> rfl

theorem single_apply (a v x : Nat) : Heap.single a v x = if x = a then some v else none := by
  simp only [Heap.single]

theorem union_none {h₁ h₂ : Heap} {a : Nat} (h : h₁ a = none) : Heap.union h₁ h₂ a = h₂ a := by
  simp [union_apply, h]

theorem union_some {h₁ h₂ : Heap} {a v : Nat} (h : h₁ a = some v) :
    Heap.union h₁ h₂ a = some v := by
  simp [union_apply, h]

theorem union_eq_none {h₁ h₂ : Heap} {a : Nat} :
    Heap.union h₁ h₂ a = none ↔ h₁ a = none ∧ h₂ a = none := by
  cases e : h₁ a <;> simp [union_apply, e]

theorem union_empty_left (h : Heap) : Heap.union Heap.empty h = h := by
  funext x; simp [union_apply, Heap.empty]

theorem union_empty_right (h : Heap) : Heap.union h Heap.empty = h := by
  funext x; cases e : h x <;> simp [union_apply, e, Heap.empty]

theorem disjoint_empty (h : Heap) : Heap.Disjoint Heap.empty h := fun _ => Or.inl rfl

theorem disjoint_empty_right (h : Heap) : Heap.Disjoint h Heap.empty := fun _ => Or.inr rfl

theorem disjoint_symm {h₁ h₂ : Heap} (d : Heap.Disjoint h₁ h₂) : Heap.Disjoint h₂ h₁ :=
  fun a => (d a).symm

theorem union_comm {h₁ h₂ : Heap} (d : Heap.Disjoint h₁ h₂) :
    Heap.union h₁ h₂ = Heap.union h₂ h₁ := by
  funext a
  rcases d a with e | e
  · rw [union_none e]; cases e' : h₂ a <;> simp [union_apply, e, e']
  · rw [union_none (h₁ := h₂) e]; cases e' : h₁ a <;> simp [union_apply, e, e']

theorem union_assoc (h₁ h₂ h₃ : Heap) :
    Heap.union (Heap.union h₁ h₂) h₃ = Heap.union h₁ (Heap.union h₂ h₃) := by
  funext a; simp only [union_apply]; cases h₁ a <;> rfl

theorem disjoint_union_left {h₁ h₂ h : Heap} :
    Heap.Disjoint (Heap.union h₁ h₂) h ↔ Heap.Disjoint h₁ h ∧ Heap.Disjoint h₂ h := by
  constructor
  · intro d
    refine ⟨fun a => ?_, fun a => ?_⟩ <;> rcases d a with e | e
    · exact Or.inl (union_eq_none.mp e).1
    · exact Or.inr e
    · exact Or.inl (union_eq_none.mp e).2
    · exact Or.inr e
  · rintro ⟨d₁, d₂⟩ a
    rcases d₁ a with e₁ | e₁
    · rcases d₂ a with e₂ | e₂
      · exact Or.inl (union_eq_none.mpr ⟨e₁, e₂⟩)
      · exact Or.inr e₂
    · exact Or.inr e₁

theorem disjoint_union_right {h₁ h₂ h : Heap} :
    Heap.Disjoint h (Heap.union h₁ h₂) ↔ Heap.Disjoint h h₁ ∧ Heap.Disjoint h h₂ := by
  constructor
  · intro d
    have := disjoint_union_left.mp (disjoint_symm d)
    exact ⟨disjoint_symm this.1, disjoint_symm this.2⟩
  · rintro ⟨d₁, d₂⟩
    exact disjoint_symm (disjoint_union_left.mpr ⟨disjoint_symm d₁, disjoint_symm d₂⟩)

theorem disjoint_some {h₁ h₂ : Heap} (d : Heap.Disjoint h₁ h₂) {a : Nat}
    (e₁ : (h₁ a).isSome) (e₂ : (h₂ a).isSome) : False := by
  rcases d a with e | e <;> simp [e] at e₁ e₂

/-- Disjointness, pointwise. -/
theorem disjoint_of {h₁ h₂ : Heap} (H : ∀ a, (h₁ a).isSome → h₂ a = none) :
    Heap.Disjoint h₁ h₂ := by
  intro a
  cases e : h₁ a with
  | none => exact Or.inl rfl
  | some v => exact Or.inr (H a (by simp [e]))

theorem sep_iff {P Q : HProp} {h : Heap} :
    (P ∗ Q) h ↔ ∃ h₁ h₂, Heap.Disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P h₁ ∧ Q h₂ := Iff.rfl

theorem sep_emp {P : HProp} {h : Heap} (H : P h) : (P ∗ hemp) h :=
  sep_iff.mpr ⟨h, Heap.empty, disjoint_empty_right h, (union_empty_right h).symm, H, rfl⟩

theorem le_union_left {h₁ h₂ : Heap} : Heap.Le h₁ (Heap.union h₁ h₂) :=
  fun _ _ e => union_some e

theorem le_union_right {h₁ h₂ : Heap} (d : Heap.Disjoint h₁ h₂) :
    Heap.Le h₂ (Heap.union h₁ h₂) := by
  rw [union_comm d]; exact le_union_left

theorem le_trans' {a b c : Heap} (h₁ : Heap.Le a b) (h₂ : Heap.Le b c) : Heap.Le a c :=
  fun x v e => h₂ x v (h₁ x v e)

theorem le_refl' (a : Heap) : Heap.Le a a := fun _ _ e => e

theorem union_or (h₁ h₂ : Heap) (a : Nat) : Heap.union h₁ h₂ a = (h₁ a).or (h₂ a) := by
  rw [union_apply]; cases h₁ a <;> rfl

theorem isSome_union_l {h₁ h₂ : Heap} {a : Nat} (h : (h₁ a).isSome) :
    (Heap.union h₁ h₂ a).isSome := by
  rw [union_or]; cases e : h₁ a <;> simp_all

theorem isSome_union_r {h₁ h₂ : Heap} {a : Nat} (h : (h₂ a).isSome) :
    (Heap.union h₁ h₂ a).isSome := by
  rw [union_or]; cases e : h₁ a <;> simp_all

/-! ## Lists of cells -/

theorem cellsH_some {l : List (Nat × Nat × Nat)} {a v : Nat} (h : cellsH l a = some v) :
    ∃ c ∈ l, c.1 = a := by
  simp only [cellsH, Option.map_eq_some_iff] at h
  obtain ⟨c, hc, -⟩ := h
  exact ⟨c, List.mem_of_find?_eq_some hc, by simpa using List.find?_some hc⟩

theorem cellVals_fst : ∀ {cs : List (Nat × Nat)} {vs : List Nat} {c : Nat × Nat × Nat},
    c ∈ cellVals cs vs → ∃ c' ∈ cs, c'.1 = c.1
  | [], _, _, h => by simp [cellVals] at h
  | _ :: _, [], _, h => by simp [cellVals] at h
  | d :: cs, v :: vs, c, h => by
    simp only [cellVals, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨d, List.mem_cons_self .., rfl⟩
    · obtain ⟨c', hc', e⟩ := cellVals_fst h
      exact ⟨c', List.mem_cons_of_mem _ hc', e⟩

theorem cellLast_some : ∀ {l : List (Nat × Nat × Nat)} {a : Nat},
    (cellLast l a).isSome → ∃ c ∈ l, c.1 = a
  | [], _, h => by simp [cellLast] at h
  | c :: l, a, h => by
    simp only [cellLast] at h
    cases e : cellLast l a with
    | some w =>
      obtain ⟨c', hc', e'⟩ := cellLast_some (l := l) (a := a) (by simp [e])
      exact ⟨c', List.mem_cons_of_mem _ hc', e'⟩
    | none =>
      rw [e] at h
      by_cases hc : c.1 = a
      · exact ⟨c, List.mem_cons_self .., hc⟩
      · simp [hc] at h

theorem cellVals_cellsH_isSome : ∀ {cs : List (Nat × Nat)} {vs : List Nat},
    cs.length ≤ vs.length → ∀ c ∈ cs, (cellsH (cellVals cs vs) c.1).isSome
  | [], _, _, c, hc => by simp at hc
  | _ :: _, [], hl, _, _ => by simp at hl
  | d :: cs, v :: vs, hl, c, hc => by
    simp only [List.mem_cons] at hc
    simp only [cellsH, cellVals, List.find?_cons]
    by_cases e : d.1 = c.1
    · simp [e]
    · have : (d.1 == c.1) = false := by simpa using e
      rw [this]
      rcases hc with rfl | hc
      · exact absurd rfl e
      · have := cellVals_cellsH_isSome (cs := cs) (vs := vs) (by simp at hl; omega) c hc
        simpa [cellsH] using this

/-! ## Items -/

namespace Item

theorem freshH_some {it : Item} {a : Nat} (h : (it.freshH a).isSome) : a ∈ it.fp := by
  simp only [Item.fp, List.mem_cons, List.mem_append, List.mem_map]
  by_cases hc : a = it.cnt
  · exact Or.inl hc
  cases e1 : cellsH (cellVals it.job.ins it.arg) a with
  | some v =>
    obtain ⟨c, hc', ec⟩ := cellsH_some e1
    obtain ⟨c', hc'', e'⟩ := cellVals_fst hc'
    exact Or.inr (Or.inl ⟨c', hc'', e'.trans ec⟩)
  | none =>
    have h2 : (cellsH (cellVals it.job.outs (it.job.outs.map fun _ => 0)) a).isSome := by
      have : it.freshH a = cellsH (cellVals it.job.outs (it.job.outs.map fun _ => 0)) a := by
        simp only [Item.freshH]
        rw [union_none (by simp [single_apply, hc]), union_none e1]
      rwa [this] at h
    obtain ⟨v, e2⟩ := Option.isSome_iff_exists.mp h2
    obtain ⟨c, hc', ec⟩ := cellsH_some e2
    obtain ⟨c', hc'', e'⟩ := cellVals_fst hc'
    exact Or.inr (Or.inr ⟨c', hc'', e'.trans ec⟩)

theorem freshH_cnt (it : Item) : it.freshH it.cnt = some 0 := by
  simp [Item.freshH, union_apply, single_apply]

theorem blkH_some {it : Item} {a : Nat} (h : (it.blkH a).isSome) : a ∈ it.fp := by
  have e0 : it.blkH a =
      (cellLast (cellVals it.job.outs (it.job.fn it.ivals)) a).or (it.freshH a) := rfl
  rw [e0] at h
  cases e : cellLast (cellVals it.job.outs (it.job.fn it.ivals)) a with
  | none => rw [e] at h; exact freshH_some (by simpa using h)
  | some w =>
    obtain ⟨c, hc, ec⟩ := cellLast_some (l := cellVals it.job.outs (it.job.fn it.ivals)) (a := a)
      (by rw [e]; rfl)
    obtain ⟨c', hc', e'⟩ := cellVals_fst hc
    simp only [Item.fp, List.mem_cons, List.mem_append, List.mem_map]
    exact Or.inr (Or.inr ⟨c', hc', e'.trans ec⟩)

theorem doneH_some {it : Item} {a : Nat} (h : (it.doneH a).isSome) : a ∈ it.fp := by
  simp only [Item.doneH] at h
  split at h
  · rename_i e; subst e; exact List.mem_cons_self ..
  · exact blkH_some h

theorem doneH_cnt (it : Item) : (it.doneH it.cnt).isSome := by simp [Item.doneH]

theorem stH_some {it : Item} {s : St} {a : Nat} (h : (it.stH s a).isSome) : a ∈ it.fp := by
  cases s with
  | fresh => exact freshH_some h
  | taken => simp [Item.stH, Heap.empty] at h
  | done => exact doneH_some h

end Item

/-! ## Footprints and owners -/

namespace Wp

variable {P : Wp}

theorem fpB_lt {j a : Nat} (h : P.fpB j a = true) : j < P.n := by
  unfold Wp.fpB at h
  cases e : P.items[j]? with
  | none => simp [e] at h
  | some it =>
    have := (List.getElem?_eq_some_iff.mp e).1
    exact this

theorem owner_spec {a j : Nat} (h : P.owner a = some j) : P.fpB j a = true ∧ j < P.n := by
  unfold Wp.owner at h
  have h1 := List.find?_some h
  exact ⟨by simpa using h1, List.mem_range.mp (List.mem_of_find?_eq_some h)⟩

theorem stH_some {j : Nat} {s : St} {a : Nat} (h : (P.stH j s a).isSome) : P.fpB j a = true := by
  unfold Wp.stH at h
  unfold Wp.fpB
  cases e : P.items[j]? with
  | none => simp [e, Heap.empty] at h
  | some it =>
    rw [e] at h
    simpa using Item.stH_some h

theorem stH_owner (hP : P.Ok) {j : Nat} {s : St} {a : Nat} (h : (P.stH j s a).isSome) :
    P.owner a = some j :=
  hP.own j (fpB_lt (stH_some h)) a (stH_some h)

theorem stH_none (hP : P.Ok) {j : Nat} {s : St} {a : Nat} (h : P.owner a ≠ some j) :
    P.stH j s a = none := by
  cases e : P.stH j s a with
  | none => rfl
  | some v => exact absurd (stH_owner hP (s := s) (by rw [e]; rfl)) h

theorem jobH_owner {σ : Nat → St} {a j : Nat} (h : P.owner a = some j) :
    P.jobH σ a = P.stH j (σ j) a := by
  simp [Wp.jobH, h]

theorem jobH_none {σ : Nat → St} {a : Nat} (h : P.owner a = none) : P.jobH σ a = none := by
  simp [Wp.jobH, h]

theorem jobH_some {σ : Nat → St} {a : Nat} (h : (P.jobH σ a).isSome) : ∃ j, P.owner a = some j := by
  cases e : P.owner a with
  | none => rw [jobH_none e] at h; simp at h
  | some j => exact ⟨j, rfl⟩

theorem jobH_upd {σ : Nat → St} {k : Nat} {s : St} (a : Nat) :
    P.jobH (upd σ k s) a = if P.owner a = some k then P.stH k s a else P.jobH σ a := by
  cases e : P.owner a with
  | none => simp [jobH_none e]
  | some j =>
    rw [jobH_owner e, jobH_owner e]
    by_cases hj : j = k
    · subst hj; simp [upd]
    · simp [upd, hj]

/-! ## The control cells -/

/-- The facts about the control cells that the proofs use. -/
structure CtlFacts (P : Wp) : Prop where
  qd : P.qa ≠ P.da
  qe : P.qa ≠ P.ea
  de : P.da ≠ P.ea
  cq : ∀ t < P.K, P.cur t ≠ P.qa
  cd : ∀ t < P.K, P.cur t ≠ P.da
  ce : ∀ t < P.K, P.cur t ≠ P.ea
  oq : P.owner P.qa = none
  od : P.owner P.da = none
  oe : P.owner P.ea = none
  oc : ∀ t < P.K, P.owner (P.cur t) = none
  lq : P.qa < 2 ^ 64
  ld : P.da < 2 ^ 64
  le : P.ea < 2 ^ 64
  lc : ∀ t < P.K, P.cur t < 2 ^ 64

theorem cur_inj {t u : Nat} (h : P.cur t = P.cur u) : t = u := by
  simp only [Wp.cur] at h; omega

theorem ctlFacts (hP : P.Ok) : CtlFacts P := by
  have hn := hP.ctlNodup
  have mq : P.qa ∈ P.ctl := by simp [Wp.ctl]
  have md : P.da ∈ P.ctl := by simp [Wp.ctl]
  have me : P.ea ∈ P.ctl := by simp [Wp.ctl]
  have mc : ∀ t < P.K, P.cur t ∈ P.ctl := fun t ht =>
    List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr ht))
  simp only [Wp.ctl, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.mem_map, List.mem_range, not_or, not_exists, not_and] at hn
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6, -⟩ := hn
  refine ⟨h1, h2, h4, fun t ht e => h3 t ht e, fun t ht e => h5 t ht e, fun t ht e => h6 t ht e,
    hP.ctlOwn _ mq, hP.ctlOwn _ md, hP.ctlOwn _ me, fun t ht => hP.ctlOwn _ (mc t ht),
    (hP.ctlLt _ mq).1, (hP.ctlLt _ md).1, (hP.ctlLt _ me).1, fun t ht => (hP.ctlLt _ (mc t ht)).1⟩

theorem ctlH_qa (k d e : Nat) : P.ctlH k d e P.qa = some k := by
  simp [Wp.ctlH, union_apply, single_apply]

theorem ctlH_da (F : CtlFacts P) (k d e : Nat) : P.ctlH k d e P.da = some d := by
  simp [Wp.ctlH, union_apply, single_apply, Ne.symm F.qd]

theorem ctlH_ea (F : CtlFacts P) (k d e : Nat) : P.ctlH k d e P.ea = some e := by
  simp [Wp.ctlH, union_apply, single_apply, Ne.symm F.qe, Ne.symm F.de]

theorem ctlH_other {k d e a : Nat} (h1 : a ≠ P.qa) (h2 : a ≠ P.da) (h3 : a ≠ P.ea) :
    P.ctlH k d e a = none := by
  simp [Wp.ctlH, union_apply, single_apply, h1, h2, h3]

theorem ctlH_some {k d e a : Nat} (h : (P.ctlH k d e a).isSome) :
    a = P.qa ∨ a = P.da ∨ a = P.ea := by
  by_cases h1 : a = P.qa
  · exact Or.inl h1
  by_cases h2 : a = P.da
  · exact Or.inr (Or.inl h2)
  by_cases h3 : a = P.ea
  · exact Or.inr (Or.inr h3)
  rw [ctlH_other h1 h2 h3] at h; simp at h

/-- A job cell is not a control cell. -/
theorem owner_ne_ctl (F : CtlFacts P) {a j : Nat} (h : P.owner a = some j) :
    a ≠ P.qa ∧ a ≠ P.da ∧ a ≠ P.ea ∧ ∀ t < P.K, a ≠ P.cur t := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun t ht e => ?_⟩ <;> subst e
  · rw [F.oq] at h; cases h
  · rw [F.od] at h; cases h
  · rw [F.oe] at h; cases h
  · rw [F.oc t ht] at h; cases h

theorem ctlH_job (F : CtlFacts P) {a j : Nat} (h : P.owner a = some j) (k d e : Nat) :
    P.ctlH k d e a = none :=
  have := owner_ne_ctl F h
  ctlH_other this.1 this.2.1 this.2.2.1

/-! ## Counting returned jobs -/

/-- `1` if `b`, else `0`. -/
def b2n (b : Bool) : Nat := if b then 1 else 0

theorem countP_range_succ (f : Nat → Bool) (n : Nat) :
    (List.range (n + 1)).countP f = (List.range n).countP f + b2n (f n) := by
  rw [List.range_succ, List.countP_append]
  simp [b2n, List.countP_cons]

theorem countP_range_congr {f g : Nat → Bool} {n : Nat} (h : ∀ j < n, f j = g j) :
    (List.range n).countP f = (List.range n).countP g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [countP_range_succ, countP_range_succ, ih (fun j hj => h j (by omega)), h n (by omega)]

theorem countP_range_upd {f g : Nat → Bool} {k n : Nat} (hk : k < n)
    (h : ∀ j, j ≠ k → g j = f j) :
    (List.range n).countP g + b2n (f k) = (List.range n).countP f + b2n (g k) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [countP_range_succ, countP_range_succ]
    by_cases hkn : k = n
    · subst hkn
      rw [countP_range_congr (f := g) (g := f) (fun j hj => h j (by omega))]
      omega
    · have := ih (by omega)
      rw [h n (Ne.symm hkn)]
      omega

theorem doneCount_le (σ : Nat → St) : P.doneCount σ ≤ P.n := by
  unfold Wp.doneCount
  exact (List.countP_le_length).trans (by simp)

theorem doneCount_upd_done {σ : Nat → St} {k : Nat} (hk : k < P.n) (h : σ k ≠ .done) :
    P.doneCount (upd σ k .done) = P.doneCount σ + 1 := by
  unfold Wp.doneCount
  have := countP_range_upd (f := fun j => σ j == .done) (g := fun j => upd σ k .done j == .done)
    hk (fun j hj => by simp [upd, hj])
  have e1 : b2n (σ k == .done) = 0 := by simp [b2n, h]
  have e2 : b2n (upd σ k .done k == .done) = 1 := by simp [b2n, upd]
  omega

theorem doneCount_upd_taken {σ : Nat → St} {k : Nat} (hk : k < P.n) (h : σ k ≠ .done) :
    P.doneCount (upd σ k .taken) = P.doneCount σ := by
  unfold Wp.doneCount
  have := countP_range_upd (f := fun j => σ j == .done) (g := fun j => upd σ k .taken j == .done)
    hk (fun j hj => by simp [upd, hj])
  have e1 : b2n (σ k == .done) = 0 := by simp [b2n, h]
  have e2 : b2n (upd σ k .taken k == .done) = 0 := by simp [b2n, upd]
  omega

theorem doneCount_all {σ : Nat → St} (h : P.doneCount σ = P.n) : ∀ j < P.n, σ j = .done := by
  unfold Wp.doneCount at h
  have h' : (List.range P.n).countP (fun j => σ j == .done) = (List.range P.n).length := by
    simpa using h
  intro j hj
  have := List.countP_eq_length.mp h' j (List.mem_range.mpr hj)
  simpa using this

theorem doneCount_fresh : P.doneCount (fun _ => .fresh) = 0 := by
  unfold Wp.doneCount
  simp

end Wp

end Silmaril.Proofs.X86.Concurrency.Cir.Pool
