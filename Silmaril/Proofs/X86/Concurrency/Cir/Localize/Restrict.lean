module

public import Silmaril.Proofs.X86.Concurrency.Cir.Localize.SurgWf

/-!
# Localisation: the fragment's units on their own

The fragment's units `F` of a candidate, renumbered from `0` and moved to
thread `0` (`F1`), with the old `rf` and `co` restricted to them, form a one-thread candidate
(`Surg.rexec`). Nothing else touches the cell bytes, so it is well-formed, its reads are right
from the same initial bytes, it is XL-consistent when the old one is, and on the cells its final
bytes are the old ones (`Surg.restrict`). The single-thread lift (`Seq.oneSem_iff`) then replays
it sequentially.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Localize

open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte rmwPairs writtenByte)

namespace Surg

variable (S : Surg)

/-- The fragment's units as a one-thread candidate. -/
def rexec (F1 : List (Ev × List Byte)) (x : Exec) : Exec where
  evs := F1.map Prod.fst
  rf := fun r y => (x.rf (S.A.length + r) y).map (· - S.A.length)
  co := fun y => if S.cb y then (x.co y).map (· - S.A.length) else []
  rmw := rmwPairs (F1.map Prod.fst)

/-- What the restriction needs: `F1` is `F` renumbered in thread `0`, and the fragment's units
cannot tear. -/
structure RHyp (F1 : List (Ev × List Byte)) : Prop where
  len : F1.length = S.F.length
  relab : ∀ k (h1 : k < F1.length) (h : k < S.F.length),
    F1[k] = ({ (S.F[k]).1 with tid := 0, pos := k }, (S.F[k]).2)
  posF : ∀ k (h : k < S.F.length), (S.F[k]).1.tid = S.i ∧ (S.F[k]).1.pos = S.p1 + k
  tameF : ∀ u ∈ S.F, u.1.isM = true → u.1.singleCopy = true ∧ ∀ v ∈ S.F, v.1.isM = true →
    u.1.accOverlap v.1 = true → u.1.accAddr = v.1.accAddr ∧ u.1.accSize = v.1.accSize

variable {S} {F1 : List (Ev × List Byte)} {x : Exec} {ib : Nat → Byte}

set_option linter.unusedSectionVars false

variable (H : S.Hyp ib) (R : S.RHyp F1) (hx : x.evs = S.old.map Prod.fst) (hwf : x.Wf = true)
  (hrmw : x.rmw = rmwPairs x.evs)
include H R hx hwf hrmw

theorem rn : (S.rexec F1 x).n = S.F.length := by
  show (F1.map Prod.fst).length = _; simp [R.len]

theorem lt_old {k : Nat} (hk : k < S.F.length) : S.A.length + k < x.n := by
  rw [n_old hx]; omega

/-- The old unit of a restricted unit. -/
def ι (a : Fin (S.rexec F1 x).n) : Fin x.n :=
  ⟨S.A.length + a.val, lt_old H R hx hwf hrmw (lt_of_lt_of_eq a.2 (rn H R hx hwf hrmw))⟩

theorem ev_F {k : Nat} (hk : k < S.F.length) (h : S.A.length + k < x.n) :
    x.ev ⟨S.A.length + k, h⟩ = (S.F[k]).1 := by
  rw [ev_old hx]
  have h' : S.A.length + k < (S.old.map Prod.fst).length := by rw [← hx]; exact h
  exact (S.old_F (k := S.A.length + k) (by omega) (by omega) h').trans (by simp)

theorem rev (a : Fin (S.rexec F1 x).n) :
    (S.rexec F1 x).ev a = { (S.F[a.val]'(lt_of_lt_of_eq a.2 (rn H R hx hwf hrmw))).1 with
      tid := 0, pos := a.val } := by
  have h1 : a.val < F1.length := by have := a.2; simp only [Exec.n, rexec, List.length_map] at this; exact this
  show (F1.map Prod.fst)[a.val] = _
  rw [List.getElem_map, R.relab a.val h1]

theorem same_r (a : Fin (S.rexec F1 x).n) :
    Same ((S.rexec F1 x).ev a) (x.ev (ι H R hx hwf hrmw a)) := by
  rw [rev H R hx hwf hrmw, ι, ev_F H R hx hwf hrmw]
  rfl

/-- An old unit covering a cell byte is a fragment unit. -/
theorem inF_of_on {w : Nat} (hw : w < x.n) (hM : (x.evs[w]).isM = true) {y : Nat}
    (hc : (x.evs[w]).covers y = true) (hy : S.cb y = true) :
    S.A.length ≤ w ∧ w < S.A.length + S.F.length := by
  have he : x.evs[w] = (S.old.map Prod.fst)[w]'(by rw [← hx]; exact hw) := List.getElem_of_eq hx _
  have hwo : w < S.A.length + S.F.length + S.C.length := lt_of_lt_of_eq hw (n_old hx)
  by_contra hn
  rcases Nat.lt_or_ge w S.A.length with h1 | h1
  · rw [he, S.old_A h1] at hM hc
    have := H.offAC _ (List.mem_append_left _ (List.getElem_mem _)) hM y hc
    rw [hy] at this; cases this
  · have h2 : S.A.length + S.F.length ≤ w := by omega
    rw [he, S.old_C h2] at hM hc
    have := H.offAC _ (List.mem_append_right _ (List.getElem_mem _)) hM y hc
    rw [hy] at this; cases this

theorem cb_of_r {a : Fin (S.rexec F1 x).n} (hM : ((S.rexec F1 x).ev a).isM = true) {y : Nat}
    (hc : ((S.rexec F1 x).ev a).covers y = true) : S.cb y = true := by
  have s := same_r H R hx hwf hrmw a
  have ha := lt_of_lt_of_eq a.2 (rn H R hx hwf hrmw)
  rw [s.isM, ι, ev_F H R hx hwf hrmw ha] at hM
  rw [s.covers, ι, ev_F H R hx hwf hrmw ha] at hc
  exact H.onF _ (List.getElem_mem _) hM y hc

/-- A restricted unit from an old fragment unit. -/
def ρ {w : Nat} (h1 : S.A.length ≤ w) (h2 : w < S.A.length + S.F.length) :
    Fin (S.rexec F1 x).n := ⟨w - S.A.length, by rw [rn H R hx hwf hrmw]; omega⟩

theorem ι_ρ {w : Nat} (h1 : S.A.length ≤ w) (h2 : w < S.A.length + S.F.length) :
    (ι H R hx hwf hrmw (ρ H R hx hwf hrmw h1 h2)).val = w := by
  simp only [ι, ρ]; omega

theorem sub_eq_iff {a : Fin (S.rexec F1 x).n} {c : Nat} (hc : S.A.length ≤ c) :
    c - S.A.length = a.val ↔ c = S.A.length + a.val := by omega

/-- Sources of restricted reads are fragment writes. -/
theorem rf_r {r : Fin (S.rexec F1 x).n} (hR : ((S.rexec F1 x).ev r).isR = true) {y : Nat}
    (hy : ((S.rexec F1 x).ev r).covers y = true) {w : Nat}
    (h : x.rf (S.A.length + r.val) y = some w) :
    ∃ hw : w < x.n, S.A.length ≤ w ∧ w < S.A.length + S.F.length ∧ (x.evs[w]).isW = true ∧
      (x.evs[w]).covers y = true := by
  have s := same_r H R hx hwf hrmw r
  have hR0 : (x.ev (ι H R hx hwf hrmw r)).isR = true := by
    rw [← s.isR]; exact hR
  have hy0 : (x.ev (ι H R hx hwf hrmw r)).covers y = true := by
    rw [← s.covers]; exact hy
  obtain ⟨hw, hW, hC⟩ := wf_rf hwf (ι H R hx hwf hrmw r).2 hR0 hy0 h
  obtain ⟨h1, h2⟩ := inF_of_on H R hx hwf hrmw hw (isM_of_W hW) hC
    (cb_of_r H R hx hwf hrmw (isM_of_R hR) hy)
  exact ⟨hw, h1, h2, hW, hC⟩

/-! ## The embedding -/

theorem emb_r : Emb x (S.rexec F1 x) (fun a => some (ι H R hx hwf hrmw a)) where
  same a a0 h := by cases h; exact same_r H R hx hwf hrmw a
  po a b a0 b0 ha hb := by
    cases ha; cases hb
    have hA := lt_of_lt_of_eq a.2 (rn H R hx hwf hrmw)
    have hB := lt_of_lt_of_eq b.2 (rn H R hx hwf hrmw)
    simp only [Exec.po, rev H R hx hwf hrmw, ι, ev_F H R hx hwf hrmw hA, ev_F H R hx hwf hrmw hB,
      (R.posF _ hA).1, (R.posF _ hB).1, (R.posF _ hA).2, (R.posF _ hB).2]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
    omega
  sm a b a0 b0 ha hb := by
    cases ha; cases hb
    have hA := lt_of_lt_of_eq a.2 (rn H R hx hwf hrmw)
    have hB := lt_of_lt_of_eq b.2 (rn H R hx hwf hrmw)
    simp only [Exec.sm, rev H R hx hwf hrmw, ι, ev_F H R hx hwf hrmw hA, ev_F H R hx hwf hrmw hB,
      (R.posF _ hA).1, (R.posF _ hB).1, (R.posF _ hA).2, (R.posF _ hB).2]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_self_eq_true, Bool.true_and, beq_iff_eq]
    omega
  ext a b a0 b0 ha hb := by
    cases ha; cases hb
    have hA := lt_of_lt_of_eq a.2 (rn H R hx hwf hrmw)
    have hB := lt_of_lt_of_eq b.2 (rn H R hx hwf hrmw)
    simp only [Exec.ext, rev H R hx hwf hrmw, ι, ev_F H R hx hwf hrmw hA, ev_F H R hx hwf hrmw hB,
      (R.posF _ hA).1, (R.posF _ hB).1, bne_self_eq_false]
  rf a b a0 b0 ha hb := by
    cases ha; cases hb
    have sa := same_r H R hx hwf hrmw a
    have sb := same_r H R hx hwf hrmw b
    simp only [Exec.rfR, ← sa.isW, ← sb.isR, ← sb.bytes, ← sa.covers]
    cases hR : ((S.rexec F1 x).ev b).isR
    · simp
    · simp only [Bool.and_true]
      congr 1
      refine any_congr' fun y hy => ?_
      congr 1
      show (Option.map (· - S.A.length) (x.rf (S.A.length + b.val) y) == some a.val) =
        (x.rf (S.A.length + b.val) y == some (S.A.length + a.val))
      cases h : x.rf (S.A.length + b.val) y with
      | none => rfl
      | some w =>
        obtain ⟨-, h1, -⟩ := rf_r H R hx hwf hrmw hR (mem_bytes.mp hy) h
        rw [Bool.eq_iff_iff]
        simp only [Option.map_some, beq_iff_eq, Option.some.injEq]
        omega
  co a b a0 b0 ha hb := by
    cases ha; cases hb
    have sa := same_r H R hx hwf hrmw a
    have sb := same_r H R hx hwf hrmw b
    simp only [Exec.coR, ← sa.isW, ← sb.isW, ← sa.bytes, ← sb.covers]
    cases hW : ((S.rexec F1 x).ev a).isW
    · simp
    · simp only [Bool.true_and]
      congr 1
      refine any_congr' fun y hy => ?_
      congr 1
      have hcb := cb_of_r H R hx hwf hrmw (isM_of_W hW) (mem_bytes.mp hy)
      show before (if S.cb y then (x.co y).map (· - S.A.length) else []) a.val b.val =
        before (x.co y) (S.A.length + a.val) (S.A.length + b.val)
      simp only [hcb, ite_true]
      have hy0 : (x.ev (ι H R hx hwf hrmw a)).covers y = true := by
        rw [← sa.covers]; exact mem_bytes.mp hy
      have hM0 : (x.ev (ι H R hx hwf hrmw a)).isM = true := by
        rw [← sa.isM]; exact isM_of_W hW
      obtain ⟨-, hall, -⟩ := wf_co hwf (touched_of (ι H R hx hwf hrmw a).2 hM0 hy0)
      have hge : ∀ c ∈ x.co y, S.A.length ≤ c := fun c hc => by
        obtain ⟨hc', hcW, hcC⟩ := hall c hc
        exact (inF_of_on H R hx hwf hrmw hc' (isM_of_W hcW) hcC hcb).1
      exact before_map_on _ (fun c hc => by have := hge c hc; omega)
        (fun c hc => by have := hge c hc; omega)
  fr a b a0 b0 ha hb := by
    cases ha; cases hb
    have sa := same_r H R hx hwf hrmw a
    have sb := same_r H R hx hwf hrmw b
    simp only [Exec.frR, ← sa.isR, ← sb.isW, ← sa.bytes, ← sb.covers]
    cases hR : ((S.rexec F1 x).ev a).isR
    · simp
    · simp only [Bool.true_and]
      congr 1
      refine any_congr' fun y hy => ?_
      congr 1
      have hcb := cb_of_r H R hx hwf hrmw (isM_of_R hR) (mem_bytes.mp hy)
      show (match Option.map (· - S.A.length) (x.rf (S.A.length + a.val) y) with
        | none => true
        | some v => before (if S.cb y then (x.co y).map (· - S.A.length) else []) v b.val) =
        (match x.rf (S.A.length + a.val) y with
        | none => true
        | some v => before (x.co y) v (S.A.length + b.val))
      simp only [hcb, ite_true]
      cases h : x.rf (S.A.length + a.val) y with
      | none => rfl
      | some w =>
        obtain ⟨hw, h1, h2, hW, hC⟩ := rf_r H R hx hwf hrmw hR (mem_bytes.mp hy) h
        obtain ⟨-, hall, -⟩ := wf_co hwf (touched_of hw (isM_of_W hW) hC)
        have hge : ∀ c ∈ x.co y, S.A.length ≤ c := fun c hc => by
          obtain ⟨hc', hcW, hcC⟩ := hall c hc
          exact (inF_of_on H R hx hwf hrmw hc' (isM_of_W hcW) hcC hcb).1
        simp only [Option.map_some]
        exact before_map_on _ (fun c hc => by have := hge c hc; omega)
          (fun c hc => by have := hge c hc; omega)
  rmw a b h := by
    refine ⟨ι H R hx hwf hrmw a, ι H R hx hwf hrmw b, rfl, rfl, ?_⟩
    simp only [Exec.rmwR, List.contains_iff_mem, hrmw] at h ⊢
    obtain ⟨ha', hb', hR, hla, hW, hlb, ht, hp, haddr, hsz⟩ := mem_rmwPairs_iff.mp h
    have ha := lt_of_lt_of_eq a.2 (rn H R hx hwf hrmw)
    have hb := lt_of_lt_of_eq b.2 (rn H R hx hwf hrmw)
    change ((S.rexec F1 x).ev a).isR = true at hR
    change ((S.rexec F1 x).ev a).locked = true at hla
    change ((S.rexec F1 x).ev b).isW = true at hW
    change ((S.rexec F1 x).ev b).locked = true at hlb
    change ((S.rexec F1 x).ev b).pos = ((S.rexec F1 x).ev a).pos + 1 at hp
    change ((S.rexec F1 x).ev a).addr = ((S.rexec F1 x).ev b).addr at haddr
    change ((S.rexec F1 x).ev a).size = ((S.rexec F1 x).ev b).size at hsz
    simp only [rev H R hx hwf hrmw] at hR hla hW hlb hp haddr hsz
    refine mem_rmwPairs_iff.mpr ⟨(ι H R hx hwf hrmw a).2, (ι H R hx hwf hrmw b).2, ?_⟩
    change (x.ev (ι H R hx hwf hrmw a)).isR = true ∧ (x.ev (ι H R hx hwf hrmw a)).locked = true ∧
      (x.ev (ι H R hx hwf hrmw b)).isW = true ∧ (x.ev (ι H R hx hwf hrmw b)).locked = true ∧
      (x.ev (ι H R hx hwf hrmw a)).tid = (x.ev (ι H R hx hwf hrmw b)).tid ∧
      (x.ev (ι H R hx hwf hrmw b)).pos = (x.ev (ι H R hx hwf hrmw a)).pos + 1 ∧
      (x.ev (ι H R hx hwf hrmw a)).addr = (x.ev (ι H R hx hwf hrmw b)).addr ∧
      (x.ev (ι H R hx hwf hrmw a)).size = (x.ev (ι H R hx hwf hrmw b)).size
    simp only [ι, ev_F H R hx hwf hrmw ha, ev_F H R hx hwf hrmw hb, (R.posF _ ha).1, (R.posF _ hb).1,
      (R.posF _ ha).2, (R.posF _ hb).2]
    refine ⟨hR, hla, hW, hlb, ?_, ?_, haddr, hsz⟩
    · simp
    · omega
  fence f _ := rfl
  locked l _ := rfl
  smK _ _ _ _ := rfl
  locK _ _ _ _ := rfl
  tear a a0 h ht := by
    cases h
    exfalso
    have ha := lt_of_lt_of_eq a.2 (rn H R hx hwf hrmw)
    simp only [Exec.tearable, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true,
      Bool.not_eq_true'] at ht
    obtain ⟨hM, ht⟩ := ht
    rw [ι, ev_F H R hx hwf hrmw ha] at hM ht
    obtain ⟨hsc, hov⟩ := R.tameF _ (List.getElem_mem _) hM
    rcases ht with ht | ⟨b0, -, ⟨hbM, hab⟩, hne⟩
    · rw [hsc] at ht; cases ht
    · have hb0 := b0.2
      rw [ev_old hx] at hbM hab hne
      have hb' : b0.val < (S.old.map Prod.fst).length := by rw [← hx]; exact b0.2
      have hbo := lt_of_lt_of_eq hb0 (n_old hx)
      rcases Nat.lt_or_ge b0.val S.A.length with h1 | h1
      · rw [S.old_A h1] at hbM hab hne
        have := H.ovF _ (List.mem_append_left _ (List.getElem_mem _)) _ (List.getElem_mem ha) hbM hM
        rw [accOverlap_comm, hab] at this; cases this
      · rcases Nat.lt_or_ge b0.val (S.A.length + S.F.length) with h2 | h2
        · rw [S.old_F h1 h2] at hbM hab hne
          obtain ⟨e1, e2⟩ := hov _ (List.getElem_mem _) hbM hab
          simp [e1, e2] at hne
        · rw [S.old_C h2] at hbM hab hne
          have := H.ovF _ (List.mem_append_right _ (List.getElem_mem _)) _ (List.getElem_mem ha) hbM hM
          rw [accOverlap_comm, hab] at this; cases this

/-! ## Consistency, well-formedness, reads, final bytes -/

theorem xl_r (hxl : x.Xl) : (S.rexec F1 x).Xl := by
  have E := emb_r H R hx hwf hrmw
  have htot : ∀ a, ((fun a => some (ι H R hx hwf hrmw a)) a).isSome := fun _ => rfl
  obtain ⟨hat, hu, hta, hg⟩ := hxl
  exact ⟨E.atomic hat, acyclic_of_total hu htot fun _ _ _ _ ha hb h => E.uniprocXl ha hb h,
    acyclic_of_total hta htot fun _ _ _ _ ha hb h => E.thinAir ha hb h,
    acyclic_of_total hg htot fun _ _ _ _ ha hb h => E.ghbXl ha hb h⟩

theorem evN_r {k : Nat} (hk : k < (S.rexec F1 x).n) : (S.rexec F1 x).evN k = (S.rexec F1 x).ev ⟨k, hk⟩ :=
  evN_eq hk

/-- An old fragment unit, seen in the restriction. -/
theorem same_ρ {w : Nat} (hw : w < x.n) (h1 : S.A.length ≤ w) (h2 : w < S.A.length + S.F.length) :
    Same ((S.rexec F1 x).ev (ρ H R hx hwf hrmw h1 h2)) (x.ev ⟨w, hw⟩) := by
  have := same_r H R hx hwf hrmw (ρ H R hx hwf hrmw h1 h2)
  have e : ι H R hx hwf hrmw (ρ H R hx hwf hrmw h1 h2) = ⟨w, hw⟩ :=
    Fin.ext (ι_ρ H R hx hwf hrmw h1 h2)
  rwa [e] at this

theorem wf_r : (S.rexec F1 x).Wf = true := by
  have E := emb_r H R hx hwf hrmw
  simp only [Exec.Wf, Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · refine List.all_eq_true.mpr fun r _ => ?_
    cases hR : ((S.rexec F1 x).ev r).isR
    · rfl
    simp only [Bool.not_true, Bool.false_or, List.all_eq_true]
    intro y hy
    show (match Option.map (· - S.A.length) (x.rf (S.A.length + r.val) y) with
      | none => true
      | some w => (S.rexec F1 x).valid w && ((S.rexec F1 x).evN w).isW &&
          ((S.rexec F1 x).evN w).covers y) = true
    cases h : x.rf (S.A.length + r.val) y with
    | none => rfl
    | some w =>
      obtain ⟨hw, h1, h2, hW, hC⟩ := rf_r H R hx hwf hrmw hR (mem_bytes.mp hy) h
      have sw := same_ρ H R hx hwf hrmw hw h1 h2
      simp only [Option.map_some]
      have hl : w - S.A.length < (S.rexec F1 x).n := (ρ H R hx hwf hrmw h1 h2).2
      rw [evN_r H R hx hwf hrmw hl]
      simp only [Exec.valid, hl, decide_true, Bool.true_and, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · rw [show (⟨w - S.A.length, hl⟩ : Fin _) = ρ H R hx hwf hrmw h1 h2 from rfl, sw.isW]
        exact hW
      · rw [show (⟨w - S.A.length, hl⟩ : Fin _) = ρ H R hx hwf hrmw h1 h2 from rfl, sw.covers]
        exact hC
  · refine List.all_eq_true.mpr fun y hy => ?_
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', Bool.and_eq_false_iff, List.contains_iff_mem]
    obtain ⟨w, hw, hM, hC⟩ := mem_touched hy
    have hcb := cb_of_r H R hx hwf hrmw (a := ⟨w, hw⟩) hM hC
    have sw := same_r H R hx hwf hrmw ⟨w, hw⟩
    have hty : y ∈ x.touched :=
      touched_of (ι H R hx hwf hrmw ⟨w, hw⟩).2 (by change (x.ev _).isM = true; rw [← sw.isM]; exact hM)
        (by change (x.ev _).covers y = true; rw [← sw.covers]; exact hC)
    obtain ⟨hnd, hall, hcov⟩ := wf_co hwf hty
    have hF : ∀ c ∈ x.co y, ∃ hc : c < x.n, S.A.length ≤ c ∧ c < S.A.length + S.F.length ∧
        (x.evs[c]).isW = true ∧ (x.evs[c]).covers y = true := by
      intro c hc
      obtain ⟨hc', hcW, hcC⟩ := hall c hc
      obtain ⟨h1, h2⟩ := inF_of_on H R hx hwf hrmw hc' (isM_of_W hcW) hcC hcb
      exact ⟨hc', h1, h2, hcW, hcC⟩
    have hco : (S.rexec F1 x).co y = (x.co y).map (· - S.A.length) := by simp [rexec, hcb]
    rw [hco]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine List.Nodup.map_on (fun u hu v hv he => ?_) hnd
      obtain ⟨-, h1, -⟩ := hF u hu
      obtain ⟨-, h1', -⟩ := hF v hv
      omega
    · intro w' hw'
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw'
      obtain ⟨hu', h1, h2, hW, hC'⟩ := hF u hu
      have su := same_ρ H R hx hwf hrmw hu' h1 h2
      have hl : u - S.A.length < (S.rexec F1 x).n := (ρ H R hx hwf hrmw h1 h2).2
      rw [evN_r H R hx hwf hrmw hl]
      refine ⟨⟨by simp [Exec.valid, hl], ?_⟩, ?_⟩
      · rw [show (⟨u - S.A.length, hl⟩ : Fin _) = ρ H R hx hwf hrmw h1 h2 from rfl, su.isW]
        exact hW
      · rw [show (⟨u - S.A.length, hl⟩ : Fin _) = ρ H R hx hwf hrmw h1 h2 from rfl, su.covers]
        exact hC'
    · intro w' _
      by_cases hwc : ((S.rexec F1 x).ev w').isW = true ∧ ((S.rexec F1 x).ev w').covers y = true
      · right
        have sw' := same_r H R hx hwf hrmw w'
        have := hcov _ (ι H R hx hwf hrmw w').2
          (by change (x.ev _).isW = true; rw [← sw'.isW]; exact hwc.1)
          (by change (x.ev _).covers y = true; rw [← sw'.covers]; exact hwc.2)
        exact List.mem_map.mpr ⟨_, this, by simp [ι]⟩
      · left
        simp only [not_and_or, Bool.not_eq_true] at hwc
        exact hwc
  · refine List.all_eq_true.mpr fun ⟨a, b⟩ hp => ?_
    have hp' : (a, b) ∈ rmwPairs (F1.map Prod.fst) := hp
    obtain ⟨ha, hb, hR, hla, hW, hlb, ht, hpos, -, -⟩ := mem_rmwPairs_iff.mp hp'
    obtain ⟨a0, b0, ha0, hb0, hold⟩ := E.rmw ⟨a, ha⟩ ⟨b, hb⟩
      (by simp only [Exec.rmwR, List.contains_iff_mem]; exact hp)
    cases ha0; cases hb0
    have hold' := hold
    simp only [Exec.rmwR, List.contains_iff_mem] at hold'
    obtain ⟨h1, h2⟩ := wf_rmw hwf hold'
    have sa := same_r H R hx hwf hrmw ⟨a, ha⟩
    have sb := same_r H R hx hwf hrmw ⟨b, hb⟩
    rw [evN_eq (ι H R hx hwf hrmw ⟨a, ha⟩).2, evN_eq (ι H R hx hwf hrmw ⟨b, hb⟩).2] at h1 h2
    change (x.ev _).accAddr = (x.ev _).accAddr at h1
    change (x.ev _).accSize = (x.ev _).accSize at h2
    simp only [Exec.valid, evN_r H R hx hwf hrmw ha, evN_r H R hx hwf hrmw hb, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq]
    change ((S.rexec F1 x).ev ⟨a, ha⟩).isR = true at hR
    change ((S.rexec F1 x).ev ⟨a, ha⟩).locked = true at hla
    change ((S.rexec F1 x).ev ⟨b, hb⟩).isW = true at hW
    change ((S.rexec F1 x).ev ⟨b, hb⟩).locked = true at hlb
    change ((S.rexec F1 x).ev ⟨a, ha⟩).tid = ((S.rexec F1 x).ev ⟨b, hb⟩).tid at ht
    change ((S.rexec F1 x).ev ⟨b, hb⟩).pos = ((S.rexec F1 x).ev ⟨a, ha⟩).pos + 1 at hpos
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hR⟩, hW⟩, ht⟩, by omega⟩, hla⟩, hlb⟩, ?_⟩, ?_⟩
    · rw [sa.accAddr, sb.accAddr]; exact h1
    · rw [sa.accSize, sb.accSize]; exact h2
  · refine List.all_eq_true.mpr fun a _ => List.all_eq_true.mpr fun b _ => ?_
    cases hsm : (S.rexec F1 x).sm a b
    · rfl
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq]
    have sa := same_r H R hx hwf hrmw a
    have sb := same_r H R hx hwf hrmw b
    rw [E.sm a b _ _ rfl rfl] at hsm
    obtain ⟨h1, h2, h3, h4, h5⟩ := wf_sm hwf hsm
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [sa.act, sb.act]; exact h1
    · rw [Same.app (g := Ev.locked) (fun _ => rfl) sa, Same.app (g := Ev.locked) (fun _ => rfl) sb]
      exact h2
    · rw [Same.app (g := Ev.ann) (fun _ => rfl) sa, Same.app (g := Ev.ann) (fun _ => rfl) sb]
      exact h3
    · rw [sa.accAddr, sb.accAddr]; exact h4
    · rw [sa.accSize, sb.accSize]; exact h5
  · show (S.rexec F1 x).evs.all unitOk = true
    refine List.all_eq_true.mpr fun e he => ?_
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
    have hk' : k < (S.rexec F1 x).n := hk
    have sa := same_r H R hx hwf hrmw ⟨k, hk'⟩
    have := wf_ev hwf (List.getElem_mem (ι H R hx hwf hrmw ⟨k, hk'⟩).2)
    show unitOk ((S.rexec F1 x).ev ⟨k, hk'⟩) = true
    rw [Same.app (g := unitOk) (fun _ => rfl) sa]
    exact this

theorem readsOk_r
    (hro : ∀ r < x.n, (x.evN r).isR = true → x.readBytes ib r = (S.old.map Prod.snd).getD r []) :
    ∀ r < (S.rexec F1 x).n, ((S.rexec F1 x).evN r).isR = true →
      (S.rexec F1 x).readBytes ib r = (F1.map Prod.snd).getD r [] := by
  intro r hr hR
  rw [evN_r H R hx hwf hrmw hr] at hR
  have sr := same_r H R hx hwf hrmw ⟨r, hr⟩
  have hrF := lt_of_lt_of_eq hr (rn H R hx hwf hrmw)
  have hr1 : r < F1.length := by rw [R.len]; exact hrF
  have hsnd : (F1.map Prod.snd).getD r [] = (S.old.map Prod.snd).getD (S.A.length + r) [] := by
    have hro' : S.A.length + r < S.old.length := by rw [S.length_old']; omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_map, List.getElem?_eq_getElem hr1, List.getElem?_eq_getElem hro']
    simp only [Option.map_some, Option.getD_some]
    rw [R.relab r hr1 hrF, S.old_snd hro']
    simp only [show ¬ S.A.length + r < S.A.length by omega,
      show S.A.length + r < S.A.length + S.F.length by omega, dite_false, dite_true]
    congr 2; omega
  have hl0 : S.A.length + r < x.n := (ι H R hx hwf hrmw ⟨r, hr⟩).2
  rw [hsnd, ← hro (S.A.length + r) hl0 (by
    rw [evN_eq hl0]; change (x.ev (ι H R hx hwf hrmw ⟨r, hr⟩)).isR = true; rw [← sr.isR]; exact hR)]
  simp only [Exec.readBytes, evN_r H R hx hwf hrmw hr, evN_eq hl0]
  change ((S.rexec F1 x).ev ⟨r, hr⟩).bytes.map _ = (x.ev (ι H R hx hwf hrmw ⟨r, hr⟩)).bytes.map _
  rw [sr.bytes]
  refine List.map_congr_left fun y hy => ?_
  have hy' : ((S.rexec F1 x).ev ⟨r, hr⟩).covers y = true := by rw [sr.covers]; exact mem_bytes.mp hy
  show (match Option.map (· - S.A.length) (x.rf (S.A.length + r) y) with
    | none => ib y
    | some w => ((S.rexec F1 x).evN w).byte y) =
    (match x.rf (S.A.length + r) y with
    | none => ib y
    | some w => (x.evN w).byte y)
  cases h : x.rf (S.A.length + r) y with
  | none => rfl
  | some w =>
    obtain ⟨hw, h1, h2, -, -⟩ := rf_r H R hx hwf hrmw (r := ⟨r, hr⟩) hR hy' h
    have sw := same_ρ H R hx hwf hrmw hw h1 h2
    have hl : w - S.A.length < (S.rexec F1 x).n := (ρ H R hx hwf hrmw h1 h2).2
    simp only [Option.map_some, evN_r H R hx hwf hrmw hl, evN_eq hw]
    exact congrFun sw.byte y

theorem final_r {y : Nat} (hy : S.cb y = true) :
    writtenByte (S.rexec F1 x) y = writtenByte x y ∧
      (writtenByte x y = true → (S.rexec F1 x).finalByte ib y = x.finalByte ib y) := by
  constructor
  · apply Bool.eq_iff_iff.mpr
    rw [written_iff, written_iff]
    constructor
    · rintro ⟨w, hw, hW, hC⟩
      have sw := same_r H R hx hwf hrmw ⟨w, hw⟩
      refine ⟨_, (ι H R hx hwf hrmw ⟨w, hw⟩).2, ?_, ?_⟩
      · change (x.ev _).isW = true
        rw [← sw.isW]; exact hW
      · change (x.ev _).covers y = true
        rw [← sw.covers]; exact hC
    · rintro ⟨w, hw, hW, hC⟩
      obtain ⟨h1, h2⟩ := inF_of_on H R hx hwf hrmw hw (isM_of_W hW) hC hy
      have sw := same_ρ H R hx hwf hrmw hw h1 h2
      refine ⟨_, (ρ H R hx hwf hrmw h1 h2).2, ?_, ?_⟩
      · change ((S.rexec F1 x).ev _).isW = true
        rw [sw.isW]; exact hW
      · change ((S.rexec F1 x).ev _).covers y = true
        rw [sw.covers]; exact hC
  · intro hwr
    obtain ⟨w, hw, hW, hC⟩ := written_iff.mp hwr
    obtain ⟨-, hall, -⟩ := wf_co hwf (touched_of hw (isM_of_W hW) hC)
    simp only [Exec.finalByte]
    show (match ((if S.cb y then (x.co y).map (· - S.A.length) else [])).getLast? with
      | none => ib y
      | some w => ((S.rexec F1 x).evN w).byte y) =
      (match (x.co y).getLast? with
      | none => ib y
      | some w => (x.evN w).byte y)
    simp only [hy, ite_true, List.getLast?_map]
    cases hl : (x.co y).getLast? with
    | none => rfl
    | some u =>
      obtain ⟨hu, hUW, hUC⟩ := hall u (List.mem_of_getLast? hl)
      obtain ⟨h1, h2⟩ := inF_of_on H R hx hwf hrmw hu (isM_of_W hUW) hUC hy
      have su := same_ρ H R hx hwf hrmw hu h1 h2
      have hl' : u - S.A.length < (S.rexec F1 x).n := (ρ H R hx hwf hrmw h1 h2).2
      simp only [Option.map_some, evN_r H R hx hwf hrmw hl', evN_eq hu]
      exact congrFun su.byte y

end Surg

end Silmaril.Proofs.X86.Concurrency.Cir.Localize
