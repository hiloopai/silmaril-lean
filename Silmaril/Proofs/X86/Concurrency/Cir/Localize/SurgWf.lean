module

public import Silmaril.Proofs.X86.Concurrency.Cir.Localize.SurgCons

/-!
# Localisation: well-formedness, reads and final bytes of the new candidate

* `Surg.wf`: the new candidate is well-formed;
* `Surg.readsOk`: its reads return the units' expected bytes (kept reads as before, the block's
  reads the initial bytes);
* `Surg.final_off`, `Surg.final_on`: off the cells the written bytes and their final values are
  unchanged; on the cells a byte is written exactly when a block write covers it, and its final
  value is that of a block write.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Localize

open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte rmwPairs writtenByte)

namespace Surg

variable {S : Surg} {x : Exec} {ib : Nat → Byte}
set_option linter.unusedSectionVars false

theorem evN_new {k : Nat} (hk : k < (S.exec x).n) : (S.exec x).evN k = (S.exec x).ev ⟨k, hk⟩ :=
  evN_eq hk

theorem evN_old {k : Nat} (hk : k < x.n) : x.evN k = x.ev ⟨k, hk⟩ := evN_eq hk

theorem lt_new {k : Nat} (hk : k < S.G.length) : S.A.length + k < (S.exec x).n := by
  rw [n_new]; omega

theorem sm_symm' {z : Exec} {a b : Fin z.n} (h : z.sm a b = true) : z.sm b a = true := by
  simp only [Exec.sm, Bool.and_eq_true, beq_iff_eq] at h ⊢
  exact ⟨h.1.symm, h.2.symm⟩

variable (H : S.Hyp ib) (hx : x.evs = S.old.map Prod.fst) (hwf : x.Wf = true)
include H hx hwf

/-- The new index of an old unit off the fragment, as a unit. -/
theorem kept_of_old {w : Nat} (hw : w < x.n)
    (hF : ¬ (S.A.length ≤ w ∧ w < S.A.length + S.F.length)) :
    ∃ a : Fin (S.exec x).n, a.val = S.σ w ∧ κ hx a = some ⟨w, hw⟩ := by
  have hwo : w < S.old.length := by
    have := lt_of_lt_of_eq hw (n_old hx); rw [S.length_old']; exact this
  obtain ⟨h1, h2⟩ := S.σ_kept hwo hF
  refine ⟨⟨S.σ w, ?_⟩, rfl, κ_some.mpr h2⟩
  rw [S.length_new'] at h1; exact lt_of_lt_of_eq h1 n_new.symm

/-- An old write covering a byte off the cells is not a fragment unit. -/
theorem notF_of_off {w : Nat} (hw : w < x.n) (hM : (x.evs[w]).isM = true) {y : Nat}
    (hc : (x.evs[w]).covers y = true) (hy : S.cb y = false) :
    ¬ (S.A.length ≤ w ∧ w < S.A.length + S.F.length) := by
  rintro ⟨h1, h2⟩
  have he : x.evs[w] = (S.old.map Prod.fst)[w]'(by rw [← hx]; exact hw) := List.getElem_of_eq hx _
  rw [he, S.old_F h1 h2] at hM hc
  have := H.onF _ (List.getElem_mem _) hM y hc
  rw [hy] at this; cases this

/-- The source of a kept read, renamed. -/
theorem rf_src {r : Fin (S.exec x).n} {r0 : Fin x.n} (hr : κ hx r = some r0)
    (hR : ((S.exec x).ev r).isR = true) {y : Nat} (hy : ((S.exec x).ev r).covers y = true)
    {w : Nat} (h : x.rf r0.val y = some w) :
    ∃ hw : w < x.n, ∃ a : Fin (S.exec x).n, a.val = S.σ w ∧ κ hx a = some ⟨w, hw⟩ ∧
      (x.evs[w]).isW = true ∧ (x.evs[w]).covers y = true := by
  have sr := same_kept hx hr
  have hR0 : (x.evs[r0.val]).isR = true := by rw [← ev_eq, ← sr.isR]; exact hR
  have hy0 : (x.evs[r0.val]).covers y = true := by rw [← ev_eq, ← sr.covers]; exact hy
  obtain ⟨hw, hW, hC⟩ := wf_rf hwf r0.2 hR0 hy0 h
  have hcb := off_kept H hx hr (isM_of_R hR) hy
  obtain ⟨a, ha1, ha2⟩ := kept_of_old H hx hwf hw (notF_of_off H hx hwf hw (isM_of_W hW) hC hcb)
  exact ⟨hw, a, ha1, ha2, hW, hC⟩

/-! ## Well-formedness -/

theorem wf_reads : (List.finRange (S.exec x).n).all (fun r =>
    !((S.exec x).ev r).isR || ((S.exec x).ev r).bytes.all fun y =>
      match (S.exec x).rf r.val y with
      | none => true
      | some w => (S.exec x).valid w && ((S.exec x).evN w).isW && ((S.exec x).evN w).covers y) =
    true := by
  refine List.all_eq_true.mpr fun r _ => ?_
  cases hR : ((S.exec x).ev r).isR
  · rfl
  simp only [Bool.not_true, Bool.false_or, List.all_eq_true]
  intro y hy
  have hy' := mem_bytes.mp hy
  cases hr : κ hx r with
  | none =>
    have : (S.exec x).rf r.val y = none := by
      obtain ⟨h1, h2⟩ := κ_none.mp hr
      simp only [exec, show ¬ r.val < S.A.length by omega, h2, ite_true, ite_false]
    rw [this]
  | some r0 =>
    rw [rf_kept hx hr]
    cases h : x.rf r0.val y with
    | none => rfl
    | some w =>
      obtain ⟨hw, a, ha1, ha2, hW, hC⟩ := rf_src H hx hwf hr hR hy' h
      have sa := same_kept hx ha2
      simp only [Option.map_some, ← ha1, Exec.valid, a.2, decide_true, Bool.true_and,
        evN_new a.2, sa.isW, sa.covers]
      simp only [Exec.ev, Fin.getElem_fin, Bool.and_eq_true] at sa ⊢
      exact ⟨hW, hC⟩

theorem new_ev_G {k : Nat} (hk : k < S.G.length) (h : S.A.length + k < (S.exec x).n) :
    (S.exec x).ev ⟨S.A.length + k, h⟩ = (S.G[k]).1 := by
  rw [ev_eq]
  refine (S.new_G (by omega) (by omega) h).trans ?_
  simp

theorem wf_coh : (S.exec x).touched.all (fun y =>
    decide ((S.exec x).co y).Nodup && ((S.exec x).co y).all (fun w => (S.exec x).valid w &&
      ((S.exec x).evN w).isW && ((S.exec x).evN w).covers y) &&
    (List.finRange (S.exec x).n).all fun w =>
      !(((S.exec x).ev w).isW && ((S.exec x).ev w).covers y) || ((S.exec x).co y).contains w.val) =
    true := by
  refine List.all_eq_true.mpr fun y hy => ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_iff, List.contains_iff_mem]
  cases hcb : S.cb y
  · -- off the cells: the old order, renamed
    rw [co_off y hcb]
    obtain ⟨w, hw, hM, hC⟩ := mem_touched hy
    have hwk : κ hx ⟨w, hw⟩ ≠ none := fun hn => by
      have := on_block H hn hC; rw [hcb] at this; cases this
    obtain ⟨w0, hw0⟩ := Option.ne_none_iff_exists'.mp hwk
    have sw := same_kept hx hw0
    have hty : y ∈ x.touched :=
      touched_of w0.2 (by rw [← ev_eq, ← sw.isM]; exact hM) (by rw [← ev_eq, ← sw.covers]; exact hC)
    obtain ⟨hnd, hall, hcov⟩ := wf_co hwf hty
    have kept : ∀ u ∈ x.co y, ∃ a : Fin (S.exec x).n, ∃ hu : u < x.n, a.val = S.σ u ∧
        κ hx a = some ⟨u, hu⟩ := by
      intro u hu
      obtain ⟨hu', hW, hC'⟩ := hall u hu
      obtain ⟨a, h1, h2⟩ := kept_of_old H hx hwf hu' (notF_of_off H hx hwf hu' (isM_of_W hW) hC' hcb)
      exact ⟨a, hu', h1, h2⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine List.Nodup.map_on (fun u hu v hv he => ?_) hnd
      obtain ⟨a, hu', ha1, ha2⟩ := kept u hu
      exact ((σ_iff hx ha2 v).mp (he ▸ ha1).symm).symm
    · intro w' hw'
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw'
      obtain ⟨a, hu', ha1, ha2⟩ := kept u hu
      obtain ⟨hu'', hW, hC'⟩ := hall u hu
      have sa := same_kept hx ha2
      rw [← ha1, evN_new a.2]
      have hW' : ((S.exec x).ev a).isW = true := by rw [sa.isW]; exact hW
      have hC'' : ((S.exec x).ev a).covers y = true := by rw [sa.covers]; exact hC'
      exact ⟨⟨by simp [Exec.valid, a.2], hW'⟩, hC''⟩
    · intro w' _
      by_cases hwc : ((S.exec x).ev w').isW = true ∧ ((S.exec x).ev w').covers y = true
      · right
        have hk : κ hx w' ≠ none := fun hn => by
          have := on_block H hn hwc.2; rw [hcb] at this; cases this
        obtain ⟨w0', hw0'⟩ := Option.ne_none_iff_exists'.mp hk
        have sw' := same_kept hx hw0'
        have := hcov w0'.val w0'.2 (by rw [← ev_eq, ← sw'.isW]; exact hwc.1)
          (by rw [← ev_eq, ← sw'.covers]; exact hwc.2)
        exact List.mem_map.mpr ⟨w0'.val, this, (σ_iff hx hw0' _).mpr rfl⟩
      · left
        simp only [not_and_or, Bool.not_eq_true] at hwc
        exact hwc
  · -- on the cells: the block's writes in order
    rw [show (S.exec x).co y = S.gW y by simp [exec, hcb]]
    refine ⟨⟨(gW_sorted y).nodup, ?_⟩, ?_⟩
    · intro w hw
      obtain ⟨k, hk, rfl, hW, hC⟩ := mem_gW hw
      have hl := lt_new (x := x) hk
      rw [evN_new hl, new_ev_G H hx hwf hk hl]
      exact ⟨⟨by simp [Exec.valid, hl], hW⟩, hC⟩
    · intro w _
      by_cases hwc : ((S.exec x).ev w).isW = true ∧ ((S.exec x).ev w).covers y = true
      · right
        cases hk : κ hx w with
        | some w0 =>
          have := off_kept H hx hk (isM_of_W hwc.1) hwc.2
          rw [hcb] at this; cases this
        | none =>
          obtain ⟨k, hk', hwk, he⟩ := block_ev hk
          rw [he] at hwc
          rw [hwk]
          exact gW_of hk' hwc.1 hwc.2
      · left
        simp only [not_and_or, Bool.not_eq_true] at hwc
        exact hwc

variable (hrmw : x.rmw = rmwPairs x.evs)
include hrmw

theorem wf_rmw' : (S.exec x).rmw.all (fun p =>
    (S.exec x).valid p.1 && (S.exec x).valid p.2 && ((S.exec x).evN p.1).isR &&
    ((S.exec x).evN p.2).isW && ((S.exec x).evN p.1).tid == ((S.exec x).evN p.2).tid &&
    decide (((S.exec x).evN p.1).pos < ((S.exec x).evN p.2).pos) &&
    ((S.exec x).evN p.1).locked && ((S.exec x).evN p.2).locked &&
    ((S.exec x).evN p.1).accAddr == ((S.exec x).evN p.2).accAddr &&
    ((S.exec x).evN p.1).accSize == ((S.exec x).evN p.2).accSize) = true := by
  refine List.all_eq_true.mpr fun ⟨a, b⟩ hp => ?_
  have hp' : (a, b) ∈ rmwPairs (S.new.map Prod.fst) := hp
  obtain ⟨ha, hb, hR, hla, hW, hlb, ht, hpos, -, -⟩ := mem_rmwPairs_iff.mp hp'
  obtain ⟨a0, b0, ha0, hb0, hold⟩ := rmw_kept H hx hrmw ⟨a, ha⟩ ⟨b, hb⟩
    (by simp only [Exec.rmwR, List.contains_iff_mem]; exact hp)
  have hold' : (a0.val, b0.val) ∈ x.rmw := by
    simpa only [Exec.rmwR, List.contains_iff_mem] using hold
  obtain ⟨h1, h2⟩ := wf_rmw hwf hold'
  have sa := same_kept hx ha0
  have sb := same_kept hx hb0
  rw [evN_old a0.2, evN_old b0.2] at h1 h2
  simp only [Fin.eta] at h1 h2
  simp only [Exec.valid, evN_new ha, evN_new hb, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  change ((S.exec x).ev ⟨a, ha⟩).isR = true at hR
  change ((S.exec x).ev ⟨a, ha⟩).locked = true at hla
  change ((S.exec x).ev ⟨b, hb⟩).isW = true at hW
  change ((S.exec x).ev ⟨b, hb⟩).locked = true at hlb
  change ((S.exec x).ev ⟨a, ha⟩).tid = ((S.exec x).ev ⟨b, hb⟩).tid at ht
  change ((S.exec x).ev ⟨b, hb⟩).pos = ((S.exec x).ev ⟨a, ha⟩).pos + 1 at hpos
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hR⟩, hW⟩, ht⟩, by omega⟩, hla⟩, hlb⟩, ?_⟩, ?_⟩
  · rw [sa.accAddr, sb.accAddr]; exact h1
  · rw [sa.accSize, sb.accSize]; exact h2

theorem wf_sm' : (List.finRange (S.exec x).n).all (fun a => (List.finRange (S.exec x).n).all fun b =>
    !(S.exec x).sm a b || (((S.exec x).ev a).act == ((S.exec x).ev b).act &&
      ((S.exec x).ev a).locked == ((S.exec x).ev b).locked &&
      ((S.exec x).ev a).ann == ((S.exec x).ev b).ann &&
      ((S.exec x).ev a).accAddr == ((S.exec x).ev b).accAddr &&
      ((S.exec x).ev a).accSize == ((S.exec x).ev b).accSize)) = true := by
  refine List.all_eq_true.mpr fun a _ => List.all_eq_true.mpr fun b _ => ?_
  cases hsm : (S.exec x).sm a b
  · rfl
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq]
  cases ha : κ hx a with
  | none =>
    have := sm_block H hx ha (sm_symm' hsm); subst this
    exact ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩
  | some a0 =>
    cases hb : κ hx b with
    | none =>
      have := sm_block H hx hb hsm; subst this
      exact ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    | some b0 =>
      have sa := same_kept hx ha
      have sb := same_kept hx hb
      rw [sm_kept H hx ha hb] at hsm
      obtain ⟨h1, h2, h3, h4, h5⟩ := wf_sm hwf hsm
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · rw [sa.act, sb.act]; exact h1
      · rw [Same.app (g := Ev.locked) (fun _ => rfl) sa, Same.app (g := Ev.locked) (fun _ => rfl) sb]
        exact h2
      · rw [Same.app (g := Ev.ann) (fun _ => rfl) sa, Same.app (g := Ev.ann) (fun _ => rfl) sb]
        exact h3
      · rw [sa.accAddr, sb.accAddr]; exact h4
      · rw [sa.accSize, sb.accSize]; exact h5

/-- The per-unit condition of `Wf`. -/
def unitOk (e : Ev) : Bool :=
  if e.isM then
    decide (0 < e.size) && decide (e.accAddr ≤ e.addr) &&
      decide (e.addr + e.size ≤ e.accAddr + e.accSize) && (!e.isW || e.data.length == e.size)
  else e.size == 0

theorem wf_units : (S.exec x).evs.all unitOk = true := by
  refine List.all_eq_true.mpr fun e he => ?_
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
  have hk' : k < (S.exec x).n := hk
  cases ha : κ hx ⟨k, hk'⟩ with
  | none =>
    obtain ⟨j, hj, -, he'⟩ := block_ev ha
    change (S.exec x).ev ⟨k, hk'⟩ = _ at he'
    show unitOk ((S.exec x).ev ⟨k, hk'⟩) = true
    rw [he']
    obtain ⟨hRW, -, -, hsz, hA, hS, hD⟩ := H.memG _ (List.getElem_mem (h := hj))
    have hM : (S.G[j]).1.isM = true := by rcases hRW with h | h <;> simp [Ev.isM, h]
    simp only [unitOk, hM, ite_true, hsz, decide_true, hA, hS, le_refl, Bool.true_and,
      Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq]
    cases hW : (S.G[j]).1.isW
    · exact .inl rfl
    · exact .inr (hD hW)
  | some a0 =>
    have sa := same_kept hx ha
    have := wf_ev hwf (List.getElem_mem a0.2 : x.evs[a0.val] ∈ x.evs)
    show unitOk ((S.exec x).ev ⟨k, hk'⟩) = true
    rw [Same.app (g := unitOk) (fun _ => rfl) sa]
    exact this

/-- **The new candidate is well-formed.** -/
theorem wf : (S.exec x).Wf = true := by
  have h5 := wf_units H hx hwf hrmw
  simp only [Exec.Wf, Bool.and_eq_true]
  exact ⟨⟨⟨⟨wf_reads H hx hwf, wf_coh H hx hwf⟩, wf_rmw' H hx hwf hrmw⟩, wf_sm' H hx hwf hrmw⟩, h5⟩

omit hrmw in
theorem snd_kept {r : Fin (S.exec x).n} {r0 : Fin x.n} (hr : κ hx r = some r0) :
    (S.new.map Prod.snd).getD r.val [] = (S.old.map Prod.snd).getD r0.val [] := by
  have hrn : r.val < S.new.length := by
    have := lt_of_lt_of_eq r.2 n_new; rw [S.length_new']; exact this
  have hro : r0.val < S.old.length := by
    have := lt_of_lt_of_eq r0.2 (n_old hx); rw [S.length_old']; exact this
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_map, List.getElem?_eq_getElem hrn, List.getElem?_eq_getElem hro]
  simp only [Option.map_some, Option.getD_some]
  rw [S.new_snd hrn, S.old_snd hro]
  rcases S.κN_some (κ_some.mp hr) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [h2, h1, dite_true]
  · have h3 : ¬ r.val < S.A.length := by omega
    have h4 : ¬ r.val < S.A.length + S.G.length := by omega
    have h5 : ¬ r0.val < S.A.length := by omega
    have h6 : ¬ r0.val < S.A.length + S.F.length := by omega
    simp only [h3, h4, h5, h6, dite_false]
    congr 2; omega

omit hrmw in
/-- **The reads of the new candidate are right.** -/
theorem readsOk
    (hro : ∀ r < x.n, (x.evN r).isR = true → x.readBytes ib r = (S.old.map Prod.snd).getD r []) :
    ∀ r < (S.exec x).n, ((S.exec x).evN r).isR = true →
      (S.exec x).readBytes ib r = (S.new.map Prod.snd).getD r [] := by
  intro r hr hR
  rw [evN_new hr] at hR
  cases hk : κ hx ⟨r, hr⟩ with
  | none =>
    obtain ⟨k, hk', hrk, he⟩ := block_ev hk
    have hrn : r < S.new.length := by
      have := lt_of_lt_of_eq hr n_new; rw [S.length_new']; exact this
    have hnone : ∀ y, (S.exec x).rf r y = none := by
      intro y
      obtain ⟨h1, h2⟩ := κ_none.mp hk
      have h1' : S.A.length ≤ r := h1
      have h2' : r < S.A.length + S.G.length := h2
      simp only [exec, show ¬ r < S.A.length by omega, h2', ite_true, ite_false]
    have hrb : (S.exec x).readByte ib r = ib := by
      funext y; simp only [Exec.readByte, hnone]
    simp only [Exec.readBytes, hrb, evN_new hr, he]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hrn]
    simp only [Option.map_some, Option.getD_some]
    rw [S.new_snd hrn]
    have hrk' : r = S.A.length + k := hrk
    have h3 : ¬ r < S.A.length := by omega
    have h4 : r < S.A.length + S.G.length := by omega
    simp only [h3, h4, dite_false, dite_true]
    have hkk : r - S.A.length = k := by omega
    simp only [hkk]
    rw [he] at hR
    exact (H.readG _ (List.getElem_mem (h := hk')) hR).symm
  | some r0 =>
    have sr := same_kept hx hk
    rw [snd_kept H hx hwf hk, ← hro r0.val r0.2 (by rw [evN_old r0.2]; rw [← sr.isR]; exact hR)]
    simp only [Exec.readBytes, evN_new hr, evN_old r0.2, Fin.eta, sr.bytes]
    refine List.map_congr_left fun y hy => ?_
    have hy' : ((S.exec x).ev ⟨r, hr⟩).covers y = true := by
      rw [sr.covers]; exact mem_bytes.mp hy
    simp only [Exec.readByte]
    rw [rf_kept hx hk]
    cases h : x.rf r0.val y with
    | none => rfl
    | some w =>
      obtain ⟨hw, a, ha1, ha2, -, -⟩ := rf_src H hx hwf hk hR hy' h
      simp only [Option.map_some, ← ha1, evN_new a.2, evN_old hw, Fin.eta]
      rw [(same_kept hx ha2).byte]

omit hrmw in
/-- **Final bytes off the cells are unchanged.** -/
theorem final_off {y : Nat} (hy : S.cb y = false) :
    writtenByte (S.exec x) y = writtenByte x y ∧
      (writtenByte x y = true → (S.exec x).finalByte ib y = x.finalByte ib y) := by
  constructor
  · apply Bool.eq_iff_iff.mpr
    rw [written_iff, written_iff]
    constructor
    · rintro ⟨w, hw, hW, hC⟩
      have hk : κ hx ⟨w, hw⟩ ≠ none := fun hn => by
        have := on_block H hn hC; rw [hy] at this; cases this
      obtain ⟨w0, hw0⟩ := Option.ne_none_iff_exists'.mp hk
      have sw := same_kept hx hw0
      exact ⟨w0.val, w0.2, by rw [← ev_eq, ← sw.isW]; exact hW, by rw [← ev_eq, ← sw.covers]; exact hC⟩
    · rintro ⟨w, hw, hW, hC⟩
      obtain ⟨a, -, ha⟩ := kept_of_old H hx hwf hw (notF_of_off H hx hwf hw (isM_of_W hW) hC hy)
      have sa := same_kept hx ha
      exact ⟨a.val, a.2, by rw [← ev_eq, sa.isW]; exact hW, by rw [← ev_eq, sa.covers]; exact hC⟩
  · intro hwr
    obtain ⟨w, hw, hW, hC⟩ := written_iff.mp hwr
    have hty : y ∈ x.touched := touched_of hw (isM_of_W hW) hC
    obtain ⟨-, hall, -⟩ := wf_co hwf hty
    simp only [Exec.finalByte, co_off y hy, List.getLast?_map]
    cases hl : (x.co y).getLast? with
    | none => rfl
    | some u =>
      obtain ⟨hu, hUW, hUC⟩ := hall u (List.mem_of_getLast? hl)
      obtain ⟨a, ha1, ha2⟩ := kept_of_old H hx hwf hu (notF_of_off H hx hwf hu (isM_of_W hUW) hUC hy)
      simp only [Option.map_some, ← ha1, evN_new a.2, evN_old hu, Fin.eta]
      rw [(same_kept hx ha2).byte]

omit hrmw in
/-- **Final bytes on the cells come from the block's writes.** -/
theorem final_on {y : Nat} (hy : S.cb y = true) :
    (writtenByte (S.exec x) y = true ↔
      ∃ k, ∃ hk : k < S.G.length, (S.G[k]).1.isW = true ∧ (S.G[k]).1.covers y = true) ∧
    (writtenByte (S.exec x) y = true → ∃ k, ∃ hk : k < S.G.length, (S.G[k]).1.isW = true ∧
      (S.G[k]).1.covers y = true ∧ (S.exec x).finalByte ib y = (S.G[k]).1.byte y) := by
  have hco : (S.exec x).co y = S.gW y := by simp [exec, hy]
  have hw1 : writtenByte (S.exec x) y = true ↔
      ∃ k, ∃ hk : k < S.G.length, (S.G[k]).1.isW = true ∧ (S.G[k]).1.covers y = true := by
    rw [written_iff]
    constructor
    · rintro ⟨w, hw, hW, hC⟩
      cases hk : κ hx ⟨w, hw⟩ with
      | some w0 =>
        have := off_kept H hx hk (isM_of_W hW) hC
        rw [hy] at this; cases this
      | none =>
        obtain ⟨k, hk', -, he⟩ := block_ev hk
        change (S.exec x).ev ⟨w, hw⟩ = _ at he
        exact ⟨k, hk', by rw [← he]; exact hW, by rw [← he]; exact hC⟩
    · rintro ⟨k, hk, hW, hC⟩
      have hl := lt_new (x := x) hk
      refine ⟨_, hl, ?_, ?_⟩
      · change ((S.exec x).ev ⟨_, hl⟩).isW = true; rw [new_ev_G H hx hwf hk hl]; exact hW
      · change ((S.exec x).ev ⟨_, hl⟩).covers y = true; rw [new_ev_G H hx hwf hk hl]; exact hC
  refine ⟨hw1, fun hwr => ?_⟩
  obtain ⟨k, hk, hW, hC⟩ := hw1.mp hwr
  have hne : S.gW y ≠ [] := by
    intro h; have := gW_of hk hW hC; rw [h] at this; simp at this
  obtain ⟨w, hw⟩ : ∃ w, (S.gW y).getLast? = some w :=
    ⟨(S.gW y).getLast hne, List.getLast?_eq_some_getLast hne⟩
  obtain ⟨k', hk', rfl, hW', hC'⟩ := mem_gW (List.mem_of_getLast? hw)
  refine ⟨k', hk', hW', hC', ?_⟩
  have hl := lt_new (x := x) hk'
  simp only [Exec.finalByte, hco, hw, evN_new hl, new_ev_G H hx hwf hk' hl]

end Surg

end Silmaril.Proofs.X86.Concurrency.Cir.Localize
