module

public import Silmaril.X86.Concurrency.Cir.Futex.Progs.Defs
public import Silmaril.X86.MemoryModel.Litmus.Models.Defs
public import Silmaril.X86.MemoryModel.Axiomatic.Thms
public import Silmaril.X86.Concurrency.Cir.Tv.CFutex.Defs

/-!
# Drepper's futex mutex under XL: the proof

`mutex_xl`: in every
XL behaviour of `Futex.Progs.mutex 1` over the domain `[0, 1, 2]`, the counter is `2`. This
discharges `Tv.CFutex.Task.mutexXl`.

No enumeration of the `210 × 210` trace combinations: a direct `ghbXl` argument over any
candidate execution, plus one kernel `decide` per thread over its own 210 runs.

* **Per-thread check** (`good`, decided for each thread's 210 runs, `good0_all`, `good1_all`):
  every unit lies in one of five disjoint aligned cells (so nothing tears and `units` is the
  unsplit `accUnits`); the run has an *acquiring* locked read of the mutex word reading `0`
  (lowest byte), whose locked write half leaves a nonzero lowest byte; then the counter load
  (value `v`) and the counter store (`v + 1`), the only store of the counter; and every store
  of the mutex word with lowest byte `0` (the unlock's `fetch_sub` from `1`, or its store `0`)
  comes after the counter store.
* **Core** (`core`): order the two acquiring writes in the coherence order of the mutex word's
  lowest byte; say `i`'s is first. Then `j`'s acquiring read cannot read the initial value
  (that would be `fre; coe` across the RMW: atomicity), and reads a `0` written by `i` after its
  counter store (a write of `j` after the read would be a `po-loc; rf` cycle). So
  `i`'s counter store, then (`ppo`) the unlock's write, then (`rfe`) `j`'s acquire, then
  (`ppo`) `j`'s counter accesses form a `ghbXl` path. Hence `j`'s load reads `i`'s store, `i`'s
  load reads the initial `0` (anything else closes a `ghbXl` or `uniproc` cycle), and `j`'s
  store of `2` is coherence-last.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.TvCFutexMutex

open Silmaril.X86.Concurrency.Cir Silmaril.X86.Concurrency.Cir.Futex.Progs
open Silmaril.X86.MemoryModel.Litmus Silmaril.X86.MemoryModel.Axiomatic
open Relation


theorem mem_tail {c a : Nat} {l : List Nat} (h : a ∈ c :: l) (hne : c ≠ a) : a ∈ l := by
  rcases List.mem_cons.mp h with h | h
  · exact absurd h.symm hne
  · exact h

theorem before_total : ∀ {l : List Nat} {a b : Nat}, a ∈ l → b ∈ l → a ≠ b →
    before l a b = true ∨ before l b a = true
  | [], _, _, ha, _, _ => by simp at ha
  | c :: l, a, b, ha, hb, hab => by
    simp only [before]
    by_cases hca : c = a
    · subst hca
      have := mem_tail hb hab
      left; simp [this]
    · by_cases hcb : c = b
      · subst hcb
        have := mem_tail ha hca
        right; simp [this]
      · have := before_total (mem_tail ha hca) (mem_tail hb hcb) hab
        simpa [beq_iff_eq, hca, hcb] using this

theorem before_last : ∀ {l : List Nat} {b c : Nat}, b ∈ l → l.getLast? = some c → b ≠ c →
    before l b c = true
  | [], _, _, hb, _, _ => by simp at hb
  | d :: l, b, c, hb, hl, hbc => by
    simp only [before]
    by_cases hdb : d = b
    · subst hdb
      cases l with
      | nil => simp at hl; exact absurd hl hbc
      | cons e l =>
        rw [List.getLast?_cons_cons] at hl
        simp only [beq_self_eq_true, ite_true, List.contains_iff_mem]
        exact List.mem_of_getLast? hl
    · have hb' := mem_tail hb hdb
      cases l with
      | nil => simp at hb'
      | cons e l =>
        rw [List.getLast?_cons_cons] at hl
        simpa [beq_iff_eq, hdb] using before_last hb' hl hbc


/-! ## Edges of an execution -/

variable {x : Exec}

theorem union_l {n : Nat} {r s : BRel n} {a b : Fin n} (h : r a b = true) : (r.union s) a b = true := by
  simp [BRel.union, h]

theorem union_r {n : Nat} {r s : BRel n} {a b : Fin n} (h : s a b = true) : (r.union s) a b = true := by
  simp [BRel.union, h]

theorem seq_smT {r : BRel x.n} {a b : Fin x.n} (h : r a b = true) : (r.seq x.smT) a b = true := by
  simp only [BRel.seq, List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true]
  exact ⟨b, h, by simp [Exec.smT]⟩

theorem po_of {a b : Fin x.n} (ht : (x.ev a).tid = (x.ev b).tid) (hp : (x.ev a).pos < (x.ev b).pos) :
    x.po a b = true := by
  simp [Exec.po, ht, hp]

theorem ghb_RM {a b : Fin x.n} (ht : (x.ev a).tid = (x.ev b).tid) (hp : (x.ev a).pos < (x.ev b).pos)
    (ha : (x.ev a).isR = true) (hb : (x.ev b).isM = true) (hwb : (x.ev b).weak = false) :
    x.ghbXl a b = true := by
  have hwa : (x.ev a).weak = false := by
    simp only [Ev.weak, Bool.and_eq_false_iff]; left
    simp only [Ev.isR, beq_iff_eq] at ha; simp [Ev.isW, ha]
  apply union_r; apply union_l
  simp [Exec.ppoXl, Exec.ppo, po_of ht hp, ha, hb, hwa, hwb]

theorem ghb_WW {a b : Fin x.n} (ht : (x.ev a).tid = (x.ev b).tid) (hp : (x.ev a).pos < (x.ev b).pos)
    (ha : (x.ev a).isW = true) (hb : (x.ev b).isW = true) (hwa : (x.ev a).weak = false)
    (hwb : (x.ev b).weak = false) : x.ghbXl a b = true := by
  apply union_r; apply union_l
  simp [Exec.ppoXl, Exec.ppo, po_of ht hp, ha, hb, hwa, hwb]

theorem ghb_com {a b : Fin x.n} (h : (x.rfe.union (x.frR.union x.coR)) a b = true) : x.ghbXl a b = true := by
  apply union_r; apply union_r; apply union_r; apply union_r
  exact seq_smT h

theorem rfR_of {w r : Fin x.n} {y : Nat} (hw : (x.ev w).isW = true) (hr : (x.ev r).isR = true)
    (hy : y ∈ (x.ev r).bytes) (hrf : x.rf r.val y = some w.val) (hc : (x.ev w).covers y = true) :
    x.rfR w r = true := by
  simp only [Exec.rfR, hw, hr, Bool.true_and, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  exact ⟨y, hy, hrf, hc⟩

theorem frR_of {r w : Fin x.n} {y : Nat} (hr : (x.ev r).isR = true) (hw : (x.ev w).isW = true)
    (hy : y ∈ (x.ev r).bytes) (hc : (x.ev w).covers y = true)
    (hrf : match x.rf r.val y with | none => True | some v => before (x.co y) v w.val = true) :
    x.frR r w = true := by
  simp only [Exec.frR, hr, hw, Bool.true_and, List.any_eq_true, Bool.and_eq_true]
  refine ⟨y, hy, hc, ?_⟩
  revert hrf; cases x.rf r.val y <;> simp

theorem coR_of {a b : Fin x.n} {y : Nat} (ha : (x.ev a).isW = true) (hb : (x.ev b).isW = true)
    (hy : y ∈ (x.ev a).bytes) (hc : (x.ev b).covers y = true) (hbf : before (x.co y) a.val b.val = true) :
    x.coR a b = true := by
  simp only [Exec.coR, ha, hb, Bool.true_and, List.any_eq_true, Bool.and_eq_true]
  exact ⟨y, hy, hc, hbf⟩

theorem ext_of {a b : Fin x.n} (h : (x.ev a).tid ≠ (x.ev b).tid) : x.ext a b = true := by
  simp [Exec.ext, h]

theorem rfe_of {w r : Fin x.n} (h : x.rfR w r = true) (he : (x.ev w).tid ≠ (x.ev r).tid) :
    (x.rfe.union (x.frR.union x.coR)) w r = true := by
  apply union_l; simp [Exec.rfe, BRel.inter, h, ext_of he]

theorem fr_ghb {r w : Fin x.n} (h : x.frR r w = true) : x.ghbXl r w = true :=
  ghb_com (union_r (union_l h))

theorem co_ghb {a b : Fin x.n} (h : x.coR a b = true) : x.ghbXl a b = true :=
  ghb_com (union_r (union_r h))

/-- Coherence with a read reading from a `po`-later write of the same cell is a cycle. -/
theorem uniproc_rf {r w : Fin x.n} (hx : x.Xl) (hpo : x.po r w = true) (hloc : x.loc r w = true)
    (hrf : x.rfR w r = true) : False := by
  apply hx.2.1 r
  refine TransGen.tail (TransGen.single (b := w) ?_) ?_
  · exact union_l (by simp [Exec.poLoc, BRel.inter, hpo, hloc])
  · exact union_r (seq_smT (union_l hrf))

theorem loc_of {a b : Fin x.n} {y : Nat} (ha : (x.ev a).isM = true) (hb : (x.ev b).isM = true)
    (hy : y ∈ (x.ev a).bytes) (hc : (x.ev b).covers y = true) : x.loc a b = true := by
  simp only [Exec.loc, ha, hb, Bool.true_and, List.any_eq_true]
  exact ⟨y, hy, hc⟩

theorem cycle {r : BRel x.n} (hr : BRel.Acyclic r) {a b : Fin x.n} (h1 : TransGen r.Holds a b)
    (h2 : TransGen r.Holds b a) : False := hr a (h1.trans h2)

/-! ## Well-formedness -/

theorem evN_eq (i : Nat) (h : i < x.n) : x.evN i = x.ev ⟨i, h⟩ := by
  simp [Exec.evN, Exec.ev, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem wf_rf (hwf : x.Wf = true) {r : Fin x.n} (hr : (x.ev r).isR = true) {y : Nat}
    (hy : y ∈ (x.ev r).bytes) {w : Nat} (h : x.rf r.val y = some w) :
    ∃ hw : w < x.n, (x.ev ⟨w, hw⟩).isW = true ∧ (x.ev ⟨w, hw⟩).covers y = true := by
  simp only [Exec.Wf, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at hwf
  have := hwf.1.1.1.1 r
  simp only [hr, Bool.not_true, Bool.false_or, List.all_eq_true] at this
  have := this y hy
  rw [h] at this
  simp only [Exec.valid, Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨hv, hW⟩, hc⟩ := this
  rw [evN_eq w hv] at hW hc
  exact ⟨hv, hW, hc⟩

theorem covers_iff (e : Ev) (y : Nat) : e.covers y = true ↔ y ∈ e.bytes := by
  simp [Ev.covers, Ev.bytes, List.mem_range'_1]

theorem touched_of {w : Fin x.n} (hM : (x.ev w).isM = true) {y : Nat} (hc : (x.ev w).covers y = true) :
    y ∈ x.touched := by
  simp only [Exec.touched, List.mem_flatMap, List.mem_filter]
  exact ⟨x.ev w, ⟨List.getElem_mem _, hM⟩, (covers_iff _ _).mp hc⟩

theorem wf_co (hwf : x.Wf = true) {y : Nat} (hy : y ∈ x.touched) {w : Nat} (h : w ∈ x.co y) :
    ∃ hw : w < x.n, (x.ev ⟨w, hw⟩).isW = true ∧ (x.ev ⟨w, hw⟩).covers y = true := by
  simp only [Exec.Wf, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at hwf
  have := (hwf.1.1.1.2 y hy).1.2 w h
  simp only [Exec.valid, decide_eq_true_eq] at this
  obtain ⟨⟨hv, hW⟩, hc⟩ := this
  rw [evN_eq w hv] at hW hc
  exact ⟨hv, hW, hc⟩

theorem wf_co_mem (hwf : x.Wf = true) {w : Fin x.n} (hW : (x.ev w).isW = true) {y : Nat}
    (hc : (x.ev w).covers y = true) : w.val ∈ x.co y := by
  have hy : y ∈ x.touched := touched_of (by simp [Ev.isM, hW]) hc
  simp only [Exec.Wf, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at hwf
  have := (hwf.1.1.1.2 y hy).2 w
  simp only [hW, hc, Bool.and_self, Bool.not_true, Bool.false_or, List.contains_iff_mem] at this
  exact this


/-! ## The core argument -/

/-- The cells of the mutex test. -/
def cells : List (Nat × Nat) := [(mW, 4), (cnt, 4), (d0, 4), (d1, 4), (qAddr mW, 1)]

theorem cell_cnt {a s y : Nat} (h : (a, s) ∈ cells) (h1 : a ≤ y) (h2 : y < a + s) (h3 : cnt ≤ y)
    (h4 : y < cnt + 4) : a = cnt ∧ s = 4 := by
  simp only [cells, qAddr, cnt, mW, d0, d1, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
    or_false] at h h3 h4 ⊢
  omega

theorem cell_mW {a s : Nat} (h : (a, s) ∈ cells) (h1 : a ≤ mW) (h2 : mW < a + s) : a = mW ∧ s = 4 := by
  simp only [cells, qAddr, cnt, mW, d0, d1, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
    or_false] at h h1 h2 ⊢
  omega

theorem cell_size_cnt {s : Nat} (h : (cnt, s) ∈ cells) : s = 4 := by
  simp only [cells, qAddr, cnt, mW, d0, d1, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
    or_false] at h
  omega

/-- What the proof needs of one thread `i` of an execution. -/
structure TF (x : Exec) (init : Nat → Byte) (i : Nat) where
  ar : Fin x.n
  aw : Fin x.n
  rc : Fin x.n
  wc : Fin x.n
  v : Nat
  hv : v ≤ 2
  ar_tid : (x.ev ar).tid = i
  ar_R : (x.ev ar).isR = true
  ar_addr : (x.ev ar).addr = mW
  ar_size : (x.ev ar).size = 4
  ar_rd : x.readByte init ar.val mW = 0
  aw_tid : (x.ev aw).tid = i
  aw_W : (x.ev aw).isW = true
  aw_addr : (x.ev aw).addr = mW
  aw_size : (x.ev aw).size = 4
  aw_byte : (x.ev aw).byte mW ≠ 0
  rmw : x.rmwR ar aw = true
  rc_tid : (x.ev rc).tid = i
  rc_R : (x.ev rc).isR = true
  rc_addr : (x.ev rc).addr = cnt
  rc_size : (x.ev rc).size = 4
  rc_pos : (x.ev ar).pos < (x.ev rc).pos
  rc_rd : x.readBytes init rc.val = natBytes v 4
  wc_tid : (x.ev wc).tid = i
  wc_W : (x.ev wc).isW = true
  wc_addr : (x.ev wc).addr = cnt
  wc_size : (x.ev wc).size = 4
  wc_ann : (x.ev wc).ann = .wb
  wc_pos : (x.ev rc).pos < (x.ev wc).pos
  wc_data : (x.ev wc).data = natBytes (v + 1) 4
  cntW : ∀ a, (x.ev a).tid = i → (x.ev a).isW = true → (x.ev a).addr = cnt → a = wc
  m0 : ∀ a, (x.ev a).tid = i → (x.ev a).isW = true → (x.ev a).addr = mW →
    (x.ev a).byte mW = 0 → (x.ev wc).pos < (x.ev a).pos

theorem mem_bytes {e : Ev} {a s y : Nat} (ha : e.addr = a) (hs : e.size = s) (h1 : a ≤ y)
    (h2 : y < a + s) : y ∈ e.bytes := by
  simp [Ev.bytes, List.mem_range'_1]; omega

theorem covers_of {e : Ev} {a s y : Nat} (ha : e.addr = a) (hs : e.size = s) (h1 : a ≤ y)
    (h2 : y < a + s) : e.covers y = true := (covers_iff _ _).mpr (mem_bytes ha hs h1 h2)

theorem isM_of_R {e : Ev} (h : e.isR = true) : e.isM = true := by simp [Ev.isM, h]
theorem isM_of_W {e : Ev} (h : e.isW = true) : e.isM = true := by simp [Ev.isM, h]
theorem weak_of_ann {e : Ev} (h : e.ann = .wb) : e.weak = false := by simp [Ev.weak, h]
theorem notR_of_W {e : Ev} (h : e.isW = true) : e.isR = false := by
  simp only [Ev.isW, beq_iff_eq] at h; simp [Ev.isR, h]

theorem weak_of_R {e : Ev} (h : e.isR = true) : e.weak = false := by
  simp only [Ev.isR, beq_iff_eq] at h; simp [Ev.weak, Ev.isW, h]

theorem natBytes_inj {v w : Nat} (hv : v ≤ 2) (hw : w ≤ 2) (h : natBytes v 4 = natBytes w 4) : v = w := by
  have hv' : v = 0 ∨ v = 1 ∨ v = 2 := by omega
  have hw' : w = 0 ∨ w = 1 ∨ w = 2 := by omega
  rcases hv' with rfl | rfl | rfl <;> rcases hw' with rfl | rfl | rfl <;> first | rfl | (revert h; decide)

theorem readBytes_cnt {init : Nat → Byte} (r : Fin x.n) (ha : (x.ev r).addr = cnt) (hs : (x.ev r).size = 4) :
    x.readBytes init r.val =
      [x.readByte init r.val cnt, x.readByte init r.val (cnt + 1), x.readByte init r.val (cnt + 2),
        x.readByte init r.val (cnt + 3)] := by
  simp [Exec.readBytes, evN_eq r.val r.isLt, Ev.bytes, ha, hs, List.range']

theorem tidW {i j : Nat} (htid : ∀ a : Fin x.n, (x.ev a).tid = i ∨ (x.ev a).tid = j) {init : Nat → Byte}
    (A : TF x init i) (B : TF x init j) (a : Fin x.n) (hW : (x.ev a).isW = true)
    (ha : (x.ev a).addr = cnt) : a = A.wc ∨ a = B.wc := by
  rcases htid a with h | h
  · exact Or.inl (A.cntW a h hW ha)
  · exact Or.inr (B.cntW a h hW ha)

/-- **The core argument**: if thread `i`'s acquiring write is coherence-before thread `j`'s,
thread `j` increments after thread `i`, and its store of `2` is coherence-last. -/
theorem core (hx : x.Xl) (hwf : x.Wf = true) {init : Nat → Byte}
    (hinit : ∀ y, cnt ≤ y → y < cnt + 4 → init y = 0)
    (hcell : ∀ a : Fin x.n, (x.ev a).isM = true → ((x.ev a).addr, (x.ev a).size) ∈ cells ∧ (x.ev a).ann = .wb)
    {i j : Nat} (hij : i ≠ j) (htid : ∀ a : Fin x.n, (x.ev a).tid = i ∨ (x.ev a).tid = j)
    (A : TF x init i) (B : TF x init j)
    (hco : before (x.co mW) A.aw.val B.aw.val = true) :
    (x.ev B.wc).data = natBytes 2 4 ∧ (x.ev B.wc).addr = cnt ∧
      ∀ y, cnt ≤ y → y < cnt + 4 → (x.co y).getLast? = some B.wc.val := by
  have hghb : BRel.Acyclic x.ghbXl := hx.2.2.2
  have hBar : mW ∈ (x.ev B.ar).bytes := mem_bytes B.ar_addr B.ar_size (le_refl _) (by omega)
  -- Step A: the acquiring read of `j` reads a `0` written by `i`'s unlock.
  obtain ⟨w, hw⟩ : ∃ w, x.rf B.ar.val mW = some w := by
    cases h : x.rf B.ar.val mW with
    | some w => exact ⟨w, rfl⟩
    | none =>
      exfalso
      have hfre : x.fre B.ar A.aw = true := by
        simp only [Exec.fre, BRel.inter, Bool.and_eq_true]
        refine ⟨frR_of B.ar_R A.aw_W hBar (covers_of A.aw_addr A.aw_size (le_refl _) (by omega))
          (by rw [h]; trivial), ext_of (by rw [B.ar_tid, A.aw_tid]; exact Ne.symm hij)⟩
      have hcoe : x.coe A.aw B.aw = true := by
        simp only [Exec.coe, BRel.inter, Bool.and_eq_true]
        refine ⟨coR_of A.aw_W B.aw_W (mem_bytes A.aw_addr A.aw_size (le_refl _) (by omega))
          (covers_of B.aw_addr B.aw_size (le_refl _) (by omega)) hco,
          ext_of (by rw [A.aw_tid, B.aw_tid]; exact hij)⟩
      have hseq : (x.fre.seq x.coe) B.ar B.aw = true := by
        simp only [BRel.seq, List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true]
        exact ⟨A.aw, hfre, hcoe⟩
      have := (BRel.emptyB_iff _).mp hx.1 B.ar B.aw
      simp [BRel.inter, B.rmw, hseq] at this
  obtain ⟨hwlt, hwW, hwc⟩ := wf_rf hwf B.ar_R hBar hw
  set W : Fin x.n := ⟨w, hwlt⟩ with hWdef
  have hW0 : (x.ev W).byte mW = 0 := by
    have := B.ar_rd
    simp only [Exec.readByte, hw, evN_eq w hwlt] at this
    exact this
  obtain ⟨hWc, hWann⟩ := hcell W (isM_of_W hwW)
  have hWaddr : (x.ev W).addr = mW := by
    have := (covers_iff _ _).mp hwc
    simp only [Ev.bytes, List.mem_range'_1] at this
    exact (cell_mW hWc this.1 this.2).1
  have hrf : x.rfR W B.ar = true := rfR_of hwW B.ar_R hBar hw hwc
  have hWi : (x.ev W).tid = i := by
    rcases htid W with h | h
    · exact h
    · exfalso
      have hp := B.m0 W h hwW hWaddr hW0
      exact uniproc_rf hx (po_of (by rw [B.ar_tid, h]) (by have := B.rc_pos; have := B.wc_pos; omega))
        (loc_of (isM_of_R B.ar_R) (isM_of_W hwW) hBar hwc) hrf
  have hWpos := A.m0 W hWi hwW hWaddr hW0
  have e1 : x.ghbXl A.wc W = true :=
    ghb_WW (by rw [A.wc_tid, hWi]) hWpos A.wc_W hwW (weak_of_ann A.wc_ann) (weak_of_ann hWann)
  have e2 : x.ghbXl W B.ar = true := ghb_com (rfe_of hrf (by rw [hWi, B.ar_tid]; exact hij))
  have e3 : x.ghbXl B.ar B.rc = true :=
    ghb_RM (by rw [B.ar_tid, B.rc_tid]) B.rc_pos B.ar_R (isM_of_R B.rc_R) (weak_of_R B.rc_R)
  have e4 : x.ghbXl B.ar B.wc = true :=
    ghb_RM (by rw [B.ar_tid, B.wc_tid]) (B.rc_pos.trans B.wc_pos) B.ar_R (isM_of_W B.wc_W)
      (weak_of_ann B.wc_ann)
  have e5 : x.ghbXl A.rc W = true :=
    ghb_RM (by rw [A.rc_tid, hWi]) (A.wc_pos.trans hWpos) A.rc_R (isM_of_W hwW) (weak_of_ann hWann)
  have P1 : TransGen x.ghbXl.Holds A.wc B.rc := TransGen.head e1 (TransGen.head e2 (TransGen.single e3))
  have P2 : TransGen x.ghbXl.Holds A.wc B.wc := TransGen.head e1 (TransGen.head e2 (TransGen.single e4))
  have P3 : TransGen x.ghbXl.Holds A.rc B.wc := TransGen.head e5 (TransGen.head e2 (TransGen.single e4))
  have hne : B.wc ≠ A.wc := fun h => hij (by rw [← A.wc_tid, ← B.wc_tid, h])
  -- Step B: `j`'s load of the counter reads `i`'s store.
  have hB : ∀ y, cnt ≤ y → y < cnt + 4 → x.rf B.rc.val y = some A.wc.val := by
    intro y h1 h2
    have hy := mem_bytes B.rc_addr B.rc_size h1 h2
    cases h : x.rf B.rc.val y with
    | none =>
      exfalso
      have := fr_ghb (frR_of B.rc_R A.wc_W hy (covers_of A.wc_addr A.wc_size h1 h2) (by rw [h]; trivial))
      exact cycle hghb P1 (TransGen.single this)
    | some w' =>
      obtain ⟨hlt, hW', hc'⟩ := wf_rf hwf B.rc_R hy h
      have hcov := (covers_iff _ _).mp hc'
      simp only [Ev.bytes, List.mem_range'_1] at hcov
      have ha := (cell_cnt (hcell _ (isM_of_W hW')).1 hcov.1 hcov.2 h1 h2).1
      rcases tidW htid A B ⟨w', hlt⟩ hW' ha with h' | h'
      · rw [← h']
      · exfalso
        rw [h'] at hc' hW'
        have hrf' : x.rfR B.wc B.rc = true := rfR_of hW' B.rc_R hy (by rw [h, ← h']) hc'
        exact uniproc_rf hx (po_of (by rw [B.rc_tid, B.wc_tid]) B.wc_pos)
          (loc_of (isM_of_R B.rc_R) (isM_of_W B.wc_W) hy hc') hrf'
  -- Step C: `i`'s load of the counter reads the initial value.
  have hC : ∀ y, cnt ≤ y → y < cnt + 4 → x.rf A.rc.val y = none := by
    intro y h1 h2
    have hy := mem_bytes A.rc_addr A.rc_size h1 h2
    cases h : x.rf A.rc.val y with
    | none => rfl
    | some w' =>
      exfalso
      obtain ⟨hlt, hW', hc'⟩ := wf_rf hwf A.rc_R hy h
      have hcov := (covers_iff _ _).mp hc'
      simp only [Ev.bytes, List.mem_range'_1] at hcov
      have ha := (cell_cnt (hcell _ (isM_of_W hW')).1 hcov.1 hcov.2 h1 h2).1
      rcases tidW htid A B ⟨w', hlt⟩ hW' ha with h' | h'
      · rw [h'] at hc' hW'
        have hrf' : x.rfR A.wc A.rc = true := rfR_of hW' A.rc_R hy (by rw [h, ← h']) hc'
        exact uniproc_rf hx (po_of (by rw [A.rc_tid, A.wc_tid]) A.wc_pos)
          (loc_of (isM_of_R A.rc_R) (isM_of_W A.wc_W) hy hc') hrf'
      · rw [h'] at hc' hW'
        have hrf' : x.rfR B.wc A.rc = true := rfR_of hW' A.rc_R hy (by rw [h, ← h']) hc'
        have := ghb_com (rfe_of hrf' (by rw [B.wc_tid, A.rc_tid]; exact Ne.symm hij))
        exact cycle hghb P3 (TransGen.single this)
  -- The values.
  have hA0 : A.v = 0 := by
    have h := A.rc_rd
    rw [readBytes_cnt A.rc A.rc_addr A.rc_size] at h
    simp only [Exec.readByte, hC cnt (le_refl _) (by omega), hC (cnt + 1) (by omega) (by omega),
      hC (cnt + 2) (by omega) (by omega), hC (cnt + 3) (by omega) (by omega),
      hinit cnt (le_refl _) (by omega), hinit (cnt + 1) (by omega) (by omega),
      hinit (cnt + 2) (by omega) (by omega), hinit (cnt + 3) (by omega) (by omega)] at h
    exact natBytes_inj A.hv (by omega) (h.symm.trans (by decide))
  have hB1 : B.v = 1 := by
    have h := B.rc_rd
    rw [readBytes_cnt B.rc B.rc_addr B.rc_size] at h
    simp only [Exec.readByte, hB cnt (le_refl _) (by omega), hB (cnt + 1) (by omega) (by omega),
      hB (cnt + 2) (by omega) (by omega), hB (cnt + 3) (by omega) (by omega),
      evN_eq _ A.wc.isLt, Ev.byte, A.wc_addr, A.wc_data, hA0] at h
    exact natBytes_inj B.hv (by omega) (h.symm.trans (by decide))
  refine ⟨by rw [B.wc_data, hB1], B.wc_addr, ?_⟩
  -- Step D: `j`'s store is coherence-last.
  intro y h1 h2
  have hc := covers_of B.wc_addr B.wc_size h1 h2
  have hmem := wf_co_mem hwf B.wc_W hc
  obtain ⟨c, hcl⟩ : ∃ c, (x.co y).getLast? = some c := by
    cases hl : (x.co y).getLast? with
    | some c => exact ⟨c, rfl⟩
    | none => simp [List.getLast?_eq_none_iff] at hl; simp [hl] at hmem
  have hcm := List.mem_of_getLast? hcl
  obtain ⟨hlt, hW', hc'⟩ := wf_co hwf (touched_of (isM_of_W B.wc_W) hc) hcm
  have hcov := (covers_iff _ _).mp hc'
  simp only [Ev.bytes, List.mem_range'_1] at hcov
  have ha := (cell_cnt (hcell _ (isM_of_W hW')).1 hcov.1 hcov.2 h1 h2).1
  rcases tidW htid A B ⟨c, hlt⟩ hW' ha with h' | h'
  · exfalso
    have hc2 : c = A.wc.val := by rw [← h']
    subst hc2
    have hbf := before_last hmem hcl (fun h => hne (Fin.ext h))
    have := co_ghb (coR_of B.wc_W A.wc_W (mem_bytes B.wc_addr B.wc_size h1 h2)
      (covers_of A.wc_addr A.wc_size h1 h2) hbf)
    exact cycle hghb P2 (TransGen.single this)
  · rw [hcl, ← h']


/-! ## The per-thread check -/

/-- A unit of thread `i`: in one of the cells, untorn, write-back. -/
def unitOk (i : Nat) (u : Ev × List Byte) : Bool :=
  u.1.tid == i && (!u.1.isM || (cells.contains (u.1.addr, u.1.size) && u.1.accAddr == u.1.addr &&
    u.1.accSize == u.1.size && u.1.ann == .wb))

/-- The acquiring read: a locked read of the mutex word that reads `0` (lowest byte). -/
def isAcq (u : Ev × List Byte) : Bool :=
  u.1.isR && u.1.locked && u.1.addr == mW && u.1.size == 4 && u.2.head? == some 0

/-- The counter load. -/
def isRc (u : Ev × List Byte) : Bool := u.1.isR && u.1.addr == cnt

/-- The counter store. -/
def isWc (u : Ev × List Byte) : Bool := u.1.isW && u.1.addr == cnt

/-- The write half of the acquiring RMW: it leaves a nonzero lowest byte. -/
def awOk (ar aw : Ev × List Byte) : Bool :=
  aw.1.pos == ar.1.pos + 1 && aw.1.isW && aw.1.locked && aw.1.addr == mW && aw.1.size == 4 &&
    aw.1.byte mW != 0

/-- The other counter stores are the counter store itself. -/
def cntOk (wc u : Ev × List Byte) : Bool := !(u.1.isW && u.1.addr == cnt) || u.1 == wc.1

/-- Every store of the mutex word with lowest byte `0` comes after the counter store. -/
def m0Ok (wc u : Ev × List Byte) : Bool :=
  !(u.1.isW && u.1.addr == mW && u.1.byte mW == 0) || decide (wc.1.pos < u.1.pos)

/-- The counter load reads `v` and the store writes `v + 1`. -/
def incOk (rc wc : Ev × List Byte) : Bool :=
  [0, 1, 2].any fun v => rc.2 == natBytes v 4 && wc.1.data == natBytes (v + 1) 4

/-- **The per-thread check** on the units of one run of thread `i`. -/
def good (i : Nat) (us : List (Ev × List Byte)) : Bool :=
  (us.map Prod.fst).Nodup && us.all (unitOk i) &&
  match us.find? isAcq, us.find? isRc, us.find? isWc with
  | some ar, some rc, some wc =>
    decide (ar.1.pos < rc.1.pos) && decide (rc.1.pos < wc.1.pos) && us.any (awOk ar) &&
      incOk rc wc && us.all (cntOk wc) && us.all (m0Ok wc)
  | _, _, _ => false

/-- What `good` gives. -/
structure GoodW (i : Nat) (us : List (Ev × List Byte)) : Prop where
  nodup : (us.map Prod.fst).Nodup
  unit : ∀ u ∈ us, unitOk i u = true
  shape : ∃ ar ∈ us, ∃ rc ∈ us, ∃ wc ∈ us, ∃ aw ∈ us, isAcq ar = true ∧ isRc rc = true ∧
    isWc wc = true ∧ ar.1.pos < rc.1.pos ∧ rc.1.pos < wc.1.pos ∧ awOk ar aw = true ∧
    incOk rc wc = true ∧ (∀ u ∈ us, cntOk wc u = true) ∧ (∀ u ∈ us, m0Ok wc u = true)

theorem goodW {i : Nat} {us : List (Ev × List Byte)} (h : good i us = true) : GoodW i us := by
  simp only [good, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hn, hu⟩, hm⟩ := h
  refine ⟨by simpa using hn, hu, ?_⟩
  cases ha : us.find? isAcq <;> cases hr : us.find? isRc <;> cases hw : us.find? isWc <;>
    simp only [ha, hr, hw, reduceCtorEq] at hm
  rename_i ar rc wc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.all_eq_true] at hm
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, ⟨aw, haw, h3⟩⟩, h4⟩, h5⟩, h6⟩ := hm
  exact ⟨ar, List.mem_of_find?_eq_some ha, rc, List.mem_of_find?_eq_some hr, wc,
    List.mem_of_find?_eq_some hw, aw, haw, List.find?_some ha, List.find?_some hr, List.find?_some hw,
    h1, h2, h3, h4, h5, h6⟩


/-! ## From the units to the per-thread facts -/

section Units
variable {us : List (Ev × List Byte)} (hevs : x.evs = us.map Prod.fst)
include hevs

theorem idx_of {u : Ev × List Byte} (hu : u ∈ us) :
    ∃ a : Fin x.n, x.ev a = u.1 ∧ (us.map Prod.snd).getD a.val [] = u.2 := by
  obtain ⟨k, hk, hku⟩ := List.mem_iff_getElem.mp hu
  have hk' : k < x.n := by simp [Exec.n, hevs, hk]
  refine ⟨⟨k, hk'⟩, ?_, ?_⟩
  · simp [Exec.ev, hevs, hku]
  · simp [List.getD_eq_getElem?_getD, hk, hku]

theorem mem_of_idx (a : Fin x.n) : ∃ u ∈ us, x.ev a = u.1 := by
  have ha : a.val < us.length := by have := a.isLt; simp [Exec.n, hevs] at this; exact this
  exact ⟨us[a.val], List.getElem_mem ha, by simp [Exec.ev, hevs]⟩

theorem ev_inj (hnd : (us.map Prod.fst).Nodup) {a b : Fin x.n} (h : x.ev a = x.ev b) : a = b := by
  have hnd' : x.evs.Nodup := by rw [hevs]; exact hnd
  exact Fin.ext ((hnd'.getElem_inj_iff).mp h)

theorem rmw_of (hrmw : x.rmw = rmwPairs (us.map Prod.fst)) {a b : Fin x.n}
    (ha : (x.ev a).isR = true) (hl : (x.ev a).locked = true) (hb : (x.ev b).isW = true)
    (hl' : (x.ev b).locked = true) (ht : (x.ev a).tid = (x.ev b).tid)
    (hp : (x.ev b).pos = (x.ev a).pos + 1) (had : (x.ev a).addr = (x.ev b).addr)
    (hs : (x.ev a).size = (x.ev b).size) : x.rmwR a b = true := by
  simp only [Exec.rmwR, hrmw, List.contains_iff_mem, rmwPairs, List.mem_flatMap]
  have ea : (us.map Prod.fst)[a.val]? = some (x.ev a) := by
    rw [← hevs]; simp [Exec.ev]
  have eb : (us.map Prod.fst)[b.val]? = some (x.ev b) := by
    rw [← hevs]; simp [Exec.ev]
  refine ⟨(x.ev a, a.val), List.mem_zipIdx_iff_getElem?.mpr ea, ?_⟩
  simp only [ha, hl, Bool.and_self, ite_true, List.mem_filterMap]
  refine ⟨(x.ev b, b.val), List.mem_zipIdx_iff_getElem?.mpr eb, ?_⟩
  simp [hb, hl', ht, hp, had, hs]

end Units

theorem readBytes_head {init : Nat → Byte} (r : Fin x.n) {a : Nat} (ha : (x.ev r).addr = a)
    (hs : (x.ev r).size = 4) : (x.readBytes init r.val).head? = some (x.readByte init r.val a) := by
  simp [Exec.readBytes, evN_eq r.val r.isLt, Ev.bytes, ha, hs, List.range']


/-- **The per-thread facts** of thread `i`, from its check. -/
theorem tf_of {init : Nat → Byte} {us U : List (Ev × List Byte)} {i : Nat}
    (hevs : x.evs = us.map Prod.fst) (hrmw : x.rmw = rmwPairs (us.map Prod.fst))
    (hnd : (us.map Prod.fst).Nodup)
    (hreads : ∀ r < x.n, (x.evN r).isR = true → x.readBytes init r = (us.map Prod.snd).getD r [])
    (hsub : ∀ u ∈ U, u ∈ us) (hown : ∀ u ∈ us, u.1.tid = i → u ∈ U) (hG : GoodW i U) :
    Nonempty (TF x init i) := by
  obtain ⟨ar, har, rc, hrc, wc, hwc, aw, haw, hA, hR, hW, hp1, hp2, hawok, hinc, hcnt, hm0⟩ := hG.shape
  obtain ⟨a, ea, sa⟩ := idx_of hevs (hsub _ har)
  obtain ⟨b, eb, -⟩ := idx_of hevs (hsub _ haw)
  obtain ⟨c, ec, sc⟩ := idx_of hevs (hsub _ hrc)
  obtain ⟨d, ed, -⟩ := idx_of hevs (hsub _ hwc)
  have tid_of : ∀ u ∈ U, u.1.tid = i := fun u hu => by
    have := hG.unit u hu; simp only [unitOk, Bool.and_eq_true, beq_iff_eq] at this; exact this.1
  simp only [isAcq, Bool.and_eq_true, beq_iff_eq] at hA
  obtain ⟨⟨⟨⟨hAR, hAl⟩, hAa⟩, hAs⟩, hAh⟩ := hA
  simp only [isRc, Bool.and_eq_true, beq_iff_eq] at hR
  simp only [isWc, Bool.and_eq_true, beq_iff_eq] at hW
  simp only [awOk, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hawok
  obtain ⟨⟨⟨⟨⟨hBp, hBW⟩, hBl⟩, hBa⟩, hBs⟩, hBb⟩ := hawok
  simp only [incOk, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, List.mem_cons,
    List.not_mem_nil, or_false] at hinc
  obtain ⟨v, hv, hrv, hwv⟩ := hinc
  have hcell : ∀ u ∈ U, u.1.isM = true → (u.1.addr, u.1.size) ∈ cells ∧ u.1.ann = .wb := by
    intro u hu hM
    have := hG.unit u hu
    simp only [unitOk, hM, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
      List.contains_iff_mem] at this
    exact ⟨this.2.1.1.1, this.2.2⟩
  have hrc4 : rc.1.size = 4 := cell_size_cnt (hR.2 ▸ (hcell rc hrc (isM_of_R hR.1)).1)
  have hwc4 : wc.1.size = 4 := cell_size_cnt (hW.2 ▸ (hcell wc hwc (isM_of_W hW.1)).1)
  have hRa : (x.evN a.val).isR = true := by rw [evN_eq a.val a.isLt, ea]; exact hAR
  have hRc : (x.evN c.val).isR = true := by rw [evN_eq c.val c.isLt, ec]; exact hR.1
  have rda := hreads a.val a.isLt hRa
  have rdc := hreads c.val c.isLt hRc
  rw [sa] at rda
  rw [sc] at rdc
  have hhead := readBytes_head (init := init) a (a := mW) (by rw [ea]; exact hAa) (by rw [ea]; exact hAs)
  rw [rda, hAh] at hhead
  refine ⟨{
    ar := a
    aw := b
    rc := c
    wc := d
    v := v
    hv := by omega
    ar_tid := by rw [ea]; exact tid_of ar har
    ar_R := by rw [ea]; exact hAR
    ar_addr := by rw [ea]; exact hAa
    ar_size := by rw [ea]; exact hAs
    ar_rd := by injection hhead with h; exact h.symm
    aw_tid := by rw [eb]; exact tid_of aw haw
    aw_W := by rw [eb]; exact hBW
    aw_addr := by rw [eb]; exact hBa
    aw_size := by rw [eb]; exact hBs
    aw_byte := by rw [eb]; exact hBb
    rmw := rmw_of hevs hrmw (by rw [ea]; exact hAR) (by rw [ea]; exact hAl) (by rw [eb]; exact hBW)
      (by rw [eb]; exact hBl) (by rw [ea, eb, tid_of ar har, tid_of aw haw]) (by rw [ea, eb]; exact hBp)
      (by rw [ea, eb, hAa, hBa]) (by rw [ea, eb, hAs, hBs])
    rc_tid := by rw [ec]; exact tid_of rc hrc
    rc_R := by rw [ec]; exact hR.1
    rc_addr := by rw [ec]; exact hR.2
    rc_size := by rw [ec]; exact hrc4
    rc_pos := by rw [ea, ec]; exact hp1
    rc_rd := by rw [rdc, hrv]
    wc_tid := by rw [ed]; exact tid_of wc hwc
    wc_W := by rw [ed]; exact hW.1
    wc_addr := by rw [ed]; exact hW.2
    wc_size := by rw [ed]; exact hwc4
    wc_ann := by rw [ed]; exact (hcell wc hwc (isM_of_W hW.1)).2
    wc_pos := by rw [ec, ed]; exact hp2
    wc_data := by rw [ed]; exact hwv
    cntW := fun a' ht hW' ha' => by
      obtain ⟨u, hu, eu⟩ := mem_of_idx hevs a'
      rw [eu] at ht hW' ha'
      have := hcnt u (hown u hu ht)
      simp only [cntOk, hW', ha', beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or,
        beq_iff_eq] at this
      exact ev_inj hevs hnd (by rw [eu, ed, this])
    m0 := fun a' ht hW' ha' h0 => by
      obtain ⟨u, hu, eu⟩ := mem_of_idx hevs a'
      rw [eu] at ht hW' ha' h0 ⊢
      have := hm0 u (hown u hu ht)
      simp only [m0Ok, hW', ha', h0, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or,
        decide_eq_true_eq] at this
      rw [ed]; exact this }⟩


/-! ## No access tears -/

theorem cells_disj : ∀ c ∈ cells, ∀ c' ∈ cells, c.1 < c'.1 + c'.2 → c'.1 < c.1 + c.2 → c = c' := by
  decide

theorem cells_sc : ∀ c ∈ cells, c.2 ≤ 8 ∧ c.1 % c.2 = 0 := by decide

/-- A memory unit in a cell, untorn. -/
def InCell (u : Ev) : Prop :=
  u.isM = true → (u.addr, u.size) ∈ cells ∧ u.accAddr = u.addr ∧ u.accSize = u.size

theorem tear_false {us : List (Ev × List Byte)} (h : ∀ v ∈ us, InCell v.1) {u : Ev × List Byte}
    (hu : u ∈ us) : tearAcc us u.1 = false := by
  cases hM : u.1.isM
  · simp [tearAcc, hM]
  · obtain ⟨hc, ha, hs⟩ := h u hu hM
    have hsc := cells_sc _ hc
    simp only [tearAcc, hM, Bool.true_and, Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false,
      List.any_eq_false]
    refine ⟨by simp [Ev.singleCopy, ha, hs, hsc.1, hsc.2], ?_⟩
    intro v hv
    cases hvM : v.1.isM
    · simp
    · obtain ⟨hc', ha', hs'⟩ := h v hv hvM
      simp only [Ev.accOverlap, ha, hs, ha', hs', Bool.true_and, Bool.and_eq_true, decide_eq_true_eq,
        Bool.or_eq_true, bne_iff_ne, ne_eq, not_and]
      intro h1
      have := cells_disj _ hc _ hc' h1.1 h1.2
      simp only [Prod.mk.injEq] at this
      omega

theorem flatMap_keep {us : List (Ev × List Byte)} {p : Ev × List Byte → Bool}
    {g : Ev × List Byte → List (Ev × List Byte)} (h : ∀ u ∈ us, p u = false) :
    us.flatMap (fun u => if p u then g u else [u]) = us := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    simp only [List.flatMap_cons, h u (List.mem_cons_self ..), Bool.false_eq_true, ite_false,
      List.singleton_append]
    rw [ih (fun v hv => h v (List.mem_cons_of_mem _ hv))]

/-! ## The final value -/

theorem leValue_cnt {mem : Nat → Option Byte}
    (h : ∀ k < 4, mem (cnt + k) = some ((natBytes 2 4)[k]?.getD 0)) : leValue mem cnt 4 = some 2 := by
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  simp only [Nat.add_zero] at h0
  simp only [leValue, h0, h1, h2, h3, Nat.add_assoc]
  decide

theorem final_cnt {init : Nat → Byte} {im : Nat → Option Byte} (W : Fin x.n)
    (hW : (x.ev W).isW = true) (ha : (x.ev W).addr = cnt) (hs : (x.ev W).size = 4)
    (hd : (x.ev W).data = natBytes 2 4)
    (hl : ∀ y, cnt ≤ y → y < cnt + 4 → (x.co y).getLast? = some W.val) :
    leValue (fun y => if writtenByte x y then some (x.finalByte init y) else im y) cnt 4 = some 2 := by
  apply leValue_cnt
  intro k hk
  have hc : (x.ev W).covers (cnt + k) = true := covers_of ha hs (by omega) (by omega)
  have hwb : writtenByte x (cnt + k) = true := by
    simp only [writtenByte, List.any_eq_true, Bool.and_eq_true]
    exact ⟨x.ev W, List.getElem_mem _, hW, hc⟩
  simp only [hwb, ite_true, Exec.finalByte, hl (cnt + k) (by omega) (by omega), evN_eq W.val W.isLt,
    Ev.byte, ha, hd, Nat.add_sub_cancel_left]


/-! ## The program -/

/-- The units of a run of thread `i`. -/
def tu (i : Nat) (p : List Lab × Regs) : List (Ev × List Byte) := threadUnits i 0 (p.1.flatMap Lab.acts)

set_option maxRecDepth 100000 in
theorem good0_all : (run [0, 1, 2] (mThread 1 d0).body Regs.zero).all (fun p => good 0 (tu 0 p)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem good1_all : (run [0, 1, 2] (mThread 1 d1).body Regs.zero).all (fun p => good 1 (tu 1 p)) = true := by
  decide +kernel

theorem acts_xtrace (n d i : Nat) (p : List Lab × Regs) :
    ((mThread n d).xtrace i p).acts = p.1.flatMap Lab.acts := by
  simp [Thread.xtrace, Silmaril.X86.Litmus.Trace.acts, Thread.acts, mThread, th]

theorem tid_of_good {i : Nat} {us : List (Ev × List Byte)} (hG : GoodW i us) {u} (hu : u ∈ us) :
    u.1.tid = i := by
  have := hG.unit u hu; simp only [unitOk, Bool.and_eq_true, beq_iff_eq] at this; exact this.1

theorem cell_of_good {i : Nat} {us : List (Ev × List Byte)} (hG : GoodW i us) {u} (hu : u ∈ us) :
    InCell u.1 ∧ (u.1.isM = true → u.1.ann = .wb) := by
  have := hG.unit u hu
  constructor
  · intro hM
    simp only [unitOk, hM, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
      List.contains_iff_mem] at this
    exact ⟨this.2.1.1.1, this.2.1.1.2, this.2.1.2⟩
  · intro hM
    simp only [unitOk, hM, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at this
    exact this.2.2

/-- **Drepper's two-thread mutex counts to 2 under XL.** -/
theorem mutex_xl : ∀ f, BehavIn (mutex 1) [0, 1, 2] Exec.Xl f →
    (Cond.atom (.mem cnt 4 2)).eval f = true := by
  intro f ⟨trs, hF, x, hevs, hrmw, hwf, hreads, hxl, hf⟩
  have hT : (mutex 1).traces [0, 1, 2] =
      [(run [0, 1, 2] (mThread 1 d0).body Regs.zero).map ((mThread 1 d0).xtrace 0),
        (run [0, 1, 2] (mThread 1 d1).body Regs.zero).map ((mThread 1 d1).xtrace 1)] := rfl
  rw [hT] at hF
  rcases trs with _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, trs⟩⟩⟩ <;> simp only [List.forall₂_cons, and_true, List.forall₂_nil_left_iff, List.forall₂_nil_right_iff,
    reduceCtorEq, and_false] at hF
  obtain ⟨h0, h1⟩ := hF
  obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp h0
  obtain ⟨p1, hp1, rfl⟩ := List.mem_map.mp h1
  have G0 : GoodW 0 (tu 0 p0) := goodW (List.all_eq_true.mp good0_all p0 hp0)
  have G1 : GoodW 1 (tu 1 p1) := goodW (List.all_eq_true.mp good1_all p1 hp1)
  have hacc : accUnits [(mThread 1 d0).xtrace 0 p0, (mThread 1 d1).xtrace 1 p1] = tu 0 p0 ++ tu 1 p1 := by
    simp [accUnits, acts_xtrace, tu]
  have hmem : ∀ u ∈ tu 0 p0 ++ tu 1 p1, (u.1.tid = 0 ∧ u ∈ tu 0 p0) ∨ (u.1.tid = 1 ∧ u ∈ tu 1 p1) := by
    intro u hu
    rcases List.mem_append.mp hu with h | h
    · exact Or.inl ⟨tid_of_good G0 h, h⟩
    · exact Or.inr ⟨tid_of_good G1 h, h⟩
  have hcellU : ∀ u ∈ tu 0 p0 ++ tu 1 p1, InCell u.1 ∧ (u.1.isM = true → u.1.ann = .wb) := by
    intro u hu
    rcases hmem u hu with ⟨-, h⟩ | ⟨-, h⟩
    · exact cell_of_good G0 h
    · exact cell_of_good G1 h
  have hunits : units [(mThread 1 d0).xtrace 0 p0, (mThread 1 d1).xtrace 1 p1] = tu 0 p0 ++ tu 1 p1 := by
    simp only [units]
    rw [hacc]
    exact flatMap_keep (fun u hu => tear_false (fun v hv => (hcellU v hv).1) hu)
  rw [hunits] at hevs hrmw hreads
  have hnd : ((tu 0 p0 ++ tu 1 p1).map Prod.fst).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨G0.nodup, G1.nodup, ?_⟩
    intro a ha b hb hab
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hb
    have := congrArg Ev.tid hab
    rw [tid_of_good G0 hu, tid_of_good G1 hw] at this
    exact absurd this (by decide)
  have hinit : ∀ y, cnt ≤ y → y < cnt + 4 → (mutex 1).memTest.initB y = 0 := by
    intro y h1 h2
    have : y = cnt ∨ y = cnt + 1 ∨ y = cnt + 2 ∨ y = cnt + 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> decide
  obtain ⟨A⟩ := tf_of (init := (mutex 1).memTest.initB) hevs hrmw hnd hreads
    (fun u hu => List.mem_append_left _ hu)
    (fun u hu ht => by
      rcases hmem u hu with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · rw [ht] at h; exact absurd h (by decide)) G0
  obtain ⟨B⟩ := tf_of (init := (mutex 1).memTest.initB) hevs hrmw hnd hreads
    (fun u hu => List.mem_append_right _ hu)
    (fun u hu ht => by
      rcases hmem u hu with ⟨h, -⟩ | ⟨-, h⟩
      · rw [ht] at h; exact absurd h (by decide)
      · exact h) G1
  have htid : ∀ a : Fin x.n, (x.ev a).tid = 0 ∨ (x.ev a).tid = 1 := by
    intro a
    obtain ⟨u, hu, eu⟩ := mem_of_idx hevs a
    rw [eu]
    rcases hmem u hu with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hcell : ∀ a : Fin x.n, (x.ev a).isM = true → ((x.ev a).addr, (x.ev a).size) ∈ cells ∧
      (x.ev a).ann = .wb := by
    intro a hM
    obtain ⟨u, hu, eu⟩ := mem_of_idx hevs a
    rw [eu] at hM ⊢
    exact ⟨((hcellU u hu).1 hM).1, (hcellU u hu).2 hM⟩
  have hA := wf_co_mem hwf A.aw_W (covers_of A.aw_addr A.aw_size (le_refl mW) (by omega))
  have hB := wf_co_mem hwf B.aw_W (covers_of B.aw_addr B.aw_size (le_refl mW) (by omega))
  have hne : A.aw.val ≠ B.aw.val := fun h => by
    have := congrArg (fun a => (x.ev a).tid) (Fin.ext h)
    simp only [A.aw_tid, B.aw_tid] at this
    exact absurd this (by decide)
  have key : ∃ W : Fin x.n, (x.ev W).isW = true ∧ (x.ev W).addr = cnt ∧ (x.ev W).size = 4 ∧
      (x.ev W).data = natBytes 2 4 ∧ ∀ y, cnt ≤ y → y < cnt + 4 → (x.co y).getLast? = some W.val := by
    rcases before_total hA hB hne with h | h
    · obtain ⟨hd, ha, hl⟩ := core hxl hwf hinit hcell (by decide) htid A B h
      exact ⟨B.wc, B.wc_W, ha, B.wc_size, hd, hl⟩
    · obtain ⟨hd, ha, hl⟩ := core hxl hwf hinit hcell (by decide) (fun a => (htid a).symm) B A h
      exact ⟨A.wc, A.wc_W, ha, A.wc_size, hd, hl⟩
  obtain ⟨W, hW, ha, hs, hd, hl⟩ := key
  subst hf
  simp only [Cond.eval, Atom.eval, finalAx, finalOf, beq_iff_eq]
  exact final_cnt W hW ha hs hd hl

/-! ## A behaviour exists (non-vacuity)

`mutexPos` is `Mutex@gcc` with the quantifier `exists`, so its witness is the condition `c = 2`
itself; the test's behaviours (`CBehav`) do not depend on the quantifier. One schedule (each
thread's fast path, thread `0` first) is a well-formed SC candidate ending with `c = 2`. -/

/-- `Mutex@gcc` asked as an `exists` test. -/
def mutexPos : Silmaril.X86.Concurrency.Cir.Tv.FTest :=
  { Silmaril.X86.Concurrency.Cir.Tv.CFutex.«Mutex@gcc» with
    test := { Silmaril.X86.Concurrency.Cir.Tv.CFutex.«Mutex@gcc».test with quant := .exists_ } }

theorem mutexPos_sched :
    mutexPos.schedOk [2, 7] [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1] = true := by decide +kernel

end Silmaril.Proofs.X86.Concurrency.Cir.TvCFutexMutex
