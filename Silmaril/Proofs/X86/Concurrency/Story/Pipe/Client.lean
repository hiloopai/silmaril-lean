module

public import Silmaril.Proofs.X86.Concurrency.Story.Pipe.Chan
public import Silmaril.X86.Concurrency.Cir.Mutex.Defs
public import Silmaril.X86.Concurrency.Cir.Mutex.Xl.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Proofs: the pipeline, proved once against the ghost-aware mutex interface

The global invariant is `gsep (M.inv m (R vs)) (Chan vs)`: the mutex's share, protecting the
resource `R vs`, next to the channel. The channel's specs (`send_chan`, `recv_chan`) are lifted
by the invariant frame rule; the mutex's lock and unlock specs are framed with the thread's other
cells (`safeR_frame`) and channel tokens (`safeR_gframe`).

**The result.** `R vs` is Story.Counter's receipt device for two parties with different
contributions (`|vs|` from the producer, `Σ vs` from the consumer), over real token cells that no
instruction touches: the resource holds `acc ↦ 0` and both receipts (`rA`), or `acc` with one
party's contribution, its permit and the second receipt (`rP`, `rC`), or both permits (`rD`). The
first party to enter takes receipt `r0`; the second finds the other's permit, adds its own
contribution, and takes `r1` and `acc ↦ |vs| + Σ vs` out. At the end the two postconditions hold
on disjoint heaps, so one of them holds `r1` and `acc`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace Silmaril.Proofs.X86.Concurrency.Story.Pipe

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Rel
open Silmaril.X86.Concurrency.Cir.Mutex
open Silmaril.X86.Concurrency.Story.Pipe

/-! ## Lifting the channel specs -/

theorem chan_lift {vs : List Nat} {P : GProp} {Q : Bool → Regs → Heap → Heap → Prop} {p : Bool}
    {s : Stmt} {rs : Regs} {h g : Heap} (H : SafeR (Chan vs) Q p s rs h g) :
    SafeR (gsep P (Chan vs)) Q p s rs h g := by
  rw [gsep_comm]; exact safeR_inv_frame H

/-- Frame a step proved from an empty heap with the thread's cells `hF` and other ghost `gF`. -/
theorem frame2 {I : GProp} {Q : Bool → Regs → Heap → Heap → Prop} {p : Bool} {s : Stmt}
    {rs : Regs} {g hF gF : Heap} (H : SafeR I Q p s rs Heap.empty g) (dg : Heap.Disjoint g gF) :
    SafeR I (fun p rs h' g' => ∃ h1 g1, Q p rs h1 g1 ∧ Heap.Disjoint h1 hF ∧
      h' = Heap.union h1 hF ∧ Heap.Disjoint g1 gF ∧ g' = Heap.union g1 gF) p s rs hF
      (Heap.union g gF) := by
  have H1 := safeR_frame (hF := hF) H (disjoint_empty _)
  rw [union_empty_left] at H1
  refine safeR_conseq (fun p rs h' g' hp => ?_) (safeR_gframe H1 dg)
  obtain ⟨g1, ⟨h1, q, d1, rfl⟩, d2, rfl⟩ := hp
  exact ⟨h1, g1, q, d1, rfl, d2, rfl⟩

/-- Frame a step with the thread's other ghost `gF` only. -/
theorem frameG {I : GProp} {Q : Bool → Regs → Heap → Heap → Prop} {p : Bool} {s : Stmt}
    {rs : Regs} {h g gF : Heap} (H : SafeR I Q p s rs h g) (dg : Heap.Disjoint g gF) :
    SafeR I (fun p rs h' g' => ∃ g1, Q p rs h' g1 ∧ Heap.Disjoint g1 gF ∧
      g' = Heap.union g1 gF) p s rs h (Heap.union g gF) :=
  safeR_gframe H dg

/-! ## The producer's sends -/

theorem drop_cons {vs : List Nat} {k : Nat} (hk : k < vs.length) :
    vs.drop k = vs.getD k 0 :: vs.drop (k + 1) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  exact List.drop_eq_getElem_cons hk

/-- **All the sends** from message `k` on, framed: the producer's cells `hF` and other ghost
`gF` are untouched, and its channel tokens advance to `prodG n n`. -/
theorem sends_safe {vs : List Nat} {B : Nat} {P : GProp} {Q : Bool → Regs → Heap → Heap → Prop}
    {t : Stmt} {hF gF : Heap} (hgF : ∀ c p, Heap.Disjoint (prodG c p) gF)
    (hvs : ∀ v ∈ vs, v < 2 ^ 64) (hn : vs.length + 1 < 2 ^ 64)
    (ht : ∀ rs p, SafeR (gsep P (Chan vs)) Q p t rs hF
      (Heap.union (prodG vs.length vs.length) gF)) :
    ∀ (l : List Nat) (k : Nat), l = vs.drop k → k ≤ vs.length → ∀ rs p,
      SafeR (gsep P (Chan vs)) Q p (sends B k l t) rs hF (Heap.union (prodG k k) gF) := by
  intro l
  induction l with
  | nil =>
    intro k hl hk rs p
    have : k = vs.length := by
      have := congrArg List.length hl; simp at this; omega
    subst this
    exact ht rs p
  | cons v l ih =>
    intro k hl hk rs p
    have hkn : k < vs.length := by
      by_contra h; have : vs.drop k = [] := List.drop_eq_nil_of_le (by omega)
      rw [this] at hl; cases hl
    rw [drop_cons hkn] at hl
    obtain ⟨rfl, rfl⟩ := List.cons.inj hl
    have hv : vs.getD k 0 < 2 ^ 64 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkn]
      exact hvs _ (List.getElem_mem _)
    apply safeR_seq
    have H := frame2 (hF := hF) (chan_lift (P := P) (send_chan (B := B) (p := p) (rs := rs)
      (Q := fun _ _ h g => h = Heap.empty ∧ g = prodG (k + 1) (k + 1)) (by omega) hv
      (fun _ => ⟨rfl, rfl⟩))) (hgF k k)
    refine safeR_conseq (fun p rs' h' g' hp => ?_) H
    obtain ⟨h1, g1, ⟨rfl, rfl⟩, -, rfl, -, rfl⟩ := hp
    rw [union_empty_left]
    exact ih (k + 1) rfl (by omega) rs' p

/-! ## The consumer's receives -/

/-- The consumer's cells after `k` messages, without its permit: `out j = vs[j]` for `j < k`
(`0` beyond), and `sm = Σ_{j < k} vs[j]`. -/
def cK (vs : List Nat) (k : Nat) : Heap := fun y =>
  if y = sm then some ((vs.take k).sum % 2 ^ 64)
  else if isOut vs.length y then some (if (y - ob) / 8 < k then vs.getD ((y - ob) / 8) 0 else 0)
  else none

/-- With the permit. -/
def cH (vs : List Nat) (k : Nat) : Heap := Heap.union (cK vs k) (Heap.single pC 0)

theorem isOut_out {n k : Nat} (hk : k < n) : isOut n (out k) := by
  simp only [isOut, out, ob]; omega

theorem out_idx (k : Nat) : (out k - ob) / 8 = k := by simp only [out, ob]; omega

theorem not_isOut_sm (n : Nat) : ¬ isOut n sm := by simp [isOut, sm, ob]
theorem not_isOut_pC (n : Nat) : ¬ isOut n pC := by simp [isOut, pC, ob]
theorem not_isOut_cdat (n : Nat) : ¬ isOut n cdat := by simp [isOut, cdat, ob]

theorem out_inj {n y k : Nat} (hy : isOut n y) (h : (y - ob) / 8 = k) : y = out k := by
  simp only [isOut] at hy; simp only [out]; omega

theorem sum_take_succ {vs : List Nat} {k : Nat} (hk : k < vs.length) :
    (vs.take (k + 1)).sum = (vs.take k).sum + vs.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  simp [List.sum_take_succ _ _ hk]

theorem took_cH {vs : List Nat} {k : Nat} (hk : k < vs.length) (r : Word)
    (hr : r = BitVec.ofNat 64 (vs.take k).sum) :
    took (cH vs k) k (vs.getD k 0) (r + BitVec.ofNat 64 (vs.getD k 0)).toNat = cH vs (k + 1) := by
  subst hr
  funext y
  simp only [took, cH, cK, union_apply, single_apply]
  by_cases h1 : y = sm
  · subst h1
    simp [sum_take_succ hk, BitVec.toNat_add, Nat.add_mod]
  · by_cases h2 : y = out k
    · subst h2
      have ho : out k ≠ sm := by simp only [out, ob, sm]; omega
      simp [ho, isOut_out hk, out_idx]
    · simp only [h1, h2, ite_false]
      by_cases h3 : isOut vs.length y
      · have hne : (y - ob) / 8 ≠ k := fun e => h2 (out_inj h3 e)
        simp only [h3, ite_true]
        congr 2
        by_cases h4 : (y - ob) / 8 < k
        · simp [h4, show (y - ob) / 8 < k + 1 by omega]
        · simp [h4, show ¬ (y - ob) / 8 < k + 1 by omega]
      · simp [h3]

theorem cH_cdat (vs : List Nat) (k : Nat) : cH vs k cdat = none := by
  simp [cH, cK, union_apply, single_apply, not_isOut_cdat, show cdat ≠ sm by decide,
    show cdat ≠ pC by decide]

theorem cH_out {vs : List Nat} {k j : Nat} (hj : j < vs.length) : (cH vs k (out j)).isSome := by
  have ho : out j ≠ sm := by simp only [out, ob, sm]; omega
  simp [cH, cK, union_apply, ho, isOut_out hj]

theorem cH_sm (vs : List Nat) (k : Nat) : (cH vs k sm).isSome := by
  simp [cH, cK, union_apply]

/-- **All the receives** from message `k` on (`r` of them), framed with the consumer's other
ghost `gF`: its cells go from `cH vs k` to `cH vs n`, `rbx` holds the running sum. -/
theorem recvs_safe {vs : List Nat} {B : Nat} {P : GProp} {Q : Bool → Regs → Heap → Heap → Prop}
    {t : Stmt} {gF : Heap} (hgF : ∀ c a, Heap.Disjoint (consG c a) gF)
    (hvs : ∀ v ∈ vs, v < 2 ^ 64) (hn : vs.length < 2 ^ 32)
    (ht : ∀ rs p, rs .rbx = BitVec.ofNat 64 vs.sum → SafeR (gsep P (Chan vs)) Q p t rs
      (cH vs vs.length) (Heap.union (consG vs.length vs.length) gF)) :
    ∀ (r k : Nat), k + r = vs.length → ∀ rs p, rs .rbx = BitVec.ofNat 64 (vs.take k).sum →
      SafeR (gsep P (Chan vs)) Q p (recvs B k r t) rs (cH vs k) (Heap.union (consG k k) gF) := by
  intro r
  induction r with
  | zero =>
    intro k hk rs p hr
    simp only [Nat.add_zero] at hk
    subst hk
    rw [List.take_length] at hr
    exact ht rs p hr
  | succ r ih =>
    intro k hk rs p hr
    have hkn : k < vs.length := by omega
    have hv : vs.getD k 0 < 2 ^ 64 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkn]
      exact hvs _ (List.getElem_mem _)
    have hko : out k < 2 ^ 64 := by simp only [out, ob]; omega
    apply safeR_seq
    have H := frameG (gF := gF) (chan_lift (P := P) (recv_chan (B := B) (p := p) (rs := rs)
      (hO := cH vs k) (Q := fun _ rs' h g => rs' .rbx = rs .rbx + BitVec.ofNat 64 (vs.getD k 0) ∧
        h = cH vs (k + 1) ∧ g = consG (k + 1) (k + 1))
      (by omega) hv hko (cH_cdat vs k) (cH_out hkn) (cH_sm vs k)
      ⟨by simp [set_get], took_cH hkn _ hr, rfl⟩)) (hgF k k)
    refine safeR_conseq (fun p rs' h' g' hp => ?_) H
    obtain ⟨g1, ⟨hrb, rfl, rfl⟩, -, rfl⟩ := hp
    refine ih (k + 1) (by omega) rs' p ?_
    rw [hrb, hr, sum_take_succ hkn, BitVec.ofNat_add]

/-! ## Distinct cells -/

theorem acc_ne_r0 : acc ≠ r0 := by decide
theorem r0_ne_acc : r0 ≠ acc := by decide
theorem acc_ne_r1 : acc ≠ r1 := by decide
theorem r1_ne_acc : r1 ≠ acc := by decide
theorem acc_ne_pP : acc ≠ pP := by decide
theorem pP_ne_acc : pP ≠ acc := by decide
theorem acc_ne_pC : acc ≠ pC := by decide
theorem pC_ne_acc : pC ≠ acc := by decide
theorem acc_ne_sm : acc ≠ sm := by decide
theorem sm_ne_acc : sm ≠ acc := by decide
theorem acc_ne_cseq : acc ≠ cseq := by decide
theorem cseq_ne_acc : cseq ≠ acc := by decide
theorem acc_ne_cack : acc ≠ cack := by decide
theorem cack_ne_acc : cack ≠ acc := by decide
theorem acc_ne_cdat : acc ≠ cdat := by decide
theorem cdat_ne_acc : cdat ≠ acc := by decide
theorem acc_ne_m : acc ≠ m := by decide
theorem m_ne_acc : m ≠ acc := by decide
theorem r0_ne_r1 : r0 ≠ r1 := by decide
theorem r1_ne_r0 : r1 ≠ r0 := by decide
theorem r0_ne_pP : r0 ≠ pP := by decide
theorem pP_ne_r0 : pP ≠ r0 := by decide
theorem r0_ne_pC : r0 ≠ pC := by decide
theorem pC_ne_r0 : pC ≠ r0 := by decide
theorem r0_ne_sm : r0 ≠ sm := by decide
theorem sm_ne_r0 : sm ≠ r0 := by decide
theorem r0_ne_cseq : r0 ≠ cseq := by decide
theorem cseq_ne_r0 : cseq ≠ r0 := by decide
theorem r0_ne_cack : r0 ≠ cack := by decide
theorem cack_ne_r0 : cack ≠ r0 := by decide
theorem r0_ne_cdat : r0 ≠ cdat := by decide
theorem cdat_ne_r0 : cdat ≠ r0 := by decide
theorem r0_ne_m : r0 ≠ m := by decide
theorem m_ne_r0 : m ≠ r0 := by decide
theorem r1_ne_pP : r1 ≠ pP := by decide
theorem pP_ne_r1 : pP ≠ r1 := by decide
theorem r1_ne_pC : r1 ≠ pC := by decide
theorem pC_ne_r1 : pC ≠ r1 := by decide
theorem r1_ne_sm : r1 ≠ sm := by decide
theorem sm_ne_r1 : sm ≠ r1 := by decide
theorem r1_ne_cseq : r1 ≠ cseq := by decide
theorem cseq_ne_r1 : cseq ≠ r1 := by decide
theorem r1_ne_cack : r1 ≠ cack := by decide
theorem cack_ne_r1 : cack ≠ r1 := by decide
theorem r1_ne_cdat : r1 ≠ cdat := by decide
theorem cdat_ne_r1 : cdat ≠ r1 := by decide
theorem r1_ne_m : r1 ≠ m := by decide
theorem m_ne_r1 : m ≠ r1 := by decide
theorem pP_ne_pC : pP ≠ pC := by decide
theorem pC_ne_pP : pC ≠ pP := by decide
theorem pP_ne_sm : pP ≠ sm := by decide
theorem sm_ne_pP : sm ≠ pP := by decide
theorem pP_ne_cseq : pP ≠ cseq := by decide
theorem cseq_ne_pP : cseq ≠ pP := by decide
theorem pP_ne_cack : pP ≠ cack := by decide
theorem cack_ne_pP : cack ≠ pP := by decide
theorem pP_ne_cdat : pP ≠ cdat := by decide
theorem cdat_ne_pP : cdat ≠ pP := by decide
theorem pP_ne_m : pP ≠ m := by decide
theorem m_ne_pP : m ≠ pP := by decide
theorem pC_ne_sm : pC ≠ sm := by decide
theorem sm_ne_pC : sm ≠ pC := by decide
theorem pC_ne_cseq : pC ≠ cseq := by decide
theorem cseq_ne_pC : cseq ≠ pC := by decide
theorem pC_ne_cack : pC ≠ cack := by decide
theorem cack_ne_pC : cack ≠ pC := by decide
theorem pC_ne_cdat : pC ≠ cdat := by decide
theorem cdat_ne_pC : cdat ≠ pC := by decide
theorem pC_ne_m : pC ≠ m := by decide
theorem m_ne_pC : m ≠ pC := by decide
theorem sm_ne_cseq : sm ≠ cseq := by decide
theorem cseq_ne_sm : cseq ≠ sm := by decide
theorem sm_ne_cack : sm ≠ cack := by decide
theorem cack_ne_sm : cack ≠ sm := by decide
theorem sm_ne_cdat : sm ≠ cdat := by decide
theorem cdat_ne_sm : cdat ≠ sm := by decide
theorem sm_ne_m : sm ≠ m := by decide
theorem m_ne_sm : m ≠ sm := by decide
theorem cseq_ne_cack : cseq ≠ cack := by decide
theorem cack_ne_cseq : cack ≠ cseq := by decide
theorem cseq_ne_cdat : cseq ≠ cdat := by decide
theorem cdat_ne_cseq : cdat ≠ cseq := by decide
theorem cseq_ne_m : cseq ≠ m := by decide
theorem m_ne_cseq : m ≠ cseq := by decide
theorem cack_ne_cdat : cack ≠ cdat := by decide
theorem cdat_ne_cack : cdat ≠ cack := by decide
theorem cack_ne_m : cack ≠ m := by decide
theorem m_ne_cack : m ≠ cack := by decide
theorem cdat_ne_m : cdat ≠ m := by decide
theorem m_ne_cdat : m ≠ cdat := by decide

attribute [local simp] acc_ne_r0 r0_ne_acc acc_ne_r1 r1_ne_acc acc_ne_pP pP_ne_acc acc_ne_pC
  pC_ne_acc acc_ne_sm sm_ne_acc acc_ne_cseq cseq_ne_acc acc_ne_cack cack_ne_acc acc_ne_cdat
  cdat_ne_acc acc_ne_m m_ne_acc r0_ne_r1 r1_ne_r0 r0_ne_pP pP_ne_r0 r0_ne_pC pC_ne_r0 r0_ne_sm
  sm_ne_r0 r0_ne_cseq cseq_ne_r0 r0_ne_cack cack_ne_r0 r0_ne_cdat cdat_ne_r0 r0_ne_m m_ne_r0
  r1_ne_pP pP_ne_r1 r1_ne_pC pC_ne_r1 r1_ne_sm sm_ne_r1 r1_ne_cseq cseq_ne_r1 r1_ne_cack
  cack_ne_r1 r1_ne_cdat cdat_ne_r1 r1_ne_m m_ne_r1 pP_ne_pC pC_ne_pP pP_ne_sm sm_ne_pP pP_ne_cseq
  cseq_ne_pP pP_ne_cack cack_ne_pP pP_ne_cdat cdat_ne_pP pP_ne_m m_ne_pP pC_ne_sm sm_ne_pC
  pC_ne_cseq cseq_ne_pC pC_ne_cack cack_ne_pC pC_ne_cdat cdat_ne_pC pC_ne_m m_ne_pC sm_ne_cseq
  cseq_ne_sm sm_ne_cack cack_ne_sm sm_ne_cdat cdat_ne_sm sm_ne_m m_ne_sm cseq_ne_cack cack_ne_cseq
  cseq_ne_cdat cdat_ne_cseq cseq_ne_m m_ne_cseq cack_ne_cdat cdat_ne_cack cack_ne_m m_ne_cack
  cdat_ne_m m_ne_cdat

/-! ## The mutex-protected result -/

/-- Nobody has added yet: `acc ↦ 0` and both receipts. -/
def rA : Heap := fun y => if y = acc ∨ y = r0 ∨ y = r1 then some 0 else none
/-- One party has added `c`: `acc ↦ c`, the second receipt and that party's permit `q`. -/
def rOne (q c : Nat) : Heap := fun y => if y = acc then some c else if y = r1 ∨ y = q then some 0
  else none
/-- Both have added: both permits. -/
def rD : Heap := fun y => if y = pP ∨ y = pC then some 0 else none
/-- What the last party takes: `acc ↦ c` and the second receipt. -/
def rT (c : Nat) : Heap := fun y => if y = acc then some c else if y = r1 then some 0 else none

/-- The producer's contribution. -/
def cpv (vs : List Nat) : Nat := vs.length % 2 ^ 64
/-- The consumer's contribution. -/
def ccv (vs : List Nat) : Nat := vs.sum % 2 ^ 64
/-- The total. -/
def tot (vs : List Nat) : Nat := (vs.length + vs.sum) % 2 ^ 64

/-- **The resource the mutex protects.** -/
def Rv (vs : List Nat) : HProp := fun h =>
  h = rA ∨ h = rOne pP (cpv vs) ∨ h = rOne pC (ccv vs) ∨ h = rD

/-- What each party ends with: the first receipt, or the second receipt and the total. -/
def Fin (vs : List Nat) (h : Heap) : Prop := h = Heap.single r0 0 ∨ h = rT (tot vs)

theorem none_of_disj {A B : Heap} (d : Heap.Disjoint A B) {y : Nat} (h : (A y).isSome) :
    B y = none := by
  rcases d y with e | e
  · rw [e] at h; cases h
  · exact e

theorem tot_cp (vs : List Nat) : (ccv vs + cpv vs) % 2 ^ 64 = tot vs := by
  simp only [ccv, cpv, tot]; omega

theorem tot_cc (vs : List Nat) : (cpv vs + ccv vs) % 2 ^ 64 = tot vs := by
  simp only [ccv, cpv, tot]; omega

theorem rdi_m (rs : Regs) : ((rs.set .rdi ((Expr.lit m).eval rs)) .rdi).toNat = m := by
  simp [Regs.set, Expr.eval, m]

theorem acc_eval (rs : Regs) : ((Expr.lit acc).eval rs).toNat = acc := lit_eval _ (by decide) _
theorem sm_eval (rs : Regs) : ((Expr.lit sm).eval rs).toNat = sm := lit_eval _ (by decide) _

theorem add_val (a c : Nat) (rs : Regs) :
    ((Expr.bin .add (.reg .rax) (.lit c)).eval (rs.set .rax (BitVec.ofNat 64 a))).toNat %
      2 ^ (8 * 8) = (a + c) % 2 ^ 64 := by
  simp [Expr.eval, BinOp.eval, set_get, BitVec.toNat_add]

/-- The heap after a plain store to a cell. -/
def upd1 (h : Heap) (a v : Nat) : Heap := fun y => if y = a then some v else h y

/-- **The unlock, framed**: from `R ∗ locked` on `hU ∪ hL`-shaped heaps, keeping `hK`. -/
theorem unlock_framed (M : IfaceG) {vs : List Nat} (hsz : m + M.size ≤ 2 ^ 64) (L : Nat)
    {rs : Regs} {hR hL gL hK gF : Heap} (hRR : Rv vs hR) (dRL : Heap.Disjoint hR hL)
    (hLk : M.locked m hL gL) (dK : Heap.Disjoint (Heap.union hR hL) hK)
    (dg : Heap.Disjoint (Heap.union Heap.empty gL) gF) {K : Heap → Prop} (hfin : K hK) :
    SafeR (gsep (M.inv m (Rv vs)) (Chan vs)) (fun _ _ h _ => K h) false (M.unlock L (.lit m))
      rs (Heap.union (Heap.union hR hL) hK) (Heap.union (Heap.union Heap.empty gL) gF) := by
  unfold IfaceG.unlock
  apply safeR_seq
  apply safeR_assign
  have U := M.unlock_spec m (Rv vs) (Chan vs) L _ (Heap.union hR hL) (Heap.union Heap.empty gL)
    (rdi_m rs) hsz ⟨hR, hL, Heap.empty, gL, dRL, rfl, disjoint_empty _, rfl, ⟨hRR, rfl⟩, hLk⟩
  have U2 := safeR_gframe (safeR_frame U dK) dg
  refine safeR_conseq (fun p rs' h g hp => ?_) U2
  obtain ⟨g1, ⟨h1, ⟨rfl, -⟩, -, rfl⟩, -, rfl⟩ := hp
  rw [union_empty_left]; exact hfin

theorem union_none {A B : Heap} {y : Nat} (h : Heap.union A B y = none) :
    A y = none ∧ B y = none := by
  rw [union_apply] at h; cases e : A y
  · rw [e, Option.none_or] at h; exact ⟨rfl, h⟩
  · rw [e] at h; cases h

/-- **The producer's critical section and unlock**, from the lock's postcondition. -/
theorem prodCs_safe (M : IfaceG) {vs : List Nat} (hsz : m + M.size ≤ 2 ^ 64) (L : Nat)
    {rs : Regs} {hR hL gL gF : Heap} (hRR : Rv vs hR) (dRL : Heap.Disjoint hR hL)
    (hLk : M.locked m hL gL) (d1 : Heap.Disjoint (Heap.union hR hL) (Heap.single pP 0))
    (dg : Heap.Disjoint (Heap.union Heap.empty gL) gF) :
    SafeR (gsep (M.inv m (Rv vs)) (Chan vs)) (fun _ _ h _ => Fin vs h) false
      (.seq (prodCs vs.length) (M.unlock L (.lit m))) rs
      (Heap.union (Heap.union hR hL) (Heap.single pP 0))
      (Heap.union (Heap.union Heap.empty gL) gF) := by
  have hpP := union_none (none_of_disj (disjoint_symm d1) (y := pP) (by simp [single_apply]))
  have dL : ∀ y, (hR y).isSome → hL y = none := fun y h => none_of_disj dRL h
  apply safeR_seq
  unfold prodCs
  apply safeR_seq
  rcases hRR with rfl | rfl | rfl | rfl
  · -- first to enter: `acc = 0`
    have hLa := dL acc (by simp [rA])
    have hL0 := dL r0 (by simp [rA])
    have hL1 := dL r1 (by simp [rA])
    refine safeR_load_own (v := 0) (by rw [acc_eval]; simp [union_apply, rA]) ?_
    refine safeR_store_own (by rw [acc_eval]; simp [union_apply, rA]) ?_
    rw [acc_eval, add_val]
    have e : (fun y => if y = acc then some ((0 + vs.length) % 2 ^ 64) else
        Heap.union (Heap.union rA hL) (Heap.single pP 0) y) =
        Heap.union (Heap.union (rOne pP (cpv vs)) hL) (Heap.single r0 0) := by
      funext y
      simp only [union_apply, single_apply, rA, rOne]
      by_cases ha : y = acc
      · subst ha; simp [cpv]
      by_cases h0 : y = r0
      · subst h0; simp [hL0]
      by_cases h1 : y = r1
      · subst h1; simp
      by_cases hp : y = pP
      · subst hp; simp [hpP.2]
      simp [ha, h0, h1, hp]
    rw [e]
    refine unlock_framed M hsz L (Or.inr (Or.inl rfl)) (fun y => ?_) hLk (fun y => ?_) dg
      (K := Fin vs) (Or.inl rfl)
    · by_cases ha : y = acc
      · subst ha; exact Or.inr hLa
      by_cases h1 : y = r1
      · subst h1; exact Or.inr hL1
      by_cases hp : y = pP
      · subst hp; exact Or.inr hpP.2
      left; simp [rOne, ha, h1, hp]
    · by_cases h0 : y = r0
      · subst h0; left; simp [union_apply, rOne, hL0]
      · right; simp [single_apply, h0]
  · exact absurd hpP.1 (by simp [union_apply, rOne])
  · -- second to enter: `acc = Σ vs`
    have hLa := dL acc (by simp [rOne])
    have hL1 := dL r1 (by simp [rOne])
    have hLc := dL pC (by simp [rOne])
    refine safeR_load_own (v := ccv vs) (by rw [acc_eval]; simp [union_apply, rOne]) ?_
    refine safeR_store_own (by rw [acc_eval]; simp [union_apply, rOne]) ?_
    rw [acc_eval, add_val]
    have e : (fun y => if y = acc then some ((ccv vs + vs.length) % 2 ^ 64) else
        Heap.union (Heap.union (rOne pC (ccv vs)) hL) (Heap.single pP 0) y) =
        Heap.union (Heap.union rD hL) (rT (tot vs)) := by
      funext y
      simp only [union_apply, single_apply, rD, rOne, rT]
      by_cases ha : y = acc
      · subst ha; simp [hLa, ← tot_cp, cpv]
      by_cases h1 : y = r1
      · subst h1; simp [hL1]
      by_cases hc : y = pC
      · subst hc; simp
      by_cases hp : y = pP
      · subst hp; simp [hpP.2]
      simp [ha, h1, hc, hp]
    rw [e]
    refine unlock_framed M hsz L (Or.inr (Or.inr (Or.inr rfl))) (fun y => ?_) hLk (fun y => ?_) dg
      (K := Fin vs) (Or.inr rfl)
    · by_cases hc : y = pC
      · subst hc; exact Or.inr hLc
      by_cases hp : y = pP
      · subst hp; exact Or.inr hpP.2
      left; simp [rD, hc, hp]
    · by_cases ha : y = acc
      · subst ha; left; simp [union_apply, rD, hLa]
      by_cases h1 : y = r1
      · subst h1; left; simp [union_apply, rD, hL1]
      right; simp [rT, ha, h1]
  · exact absurd hpP.1 (by simp [union_apply, rD])

theorem add_val2 (a b : Nat) (rs : Regs) :
    ((Expr.bin .add (.reg .rax) (.reg .rcx)).eval
      ((rs.set .rax (BitVec.ofNat 64 a)).set .rcx (BitVec.ofNat 64 b))).toNat % 2 ^ (8 * 8) =
      (a + b) % 2 ^ 64 := by
  simp [Expr.eval, BinOp.eval, set_get, Regs.set, BitVec.toNat_add]

/-- The consumer's cells keep their values at the result's cells' addresses: none. -/
theorem cK_far (vs : List Nat) {y : Nat} (h : y = acc ∨ y = r0 ∨ y = r1 ∨ y = pP ∨ y = pC) :
    cK vs vs.length y = none := by
  have : ¬ isOut vs.length y := by
    rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [isOut, acc, r0, r1, pP, pC, ob]
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [cK, this]

theorem cK_sm (vs : List Nat) : cK vs vs.length sm = some (vs.sum % 2 ^ 64) := by
  simp [cK, List.take_length]

/-- What the consumer ends with. -/
def FinC (vs : List Nat) (h : Heap) : Prop := ∃ hr, Fin vs hr ∧ h = Heap.union hr (cK vs vs.length)

/-- **The consumer's critical section and unlock**, from the lock's postcondition. -/
theorem consCs_safe (M : IfaceG) {vs : List Nat} (hsz : m + M.size ≤ 2 ^ 64) (L : Nat)
    {rs : Regs} {hR hL gL gF : Heap} (hRR : Rv vs hR) (dRL : Heap.Disjoint hR hL)
    (hLk : M.locked m hL gL) (d1 : Heap.Disjoint (Heap.union hR hL) (cH vs vs.length))
    (dg : Heap.Disjoint (Heap.union Heap.empty gL) gF) :
    SafeR (gsep (M.inv m (Rv vs)) (Chan vs)) (fun _ _ h _ => FinC vs h) false
      (.seq consCs (M.unlock L (.lit m))) rs
      (Heap.union (Heap.union hR hL) (cH vs vs.length))
      (Heap.union (Heap.union Heap.empty gL) gF) := by
  have hpC := union_none (none_of_disj (disjoint_symm d1) (y := pC)
    (by simp [cH, union_apply, single_apply, cK_far vs (y := pC) (by simp)]))
  have hsmn := union_none (none_of_disj (disjoint_symm d1) (y := sm)
    (by simp [cH, union_apply, cK_sm]))
  have dL : ∀ y, (hR y).isSome → hL y = none := fun y h => none_of_disj dRL h
  have dK : ∀ y, (cK vs vs.length y).isSome → hL y = none := fun y h =>
    (union_none (none_of_disj (disjoint_symm d1) (y := y) (by simp [cH, union_apply, h]))).2
  have hsmv : Heap.union (Heap.union hR hL) (cH vs vs.length) sm = some (vs.sum % 2 ^ 64) := by
    simp [union_apply, hsmn.1, hsmn.2, cH, cK_sm]
  have hS : vs.sum % 2 ^ 64 = ccv vs := rfl
  apply safeR_seq
  unfold consCs
  apply safeR_seq
  rcases hRR with rfl | rfl | rfl | rfl
  · -- first to enter: `acc = 0`
    have hLa := dL acc (by simp [rA])
    have hL0 := dL r0 (by simp [rA])
    have hL1 := dL r1 (by simp [rA])
    refine safeR_load_own (v := 0) (by rw [acc_eval]; simp [union_apply, rA]) ?_
    apply safeR_seq
    refine safeR_load_own (v := vs.sum % 2 ^ 64) (by rw [sm_eval]; exact hsmv) ?_
    refine safeR_store_own (by rw [acc_eval]; simp [union_apply, rA]) ?_
    rw [acc_eval, add_val2]
    have e : (fun y => if y = acc then some ((0 + vs.sum % 2 ^ 64) % 2 ^ 64) else
        Heap.union (Heap.union rA hL) (cH vs vs.length) y) =
        Heap.union (Heap.union (rOne pC (ccv vs)) hL)
          (Heap.union (Heap.single r0 0) (cK vs vs.length)) := by
      funext y
      simp only [union_apply, single_apply, rA, rOne, cH]
      by_cases ha : y = acc
      · subst ha; simp [ccv]
      by_cases h0 : y = r0
      · subst h0; simp [hL0, cK_far vs (y := r0) (by simp)]
      by_cases h1 : y = r1
      · subst h1; simp [cK_far vs (y := r1) (by simp)]
      by_cases hc : y = pC
      · subst hc; simp [hpC.2, cK_far vs (y := pC) (by simp)]
      simp only [ha, h0, h1, hc, false_or, ite_false, Option.none_or, Option.or_none]
    rw [e]
    refine unlock_framed M hsz L (Or.inr (Or.inr (Or.inl rfl))) (fun y => ?_) hLk (fun y => ?_) dg
      (K := FinC vs) ⟨Heap.single r0 0, Or.inl rfl, rfl⟩
    · by_cases ha : y = acc
      · subst ha; exact Or.inr hLa
      by_cases h1 : y = r1
      · subst h1; exact Or.inr hL1
      by_cases hc : y = pC
      · subst hc; exact Or.inr hpC.2
      left; simp [rOne, ha, h1, hc]
    · by_cases h0 : y = r0
      · subst h0; left; simp [union_apply, rOne, hL0]
      cases e : cK vs vs.length y with
      | none => right; simp [union_apply, single_apply, h0, e]
      | some w =>
        have hl := dK y (by rw [e]; rfl)
        have : ¬ (y = acc ∨ y = r0 ∨ y = r1 ∨ y = pP ∨ y = pC) := fun h => by
          rw [cK_far vs h] at e; cases e
        simp only [not_or] at this
        left; simp [union_apply, rOne, hl, this.1, this.2.2.1, this.2.2.2.2]
  · -- second to enter: `acc = |vs|`
    have hLa := dL acc (by simp [rOne])
    have hL1 := dL r1 (by simp [rOne])
    have hLp := dL pP (by simp [rOne])
    refine safeR_load_own (v := cpv vs) (by rw [acc_eval]; simp [union_apply, rOne]) ?_
    apply safeR_seq
    refine safeR_load_own (v := vs.sum % 2 ^ 64) (by rw [sm_eval]; exact hsmv) ?_
    refine safeR_store_own (by rw [acc_eval]; simp [union_apply, rOne]) ?_
    rw [acc_eval, add_val2]
    have e : (fun y => if y = acc then some ((cpv vs + vs.sum % 2 ^ 64) % 2 ^ 64) else
        Heap.union (Heap.union (rOne pP (cpv vs)) hL) (cH vs vs.length) y) =
        Heap.union (Heap.union rD hL) (Heap.union (rT (tot vs)) (cK vs vs.length)) := by
      funext y
      simp only [union_apply, single_apply, rD, rOne, rT, cH]
      by_cases ha : y = acc
      · subst ha; simp [hLa, ← tot_cc, ccv]
      by_cases h1 : y = r1
      · subst h1; simp [hL1, cK_far vs (y := r1) (by simp)]
      by_cases hp : y = pP
      · subst hp; simp [cK_far vs (y := pP) (by simp)]
      by_cases hc : y = pC
      · subst hc; simp [hpC.2, cK_far vs (y := pC) (by simp)]
      simp only [ha, h1, hp, hc, false_or, ite_false, Option.none_or, Option.or_none]
    rw [e]
    refine unlock_framed M hsz L (Or.inr (Or.inr (Or.inr rfl))) (fun y => ?_) hLk (fun y => ?_) dg
      (K := FinC vs) ⟨rT (tot vs), Or.inr rfl, rfl⟩
    · by_cases hc : y = pC
      · subst hc; exact Or.inr hpC.2
      by_cases hp : y = pP
      · subst hp; exact Or.inr hLp
      left; simp [rD, hc, hp]
    · by_cases ha : y = acc
      · subst ha; left; simp [union_apply, rD, hLa]
      by_cases h1 : y = r1
      · subst h1; left; simp [union_apply, rD, hL1]
      cases e : cK vs vs.length y with
      | none => right; simp [union_apply, rT, ha, h1, e]
      | some w =>
        have hl := dK y (by rw [e]; rfl)
        have : ¬ (y = acc ∨ y = r0 ∨ y = r1 ∨ y = pP ∨ y = pC) := fun h => by
          rw [cK_far vs h] at e; cases e
        simp only [not_or] at this
        left; simp [union_apply, rD, hl, this.2.2.2.1, this.2.2.2.2]
  · exact absurd hpC.1 (by simp [union_apply, rOne])
  · exact absurd hpC.1 (by simp [union_apply, rD])

/-! ## The two threads -/

/-- The global invariant at `M`. -/
def gInv (M : IfaceG) (vs : List Nat) : GProp := gsep (M.inv m (Rv vs)) (Chan vs)

theorem gthr_far (M : IfaceG) (t : Nat) : ∀ x, (M.gthr m t x).isSome → (Nat.unpair x).1 ≠ gbase :=
  fun x h => by rw [M.gdom m x (Or.inr ⟨t, h⟩)]; decide

theorem ginit_far (M : IfaceG) : ∀ x, (M.ginit m x).isSome → (Nat.unpair x).1 ≠ gbase :=
  fun x h => by rw [M.gdom m x (Or.inl h)]; decide

/-- **The producer's lock, critical section and unlock.** -/
theorem prodTail_safe (M : IfaceG) {vs : List Nat} (hsz : m + M.size ≤ 2 ^ 64) (L : Nat)
    {p : Bool} {rs : Regs} (hready : M.ready m (M.gthr m 0)) :
    SafeR (gInv M vs) (fun _ _ h _ => Fin vs h) p
      (.seq (M.lock L (.lit m)) (.seq (prodCs vs.length) (M.unlock L (.lit m)))) rs
      (Heap.single pP 0) (Heap.union (prodG vs.length vs.length) (M.gthr m 0)) := by
  have hgd : Heap.Disjoint (M.gthr m 0) (prodG vs.length vs.length) :=
    disjoint_symm (gh_disj_far (gthr_far M 0))
  rw [union_comm (disjoint_symm hgd)]
  apply safeR_seq
  unfold IfaceG.lock
  apply safeR_seq
  apply safeR_assign
  have H := frame2 (hF := Heap.single pP 0)
    (M.lock_spec m (Rv vs) (Chan vs) L _ p (M.gthr m 0) (rdi_m rs) hsz hready) hgd
  refine safeR_conseq (fun p' rs' h' g' hp => ?_) H
  obtain ⟨h1, g1, ⟨rfl, hRL⟩, d1, rfl, d2, rfl⟩ := hp
  obtain ⟨hR, hL, gR, gL, dRL, rfl, -, rfl, ⟨hRR, rfl⟩, hLk⟩ := hRL
  exact prodCs_safe M hsz L hRR dRL hLk d1 d2

/-- **The consumer's lock, critical section and unlock.** -/
theorem consTail_safe (M : IfaceG) {vs : List Nat} (hsz : m + M.size ≤ 2 ^ 64) (L : Nat)
    {p : Bool} {rs : Regs} (hready : M.ready m (M.gthr m 1)) :
    SafeR (gInv M vs) (fun _ _ h _ => FinC vs h) p
      (.seq (M.lock L (.lit m)) (.seq consCs (M.unlock L (.lit m)))) rs
      (cH vs vs.length) (Heap.union (consG vs.length vs.length) (M.gthr m 1)) := by
  have hgd : Heap.Disjoint (M.gthr m 1) (consG vs.length vs.length) :=
    disjoint_symm (gh_disj_far (gthr_far M 1))
  rw [union_comm (disjoint_symm hgd)]
  apply safeR_seq
  unfold IfaceG.lock
  apply safeR_seq
  apply safeR_assign
  have H := frame2 (hF := cH vs vs.length)
    (M.lock_spec m (Rv vs) (Chan vs) L _ p (M.gthr m 1) (rdi_m rs) hsz hready) hgd
  refine safeR_conseq (fun p' rs' h' g' hp => ?_) H
  obtain ⟨h1, g1, ⟨rfl, hRL⟩, d1, rfl, d2, rfl⟩ := hp
  obtain ⟨hR, hL, gR, gL, dRL, rfl, -, rfl, ⟨hRR, rfl⟩, hLk⟩ := hRL
  exact consCs_safe M hsz L hRR dRL hLk d1 d2

/-- **The producer is `SafeR`**, for every mutex meeting the ghost-aware interface. -/
theorem prod_safe (M : IfaceG) {vs : List Nat} (hvs : ∀ v ∈ vs, v < 2 ^ 64)
    (hn : vs.length + 1 < 2 ^ 64) (hsz : m + M.size ≤ 2 ^ 64) (B L : Nat)
    (hready : M.ready m (M.gthr m 0)) :
    SafeR (gInv M vs) (fun _ _ h _ => Fin vs h) false (prod vs B (M.lock L) (M.unlock L))
      Regs.zero (Heap.single pP 0) (Heap.union (prodG 0 0) (M.gthr m 0)) :=
  sends_safe (fun _ _ => gh_disj_far (gthr_far M 0)) hvs hn
    (fun _ _ => prodTail_safe M hsz L hready) vs 0 (by simp) (Nat.zero_le _) _ _

/-- **The consumer is `SafeR`**, for every mutex meeting the ghost-aware interface. -/
theorem cons_safe (M : IfaceG) {vs : List Nat} (hvs : ∀ v ∈ vs, v < 2 ^ 64)
    (hn : vs.length < 2 ^ 32) (hsz : m + M.size ≤ 2 ^ 64) (B L : Nat)
    (hready : M.ready m (M.gthr m 1)) :
    SafeR (gInv M vs) (fun _ _ h _ => FinC vs h) false (cons vs.length B (M.lock L) (M.unlock L))
      Regs.zero (cH vs 0) (Heap.union (consG 0 0) (M.gthr m 1)) :=
  recvs_safe (fun _ _ => gh_disj_far (gthr_far M 1)) hvs hn
    (fun _ _ _ => consTail_safe M hsz L hready) vs.length 0 (by simp) _ _ (by simp [Regs.zero])

/-! ## The certificate -/

/-- The postconditions. -/
def post (vs : List Nat) (t : Nat) : Bool → Regs → Heap → Heap → Prop :=
  fun _ _ h _ => if t = 0 then Fin vs h else FinC vs h

/-- The threads' cells at the start. -/
def hs0 (vs : List Nat) (t : Nat) : Heap :=
  if t = 0 then Heap.single pP 0 else if t = 1 then cH vs 0 else Heap.empty

/-- The threads' ghost cells at the start. -/
def gs0 (M : IfaceG) (t : Nat) : Heap :=
  if t = 0 then Heap.union (prodG 0 0) (M.gthr m 0)
  else if t = 1 then Heap.union (consG 0 0) (M.gthr m 1) else Heap.empty

/-- The invariant's cells at the start. -/
def hI0 (M : IfaceG) (vs : List Nat) : Heap :=
  Heap.union (Heap.union (M.init m) rA) (chanH vs 0 0 0 0 0)

/-- The invariant's ghost cells at the start. -/
def gI0 (M : IfaceG) : Heap := Heap.union (M.ginit m) (invG 0 0 0 0)

theorem init_low (M : IfaceG) (hM : M.size ≤ 8) {y : Nat} (h : (M.init m y).isSome) :
    m ≤ y ∧ y < m + 8 := by
  have := M.init_dom m y h; omega

theorem init_none (M : IfaceG) (hM : M.size ≤ 8) {y : Nat} (h : y < m ∨ m + 8 ≤ y) :
    M.init m y = none := by
  cases e : M.init m y with
  | none => rfl
  | some _ => have := init_low M hM (y := y) (by rw [e]; rfl); omega

theorem cK0 (vs : List Nat) (y : Nat) :
    cK vs 0 y = if y = sm ∨ isOut vs.length y then some 0 else none := by
  simp only [cK, List.take_zero, List.sum_nil, Nat.zero_mod]
  by_cases h1 : y = sm
  · simp [h1]
  · by_cases h2 : isOut vs.length y <;> simp [h1, h2]

/-- Every cell of a thread or of the invariant at the start lies at or above `0x200` or in the
mutex's slot. -/
theorem hs0_far (vs : List Nat) (t : Nat) {y : Nat} (h : (hs0 vs t y).isSome) : 0x200 ≤ y := by
  simp only [hs0] at h
  split_ifs at h with h0 h1
  · simp [single_apply] at h; rw [h]; decide
  · simp only [cH, union_apply, single_apply, cK0] at h
    by_cases e1 : y = sm ∨ isOut vs.length y
    · rcases e1 with rfl | e1
      · decide
      · simp only [isOut, ob] at e1; omega
    · by_cases e2 : y = pC
      · rw [e2]; decide
      · simp [e1, e2] at h
  · simp [Heap.empty] at h

theorem hI0_far (M : IfaceG) (hM : M.size ≤ 8) (vs : List Nat) {y : Nat} (hy : 0x200 ≤ y)
    (h1 : y ≠ acc) (h2 : y ≠ r0) (h3 : y ≠ r1) (h4 : y ≠ cseq) (h5 : y ≠ cack) (h6 : y ≠ cdat) :
    hI0 M vs y = none := by
  simp only [hI0, union_apply, init_none M hM (y := y) (Or.inr (by simp only [m]; omega)), rA,
    h1, h2, h3, false_or, ite_false, Option.none_or]
  exact chanH_other _ _ _ _ _ _ h4 h5 h6

theorem hs0_cells (vs : List Nat) {t y : Nat} (h : (hs0 vs t y).isSome) :
    y = pP ∨ y = sm ∨ y = pC ∨ isOut vs.length y := by
  simp only [hs0] at h
  split_ifs at h with h0 h1
  · simp [single_apply] at h; exact Or.inl h
  · simp only [cH, union_apply, single_apply, cK0] at h
    by_cases e1 : y = sm
    · exact Or.inr (Or.inl e1)
    by_cases e2 : isOut vs.length y
    · exact Or.inr (Or.inr (Or.inr e2))
    by_cases e3 : y = pC
    · exact Or.inr (Or.inr (Or.inl e3))
    simp [e1, e2, e3] at h
  · simp [Heap.empty] at h

theorem isOut_ge {n y : Nat} (h : isOut n y) : ob ≤ y := h.1

theorem hs0_hI0 (M : IfaceG) (hM : M.size ≤ 8) (vs : List Nat) (t : Nat) :
    Heap.Disjoint (hs0 vs t) (hI0 M vs) := fun y => by
  cases e : (hs0 vs t y).isSome
  · left; cases e' : hs0 vs t y
    · rfl
    · rw [e'] at e; cases e
  · right
    have hf := hs0_far vs t (y := y) (by rw [e])
    rcases hs0_cells vs (by rw [e]) with rfl | rfl | rfl | ho
    · exact hI0_far M hM vs hf (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact hI0_far M hM vs hf (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · exact hI0_far M hM vs hf (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    · have := isOut_ge ho
      exact hI0_far M hM vs hf (by simp only [acc, ob] at *; omega)
        (by simp only [r0, ob] at *; omega)
        (by simp only [r1, ob] at *; omega) (by simp only [cseq, ob] at *; omega)
        (by simp only [cack, ob] at *; omega) (by simp only [cdat, ob] at *; omega)

theorem hs0_disj (vs : List Nat) {t u : Nat} (htu : t ≠ u) :
    Heap.Disjoint (hs0 vs t) (hs0 vs u) := by
  have key : Heap.Disjoint (Heap.single pP 0) (cH vs 0) := fun y => by
    by_cases hy : y = pP
    · subst hy; right
      simp [cH, union_apply, single_apply, cK0, isOut, pP, ob, sm, pC]
    · left; simp [single_apply, hy]
  intro y
  simp only [hs0]
  by_cases t0 : t = 0 <;> by_cases t1 : t = 1 <;> by_cases u0 : u = 0 <;> by_cases u1 : u = 1 <;>
    simp only [t0, t1, u0, u1, ite_true, ite_false] <;> first
    | omega
    | exact Or.inl rfl
    | exact Or.inr rfl
    | exact key y
    | exact (key y).symm

/-- **The pipeline's certificate** at every mutex meeting the ghost-aware interface that fits
the slot and supports two threads. -/
theorem pipe_ginvG (M : IfaceG) (hM : M.size ≤ 8) (hN : M.thrOk 2) {vs : List Nat}
    (hvs : ∀ v ∈ vs, v < 2 ^ 64) (hn : vs.length < 2 ^ 32) (B L : Nat) :
    GInvR (gInv M vs) (post vs) 2 ((client vs B).linkG M L) (hs0 vs) (gs0 M) (hI0 M vs)
      (gI0 M) := by
  have hsz : m + M.size ≤ 2 ^ 64 := by simp only [m]; omega
  have hmem : ((client vs B).linkG M L).mem =
      Heap.union (mem vs.length) (Heap.union (M.init m) Heap.empty) := rfl
  have memsome : ∀ y, mem vs.length y = some 0 → ((client vs B).linkG M L).mem y = some 0 :=
    fun y h => by rw [hmem, union_apply, h]; rfl
  refine ⟨fun t u h => hs0_disj vs h, fun t => hs0_hI0 M hM vs t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ghost cells of the threads
    intro t u htu
    have dPC : Heap.Disjoint (prodG 0 0) (consG 0 0) := by
      simp only [prodG, consG, gh_disj]; intro f i hf
      rcases f with _ | _ | _ | _ | _ | _ | f <;> simp
    have d01 : Heap.Disjoint (Heap.union (prodG 0 0) (M.gthr m 0))
        (Heap.union (consG 0 0) (M.gthr m 1)) :=
      disj_union_left (disj_union_right dPC (gh_disj_far (gthr_far M 1)))
        (disj_union_right (disjoint_symm (gh_disj_far (gthr_far M 0)))
          (M.gthr_disj m 0 1 (by decide)))
    intro y
    simp only [gs0]
    by_cases t0 : t = 0 <;> by_cases t1 : t = 1 <;> by_cases u0 : u = 0 <;> by_cases u1 : u = 1 <;>
      simp only [t0, t1, u0, u1, ite_true, ite_false] <;> first
      | omega
      | exact Or.inl rfl
      | exact Or.inr rfl
      | exact d01 y
      | exact (d01 y).symm
  · -- threads' ghost cells against the invariant's
    intro t
    have dP : Heap.Disjoint (Heap.union (prodG 0 0) (M.gthr m 0)) (gI0 M) :=
      disj_union_left (disj_union_right (gh_disj_far (ginit_far M)) (prod_disj (Nat.le_refl _)))
        (disj_union_right (fun y => (M.ginit_disj m 0 y).symm)
          (disjoint_symm (gh_disj_far (gthr_far M 0))))
    have dC : Heap.Disjoint (Heap.union (consG 0 0) (M.gthr m 1)) (gI0 M) :=
      disj_union_left (disj_union_right (gh_disj_far (ginit_far M)) (cons_disj (Nat.le_refl _)))
        (disj_union_right (fun y => (M.ginit_disj m 1 y).symm)
          (disjoint_symm (gh_disj_far (gthr_far M 1))))
    simp only [gs0]
    split_ifs
    · exact dP
    · exact dC
    · exact disjoint_empty _
  · -- threads' cells in memory
    intro t y v hv
    have hs := hs0_cells vs (t := t) (y := y) (by rw [hv]; rfl)
    simp only [hs0] at hv
    split_ifs at hv with h0 h1
    · simp [single_apply] at hv
      obtain ⟨rfl, rfl⟩ := hv
      exact memsome _ (by simp [mem])
    · simp only [cH, union_apply, single_apply, cK0] at hv
      have hv0 : v = 0 := by
        split_ifs at hv <;> simp_all
      subst hv0
      apply memsome
      rcases hs with rfl | rfl | rfl | ho
      · simp [cK0, isOut, pP, sm, pC, ob] at hv
      · simp [mem]
      · simp [mem]
      · simp [mem, ho]
    · simp [Heap.empty] at hv
  · -- the invariant's cells in memory
    intro y v hv
    simp only [hI0, union_apply] at hv
    cases ei : M.init m y with
    | some w =>
      rw [ei] at hv; cases hv
      have hl := init_low M hM (y := y) (by rw [ei]; rfl)
      rw [hmem, union_apply, union_apply, ei]
      have : mem vs.length y = none := by
        simp only [mem, isOut, ob, cseq, cack, cdat, acc, r0, r1, pP, pC, sm, m] at hl ⊢
        refine ite_eq_right_iff.mpr (fun hc => ?_)
        exfalso; omega
      rw [this]; rfl
    | none =>
      rw [ei, Option.none_or] at hv
      by_cases hA : y = acc ∨ y = r0 ∨ y = r1
      · simp only [rA, hA, ite_true] at hv
        cases hv
        apply memsome
        rcases hA with rfl | rfl | rfl <;> simp [mem]
      · simp only [rA, hA, ite_false, Option.none_or] at hv
        by_cases h1 : y = cseq
        · subst h1; rw [chanH_sq] at hv; cases hv; exact memsome _ (by simp [mem])
        by_cases h2 : y = cack
        · subst h2; rw [chanH_ak] at hv; cases hv; exact memsome _ (by simp [mem])
        by_cases h3 : y = cdat
        · subst h3; rw [chanH_dt] at hv; simp at hv; subst hv; exact memsome _ (by simp [mem])
        rw [chanH_other _ _ _ _ _ _ h1 h2 h3] at hv; cases hv
  · -- the invariant holds
    refine ⟨Heap.union (M.init m) rA, chanH vs 0 0 0 0 0, M.ginit m, invG 0 0 0 0, ?_, rfl,
      gh_disj_far (ginit_far M) |> disjoint_symm, rfl,
      M.init_inv m (Rv vs) rA (Or.inl rfl) ?_, 0, 0, 0, 0, 0,
      ⟨by omega, by omega, by omega, by omega⟩,
      rfl, rfl⟩
    · refine disj_union_left (fun y => ?_) (fun y => ?_)
      · cases e : M.init m y with
        | none => exact Or.inl rfl
        | some _ =>
          have hl := init_low M hM (y := y) (by rw [e]; rfl)
          right; exact chanH_other _ _ _ _ _ _ (by simp only [cseq, m] at *; omega)
            (by simp only [cack, m] at *; omega) (by simp only [cdat, m] at *; omega)
      · by_cases h : y = acc ∨ y = r0 ∨ y = r1
        · right
          rcases h with rfl | rfl | rfl <;> exact chanH_other _ _ _ _ _ _ (by decide) (by decide)
            (by decide)
        · left; simp [rA, h]
    · intro y
      by_cases h : y = acc ∨ y = r0 ∨ y = r1
      · left
        rcases h with rfl | rfl | rfl <;>
          exact init_none M hM (by simp only [acc, r0, r1, m]; omega)
      · right; simp [rA, h]
  · -- the threads are safe
    intro t ht
    have hts : ((client vs B).linkG M L).ts t =
        (body vs B (M.lock L) (M.unlock L) t, Regs.zero) := by
      simp [Mutex.Client.linkG, Mutex.Client.startWith, client, ht]
    rw [hts]
    rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
    · simp only [body, post, hs0, gs0, ite_true]
      exact prod_safe M hvs (by omega) hsz B L (M.ready_thr m 2 0 hN (by decide))
    · simp only [body, post, hs0, gs0, show (1 : Nat) ≠ 0 by decide, ite_true, ite_false]
      exact cons_safe M hvs hn hsz B L (M.ready_thr m 2 1 hN (by decide))

/-! ## Adequacy -/

theorem fin_out {vs : List Nat} {hr : Heap} (h : Fin vs hr) {y : Nat} (hy : y ≠ r0) (h1 : y ≠ r1)
    (h2 : y ≠ acc) : hr y = none := by
  rcases h with rfl | rfl
  · simp [single_apply, hy]
  · simp [rT, h1, h2]

/-- **The pipeline's goal from the final postconditions**: the two parties' final heaps are
disjoint, so they hold different receipts, and the holder of `r1` holds `acc ↦ |vs| + Σ vs`. -/
theorem goal_of_posts {vs : List Nat} {mem' : Heap} {h0 h1 : Heap} (q0 : Fin vs h0)
    (q1 : FinC vs h1) (d : Heap.Disjoint h0 h1) (l0 : Heap.Le h0 mem') (l1 : Heap.Le h1 mem') :
    Goal vs mem' := by
  obtain ⟨hr, qr, rfl⟩ := q1
  have k0 : ∀ y, cK vs vs.length y = none → (y = acc ∨ y = r0 ∨ y = r1) →
      Heap.union hr (cK vs vs.length) y = hr y := fun y e _ => by rw [union_apply, e]; simp
  refine ⟨?_, fun k hk => ?_⟩
  · have ha : cK vs vs.length acc = none := cK_far vs (by simp)
    rcases q0 with rfl | rfl
    · rcases qr with rfl | rfl
      · exfalso
        rcases d r0 with e | e
        · simp [single_apply] at e
        · rw [k0 r0 (cK_far vs (by simp)) (by simp)] at e; simp [single_apply] at e
      · exact l1 _ _ (by rw [k0 acc ha (by simp)]; simp [rT, tot])
    · exact l0 _ _ (by simp [rT, tot])
  · have hok : out k ≠ r0 ∧ out k ≠ r1 ∧ out k ≠ acc := by
      simp only [out, ob, r0, r1, acc]; omega
    apply l1
    rw [union_apply, fin_out qr hok.1 hok.2.1 hok.2.2, Option.none_or]
    have ho : out k ≠ sm := by simp only [out, ob, sm]; omega
    simp [cK, ho, isOut_out hk, out_idx, hk]

/-- **The pipeline on TSO**, for every mutex meeting the ghost-aware interface. -/
theorem pipe_linkG (M : IfaceG) (hM : M.size ≤ 8) (hN : M.thrOk 2) {vs : List Nat}
    (hvs : ∀ v ∈ vs, v < 2 ^ 64) (hn : vs.length < 2 ^ 32) (B L : Nat) {Cf : OCfg}
    (hr : OReach .tso 2 ((client vs B).linkG M L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < 2, (Cf.ts t).1 = .skip) : Goal vs Cf.mem := by
  obtain ⟨hs', gs', hI', gI', ps', q, -, le, -, dp, -, -⟩ :=
    rel_tsoG (G0 := Heap.empty) (pipe_ginvG M hM hN hvs hn B L)
      (fun c h => by simp [empty_apply] at h)
      hr hd hf
  have q0 := q 0 (by decide)
  have q1 := q 1 (by decide)
  simp only [post, ite_true, show (1 : Nat) ≠ 0 by decide, ite_false] at q0 q1
  exact goal_of_posts q0 q1 (dp 0 1 (by decide)) (le 0) (le 1)

/-! ## The client is tame -/

theorem sends_wb (B : Nat) (t : Stmt) : ∀ (k : Nat) (l : List Nat),
    (sends B k l t).wbStores = t.wbStores := by
  intro k l
  induction l generalizing k with
  | nil => rfl
  | cons v l ih => simp [sends, send, spin, sendPub, Stmt.wbStores, ih]

theorem recvs_wb (B : Nat) (t : Stmt) : ∀ (k r : Nat), (recvs B k r t).wbStores = t.wbStores := by
  intro k r
  induction r generalizing k with
  | zero => rfl
  | succ r ih => simp [recvs, recv, spin, recvTake, Stmt.wbStores, ih]

/-- **The pipeline is tame**: every store is write-back. -/
theorem pipe_wb (vs : List Nat) (B : Nat) : (client vs B).WbIn := by
  intro lk ul hl hu t
  simp only [client, body]
  split_ifs
  · simp [prod, sends_wb, Stmt.wbStores, prodCs, hl, hu]
  · simp [cons, recvs_wb, Stmt.wbStores, consCs, hl, hu]

end Silmaril.Proofs.X86.Concurrency.Story.Pipe

