module

public import Silmaril.Proofs.X86.Concurrency.Cir.Rc.Arc

/-!
# Proofs: the `Drop2` client

`drop2_certified`: for **every** CIR allocator `A` (any `Alloc`, used only through
`free_spec`) and every placement of its heaps away from the client's cells, the start of
`Drop2` has a CSL certificate with the invariant `rcInv l (P A) ∗ A.mm` and the postconditions
`blank l t ∗ blank l (2 + t) ∗ out t ↦ 42`.

Each thread: clones (`rc_inc_spec`, with its blank), reads the payload through its token
(`rc_load_spec`), stores it to its own output cell (`na`), drops the clone (`rc_drop_keep`: it
still holds its own token, so this is not the last reference), and drops its own reference
(`rc_drop_spec`). On the last reference the cold path owns `l ↦ 0 ∗ 42 at l + 4 ∗ blk l`: it
overwrites the payload non-atomically and frees the object through `A.free_spec`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Rc

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Rc
open Silmaril.X86.Concurrency.Cir.Rc.Drop2
open Silmaril.X86.Concurrency.Cir.Mutex (safe_inv_frame safe_inv_eq)

/-! ## Addresses -/

theorem l_lt : l < gbase := by unfold l gbase; decide
theorem out_lt {t : Nat} (ht : t < 2) : out t < gbase := by unfold out gbase; omega
theorem l4_lt : l + 4 < gbase := by unfold l gbase; decide
theorem lit_eval (n : Nat) (hn : n < gbase) (rs : Regs) : ((Expr.lit n).eval rs).toNat = n := by
  simp only [Expr.eval, BitVec.toNat_ofNat]; unfold gbase at hn; omega
theorem out_ne_l {t : Nat} : out t ≠ l := by unfold out l; omega
theorem out_ne_l4 {t : Nat} : out t ≠ l + 4 := by unfold out l; omega
theorem l_ne_l4 : l ≠ l + 4 := by omega
theorem M_ge : 4 ≤ M := by unfold M; omega

/-! ## Heap rearrangements -/

theorem union_swap {A B C : Heap} (d : Heap.Disjoint B C) :
    Heap.union (Heap.union A B) C = Heap.union (Heap.union A C) B := by
  rw [union_assoc, union_comm d, ← union_assoc]

theorem updH_wr_last {m : Mode} {fl : Flav} {X : Heap} {a sz v w : Nat} (hX : X a = none) :
    (Lab.wr m fl a sz v).updH (Heap.union X (Heap.single a w)) =
      Heap.union X (Heap.single a v) := by
  funext x
  simp only [Lab.updH, Lab.wval, union_or]
  by_cases hx : x = a
  · subst hx; simp [hX, single_self]
  · have : a ≠ x := Ne.symm hx
    simp [this, single_ne hx]

theorem updH_wr_mid {m : Mode} {fl : Flav} {X Y : Heap} {a sz v w : Nat} (hX : X a = none) :
    (Lab.wr m fl a sz v).updH (Heap.union X (Heap.union (Heap.single a w) Y)) =
      Heap.union X (Heap.union (Heap.single a v) Y) := by
  funext x
  simp only [Lab.updH, Lab.wval, union_or]
  by_cases hx : x = a
  · subst hx; simp [hX, single_self]
  · have : a ≠ x := Ne.symm hx
    simp [this, single_ne hx]

theorem disj_of {h₁ h₂ : Heap} (H : ∀ x, (h₁ x).isSome → h₂ x = none) : Heap.Disjoint h₁ h₂ := by
  intro x
  cases e : h₁ x with
  | none => exact Or.inl rfl
  | some v => exact Or.inr (H x (by simp [e]))

/-! ## The cold path -/

/-- **The cold path**: from the count cell and the payload, write the payload (`na`, owned)
and free the object; nothing is left. -/
theorem slow_safe (A : Alloc) {rs : Regs} {hP : Heap} (hp : P A hP)
    (d : Heap.Disjoint (Heap.single l 0) hP) :
    Csl.Safe (inv A) (fun _ => hemp) (slow A) rs (Heap.union (Heap.single l 0) hP) := by
  obtain ⟨h4, hb, d4b, rfl, rfl, hblk⟩ := sep_iff.mp hp
  have hl4 : Heap.single l 0 (l + 4) = none := single_ne (Ne.symm l_ne_l4)
  refine safe_seq (safe_store_na (by rw [lit_eval _ l4_lt]; simp [union_or, hl4, single_self])
    ?_)
  have hz : ((Expr.lit 0).eval rs).toNat % 2 ^ (8 * 4) = 0 := by simp [Expr.eval]
  rw [lit_eval _ l4_lt, hz, updH_wr_mid hl4]
  refine safe_seq (safe_assign ?_)
  have hrdi : ((Regs.set rs .rdi ((Expr.lit l).eval rs)) .rdi).toNat = l := by
    simp [Regs.set, lit_eval _ l_lt]
  obtain ⟨dl4, dlb⟩ := disjoint_union_right.mp d
  have d4b' := disjoint_single_val (w := 0) d4b
  refine safe_inv_eq (fun _ => sep_comm_iff) (A.free_spec l (rcInv l (P A)) _ _ hrdi ?_)
  refine sep_iff.mpr ⟨hb, Heap.union (Heap.single l 0) (Heap.single (l + 4) 0), ?_, ?_, hblk,
    ⟨0, 0, rfl⟩⟩
  · exact disjoint_symm (disjoint_union_left.mpr ⟨dlb, d4b'⟩)
  · rw [← union_assoc, union_comm (disjoint_union_left.mpr ⟨dlb, d4b'⟩)]

/-! ## One thread -/

theorem body_safe (A : Alloc) {t : Nat} (ht : t < 2) :
    Csl.Safe (inv A) (post t) (body A t) Regs.zero (own t) := by
  have hM := M_ge
  have htM : t < M := by omega
  have ht2M : 2 + t < M := by omega
  have hl := l_lt
  have hot := out_lt ht
  -- distinct cells
  have nAA : gA l t ≠ gA l (2 + t) := fun e => by have := gA_inj hl e; omega
  have nAB : gA l t ≠ gB l (2 + t) := gA_ne_gB l t (2 + t) hl
  have nAB' : gA l (2 + t) ≠ gB l (2 + t) := gA_ne_gB l (2 + t) (2 + t) hl
  have nAt : gA l t ≠ gB l t := gA_ne_gB l t t hl
  have nBB : gB l t ≠ gB l (2 + t) := fun e => by have := gB_inj hl e; omega
  have nAo : ∀ k, gA l k ≠ out t := fun _ => gA_ne_lt hot
  have nBo : ∀ k, gB l k ≠ out t := fun _ => gB_ne_lt hot
  -- the start heap
  have h0 : own t = Heap.union (Heap.union (Heap.single (gA l t) 0) (Heap.single (gB l (2 + t)) 0))
      (Heap.single (out t) 0) := by
    simp only [own, ite_eq_left ht]; rw [union_assoc]
  rw [h0]
  -- clone
  have dTB : Heap.Disjoint (Heap.single (gA l t) 0) (Heap.single (gB l (2 + t)) 0) :=
    disjoint_single nAB
  have dO : Heap.Disjoint (Heap.union (Heap.single (gA l t) 0) (Heap.single (gB l (2 + t)) 0))
      (Heap.single (out t) 0) :=
    disjoint_union_left.mpr ⟨disjoint_single (nAo t), disjoint_single (nBo _)⟩
  refine safe_seq (safe_conseq ?_ (safe_frame (F := pt (out t) 0)
    (rc_inc_spec (J := A.mm) (P := P A) (d := .rax) (lit_eval l hl _)
      (sep_iff.mpr ⟨_, _, dTB, rfl, ⟨htM, rfl⟩, ⟨ht2M, rfl⟩⟩)) dO rfl))
  intro rs1 h1 H1
  obtain ⟨h12, ho, -, rfl, H12, rfl⟩ := sep_iff.mp H1
  obtain ⟨-, -, -, rfl, ⟨-, rfl⟩, ⟨-, rfl⟩⟩ := sep_iff.mp H12
  -- read the payload through the token
  refine safe_seq (rc_load_spec (k := t) (c := l + 4) (v0 := 42) (by decide)
    (lit_eval _ l4_lt _) hl htM (by simp [union_or, single_self]) ?_ ?_)
  · intro hP hp
    obtain ⟨-, -, -, rfl, rfl, -⟩ := sep_iff.mp hp
    simp [union_or, single_self]
  -- store it to the own output cell
  have hX : Heap.union (Heap.single (gA l t) 0) (Heap.single (gA l (2 + t)) 0) (out t) = none := by
    simp [union_or, single_ne (nAo _).symm]
  refine safe_seq (safe_store_na (by rw [lit_eval _ hot]; simp [union_or, hX, single_self]) ?_)
  rw [lit_eval _ hot, updH_wr_last hX]
  have h42 : ((Expr.reg .rbx).eval (Regs.set rs1 .rbx (BitVec.ofNat 64 42))).toNat %
      2 ^ (8 * 8) = 42 := by simp [Expr.eval, Regs.set]
  rw [h42]
  -- drop the clone: never the last, the thread keeps slot `t`
  have dAo : Heap.Disjoint (Heap.single (gA l (2 + t)) 0) (Heap.single (out t) 42) :=
    disjoint_single (nAo _)
  rw [union_swap dAo]
  have hTj : Heap.union (Heap.single (gA l t) 0) (Heap.single (out t) 42) (gA l t) = some 0 := by
    simp [union_or, single_self]
  have dT : Heap.Disjoint (Heap.union (Heap.single (gA l t) 0) (Heap.single (out t) 42))
      (Heap.single (gA l (2 + t)) 0) :=
    disjoint_union_left.mpr ⟨disjoint_single nAA, disjoint_single (nAo _).symm⟩
  refine safe_seq (rc_drop_keep (j := t) (lit_eval l hl _) ht2M htM (by omega) hTj dT ?_)
  intro rs2
  -- drop the own reference
  have dOB : Heap.Disjoint (Heap.single (out t) 42) (Heap.single (gB l (2 + t)) 0) :=
    disjoint_single (nBo _).symm
  have dA2 : Heap.Disjoint (Heap.single (gA l t) 0)
      (Heap.union (Heap.single (out t) 42) (Heap.single (gB l (2 + t)) 0)) :=
    disjoint_union_right.mpr ⟨disjoint_single (nAo _), disjoint_single nAB⟩
  rw [union_assoc, union_comm dA2]
  have dT2 : Heap.Disjoint (Heap.union (Heap.single (out t) 42) (Heap.single (gB l (2 + t)) 0))
      (Heap.single (gA l t) 0) := disjoint_symm dA2
  -- the final heap: both blanks and the output
  have dF : Heap.Disjoint (Heap.union (Heap.single (out t) 42) (Heap.single (gB l (2 + t)) 0))
      (Heap.single (gB l t) 0) :=
    disjoint_union_left.mpr ⟨disjoint_single (nBo _).symm, disjoint_single (Ne.symm nBB)⟩
  have hpost : ∀ rs', post t rs'
      (Heap.union (Heap.union (Heap.single (out t) 42) (Heap.single (gB l (2 + t)) 0))
        (Heap.single (gB l t) 0)) := by
    intro rs'
    refine sep_iff.mpr ⟨Heap.single (gB l t) 0,
      Heap.union (Heap.single (gB l (2 + t)) 0) (Heap.single (out t) 42),
      disjoint_union_right.mpr ⟨disjoint_single nBB, disjoint_single (nBo _)⟩, ?_, ⟨htM, rfl⟩,
      sep_iff.mpr ⟨Heap.single (gB l (2 + t)) 0, Heap.single (out t) 42, disjoint_symm dOB, rfl,
        ⟨ht2M, rfl⟩, rfl⟩⟩
    rw [union_comm dF, union_comm dOB]
  refine rc_drop_spec (lit_eval l hl _) htM dT2 ?_ hpost
  intro rs' hP _ hp _ d1 d2
  rw [union_comm d1]
  refine safe_conseq ?_ (safe_frame (F := exactly _) (slow_safe A hp d2) (disjoint_symm d1) rfl)
  intro rs'' h'' H
  obtain ⟨he, hf, -, rfl, rfl, rfl⟩ := sep_iff.mp H
  rw [union_empty_left]; exact hpost rs''

/-! ## The certificate -/

theorem own_cells {t x : Nat} (ht : t < 2) (hx : (own t x).isSome) :
    x = gA l t ∨ x = gB l (2 + t) ∨ x = out t := by
  simp only [own, ite_eq_left ht, union_or, single_apply] at hx
  by_cases h1 : x = gA l t
  · exact Or.inl h1
  · by_cases h2 : x = gB l (2 + t)
    · exact Or.inr (Or.inl h2)
    · by_cases h3 : x = out t
      · exact Or.inr (Or.inr h3)
      · simp [h1, h2, h3] at hx

theorem own_ge {t : Nat} (ht : ¬ t < 2) : own t = Heap.empty := by
  simp only [own, ite_eq_right ht]

theorem away_none {hmm hblk : Heap} (haw : AllocAway hmm hblk) {x : Nat}
    (hx : gbase ≤ x ∨ x = l ∨ x = l + 4 ∨ x = out 0 ∨ x = out 1) :
    hmm x = none ∧ hblk x = none := by
  have key : ¬ ((hmm x).isSome ∨ (hblk x).isSome) := fun h => by
    have := haw.2 x h; omega
  constructor
  · cases e : hmm x with
    | none => rfl
    | some v => exact absurd (Or.inl (by simp [e])) key
  · cases e : hblk x with
    | none => rfl
    | some v => exact absurd (Or.inr (by simp [e])) key

theorem own_ownI {hmm hblk : Heap} (haw : AllocAway hmm hblk) (t : Nat) :
    Heap.Disjoint (own t) (ownI hmm hblk) := by
  by_cases ht : t < 2
  · refine disj_of fun x hx => ?_
    have hl := l_lt
    have hot := out_lt ht
    rcases own_cells ht hx with rfl | rfl | rfl
    · obtain ⟨n1, n2⟩ := away_none haw (Or.inl (gA_ge l t))
      have := ledger_gA (l := l) (k := t) [0, 1] hl (by have := M_ge; omega)
      simp only [ownI, union_or, this, single_ne (gA_ne_lt hl), single_ne (gA_ne_lt l4_lt), n1, n2]
      have : t ∈ [0, 1] := by simp; omega
      simp [this]
    · obtain ⟨n1, n2⟩ := away_none haw (Or.inl (gB_ge l (2 + t)))
      have := ledger_gB (l := l) (k := 2 + t) [0, 1] hl (by have := M_ge; omega)
      simp only [ownI, union_or, this, single_ne (gB_ne_lt hl), single_ne (gB_ne_lt l4_lt), n1, n2]
      have : 2 + t ∉ [0, 1] := by simp; omega
      simp [this]
    · obtain ⟨n1, n2⟩ := away_none haw (x := out t) (by
        rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl <;> simp)
      simp [ownI, union_or, ledger_lt _ hot, single_ne out_ne_l, single_ne out_ne_l4, n1, n2]
  · rw [own_ge ht]; exact disjoint_empty _

theorem own_own {t u : Nat} (htu : t ≠ u) : Heap.Disjoint (own t) (own u) := by
  by_cases ht : t < 2
  · by_cases hu : u < 2
    · refine disj_of fun x hx => ?_
      have hl := l_lt
      have nA : ∀ k, gA l k ≠ out u := fun _ => gA_ne_lt (out_lt hu)
      have nB : ∀ k, gB l k ≠ out u := fun _ => gB_ne_lt (out_lt hu)
      simp only [own, ite_eq_left hu, union_or]
      rcases own_cells ht hx with rfl | rfl | rfl
      · rw [single_ne (fun e => htu (gA_inj hl e)), single_ne (gA_ne_gB l t _ hl), single_ne (nA t)]
        rfl
      · rw [single_ne (Ne.symm (gA_ne_gB l u _ hl)), single_ne (fun e => by
          have := gB_inj hl e; omega), single_ne (nB _)]
        rfl
      · rw [single_ne (Ne.symm (gA_ne_lt (out_lt ht))), single_ne (Ne.symm (gB_ne_lt (out_lt ht))),
          single_ne (by unfold out; omega)]
        rfl
    · rw [own_ge hu]; exact disjoint_empty_right _
  · rw [own_ge ht]; exact disjoint_empty _

theorem le_trans' {a b c : Heap} (h1 : Heap.Le a b) (h2 : Heap.Le b c) : Heap.Le a c :=
  fun x v h => h2 x v (h1 x v h)

theorem le_empty (h : Heap) : Heap.Le Heap.empty h := fun _ _ e => by cases e

theorem ownI_inv {A : Alloc} {hmm hblk : Heap} (haw : AllocAway hmm hblk) (hm : A.mm hmm)
    (hb : A.blk l hblk) : inv A (ownI hmm hblk) := by
  have hl := l_lt
  -- the object's part is away from the allocator's invariant heap
  have dR4 : Heap.Disjoint (Heap.single (l + 4) 42) hblk :=
    disj_of fun x hx => by
      have : x = l + 4 := by by_contra hne; simp [single_apply, hne] at hx
      subst this; exact (away_none haw (x := l + 4) (Or.inr (Or.inr (Or.inl rfl)))).2
  have dRl : Heap.Disjoint (Heap.single l 2) (Heap.union (Heap.single (l + 4) 42) hblk) :=
    disj_of fun x hx => by
      have : x = l := by by_contra hne; simp [single_apply, hne] at hx
      subst this
      simp [union_or, single_ne l_ne_l4, (away_none haw (x := l) (Or.inr (Or.inl rfl))).2]
  have dLR : Heap.Disjoint (ledger l [0, 1])
      (Heap.union (Heap.single l 2) (Heap.union (Heap.single (l + 4) 42) hblk)) := by
    refine disj_of fun x hx => ?_
    have hx' : gbase ≤ x := by
      by_contra h; rw [ledger_lt _ (by omega)] at hx; simp at hx
    have := l4_lt
    simp [union_or, single_ne (show x ≠ l by omega), single_ne (show x ≠ l + 4 by omega),
      (away_none haw (Or.inl hx')).2]
  have dI : Heap.Disjoint (Heap.union (ledger l [0, 1])
      (Heap.union (Heap.single l 2) (Heap.union (Heap.single (l + 4) 42) hblk))) hmm := by
    refine disj_of fun x hx => ?_
    rcases union_isSome.mp hx with h1 | h1
    · have : gbase ≤ x := by
        by_contra h; rw [ledger_lt _ (by omega)] at h1; simp at h1
      exact (away_none haw (Or.inl this)).1
    · rcases union_isSome.mp h1 with h2 | h2
      · have : x = l := by by_contra hne; simp [single_apply, hne] at h2
        exact (away_none haw (Or.inr (Or.inl this))).1
      · rcases union_isSome.mp h2 with h3 | h3
        · have : x = l + 4 := by by_contra hne; simp [single_apply, hne] at h3
          exact (away_none haw (Or.inr (Or.inr (Or.inl this)))).1
        · exact none_of_disjoint (disjoint_symm haw.1) h3
  refine sep_iff.mpr ⟨_, hmm, dI, rfl, ⟨[0, 1], by decide, fun k hk => ?_, Or.inr ⟨by simp,
    sep_iff.mpr ⟨_, _, dLR, rfl, rfl, sep_iff.mpr ⟨_, _, dRl, rfl, rfl,
      sep_iff.mpr ⟨_, _, dR4, rfl, rfl, hb⟩⟩⟩⟩⟩, hm⟩
  have := M_ge; simp at hk; omega

/-- **The CSL certificate of `Drop2`**, for every allocator. -/
theorem drop2_certified (A : Alloc) {hmm hblk : Heap} (haw : AllocAway hmm hblk)
    (hm : A.mm hmm) (hb : A.blk l hblk) :
    GInv (inv A) post 2 (start A hmm hblk) own (ownI hmm hblk) := by
  have d01 : Heap.Disjoint (own 0) (own 1) := own_own (by decide)
  have dI : Heap.Disjoint (ownI hmm hblk) (Heap.union (own 0) (own 1)) :=
    disjoint_symm (disjoint_union_left.mpr ⟨own_ownI haw 0, own_ownI haw 1⟩)
  refine ⟨fun t u h => own_own h, own_ownI haw, fun t => ?_, le_union_left, ownI_inv haw hm hb,
    fun t ht => ?_⟩
  · by_cases ht : t < 2
    · have : t = 0 ∨ t = 1 := by omega
      rcases this with rfl | rfl
      · exact le_trans' le_union_left (le_union_right dI)
      · exact le_trans' (le_union_right d01) (le_union_right dI)
    · rw [own_ge ht]; exact le_empty _
  · simp only [start, ite_eq_left ht]
    exact body_safe A ht

/-- The postcondition pins the output cell. -/
theorem post_out {t : Nat} (ht : t < 2) {rs : Regs} {h : Heap} (H : post t rs h) :
    h (out t) = some 42 := by
  obtain ⟨b1, r, -, rfl, ⟨-, rfl⟩, H2⟩ := sep_iff.mp H
  obtain ⟨b2, o, -, rfl, ⟨-, rfl⟩, rfl⟩ := sep_iff.mp H2
  have hot := out_lt ht
  simp [union_or, single_ne (gB_ne_lt hot).symm, single_self]

/-! ## A trivial allocator (non-vacuity of the hypotheses) -/

/-- `free` by `mfence`: the block is handed to an allocator whose invariant is `True`. -/
theorem leak_free_spec (J : HProp) (rs : Regs) (h : Heap) :
    Csl.Safe ((fun _ => True) ∗ J) (fun _ => hemp) (.fence .mfence) rs h := by
  refine safe_atomic (by intro e; cases e) (fun s' rs' st => by cases st) ?_
  intro lab s' rs' st
  cases st
  refine ⟨rfl, rfl, (fun e => by cases e), fun _ hI hIi hd => ?_⟩
  refine ⟨fun x hx => by simp [Lab.Touches, Lab.reads, Lab.wval] at hx, (fun e => by cases e),
    fun _ => ?_⟩
  obtain ⟨hT, hJ, dTJ, rfl, -, hj⟩ := sep_iff.mp hIi
  obtain ⟨dhT, dhJ⟩ := disjoint_union_right.mp hd
  refine ⟨Heap.empty, Heap.union h (Heap.union hT hJ), disjoint_empty _, ?_,
    sep_iff.mpr ⟨Heap.union h hT, hJ, disjoint_union_left.mpr ⟨dhJ, dTJ⟩, (union_assoc _ _ _).symm,
      trivial, hj⟩, rfl, fun e => by cases e⟩
  rw [union_empty_left]; funext x; simp [Lab.updH, Lab.wval]

end Silmaril.Proofs.X86.Concurrency.Cir.Rc

namespace Silmaril.X86.Concurrency.Cir.Rc

/-- **The leaking allocator**: invariant `True`, no block token, `free` is an `mfence` that
gives the block to the allocator. A non-vacuity instance of `Alloc`. -/
def leakAlloc : Alloc where
  mm := fun _ => True
  blk := fun _ => Csl.hemp
  freeCode := .fence .mfence
  free_spec _ J rs h _ _ := Silmaril.Proofs.X86.Concurrency.Cir.Rc.leak_free_spec J rs h

end Silmaril.X86.Concurrency.Cir.Rc
