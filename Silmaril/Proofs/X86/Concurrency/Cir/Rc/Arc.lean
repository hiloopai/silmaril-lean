module

public import Silmaril.Proofs.X86.Concurrency.Cir.Rc.Spec
public import Silmaril.X86.Concurrency.Cir.Mutex.Thms

/-!
# Proofs: the Arc specification under every frame invariant

The rules of `Spec` are stated under the object's invariant alone. Here they are lifted to
`rcInv l P ∗ J` (the invariant frame rule `safe_inv_frame`, through the `Mutex.Thms` header),
and `rc_drop` is given its RustBelt-style rule: the cold path runs on the last reference with
full ownership of the count and the payload, the fast path ends with the slot's blank.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Rc

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Rc
open Silmaril.X86.Concurrency.Cir.Mutex (safe_inv_frame safe_inv_eq)

theorem last_key {old : Nat} (hlt : old < 2 ^ 32) :
    (BitVec.ofNat 64 old - 1#64) &&& 0xffffffff#64 = 0#64 ↔ old = 1 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_and]
  have e : (0xffffffff#64).toNat = 2 ^ 32 - 1 := by decide
  rw [e, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

/-- The old count was `1` exactly when `isLast` holds. -/
theorem isLast_iff {rs : Regs} {d : Reg} {old : Nat} (hd : rs d = BitVec.ofNat 64 old)
    (hlt : old < 2 ^ 32) : truthy ((isLast d).eval rs) = true ↔ old = 1 := by
  have key := last_key hlt
  simp only [isLast, zfOf, Expr.eval, BinOp.eval, hd, truthy]
  by_cases e : (BitVec.ofNat 64 old - 1#64) &&& 0xffffffff#64 = 0#64
  · have := key.mp e
    simp only [BitVec.ofNat_eq_ofNat] at e ⊢
    simp [this]
  · have : old ≠ 1 := fun h => e (key.mpr h)
    simp only [BitVec.ofNat_eq_ofNat] at e ⊢
    simp [e, this]

/-- **Clone** under any frame invariant: `{tok l j ∗ blank l k} rc_inc {tok l j ∗ tok l k}`. -/
theorem rc_inc_spec {P J : HProp} {l j k : Nat} {d : Reg} {a : Expr} {rs : Regs} {h : Heap}
    (ha : (a.eval rs).toNat = l) (hh : (tok l j ∗ blank l k) h) :
    Csl.Safe (rcInv l P ∗ J) (fun _ => tok l j ∗ tok l k) (rcInc d a) rs h :=
  safe_inv_frame (rc_inc_tok ha hh)

/-- **Drop** under any frame invariant, with the cold path `slow`: from the token of slot `k`
and a frame `T`, the cold path runs (old count `1`) on the slot's blank, the frame, the count
cell `l ↦ 0` and the payload; otherwise the drop ends on the blank and the frame. -/
theorem rc_drop_spec {P J : HProp} {Q : Regs → HProp} {l k : Nat} {d : Reg} {a : Expr}
    {slow : Stmt} {rs : Regs} {T : Heap} (ha : (a.eval rs).toNat = l) (hk : k < M)
    (dT : Heap.Disjoint T (Heap.single (gA l k) 0))
    (hslow : ∀ rs' hP, rs' d = 1 → P hP → (∀ j < M, j ≠ k → T (gA l j) = none) →
      Heap.Disjoint (Heap.union T (Heap.single (gB l k) 0)) (Heap.union (Heap.single l 0) hP) →
      Heap.Disjoint (Heap.single l 0) hP →
      Csl.Safe (rcInv l P ∗ J) Q slow rs'
        (Heap.union (Heap.union T (Heap.single (gB l k) 0)) (Heap.union (Heap.single l 0) hP)))
    (hfast : ∀ rs', Q rs' (Heap.union T (Heap.single (gB l k) 0))) :
    Csl.Safe (rcInv l P ∗ J) Q (rcDrop d a slow) rs (Heap.union T (Heap.single (gA l k) 0)) := by
  refine safe_seq (safe_conseq ?_ (safe_inv_frame (J := J) (rc_dec_gen (P := P) (d := d) ha hk dT)))
  rintro rs' h' ⟨old, hlt, hd, (⟨rfl, hno, hP, hp, d1, d2, rfl⟩ | ⟨hne, rfl⟩)⟩
  · refine safe_ite (fun _ => hslow rs' hP (by simp [hd]) hp hno d1 d2) (fun hf => ?_)
    exact absurd ((isLast_iff hd hlt).mpr rfl) (by simp [hf])
  · refine safe_ite (fun ht => absurd ((isLast_iff hd hlt).mp ht) hne) (fun _ => ?_)
    exact safe_skip (hfast rs')

/-- **A drop that is never the last**: while the thread keeps the token of another slot `j`,
the cold path does not run. -/
theorem rc_drop_keep {P J : HProp} {Q : Regs → HProp} {l j k : Nat} {d : Reg} {a : Expr}
    {slow : Stmt} {rs : Regs} {T : Heap} (ha : (a.eval rs).toNat = l) (hk : k < M) (hj : j < M)
    (hjk : j ≠ k) (hTj : T (gA l j) = some 0) (dT : Heap.Disjoint T (Heap.single (gA l k) 0))
    (hfast : ∀ rs', Q rs' (Heap.union T (Heap.single (gB l k) 0))) :
    Csl.Safe (rcInv l P ∗ J) Q (rcDrop d a slow) rs (Heap.union T (Heap.single (gA l k) 0)) :=
  rc_drop_spec ha hk dT (fun _ _ _ _ hno _ _ => by simp [hno j hj hjk] at hTj) hfast

/-- **Read through a token** under any frame invariant. -/
theorem rc_load_spec {P J : HProp} {Q : Regs → HProp} {l k c v0 : Nat} {d : Reg} {m : Mode}
    {sz : Nat} {fl : Flav} {a : Expr} {rs : Regs} {h : Heap} (hm : m ≠ .na)
    (hc : (a.eval rs).toNat = c) (hl : l < gbase) (hk : k < M) (hT : (h (gA l k)).isSome)
    (hPc : ∀ hP, P hP → hP c = some v0) (hq : Q (rs.set d (BitVec.ofNat 64 v0)) h) :
    Csl.Safe (rcInv l P ∗ J) Q (.load d m sz fl a) rs h :=
  safe_inv_frame (rc_load_tok hm hc hl hk hT hPc hq)

/-! ## Counting laws -/

/-- Tokens are exclusive: one slot's token cannot be held twice. -/
theorem tok_excl (l k : Nat) (h : Heap) : ¬ (tok l k ∗ tok l k) h := by
  intro H
  obtain ⟨h₁, h₂, d, -, ⟨-, rfl⟩, ⟨-, rfl⟩⟩ := sep_iff.mp H
  exact disjoint_some d (a := gA l k) (by simp [single_self]) (by simp [single_self])

/-- **A token keeps the object alive**: next to a token, the invariant holds a positive count
(at least the number of slots in use, which includes the token's) and the payload. -/
theorem tok_live {P : HProp} {l : Nat} {h : Heap} (hl : l < gbase) (H : (rcInv l P ∗ Tok l) h) :
    ∃ c, 1 ≤ c ∧ h l = some c := by
  obtain ⟨hI, hT, d, rfl, hi, ⟨k, hk, rfl⟩⟩ := sep_iff.mp H
  obtain ⟨S, hP, -, -, hkS, -, -, -, rfl⟩ :=
    live_of_tok hl hk (hT := Heap.single (gA l k) 0) (by simp [single_self]) (disjoint_symm d) hi
  exact ⟨S.length, List.length_pos_of_mem hkS, by simp [union_or, ledger_lt _ hl, single_self]⟩

/-- **The last reference is unique**: two tokens of different slots next to the invariant
mean the count is at least `2`, so a drop of either is not the last. -/
theorem two_toks {P : HProp} {l j k : Nat} {h : Heap} (hl : l < gbase) (hjk : j ≠ k)
    (H : (rcInv l P ∗ tok l j ∗ tok l k) h) : ∃ c, 2 ≤ c ∧ h l = some c := by
  obtain ⟨hI, hT, d, rfl, hi, H2⟩ := sep_iff.mp H
  obtain ⟨h1, h2, d12, rfl, ⟨hj, rfl⟩, ⟨hk, rfl⟩⟩ := sep_iff.mp H2
  obtain ⟨S, hP, hn, -, hjS, -, -, -, rfl⟩ :=
    live_of_tok hl hj (hT := Heap.union (Heap.single (gA l j) 0) (Heap.single (gA l k) 0))
      (by simp [union_or, single_self]) (disjoint_symm d) hi
  have hkS : k ∈ S := by
    by_contra hkS
    have := (union_eq_none.mp (none_of_disjoint (disjoint_symm d)
      (show (Heap.union (Heap.single (gA l j) 0) (Heap.single (gA l k) 0) (gA l k)).isSome by
        simp [union_or, single_self]))).1
    rw [ledger_gA _ hl hk] at this; simp [hkS] at this
  refine ⟨S.length, ?_, by simp [union_or, ledger_lt _ hl, single_self]⟩
  have : [j, k].Subperm S :=
    (List.nodup_cons.mpr ⟨by simpa using hjk, List.nodup_singleton k⟩).subperm
    (fun x hx => by simp at hx; rcases hx with rfl | rfl; exacts [hjS, hkS])
  simpa using this.length_le

end Silmaril.Proofs.X86.Concurrency.Cir.Rc
