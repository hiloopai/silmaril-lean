module

public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Rel
public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Client

/-!
# Proofs: `Even` is proved against the interface with release stores

`even_provedR : Even.client.ProvedR Even.goal`: for every `M : IfaceR` with an object of at most
8 bytes and every loop bound, the linked start has a `GInvR` certificate whose postconditions give
both outputs even. The proof `even_proved` is in `SafeR`: lock (`lock_spec`, framed with
the output cell), the critical section (its proof, lifted), unlock (`unlock_spec`, framed).
So `Task.movUnlock` (proved) applies to `Even` for every loop bound, not only at the explored
bound 2 (`movUnlock_even`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Rel
open Silmaril.X86.Concurrency.Cir.Mutex
open Silmaril.X86.Concurrency.Cir.Mutex.Even

/-- The invariant of the client at `M`. -/
def evInvR (M : IfaceR) : HProp := M.inv m R ∗ hemp

/-- Thread `t` ends owning its output cell, with an even value, and no ghost. -/
def evPostR (t : Nat) : Bool → Regs → Heap → Heap → Prop :=
  fun _ _ h g => (∃ v, v % 2 = 0 ∧ h = Heap.single (out t) v) ∧ g = Heap.empty

/-- **The critical section**, from `x ↦ v` (even), the token and `out t ↦ 0`, to
`x ↦ w`, the token and `out t ↦ w` with `w` even. -/
theorem safe_cs0 {I0 : HProp} {t : Nat} (ht : t < 2) {rs : Regs} {htok : Heap} {v : Nat}
    (hv : v % 2 = 0) (ho : htok (out t) = none) :
    Csl.Safe I0 (fun _ h => ∃ w, w % 2 = 0 ∧ h = shape htok (out t) w w) (cs t) rs
      (shape htok (out t) v 0) := by
  have hxo := x_ne_out t
  have hout : out t < 2 ^ 64 := by simp [out]; omega
  apply safe_seq
  refine load_at (lit_toNat x (by decide) rs) (shape_x) ?_
  apply safe_seq
  refine store_at (val := 1) (lit_toNat x (by decide) _) (by simp [Expr.eval])
    (by rw [shape_x]; rfl)
    (shape_wx) ?_
  apply safe_seq
  refine store_at (lit_toNat (out t) hout _) rfl (by rw [shape_o ho hxo]; rfl)
    (shape_wo ho hxo) ?_
  apply safe_seq
  refine store_at (lit_toNat x (by decide) _) rfl (by rw [shape_x]; rfl)
    (shape_wx) ?_
  apply safe_skip
  refine ⟨_, ?_, rfl⟩
  simp [Regs.set, Expr.eval]
  omega

/-- **One thread is `SafeR`**, for every mutex meeting `IfaceR`. -/
theorem thread_safeR (M : IfaceR) (L : Nat) {t : Nat} (ht : t < 2) :
    SafeR (liftI (evInvR M)) (evPostR t) false (body (M.lock L) (M.unlock L) t) Regs.zero
      (Heap.single (out t) 0) Heap.empty := by
  have hxo := x_ne_out t
  apply safeR_seq
  apply safeR_seq
  apply safeR_assign
  have H := safeR_frame (M.lock_spec m R hemp L _ false (rdi_m Regs.zero))
    (disjoint_empty (Heap.single (out t) 0))
  rw [union_empty_left] at H
  refine safeR_conseq (fun p rs h g hp => ?_) H
  obtain ⟨h12, ⟨rfl, hRL, rfl⟩, d, rfl⟩ := hp
  obtain ⟨h₁, htok, d12, rfl, ⟨v, hv, rfl⟩, htk⟩ := sep_iff.mp hRL
  have hx : htok x = none := by
    rcases d12 x with e | e
    · simp [single_apply] at e
    · exact e
  have ho : htok (out t) = none := by
    rcases d (out t) with e | e
    · exact (union_eq_none.mp e).2
    · simp [single_apply] at e
  apply safeR_seq
  have C := safeR_lift (I := liftI (evInvR M)) (g := Heap.empty) liftI_split
    (safe_cs0 (I0 := evInvR M) ht hv ho (rs := rs))
  refine safeR_conseq (fun p rs' h g hp => ?_) C
  obtain ⟨rfl, ⟨w, hw, rfl⟩, rfl⟩ := hp
  apply safeR_seq
  apply safeR_assign
  have U := safeR_frame (M.unlock_spec m R hemp L _ false (Heap.union (Heap.single x w) htok)
    (rdi_m rs') (sep_iff.mpr ⟨_, htok, disjoint_single_left hx, rfl, ⟨w, hw, rfl⟩, htk⟩))
    (shape_disj (a := w) (b := w) ho hxo)
  refine safeR_conseq (fun p rs'' h g hp => ?_) U
  obtain ⟨h1, ⟨rfl, rfl⟩, -, rfl⟩ := hp
  exact ⟨⟨w, hw, union_empty_left _⟩, rfl⟩

theorem initR_far (M : IfaceR) (hM : M.size ≤ 8) {a : Nat} (ha : a < m ∨ m + 8 ≤ a) :
    M.init m a = none := by
  cases e : M.init m a with
  | none => rfl
  | some w =>
    have := M.init_dom m a (by simp [e])
    omega

/-- The invariant's start: the unlocked mutex and `x ↦ 0`. -/
def evHIR (M : IfaceR) : Heap := Heap.union (M.init m) (Heap.single x 0)

theorem evHIR_out (M : IfaceR) (hM : M.size ≤ 8) (t : Nat) : evHIR M (out t) = none := by
  rw [evHIR, union_none (initR_far M hM (Or.inr (out_far t)))]
  simp [single_apply, Ne.symm (x_ne_out t)]

theorem ginvR (M : IfaceR) (hM : M.size ≤ 8) (L : Nat) :
    GInvR (liftI (evInvR M)) (fun t => evPostR t) 2 (client.linkR M L) evOwn
      (fun _ => Heap.empty) (evHIR M) Heap.empty := by
  have hmem : (client.linkR M L).mem =
      Heap.union Even.mem (Heap.union (M.init m) Heap.empty) := rfl
  refine ⟨?_, ?_, fun _ _ _ => disjoint_empty _, fun _ => disjoint_empty _, ?_, ?_, ?_, ?_⟩
  · intro t u htu
    unfold evOwn
    split
    · split
      · exact disjoint_single (by simp [out]; omega)
      · exact disjoint_empty_right _
    · exact disjoint_empty _
  · intro t
    unfold evOwn
    split
    · exact disjoint_single_left (evHIR_out M hM t)
    · exact disjoint_empty _
  · intro t a v hv
    unfold evOwn at hv
    split at hv
    · rename_i ht
      simp only [single_apply] at hv
      split at hv
      · rename_i e
        subst e
        cases hv
        rw [hmem]
        apply union_some
        rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl <;> simp [Even.mem]
      · cases hv
    · simp [Heap.empty] at hv
  · intro a v hv
    rw [hmem]
    simp only [evHIR] at hv
    cases e : M.init m a with
    | some w =>
      rw [union_some e] at hv
      cases hv
      have := M.init_dom m a (by simp [e])
      have hn : Even.mem a = none := by
        have hne : ¬ (a = x ∨ a = out 0 ∨ a = out 1) := by
          simp only [x, out, m] at this ⊢; omega
        simp only [Even.mem, hne, ite_false]
      rw [union_none hn, union_some e]
    | none =>
      rw [union_none e] at hv
      simp only [single_apply] at hv
      split at hv
      · rename_i ex
        subst ex
        cases hv
        exact union_some (by simp [Even.mem])
      · cases hv
  · refine sep_emp (M.init_inv m R _ ⟨0, rfl, rfl⟩ ?_)
    intro a
    by_cases ha : a = x
    · subst ha; exact Or.inl (initR_far M hM (Or.inr (by simp [m, x])))
    · exact Or.inr (by simp [single_apply, ha])
  · intro t ht
    have : (client.linkR M L).ts t = (body (M.lock L) (M.unlock L) t, Regs.zero) := by
      simp [Client.linkR, Client.startWith, client, ht]
    rw [this]
    have : evOwn t = Heap.single (out t) 0 := by simp [evOwn, ht]
    rw [this]
    exact thread_safeR M L ht

/-- **`Even` is proved against the interface with release stores.** -/
theorem even_provedR : client.ProvedR goal := by
  intro M hM L
  refine ⟨liftI (evInvR M), fun t => evPostR t, evOwn, fun _ => Heap.empty, evHIR M, Heap.empty,
    ginvR M hM L, ?_⟩
  intro rs mem hs' gs' hI' gI' ps hq _ hle _ t ht
  obtain ⟨⟨v, hv, e⟩, -⟩ := hq t ht
  exact ⟨v, hle t (out t) v (by rw [e]; simp [single_apply]), hv⟩

end Silmaril.Proofs.X86.Concurrency.Cir.Mutex
