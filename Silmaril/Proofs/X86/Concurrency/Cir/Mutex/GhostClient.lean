module

public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Ghost
public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.RelClient

/-!
# Proofs: `Even` is proved against the interface with ghost state

`even_provedG : Even.client.ProvedG Even.goal`: for every `M : IfaceG` with an object of at most
8 bytes that supports two threads, and every loop bound, the linked start has a `GInvR`
certificate whose postconditions give both outputs even. The proof is `even_provedR` with
ghost state: thread `t` starts with `M.gthr m t` (ready), the lock's token may carry ghost cells,
the critical section is the base-CSL proof of the spin mutex lifted, and the unlock gives back a
ready ghost heap.
So `ProvedG` is not vacuous, and `Task.ticketIface` applies to `Even` (`Futex.even_ticket`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Rel
open Silmaril.X86.Concurrency.Cir.Mutex
open Silmaril.X86.Concurrency.Cir.Mutex.Even

/-- The empty `GProp`. -/
def gemp : GProp := fun h g => h = Heap.empty ∧ g = Heap.empty

/-- The invariant of the client at `M`. -/
def evInvG (M : IfaceG) : GProp := gsep (M.inv m R) gemp

/-- Thread `t` ends owning its output cell, with an even value, and a ready ghost heap. -/
def evPostG (M : IfaceG) (t : Nat) : Bool → Regs → Heap → Heap → Prop :=
  fun _ _ h g => (∃ v, v % 2 = 0 ∧ h = Heap.single (out t) v) ∧ M.ready m g

/-- **One thread is `SafeR`**, for every mutex meeting `IfaceG`. -/
theorem thread_safeG (M : IfaceG) (hM : M.size ≤ 8) (hN : M.thrOk 2) (L : Nat) {t : Nat}
    (ht : t < 2) :
    SafeR (evInvG M) (evPostG M t) false (body (M.lock L) (M.unlock L) t) Regs.zero
      (Heap.single (out t) 0) (M.gthr m t) := by
  have hxo := x_ne_out t
  have hsz : m + M.size ≤ 2 ^ 64 := by simp only [m]; omega
  apply safeR_seq
  apply safeR_seq
  apply safeR_assign
  have H := safeR_frame (M.lock_spec m R gemp L _ false (M.gthr m t) (rdi_m Regs.zero) hsz
    (M.ready_thr m 2 t hN ht)) (disjoint_empty (Heap.single (out t) 0))
  rw [union_empty_left] at H
  refine safeR_conseq (fun p rs h g hp => ?_) H
  obtain ⟨h12, ⟨rfl, hRL⟩, d, rfl⟩ := hp
  obtain ⟨h₁, htok, g₁, gtok, d12, rfl, -, rfl, ⟨⟨v, hv, rfl⟩, rfl⟩, htk⟩ := hRL
  have hx : htok x = none := by
    rcases d12 x with e | e
    · simp [single_apply] at e
    · exact e
  have ho : htok (out t) = none := by
    rcases d (out t) with e | e
    · exact (union_eq_none.mp e).2
    · simp [single_apply] at e
  apply safeR_seq
  have C := safeR_lift (I := evInvG M) (I0 := fun h => h = Heap.empty)
    (g := Heap.union Heap.empty gtok)
    (fun hI gI i => ⟨Heap.empty, hI, disjoint_empty _, (union_empty_left hI).symm, rfl,
      fun hA' e _ => by rw [e, union_empty_left]; exact i⟩)
    (safe_cs0 (I0 := fun h => h = Heap.empty) ht hv ho (rs := rs))
  refine safeR_conseq (fun p rs' h g hp => ?_) C
  obtain ⟨rfl, ⟨w, hw, rfl⟩, rfl⟩ := hp
  apply safeR_seq
  apply safeR_assign
  have U := safeR_frame (M.unlock_spec m R gemp L _ (Heap.union (Heap.single x w) htok)
    (Heap.union Heap.empty gtok) (rdi_m rs') hsz
    ⟨Heap.single x w, htok, Heap.empty, gtok, disjoint_single_left hx, rfl, disjoint_empty _, rfl,
      ⟨⟨w, hw, rfl⟩, rfl⟩, htk⟩)
    (shape_disj (a := w) (b := w) ho hxo)
  refine safeR_conseq (fun p rs'' h g hp => ?_) U
  obtain ⟨h1, ⟨rfl, hr⟩, -, rfl⟩ := hp
  exact ⟨⟨w, hw, union_empty_left _⟩, hr⟩

theorem initG_far (M : IfaceG) (hM : M.size ≤ 8) {a : Nat} (ha : a < m ∨ m + 8 ≤ a) :
    M.init m a = none := by
  cases e : M.init m a with
  | none => rfl
  | some w =>
    have := M.init_dom m a (by simp [e])
    omega

/-- The invariant's start: the unlocked mutex and `x ↦ 0`. -/
def evHIG (M : IfaceG) : Heap := Heap.union (M.init m) (Heap.single x 0)

theorem evHIG_out (M : IfaceG) (hM : M.size ≤ 8) (t : Nat) : evHIG M (out t) = none := by
  rw [evHIG, union_none (initG_far M hM (Or.inr (out_far t)))]
  simp [single_apply, Ne.symm (x_ne_out t)]

theorem ginvG (M : IfaceG) (hM : M.size ≤ 8) (hN : M.thrOk 2) (L : Nat) :
    GInvR (evInvG M) (fun t => evPostG M t) 2 (client.linkG M L) evOwn (M.gthr m)
      (evHIG M) (M.ginit m) := by
  have hmem : (client.linkG M L).mem =
      Heap.union Even.mem (Heap.union (M.init m) Heap.empty) := rfl
  refine ⟨?_, ?_, fun t u h => M.gthr_disj m t u h, fun t => disjoint_symm (M.ginit_disj m t),
    ?_, ?_, ?_, ?_⟩
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
    · exact disjoint_single_left (evHIG_out M hM t)
    · exact disjoint_empty _
  · intro t a v hv
    unfold evOwn at hv
    split at hv
    · simp only [single_apply] at hv
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
    simp only [evHIG] at hv
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
  · refine ⟨evHIG M, Heap.empty, M.ginit m, Heap.empty, disjoint_empty_right _,
      (union_empty_right _).symm, disjoint_empty_right _, (union_empty_right _).symm,
      M.init_inv m R _ ⟨0, rfl, rfl⟩ ?_, rfl, rfl⟩
    intro a
    by_cases ha : a = x
    · subst ha; exact Or.inl (initG_far M hM (Or.inr (by simp [m, x])))
    · exact Or.inr (by simp [single_apply, ha])
  · intro t ht
    have : (client.linkG M L).ts t = (body (M.lock L) (M.unlock L) t, Regs.zero) := by
      simp [Client.linkG, Client.startWith, client, ht]
    rw [this]
    have : evOwn t = Heap.single (out t) 0 := by simp [evOwn, ht]
    rw [this]
    exact thread_safeG M hM hN L ht

/-- **`Even` is proved against the interface with ghost state.** -/
theorem even_provedG : client.ProvedG goal := by
  intro M hM hN L
  refine ⟨evInvG M, fun t => evPostG M t, evOwn, M.gthr m, evHIG M, M.ginit m,
    ginvG M hM hN L, ?_⟩
  intro rs mem hs' gs' hI' gI' ps hq _ hle _ t ht
  obtain ⟨⟨v, hv, e⟩, -⟩ := hq t ht
  exact ⟨v, hle t (out t) v (by rw [e]; simp [single_apply]), hv⟩

end Silmaril.Proofs.X86.Concurrency.Cir.Mutex
