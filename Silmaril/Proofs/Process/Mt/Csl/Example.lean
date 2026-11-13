module

public import Silmaril.Process.Mt.Csl.Example.Defs

/-!
# The mutex-protected counter is safe (proofs)

`safeF_own`: `own` is a post-fixed point of the safety functional, so a thread at pc 0 owning
nothing is safe (`safe_start`); the start satisfies the compatibility conditions
(`ginv_start`).
-/

@[expose] public section

namespace Silmaril.Proofs.Process.Mt.Csl.Example

open Silmaril.Process.Mt.Csl
open Silmaril.Process.Mt.Csl.Example

theorem agrees_iff {h : Heap Nat Nat} {m : Nat → Nat} :
    store.Agrees h m ↔ ∀ a v, h a = some v → m a = v := by
  simp [Store.Agrees, store]

theorem union_empty (h : Heap Nat Nat) : Heap.union Heap.empty h = h := by
  funext a; simp [Heap.union, Heap.empty]

theorem safeF_own {t s : Nat} {h : Heap Nat Nat} (ho : own t s h) :
    SafeF thr inv post own t s h := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- finished
    intro hd
    change s = 3 at hd
    subst hd
    rcases ho with ⟨-, rfl⟩ | ⟨hs, -⟩
    · rfl
    · omega
  · -- the plain step
    intro m _
    refine ⟨fun f => f, ?_, ?_⟩
    · rintro a ⟨rfl, rfl⟩
      rcases ho with ⟨hs, -⟩ | ⟨-, v, rfl⟩
      · omega
      · simp [counter]
    · rintro s' m' ⟨rfl, rfl, rfl⟩
      rcases ho with ⟨hs, -⟩ | ⟨-, v, rfl⟩
      · omega
      refine ⟨?_, Or.inr ⟨Or.inr rfl, m ctr + 1, ?_⟩⟩
      · intro a ha
        have : a ≠ ctr := by intro e; subst e; simp [counter] at ha
        simp [store, wr, this]
      · funext a
        by_cases e : a = ctr
        · subst e; simp [Store.cut, counter, store, wr]
        · simp [Store.cut, counter, e]
  · -- the atomic steps
    intro hI hIp dj m ag
    rw [agrees_iff] at ag
    refine ⟨?_, ?_⟩
    · rintro ⟨rfl, hne⟩
      rcases ho with ⟨hs, -⟩ | ⟨-, v, rfl⟩
      · omega
      rcases hIp with ⟨w, rfl⟩ | rfl
      · rcases dj ctr with e | e <;> simp [counter, unlocked, ctr, lk] at e
      · exact hne (ag lk 1 (by simp [Heap.union, counter, locked, ctr, lk]))
    · rintro s' m' (⟨rfl, h0, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
      · -- lock: the counter moves to the thread
        have hh : h = Heap.empty := by
          rcases ho with ⟨-, e⟩ | ⟨hs, -⟩
          · exact e
          · omega
        subst hh
        rw [union_empty] at ag ⊢
        obtain ⟨w, rfl⟩ : ∃ w, hI = unlocked w := by
          rcases hIp with hu | rfl
          · exact hu
          · have := ag lk 1 (by simp [locked]); rw [h0] at this; cases this
        have hw : m ctr = w := ag ctr w (by simp [unlocked, ctr, lk])
        refine ⟨?_, counter w, locked, ?_, ?_, ?_, Or.inr rfl, Or.inr ⟨Or.inl rfl, w, rfl⟩⟩
        · intro a ha
          have h1 : a ≠ lk := by intro e; subst e; simp [unlocked] at ha
          simp [store, wr, h1]
        · intro a
          by_cases e : a = ctr
          · subst e; right; simp [locked, ctr, lk]
          · left; simp [counter, e]
        · intro a ha
          by_cases e1 : a = lk
          · subst e1; simp [unlocked]
          · by_cases e2 : a = ctr
            · subst e2; simp [unlocked, ctr, lk]
            · simp [Heap.union, counter, locked, e1, e2] at ha
        · intro a x ha
          by_cases e2 : a = ctr
          · subst e2; simp [Heap.union, counter] at ha; subst ha
            simp [store, wr, ctr, lk]; exact hw
          · by_cases e1 : a = lk
            · subst e1; simp [Heap.union, counter, locked, ctr, lk] at ha; subst ha
              simp [store, wr]
            · simp [Heap.union, counter, locked, e1, e2] at ha
      · -- unlock: the counter moves back to the invariant
        rcases ho with ⟨hs, -⟩ | ⟨-, v, rfl⟩
        · omega
        rcases hIp with ⟨w, rfl⟩ | rfl
        · rcases dj ctr with e | e <;> simp [counter, unlocked, ctr, lk] at e
        have hv : m ctr = v := ag ctr v (by simp [Heap.union, counter])
        refine ⟨?_, Heap.empty, unlocked v, fun a => Or.inl rfl, ?_, ?_, Or.inl ⟨v, rfl⟩,
          Or.inl ⟨Or.inr rfl, rfl⟩⟩
        · intro a ha
          have h1 : a ≠ lk := by intro e; subst e; simp [Heap.union, counter, locked, ctr, lk] at ha
          simp [store, wr, h1]
        · intro a ha
          rw [union_empty] at ha
          by_cases e1 : a = lk
          · subst e1; simp [Heap.union, locked]
          · by_cases e2 : a = ctr
            · subst e2; simp [Heap.union, counter]
            · simp [unlocked, e1, e2] at ha
        · rw [union_empty]
          intro a x ha
          by_cases e1 : a = lk
          · subst e1; simp [unlocked] at ha; subst ha; simp [store, wr]
          · by_cases e2 : a = ctr
            · subst e2; simp [unlocked, ctr, lk] at ha; subst ha
              simp [store, wr, ctr, lk]; exact hv
            · simp [unlocked, e1, e2] at ha
  · -- no `clone`
    intro u hI _ _ m _
    exact ⟨fun f => f, fun _ _ f => f.elim⟩

theorem safe_start (t : Nat) : Safe thr inv post t (0 : Nat) Heap.empty :=
  ⟨own, Or.inl ⟨Or.inl rfl, rfl⟩, fun _ _ _ ho => safeF_own ho⟩

theorem ginv_start (n v : Nat) :
    GInv thr inv post (start n v) (fun _ => Heap.empty) (unlocked v) := by
  refine ⟨fun _ _ _ _ => Or.inl rfl, fun _ _ => Or.inl rfl, fun _ _ _ e => by simp [Heap.empty] at e, ?_,
    Or.inl ⟨v, rfl⟩, fun _ _ => rfl, ?_⟩
  · intro a x ha
    by_cases e1 : a = lk
    · subst e1; simp [unlocked] at ha; subst ha; simp [store, start, lk, ctr]
    · by_cases e2 : a = ctr
      · subst e2; simp [unlocked, ctr, lk] at ha; subst ha; simp [store, start]
      · simp [unlocked, e1, e2] at ha
  · intro t s e
    simp only [start] at e
    split at e
    · cases e; exact safe_start t
    · cases e

end Silmaril.Proofs.Process.Mt.Csl.Example
