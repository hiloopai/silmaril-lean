module

public import Silmaril.Libc.AllocSig.Defs

/-!
# The allocator signature hierarchy: reducts and non-vacuity

* `ops_mono`: `s ≤ s'` is inclusion of the functions; `le_full`, `mf_le`.
* `SafeWith.reduct`, `SafeOn.reduct`: **a contract at `s'` gives the contract at every
  `s ≤ s'`** (same invariant).
* `SafeOn.mono`: a stronger relation gives the weaker one (`Rel.Le`).
* `never_le_loose`, `bottom_safe`: **the bottom allocator is POSIX-safe at every level**
  (non-vacuity of the existential: some model meets the contract).
* `loose_malloc_success`, `loose_posixMemalign_success`: the success branches of `loose` are
  satisfiable (a contract that allowed only failure would be vacuous in the other direction).

Standard axioms only.
-/

@[expose] public section

namespace Silmaril.Libc.AllocSig

open Silmaril.Libc (Heap)

/-- A function is in exactly the levels above its own. -/
theorem mem_ops_iff (o : Op) (s : Sig) : o ∈ s.ops ↔ o.level ≤ s := by
  cases o <;> cases s <;> decide

/-- **The level order is inclusion of the functions.** -/
theorem ops_mono {s s' : Sig} (h : s ≤ s') {o : Op} (ho : o ∈ s.ops) : o ∈ s'.ops :=
  (mem_ops_iff o s').2 (Nat.le_trans ((mem_ops_iff o s).1 ho) h)

theorem mf_le (s : Sig) : Sig.mf ≤ s := by cases s <;> decide

theorem le_full (s : Sig) : s ≤ Sig.full := by cases s <;> decide

namespace Model

variable {A : Model}

/-- **Reduct along `s ≤ s'`**, with the same invariant. -/
theorem SafeWith.reduct {s s' : Sig} {T : Rel} {Inv : A.St → Prop} (hle : s ≤ s')
    (h : A.SafeWith s' T Inv) : A.SafeWith s T Inv where
  init := h.init
  empty := h.empty
  progress x c hi ho hv := h.progress x c hi (ops_mono hle ho) hv
  rel x c y r q hi ho hv hs := h.rel x c y r q hi (ops_mono hle ho) hv hs
  inv x c y r q hi ho hv hs := h.inv x c y r q hi (ops_mono hle ho) hv hs

/-- **Reduct along `s ≤ s'`.** -/
theorem SafeOn.reduct {s s' : Sig} {T : Rel} (hle : s ≤ s') (h : A.SafeOn s' T) : A.SafeOn s T :=
  let ⟨Inv, hI⟩ := h
  ⟨Inv, hI.reduct hle⟩

/-- **A stronger relation gives the weaker one.** -/
theorem SafeOn.mono {s : Sig} {R T : Rel} (hRT : R.Le T) (h : A.SafeOn s R) : A.SafeOn s T :=
  let ⟨Inv, hI⟩ := h
  ⟨Inv, { init := hI.init, empty := hI.empty, progress := hI.progress,
          rel := fun x c y r q hi ho hv hs => hRT _ _ _ _ _ (hI.rel x c y r q hi ho hv hs),
          inv := hI.inv }⟩

end Model

/-- **The bottom relation is POSIX-safe.** -/
theorem never_le_loose : Rel.Le never loose := by
  intro h c h' r q hn
  cases c with
  | malloc n => obtain ⟨hr, hq, hh⟩ := hn; exact ⟨by rw [hr, hq], .inl ⟨hq, hh⟩⟩
  | calloc k m => obtain ⟨hr, hq, hh⟩ := hn; exact ⟨by rw [hr, hq], .inl ⟨hq, hh⟩⟩
  | alignedAlloc al n => obtain ⟨hr, hq, hh⟩ := hn; exact ⟨by rw [hr, hq], .inl ⟨hq, hh⟩⟩
  | free p => exact hn
  | posixMemalign al n => obtain ⟨hr, hq, hh⟩ := hn; exact .inl ⟨by rw [hr]; decide, hq, hh⟩
  | usableSize p =>
    obtain ⟨hq, hh, hr⟩ := hn
    refine ⟨hq, hh, fun hp => by simp [hr, hp], fun n hp hs => ?_⟩
    simp [hr, hp, hs]
  | realloc p n =>
    obtain ⟨hr, hq, hh⟩ := hn
    refine ⟨by rw [hr, hq], ?_⟩
    by_cases hp : p = 0
    · simp only [hp, ite_true]
      exact .inl ⟨hq, by simpa [hp] using hh⟩
    · simp only [hp, ite_false]
      by_cases hn0 : n = 0
      · exact .inr (.inl ⟨hn0, hq, by simpa [hp, hn0] using hh⟩)
      · exact .inl ⟨hq, by simpa [hp, hn0] using hh⟩

theorem remove_empty (p : Nat) : Heap.empty.remove p = Heap.empty := by
  funext a; simp [Heap.remove, Heap.empty]

/-- **The bottom allocator is POSIX-safe at every level** (its heap stays empty). -/
theorem bottom_safe (s : Sig) : bottom.SafeOn s := by
  refine ⟨fun h => h = Heap.empty, ⟨rfl, rfl, ?_, ?_, ?_⟩⟩
  · intro x c _ _ _
    cases c with
    | malloc n => exact ⟨x, 0, 0, rfl, rfl, rfl⟩
    | calloc k m => exact ⟨x, 0, 0, rfl, rfl, rfl⟩
    | alignedAlloc al n => exact ⟨x, 0, 0, rfl, rfl, rfl⟩
    | free p => exact ⟨_, 0, 0, rfl, rfl⟩
    | realloc p n => exact ⟨_, 0, 0, rfl, rfl, rfl⟩
    | posixMemalign al n => exact ⟨x, 12, 0, rfl, rfl, rfl⟩
    | usableSize p => exact ⟨x, _, 0, rfl, rfl, rfl⟩
  · intro x c y r q _ _ _ hs
    exact never_le_loose _ _ _ _ _ hs
  · intro x c y r q hi _ _ hs
    subst hi
    change never Heap.empty c y r q at hs
    cases c with
    | malloc n => exact hs.2.2
    | calloc k m => exact hs.2.2
    | alignedAlloc al n => exact hs.2.2
    | posixMemalign al n => exact hs.2.2
    | usableSize p => exact hs.2.1
    | free p =>
      show y = Heap.empty
      rw [hs.2]; split
      · rfl
      · exact remove_empty p
    | realloc p n =>
      show y = Heap.empty
      rw [hs.2.2]; split
      · exact remove_empty p
      · rfl

/-- **`malloc` may succeed**: from the empty heap, a block at `16`. -/
theorem loose_malloc_success :
    loose Heap.empty (.malloc 1) (Heap.empty.add 16 1) 16 16 := by
  refine ⟨rfl, .inr ⟨⟨by decide, by decide, fun a m h => (by simp [Heap.empty] at h)⟩, rfl, rfl⟩⟩

/-- **`posix_memalign` may succeed**: from the empty heap, a block at `4096` aligned to `4096`. -/
theorem loose_posixMemalign_success :
    loose Heap.empty (.posixMemalign 4096 1) (Heap.empty.add 4096 1) 0 4096 := by
  exact .inr (.inr ⟨rfl, ⟨by decide, by decide, fun a m h => (by simp [Heap.empty] at h)⟩, rfl, rfl⟩)

end Silmaril.Libc.AllocSig
