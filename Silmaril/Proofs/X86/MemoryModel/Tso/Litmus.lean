module

public import Silmaril.X86.MemoryModel.Tso.Defs

/-!
# Byte-granular TSO: proofs

Proofs behind `Silmaril.X86.MemoryModel.Tso.Thms`: the generic invariant principle for
`Concurrent`, the SC embedding, `rmw` atomicity, and the SB / SB+mfence litmus tests.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Tso.Proofs

open Silmaril.X86.MemoryModel.Tso
open Silmaril.Memory (shuffles)

/-! ## Invariants over binary parallel compositions -/

section Invariant
variable {S L : Type} {step : S → L → S → Prop}

theorem exec_left (P : List L → List L → S → Prop)
    (hl : ∀ x xs ys s s', P (x :: xs) ys s → step s x s' → P xs ys s')
    (ys : List L) :
    ∀ (xs : List L) (s s' : S), Silmaril.Memory.Execution step s xs s' → P xs ys s → P [] ys s' := by
  intro xs
  induction xs with
  | nil => intro s s' h hp; cases h; exact hp
  | cons x xs ih =>
      intro s s' h hp
      cases h with
      | cons hs rest => exact ih _ _ rest (hl _ _ _ _ _ hp hs)

theorem exec_right (P : List L → List L → S → Prop)
    (hr : ∀ y xs ys s s', P xs (y :: ys) s → step s y s' → P xs ys s')
    (xs : List L) :
    ∀ (ys : List L) (s s' : S), Silmaril.Memory.Execution step s ys s' → P xs ys s → P xs [] s' := by
  intro ys
  induction ys with
  | nil => intro s s' h hp; cases h; exact hp
  | cons y ys ih =>
      intro s s' h hp
      cases h with
      | cons hs rest => exact ih _ _ rest (hr _ _ _ _ _ hp hs)

/-- A predicate on (remaining left program, remaining right program, state) that every step
of either thread preserves holds at the end of every concurrent execution. -/
theorem concurrent_invariant (P : List L → List L → S → Prop)
    (hl : ∀ x xs ys s s', P (x :: xs) ys s → step s x s' → P xs ys s')
    (hr : ∀ y xs ys s s', P xs (y :: ys) s → step s y s' → P xs ys s') :
    ∀ (xs ys trace : List L) (s s' : S), trace ∈ shuffles xs ys →
      Silmaril.Memory.Execution step s trace s' → P xs ys s → P [] [] s' := by
  intro xs
  induction xs with
  | nil =>
      intro ys trace s s' hm h hp
      simp only [shuffles, List.mem_singleton] at hm
      subst hm
      exact exec_right P hr [] _ _ _ h hp
  | cons x xs ihx =>
      intro ys
      induction ys with
      | nil =>
          intro trace s s' hm h hp
          simp only [shuffles, List.mem_singleton] at hm
          subst hm
          exact exec_left P hl [] _ _ _ h hp
      | cons y ys ihy =>
          intro trace s s' hm h hp
          simp only [shuffles, List.mem_append, List.mem_map] at hm
          rcases hm with ⟨tr, htr, rfl⟩ | ⟨tr, htr, rfl⟩
          · cases h with
            | cons hs rest => exact ihx _ _ _ _ htr rest (hl _ _ _ _ _ hp hs)
          · cases h with
            | cons hs rest => exact ihy _ _ _ htr rest (hr _ _ _ _ _ hp hs)

end Invariant

/-! ## SC embedding and `rmw` atomicity -/

section Embed
variable {Tid : Type} [DecidableEq Tid]

omit [DecidableEq Tid] in
theorem viewMem_xembed (m : Mem) (t : Tid) : viewMem (xembed m : XState Tid) t = m := by
  funext x; simp [viewMem, xembed, readBufByte]

omit [DecidableEq Tid] in
theorem readView_xembed (m : Mem) (t : Tid) (a n : Nat) :
    readView (xembed m : XState Tid) t a n = readMem m a n := by
  simp [readView, viewMem_xembed]

theorem flush_enqueue_xembed (m : Mem) (t : Tid) (a : Nat) (bs : List Byte) :
    XFlush (enqueue (xembed m) t a bs) (xembed (writeMem m a bs)) := by
  have f := XFlush.head (enqueue (xembed m : XState Tid) t a bs) t a bs []
    (by simp [enqueue, xembed])
  have e : (⟨writeMem (enqueue (xembed m : XState Tid) t a bs).memory a bs,
      Function.update (enqueue (xembed m : XState Tid) t a bs).buffer t []⟩ : XState Tid) =
      xembed (writeMem m a bs) := by
    simp only [enqueue, xembed, Function.update_idem, XState.mk.injEq, true_and]
    funext x
    by_cases hx : x = t
    · subst hx; simp
    · simp [Function.update_of_ne hx]
  rw [e] at f
  exact f

theorem of_sc_step {m m' : Mem} {e : XEvent Tid} (h : SCStep m e m') :
    XWeakStep (xembed m) e (xembed m') := by
  cases h with
  | load t a bs h =>
      exact ⟨_, _, .refl, .load _ t a bs (by rw [readView_xembed]; exact h), .refl⟩
  | store t a bs =>
      exact ⟨_, _, .refl, .store _ t a bs, .single (flush_enqueue_xembed m t a bs)⟩
  | rmw t a old new h len =>
      exact ⟨_, _, .refl, .rmw (xembed m) t a old new rfl h len, .refl⟩
  | fence t => exact ⟨_, _, .refl, .fence _ t rfl, .refl⟩

theorem of_sc_x {m m' : Mem} {es : List (XEvent Tid)}
    (h : Silmaril.Memory.Execution SCStep m es m') :
    Silmaril.Memory.Execution XWeakStep (xembed m) es (xembed m') :=
  h.map xembed (fun hs => of_sc_step hs)

theorem rmw_atomic {s s' : XState Tid} {t : Tid} {a : Nat} {old new : List Byte} :
    XStep s (.rmw t a old new) s' ↔
      s.buffer t = [] ∧ readMem s.memory a old.length = some old ∧
        new.length = old.length ∧ s' = { s with memory := writeMem s.memory a new } := by
  constructor
  · intro h; cases h with | rmw _ _ _ _ e r l => exact ⟨e, r, l, rfl⟩
  · rintro ⟨e, r, l, rfl⟩; exact .rmw s t a old new e r l

theorem XFlush.empty_preserved {s s' : XState Tid} (h : XFlush s s') {t : Tid}
    (empty : s.buffer t = []) : s'.buffer t = [] := by
  cases h with
  | head u a bs rest oldest =>
      by_cases ht : t = u
      · subst ht; rw [empty] at oldest; cases oldest
      · simpa [Function.update_of_ne ht] using empty

theorem xflushes_empty_preserved {s s' : XState Tid} (h : XFlushes s s') {t : Tid}
    (empty : s.buffer t = []) : s'.buffer t = [] := by
  induction h with
  | refl => exact empty
  | tail _ last ih => exact XFlush.empty_preserved last ih

theorem weak_rmw_atomic {s s' : XState Tid} {t : Tid} {a : Nat} {old new : List Byte}
    (h : XWeakStep s (.rmw t a old new) s') :
    ∃ mid, XFlushes s mid ∧ mid.buffer t = [] ∧ readMem mid.memory a old.length = some old ∧
      new.length = old.length ∧ XFlushes { mid with memory := writeMem mid.memory a new } s' := by
  rcases h with ⟨mid, after, h₁, hs, h₂⟩
  rcases rmw_atomic.mp hs with ⟨e, r, l, rfl⟩
  exact ⟨mid, h₁, e, r, l, h₂⟩

theorem weak_rmw_empty {s s' : XState Tid} {t : Tid} {a : Nat} {old new : List Byte}
    (h : XWeakStep s (.rmw t a old new) s') : s'.buffer t = [] := by
  rcases weak_rmw_atomic h with ⟨mid, _, e, _, _, h₂⟩
  exact xflushes_empty_preserved h₂ e

theorem weak_fence_empty {s s' : XState Tid} {t : Tid}
    (h : XWeakStep s (.fence t) s') : s'.buffer t = [] := by
  rcases h with ⟨b, a, _, hs, h₂⟩
  cases hs with | fence _ e => exact xflushes_empty_preserved h₂ e

end Embed

/-! ## Store forwarding -/

theorem readBufByte_append (x : Nat) (l r : List (Nat × List Byte)) :
    readBufByte x (l ++ r) = (readBufByte x r).or (readBufByte x l) := by
  induction l with
  | nil => simp [readBufByte]
  | cons e l ih =>
      rcases e with ⟨b, bs⟩
      simp only [List.cons_append, readBufByte, ih, Option.or_assoc]

theorem readMem_of_bytes (m : Mem) :
    ∀ (bs : List Byte) (a : Nat), (∀ i, i < bs.length → m (a + i) = bs[i]?) →
      readMem m a bs.length = some bs := by
  intro bs
  induction bs with
  | nil => intro a _; rfl
  | cons b bs ih =>
      intro a h
      have h0 : m a = some b := by simpa using h 0 (by simp)
      have hr := ih (a + 1) (fun i hi => by
        have := h (i + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
      simp [readMem, h0, hr]

/-- Store forwarding: a thread reads back the bytes of its newest store at once, before
any flush. -/
theorem readView_enqueue_same {Tid : Type} [DecidableEq Tid] (s : XState Tid) (t : Tid)
    (a : Nat) (bs : List Byte) :
    readView (enqueue s t a bs) t a bs.length = some bs := by
  apply readMem_of_bytes
  intro i hi
  simp [viewMem, enqueue, readBufByte_append, readBufByte, entryByte, List.getElem?_eq_getElem hi]

/-! ## Litmus tests -/

section Litmus
open Litmus

/-- The two stores stay buffered while both loads read zero. -/
theorem sb_execution :
    Silmaril.Memory.Execution XWeakStep xinitial
      [.store false 0 [1], .store true 1 [1], .load false 1 [0], .load true 0 [0]]
      (enqueue (enqueue xinitial false 0 [1]) true 1 [1]) := by
  refine .cons ⟨_, _, .refl, .store _ _ _ _, .refl⟩
    (.cons ⟨_, _, .refl, .store _ _ _ _, .refl⟩ ?_)
  refine .cons ⟨_, _, .refl, .load _ false 1 [0] (by decide), .refl⟩
    (.cons ⟨_, _, .refl, .load _ true 0 [0] (by decide), .refl⟩ (.nil _))

theorem sb_allowed : Silmaril.Memory.Concurrent XWeakStep xinitial sbLeft sbRight :=
  ⟨_, by simp [sbLeft, sbRight, shuffles], _, sb_execution⟩

/-- Non-vacuity witness for `sb_mfence_forbidden`: the fenced programs do run, and the outcome
`r0 = 0, r1 = 1` (thread `false` runs first, each store flushed before its fence) is allowed. -/
theorem sb_mfence_r1_allowed :
    Silmaril.Memory.Concurrent XWeakStep xinitial sbFenceLeft
      [.store true 1 [1], .fence true, .load true 0 [1]] := by
  refine ⟨[.store false 0 [1], .fence false, .load false 1 [0],
           .store true 1 [1], .fence true, .load true 0 [1]],
    by simp [sbFenceLeft, shuffles], ?_⟩
  apply Exists.intro
  apply Silmaril.Memory.Execution.cons
  · exact ⟨_, _, .refl, .store _ _ _ _,
      .single (.head _ false 0 [1] [] (by simp [xinitial, xembed, enqueue]))⟩
  apply Silmaril.Memory.Execution.cons
  · exact ⟨_, _, .refl, .fence _ _ (by simp), .refl⟩
  apply Silmaril.Memory.Execution.cons
  · exact ⟨_, _, .refl, .load _ false 1 [0] (by decide), .refl⟩
  apply Silmaril.Memory.Execution.cons
  · exact ⟨_, _, .refl, .store _ _ _ _,
      .single (.head _ true 1 [1] [] (by simp [enqueue, xinitial, xembed]))⟩
  apply Silmaril.Memory.Execution.cons
  · exact ⟨_, _, .refl, .fence _ _ (by simp), .refl⟩
  apply Silmaril.Memory.Execution.cons
  · exact ⟨_, _, .refl, .load _ true 0 [1] (by decide), .refl⟩
  exact .nil _

/-- Thread `false`'s part of the SB+mfence invariant (`i` events done; `x` at 0). -/
def I0 (i : Nat) (s : XState Bool) : Prop :=
  (i = 0 ∧ s.buffer false = [] ∧ s.memory 0 = some 0) ∨
  (i = 1 ∧ s.buffer false = [(0, [1])] ∧ s.memory 0 = some 0) ∨
  (1 ≤ i ∧ s.buffer false = [] ∧ s.memory 0 = some 1)

/-- Thread `true`'s part of the SB+mfence invariant (`j` events done; `y` at 1). -/
def I1 (j : Nat) (s : XState Bool) : Prop :=
  (j = 0 ∧ s.buffer true = [] ∧ s.memory 1 = some 0) ∨
  (j = 1 ∧ s.buffer true = [(1, [1])] ∧ s.memory 1 = some 0) ∨
  (1 ≤ j ∧ s.buffer true = [] ∧ s.memory 1 = some 1)

/-- The SB+mfence invariant: both loads cannot both have read zero. -/
def Inv (i j : Nat) (s : XState Bool) : Prop := I0 i s ∧ I1 j s ∧ ¬ (i = 3 ∧ j = 3)

theorem inv_flush {i j : Nat} {s s' : XState Bool} (h : XFlush s s') (hi : Inv i j s) :
    Inv i j s' := by
  obtain ⟨h0, h1, hn⟩ := hi
  cases h with
  | head t a bs rest oldest =>
      refine ⟨?_, ?_, hn⟩ <;> cases t
      · rcases h0 with ⟨_, e, _⟩ | ⟨i1, e, m⟩ | ⟨_, e, _⟩ <;> rw [e] at oldest <;>
          simp only [reduceCtorEq, List.cons.injEq, Prod.mk.injEq] at oldest
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := oldest
        right; right; exact ⟨by omega, by simp, by simp [writeMem, entryByte]⟩
      · rcases h1 with ⟨_, e, _⟩ | ⟨_, e, _⟩ | ⟨_, e, _⟩ <;> rw [e] at oldest <;>
          simp only [reduceCtorEq, List.cons.injEq, Prod.mk.injEq] at oldest
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := oldest
        simpa [I0, writeMem, entryByte] using h0
      · rcases h0 with ⟨_, e, _⟩ | ⟨_, e, _⟩ | ⟨_, e, _⟩ <;> rw [e] at oldest <;>
          simp only [reduceCtorEq, List.cons.injEq, Prod.mk.injEq] at oldest
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := oldest
        simpa [I1, writeMem, entryByte] using h1
      · rcases h1 with ⟨_, e, _⟩ | ⟨j1, e, m⟩ | ⟨_, e, _⟩ <;> rw [e] at oldest <;>
          simp only [reduceCtorEq, List.cons.injEq, Prod.mk.injEq] at oldest
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := oldest
        right; right; exact ⟨by omega, by simp, by simp [writeMem, entryByte]⟩

theorem inv_flushes {i j : Nat} {s s' : XState Bool} (h : XFlushes s s') (hi : Inv i j s) :
    Inv i j s' := by
  induction h with
  | refl => exact hi
  | tail _ last ih => exact inv_flush last ih

/-- One observable step of thread `false`'s SB+mfence program from position `i`. -/
theorem inv_step_left {i j : Nat} {x : XEvent Bool} {xs : List (XEvent Bool)}
    {s s' : XState Bool} (hx : x :: xs = sbFenceLeft.drop i) (h : XStep s x s')
    (hi : Inv i j s) : xs = sbFenceLeft.drop (i + 1) ∧ Inv (i + 1) j s' := by
  obtain ⟨h0, h1, hn⟩ := hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | rfl | hi3
  · simp only [sbFenceLeft, List.drop_zero, List.cons.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    refine ⟨rfl, ?_⟩
    cases h
    rcases h0 with ⟨_, e, m⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> try omega
    refine ⟨Or.inr (Or.inl ⟨rfl, by simp [enqueue, e], m⟩), ?_, by omega⟩
    simpa [I1, enqueue] using h1
  · simp only [sbFenceLeft, List.drop_succ_cons, List.drop_zero, List.cons.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    refine ⟨rfl, ?_⟩
    cases h with
    | fence _ empty =>
      rcases h0 with ⟨h, _⟩ | ⟨_, e, _⟩ | ⟨_, e, m⟩
      · omega
      · rw [e] at empty; cases empty
      · exact ⟨Or.inr (Or.inr ⟨by omega, e, m⟩), h1, by omega⟩
  · simp only [sbFenceLeft, List.drop_succ_cons, List.drop_zero, List.cons.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    refine ⟨rfl, ?_⟩
    cases h with
    | load _ _ _ hr =>
      rcases h0 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, e, m⟩ <;> try omega
      refine ⟨Or.inr (Or.inr ⟨by omega, e, m⟩), h1, ?_⟩
      rcases h1 with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨_, _, m1⟩
      · omega
      · omega
      · simp [readView, readMem, viewMem, e, readBufByte, m1] at hr
  · have : sbFenceLeft.drop i = [] := List.drop_eq_nil_of_le (by simp [sbFenceLeft]; omega)
    rw [this] at hx; cases hx

/-- One observable step of thread `true`'s SB+mfence program from position `j`. -/
theorem inv_step_right {i j : Nat} {y : XEvent Bool} {ys : List (XEvent Bool)}
    {s s' : XState Bool} (hy : y :: ys = sbFenceRight.drop j) (h : XStep s y s')
    (hi : Inv i j s) : ys = sbFenceRight.drop (j + 1) ∧ Inv i (j + 1) s' := by
  obtain ⟨h0, h1, hn⟩ := hi
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j by omega) with rfl | rfl | rfl | hj3
  · simp only [sbFenceRight, List.drop_zero, List.cons.injEq] at hy
    obtain ⟨rfl, rfl⟩ := hy
    refine ⟨rfl, ?_⟩
    cases h
    rcases h1 with ⟨_, e, m⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> try omega
    refine ⟨?_, Or.inr (Or.inl ⟨rfl, by simp [enqueue, e], m⟩), by omega⟩
    simpa [I0, enqueue] using h0
  · simp only [sbFenceRight, List.drop_succ_cons, List.drop_zero, List.cons.injEq] at hy
    obtain ⟨rfl, rfl⟩ := hy
    refine ⟨rfl, ?_⟩
    cases h with
    | fence _ empty =>
      rcases h1 with ⟨h, _⟩ | ⟨_, e, _⟩ | ⟨_, e, m⟩
      · omega
      · rw [e] at empty; cases empty
      · exact ⟨h0, Or.inr (Or.inr ⟨by omega, e, m⟩), by omega⟩
  · simp only [sbFenceRight, List.drop_succ_cons, List.drop_zero, List.cons.injEq] at hy
    obtain ⟨rfl, rfl⟩ := hy
    refine ⟨rfl, ?_⟩
    cases h with
    | load _ _ _ hr =>
      rcases h1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, e, m⟩ <;> try omega
      refine ⟨h0, Or.inr (Or.inr ⟨by omega, e, m⟩), ?_⟩
      rcases h0 with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨_, _, m0⟩
      · omega
      · omega
      · simp [readView, readMem, viewMem, e, readBufByte, m0] at hr
  · have : sbFenceRight.drop j = [] := List.drop_eq_nil_of_le (by simp [sbFenceRight]; omega)
    rw [this] at hy; cases hy

/-- SB+mfence: from any state with empty buffers and `x = y = 0`, no interleaving and no
choice of flushes lets both loads read zero. -/
theorem sb_mfence_forbidden (s₀ : XState Bool) (hb : ∀ t, s₀.buffer t = [])
    (hx : s₀.memory 0 = some 0) (hy : s₀.memory 1 = some 0) :
    ¬ Silmaril.Memory.Concurrent XWeakStep s₀ sbFenceLeft sbFenceRight := by
  rintro ⟨trace, hm, s', hexec⟩
  let P : List (XEvent Bool) → List (XEvent Bool) → XState Bool → Prop := fun xs ys s =>
    ∃ i j, i ≤ 3 ∧ j ≤ 3 ∧ xs = sbFenceLeft.drop i ∧ ys = sbFenceRight.drop j ∧ Inv i j s
  have hP := concurrent_invariant P
    (by
      rintro x xs ys s s'' ⟨i, j, -, lj, hx, hy, hi⟩ ⟨b, a, h₁, hs, h₂⟩
      have li : i < 3 := by
        have := congrArg List.length hx; simp [sbFenceLeft] at this; omega
      obtain ⟨hxs, hi'⟩ := inv_step_left hx hs (inv_flushes h₁ hi)
      exact ⟨i + 1, j, li, lj, hxs, hy, inv_flushes h₂ hi'⟩)
    (by
      rintro y xs ys s s'' ⟨i, j, li, -, hx, hy, hi⟩ ⟨b, a, h₁, hs, h₂⟩
      have lj : j < 3 := by
        have := congrArg List.length hy; simp [sbFenceRight] at this; omega
      obtain ⟨hys, hi'⟩ := inv_step_right hy hs (inv_flushes h₁ hi)
      exact ⟨i, j + 1, li, lj, hx, hys, inv_flushes h₂ hi'⟩)
    _ _ _ _ _ hm hexec
    ⟨0, 0, by omega, by omega, rfl, rfl, Or.inl ⟨rfl, hb false, hx⟩,
      Or.inl ⟨rfl, hb true, hy⟩, by omega⟩
  obtain ⟨i, j, ui, uj, hi, hj, -, -, hn⟩ := hP
  have li : 3 ≤ i := by
    have := congrArg List.length hi; simp [sbFenceLeft] at this; omega
  have lj : 3 ≤ j := by
    have := congrArg List.length hj; simp [sbFenceRight] at this; omega
  exact hn ⟨by omega, by omega⟩

end Litmus

end Silmaril.X86.MemoryModel.Tso.Proofs
