module

public import Silmaril.Wasm.Component.Streams.Spec.Defs

/-!
# Stream transformers: proofs

Proofs of `Silmaril.Wasm.Component.Streams.Spec.Thms`.

* `feed_done`, `feed_append`: feeding stops at a `done` state; feeding is a fold.
* `feed_comp`: feeding a composite gives `U`'s state and outputs of feeding `U` the outputs of
  `T`, and `T`'s state unless `U` stopped.
* the closed forms of `id`, `map`, `filter`, `filterMap`, `flatMap`, `take`, `tee`.
-/

public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Spec

open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Tr

variable {σ τ α β γ : Type}

theorem ite_ff {X : Type} (a b : X) : (if false = true then a else b) = b := rfl

theorem feed_nil (T : Tr σ α β) (s : σ) : T.feed s [] = (s, []) := rfl

theorem feed_cons (T : Tr σ α β) (s : σ) (x : α) (xs : List α) :
    T.feed s (x :: xs) =
      if T.done s then (s, []) else ((T.feed (T.step s x).1 xs).1,
        (T.step s x).2 ++ (T.feed (T.step s x).1 xs).2) := rfl

/-- At a `done` state nothing is read. -/
theorem feed_done (T : Tr σ α β) (s : σ) (h : T.done s = true) (xs : List α) :
    T.feed s xs = (s, []) := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [feed_cons, h]

/-- **Feeding is a fold.** -/
theorem feed_append (T : Tr σ α β) (s : σ) (xs ys : List α) :
    T.feed s (xs ++ ys) =
      ((T.feed (T.feed s xs).1 ys).1, (T.feed s xs).2 ++ (T.feed (T.feed s xs).1 ys).2) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : T.done s = true
    · simp [feed_done T s h]
    · simp [feed_cons, h, ih]

theorem comp_done (T : Tr σ α β) (U : Tr τ β γ) (s : σ) (u : τ) :
    (T.comp U).done (s, u) = (T.done s || U.done u) := rfl

theorem comp_step (T : Tr σ α β) (U : Tr τ β γ) (s : σ) (u : τ) (x : α) :
    (T.comp U).step (s, u) x =
      (((T.step s x).1, (U.feed u (T.step s x).2).1), (U.feed u (T.step s x).2).2) := rfl

theorem comp_feed_cons (T : Tr σ α β) (U : Tr τ β γ) (s : σ) (u : τ) (x : α) (xs : List α) :
    (T.comp U).feed (s, u) (x :: xs) =
      if (T.done s || U.done u) then ((s, u), []) else
        (((T.comp U).feed ((T.step s x).1, (U.feed u (T.step s x).2).1) xs).1,
          (U.feed u (T.step s x).2).2 ++
            ((T.comp U).feed ((T.step s x).1, (U.feed u (T.step s x).2).1) xs).2) := rfl

theorem comp_flush (T : Tr σ α β) (U : Tr τ β γ) (s : σ) (u : τ) :
    (T.comp U).flush (s, u) = (U.feed u (T.flush s)).2 ++ U.flush (U.feed u (T.flush s)).1 := rfl

/-- **Feeding a composite.** Its outputs and `U`'s state are those of feeding `U` the outputs of
feeding `T`; `T`'s state is that of feeding `T`, unless `U` stopped. -/
theorem feed_comp (T : Tr σ α β) (U : Tr τ β γ) (s : σ) (u : τ) (xs : List α) :
    ((T.comp U).feed (s, u) xs).2 = (U.feed u (T.feed s xs).2).2 ∧
      ((T.comp U).feed (s, u) xs).1.2 = (U.feed u (T.feed s xs).2).1 ∧
      (((T.comp U).feed (s, u) xs).1.1 = (T.feed s xs).1 ∨
        U.done (U.feed u (T.feed s xs).2).1 = true) := by
  induction xs generalizing s u with
  | nil => exact ⟨rfl, rfl, Or.inl rfl⟩
  | cons x xs ih =>
    by_cases hT : T.done s = true
    · simp [feed_cons, comp_done, feed_nil, hT]
    by_cases hU : U.done u = true
    · simp [feed_cons, comp_done, hT, hU, feed_done U u hU]
    obtain ⟨h1, h2, h3⟩ := ih (T.step s x).1 (U.feed u (T.step s x).2).1
    have hT' : T.done s = false := by simpa using hT
    have hU' : U.done u = false := by simpa using hU
    rw [comp_feed_cons, hT', hU', Bool.false_or, ite_ff, feed_cons, hT',
      ite_ff, feed_append U u]
    exact ⟨by rw [h1], h2, h3⟩

/-- **Composition, output so far.** -/
theorem runP_comp (T : Tr σ α β) (U : Tr τ β γ) (xs : List α) :
    (T.comp U).runP xs = U.runP (T.runP xs) :=
  (feed_comp T U T.init U.init xs).1

/-- **Composition, whole output.** -/
theorem run_comp (T : Tr σ α β) (U : Tr τ β γ) (xs : List α) :
    (T.comp U).run xs = U.run (T.run xs) := by
  obtain ⟨h1, h2, h3⟩ := feed_comp T U T.init U.init xs
  have hR : U.run (T.run xs) =
      (U.feed U.init (T.feed T.init xs).2).2 ++
        ((U.feed (U.feed U.init (T.feed T.init xs).2).1 (T.flush (T.feed T.init xs).1)).2 ++
        U.flush (U.feed (U.feed U.init (T.feed T.init xs).2).1
          (T.flush (T.feed T.init xs).1)).1) := by
    simp [run, feed_append]
  have hL : (T.comp U).run xs = ((T.comp U).feed (T.init, U.init) xs).2 ++
      (T.comp U).flush (((T.comp U).feed (T.init, U.init) xs).1.1,
        ((T.comp U).feed (T.init, U.init) xs).1.2) := rfl
  rw [hR, hL, comp_flush, h1, h2]
  rcases h3 with h3 | h3
  · rw [h3]
  · rw [feed_done U _ h3, feed_done U _ h3]

/-- Outputs so far are monotone in the input. -/
theorem runP_append (T : Tr σ α β) (xs ys : List α) :
    T.runP (xs ++ ys) = T.runP xs ++ (T.feed (T.feed T.init xs).1 ys).2 := by
  simp [runP, feed_append]

/-- Feeding the items that are read gives the same result as feeding everything. -/
theorem feed_take_used (T : Tr σ α β) (s : σ) (xs : List α) (k : Nat) (hk : T.used s xs ≤ k) :
    T.feed s (xs.take k) = T.feed s xs := by
  induction xs generalizing s k with
  | nil => simp
  | cons x xs ih =>
    by_cases h : T.done s = true
    · cases k <;> simp [feed_done T s h]
    · have hu : T.used s (x :: xs) = T.used (T.step s x).1 xs + 1 := by simp [used, h]
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hk' : T.used (T.step s x).1 xs ≤ k := by omega
      simp [feed_cons, h, ih _ _ hk']

/-- Once the transformer is done, the rest of the input does not matter. -/
theorem run_prefix_done (T : Tr σ α β) (R F : List α) (hd : T.done (T.feed T.init R).1 = true)
    (hp : R <+: F) : T.run R = T.run F := by
  obtain ⟨X, rfl⟩ := hp
  have hf : T.feed T.init (R ++ X) = T.feed T.init R := by
    rw [feed_append, feed_done T _ hd X]
    simp
  show (T.feed T.init R).2 ++ T.flush (T.feed T.init R).1 =
    (T.feed T.init (R ++ X)).2 ++ T.flush (T.feed T.init (R ++ X)).1
  rw [hf]

/-! ## Closed forms -/

/-- A transformer that is never done and whose outputs depend only on the item feeds as a
`flatMap`. -/
theorem feed_unit (T : Tr σ α β) (g : α → List β)
    (hstep : ∀ s x, (T.step s x).2 = g x) (hd : ∀ s, T.done s = false) (s : σ) (xs : List α) :
    (T.feed s xs).2 = xs.flatMap g := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp [feed_cons, hd, hstep, ih]

theorem runP_unit (T : Tr σ α β) (g : α → List β)
    (hstep : ∀ s x, (T.step s x).2 = g x) (hd : ∀ s, T.done s = false) (xs : List α) :
    T.runP xs = xs.flatMap g := feed_unit T g hstep hd T.init xs

theorem run_unit (T : Tr σ α β) (g : α → List β)
    (hstep : ∀ s x, (T.step s x).2 = g x) (hd : ∀ s, T.done s = false)
    (hf : ∀ s, T.flush s = []) (xs : List α) :
    T.run xs = xs.flatMap g := by
  show (T.feed T.init xs).2 ++ T.flush (T.feed T.init xs).1 = _
  rw [hf, feed_unit T g hstep hd, List.append_nil]

theorem flatMap_singleton' (f : α → β) (xs : List α) : xs.flatMap (fun x => [f x]) = xs.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem flatMap_filter (p : α → Bool) (xs : List α) :
    xs.flatMap (fun x => if p x then [x] else []) = xs.filter p := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [hp, ih]

theorem flatMap_filterMap (f : α → Option β) (xs : List α) :
    xs.flatMap (fun x => (f x).toList) = xs.filterMap f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hf : f x <;> simp [hf, ih]

theorem feed_take (n : Nat) (k : Nat) (xs : List α) :
    (Tr.take n : Tr Nat α α).feed k xs = (k - xs.length, xs.take k) := by
  induction xs generalizing k with
  | nil => simp [feed_nil]
  | cons x xs ih =>
    cases k with
    | zero => simp [feed_cons, Tr.take]
    | succ k =>
      have h : (Tr.take n : Tr Nat α α).feed k xs = (k - xs.length, xs.take k) := ih k
      have hs : (Tr.take n : Tr Nat α α).step (k + 1) x = (k, [x]) := rfl
      have hd : (Tr.take n : Tr Nat α α).done (k + 1) = false := rfl
      rw [feed_cons, hs, hd, ite_ff, h]
      simp

theorem used_take (n : Nat) (k : Nat) (xs : List α) :
    (Tr.take n : Tr Nat α α).used k xs = min k xs.length := by
  induction xs generalizing k with
  | nil => simp [used]
  | cons x xs ih =>
    cases k with
    | zero => simp [used, Tr.take]
    | succ k =>
      have h : (Tr.take n : Tr Nat α α).used k xs = min k xs.length := ih k
      have hs : (Tr.take n : Tr Nat α α).step (k + 1) x = (k, [x]) := rfl
      have hd : (Tr.take n : Tr Nat α α).done (k + 1) = false := rfl
      simp only [used, hs, hd, ite_ff, h, List.length_cons]
      omega

theorem chan_tee (b : Bool) (xs : List α) :
    chan b (xs.flatMap fun x => [(false, x), (true, x)]) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases b
    · simpa [chan, List.filterMap_cons] using ih
    · simpa [chan, List.filterMap_cons] using ih

end Silmaril.Proofs.Wasm.Component.Streams.Spec
