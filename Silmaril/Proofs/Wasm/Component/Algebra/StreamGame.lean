module

public import Silmaril.Wasm.Component.Algebra.StreamGame.Defs
public import Silmaril.Wasm.Component.Streams.Spec.Thms

/-!
# The stream game of transformers: proofs

* `feedA_append`, `ans_mono`: reacting is a fold, so the stream function is monotone.
* `feedA_items`: on items only, reacting is feeding.
* `ans_id`: the identity transformer is the identity stream function.
* `react_comp`, `feedA_comp`, `ans_comp`: the composite transformer reacts as the downstream
  transformer applied to the reactions of the upstream one (`Streams.Spec`'s `feed_comp`; an
  end restarts both).
* `feedA_congr`, `ans_congr`: the stream function depends only on `runP` and `run`, so
  equivalent transformers have the same one.
-/

public section

namespace Silmaril.Proofs.Wasm.Component.Algebra.StreamGame

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Streams Silmaril.Wasm.Component.Algebra.Kahn
open Silmaril.Wasm.Component.Algebra.StreamGame
open Silmaril.Proofs.Wasm.Component.Streams.Spec (feed_append feed_done feed_comp)

variable {σ τ : Type}

theorem ofItem_item (v : Val) : ofItem (item v) = some v := rfl

theorem eq_item_of_ofItem {a : Ans} {v : Val} (h : ofItem a = some v) : a = item v := by
  rcases a with _ | (_ | vs)
  · cases h
  · cases h
  · rcases vs with _ | ⟨w, _ | ⟨_, _⟩⟩
    · cases h
    · cases h
      rfl
    · cases h

theorem feedA_nil (T : Tr σ Val Val) (s : σ) : feedA T s [] = (s, []) := rfl

theorem feedA_cons (T : Tr σ Val Val) (s : σ) (a : Ans) (h : List Ans) :
    feedA T s (a :: h) =
      ((feedA T (react T s a).1 h).1, (react T s a).2 ++ (feedA T (react T s a).1 h).2) := rfl

/-- Reacting is a fold. -/
theorem feedA_append (T : Tr σ Val Val) (s : σ) (h h' : List Ans) :
    feedA T s (h ++ h') =
      ((feedA T (feedA T s h).1 h').1, (feedA T s h).2 ++ (feedA T (feedA T s h).1 h').2) := by
  induction h generalizing s with
  | nil => rfl
  | cons a h ih => simp [feedA_cons, ih]

/-- The stream function of a transformer is monotone. -/
theorem ans_mono (T : Tr σ Val Val) : Mono (ans T) := fun h h' => by
  simp only [ans, feedA_append]
  exact List.prefix_append _ _

/-- On items only, reacting is feeding. -/
theorem feedA_items (T : Tr σ Val Val) (s : σ) (xs : List Val) :
    feedA T s (xs.map item) = ((T.feed s xs).1, (T.feed s xs).2.map item) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    have hx : T.feed s (x :: xs) =
        ((T.feed (T.feed s [x]).1 xs).1, (T.feed s [x]).2 ++ (T.feed (T.feed s [x]).1 xs).2) :=
      feed_append T s [x] xs
    simp only [List.map_cons, feedA_cons, react, ofItem_item, ih, hx, List.map_append]

/-! ## The identity -/

theorem feedA_id (s : Unit) (h : List Ans) : feedA (Tr.id : Tr Unit Val Val) s h = ((), h) := by
  induction h generalizing s with
  | nil => rfl
  | cons a h ih =>
    rw [feedA_cons, ih]
    cases ho : ofItem a with
    | some v =>
      simp only [react, ho]
      rw [eq_item_of_ofItem ho]
      rfl
    | none =>
      simp only [react, ho]
      rfl

/-- The identity transformer is the identity stream function. -/
theorem ans_id (h : List Ans) : ans (Tr.id : Tr Unit Val Val) h = h := by
  rw [ans, feedA_id]

/-! ## Composition -/

/-- The composite's state is related to the pair of states, as in `feed_comp`. -/
def CompR (U : Tr τ Val Val) (c₁ s₁ : σ) (s₂ : τ) : Prop := c₁ = s₁ ∨ U.done s₂ = true

theorem react_comp (T : Tr σ Val Val) (U : Tr τ Val Val) {c₁ s₁ : σ} {s₂ : τ}
    (hr : CompR U c₁ s₁ s₂) (a : Ans) :
    (react (T.comp U) (c₁, s₂) a).2 = (feedA U s₂ (react T s₁ a).2).2 ∧
      (react (T.comp U) (c₁, s₂) a).1.2 = (feedA U s₂ (react T s₁ a).2).1 ∧
      CompR U (react (T.comp U) (c₁, s₂) a).1.1 (react T s₁ a).1
        (feedA U s₂ (react T s₁ a).2).1 := by
  cases ho : ofItem a with
  | some v =>
    show (react (T.comp U) (c₁, s₂) a).2 = _ ∧ _
    simp only [react, ho, feedA_items]
    rcases hr with rfl | hd
    · obtain ⟨h₁, h₂, h₃⟩ := feed_comp T U c₁ s₂ [v]
      exact ⟨by rw [h₁], h₂, h₃⟩
    · have hd' : (T.comp U).done (c₁, s₂) = true := by simp [Tr.comp, hd]
      rw [feed_done _ _ hd', feed_done U s₂ hd]
      exact ⟨rfl, rfl, .inr hd⟩
  | none =>
    show (react (T.comp U) (c₁, s₂) a).2 = _ ∧ _
    simp only [react, ho]
    have hfa : feedA U s₂ ((T.flush s₁).map item ++ [a]) =
        (U.init, ((U.feed s₂ (T.flush s₁)).2.map item) ++
          ((U.flush (U.feed s₂ (T.flush s₁)).1).map item ++ [a])) := by
      rw [feedA_append, feedA_items]
      simp only [feedA_cons, react, ho, feedA_nil, List.append_nil]
    rw [hfa]
    refine ⟨?_, rfl, .inl rfl⟩
    rcases hr with rfl | hd
    · simp [Tr.comp]
    · simp [Tr.comp, feed_done U s₂ hd]

theorem feedA_comp (T : Tr σ Val Val) (U : Tr τ Val Val) (h : List Ans) :
    ∀ {c₁ s₁ : σ} {s₂ : τ}, CompR U c₁ s₁ s₂ →
      (feedA (T.comp U) (c₁, s₂) h).2 = (feedA U s₂ (feedA T s₁ h).2).2 ∧
      (feedA (T.comp U) (c₁, s₂) h).1.2 = (feedA U s₂ (feedA T s₁ h).2).1 ∧
      CompR U (feedA (T.comp U) (c₁, s₂) h).1.1 (feedA T s₁ h).1
        (feedA U s₂ (feedA T s₁ h).2).1 := by
  induction h with
  | nil => exact fun hr => ⟨rfl, rfl, hr⟩
  | cons a h ih =>
    intro c₁ s₁ s₂ hr
    obtain ⟨e₁, e₂, e₃⟩ := react_comp T U hr a
    have hpair : (react (T.comp U) (c₁, s₂) a).1 =
        ((react (T.comp U) (c₁, s₂) a).1.1, (feedA U s₂ (react T s₁ a).2).1) := by
      rw [← e₂]
    obtain ⟨f₁, f₂, f₃⟩ := ih e₃
    rw [feedA_cons, feedA_cons, hpair, feedA_append]
    exact ⟨by rw [e₁, f₁], f₂, f₃⟩

/-- **The composite transformer's stream function is the composite of stream functions.** -/
theorem ans_comp (T : Tr σ Val Val) (U : Tr τ Val Val) (h : List Ans) :
    ans (T.comp U) h = ans U (ans T h) :=
  (feedA_comp T U h (c₁ := T.init) (s₁ := T.init) (s₂ := U.init) (.inl rfl)).1

/-! ## Equivalence -/

theorem feed_snoc (T : Tr σ Val Val) (xs : List Val) (v : Val) :
    T.runP (xs ++ [v]) = T.runP xs ++ (T.feed (T.feed T.init xs).1 [v]).2 ∧
      (T.feed T.init (xs ++ [v])).1 = (T.feed (T.feed T.init xs).1 [v]).1 := by
  exact ⟨by simp only [Tr.runP, feed_append], by simp only [feed_append]⟩

/-- Equivalent transformers emit the same outputs on one more item. -/
theorem step_congr {T : Tr σ Val Val} {U : Tr τ Val Val} (hTU : T.Equiv U) (xs : List Val)
    (v : Val) :
    (T.feed (T.feed T.init xs).1 [v]).2 = (U.feed (U.feed U.init xs).1 [v]).2 := by
  have e : T.runP (xs ++ [v]) = U.runP (xs ++ [v]) := (hTU (xs ++ [v])).1
  rw [(feed_snoc T xs v).1, (feed_snoc U xs v).1, (hTU xs).1] at e
  exact List.append_cancel_left e

/-- Equivalent transformers flush the same outputs. -/
theorem flush_congr {T : Tr σ Val Val} {U : Tr τ Val Val} (hTU : T.Equiv U) (xs : List Val) :
    T.flush (T.feed T.init xs).1 = U.flush (U.feed U.init xs).1 := by
  have e : T.runP xs ++ T.flush (T.feed T.init xs).1 =
      U.runP xs ++ U.flush (U.feed U.init xs).1 := (hTU xs).2
  rw [(hTU xs).1] at e
  exact List.append_cancel_left e

theorem feedA_congr {T : Tr σ Val Val} {U : Tr τ Val Val} (hTU : T.Equiv U) (h : List Ans) :
    ∀ xs : List Val,
      (feedA T (T.feed T.init xs).1 h).2 = (feedA U (U.feed U.init xs).1 h).2 := by
  induction h with
  | nil => exact fun _ => rfl
  | cons a h ih =>
    intro xs
    rw [feedA_cons, feedA_cons]
    cases ho : ofItem a with
    | some v =>
      simp only [react, ho]
      rw [← (feed_snoc T xs v).2, ← (feed_snoc U xs v).2, step_congr hTU xs v, ih (xs ++ [v])]
    | none =>
      simp only [react, ho]
      rw [flush_congr hTU xs]
      exact congrArg _ (ih [])

/-- **Equivalent transformers have the same stream function.** -/
theorem ans_congr {T : Tr σ Val Val} {U : Tr τ Val Val} (hTU : T.Equiv U) (h : List Ans) :
    ans T h = ans U h :=
  feedA_congr hTU h []

end Silmaril.Proofs.Wasm.Component.Algebra.StreamGame
