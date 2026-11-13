module

public import Silmaril.Wasm.JcoTool.KRead.Defs
public import Silmaril.Wasm.Component.Streams.Spec.Thms
public import Silmaril.Wasm.Component.Algebra.StreamGame.Thms

/-!
# The strategy reading of an observation

* `ofObs_feed`, `ofObs_equiv`: for monotone outputs so far `P` with `P [] = []` below the whole
  outputs `R`, `ofObs P R` has outputs so far `P` and whole outputs `R`; so `ofObs T.runP T.run`
  is equivalent to `T`.
* `reads_partF`, `reads_wholeF`: an observation that reads as `T` determines `T.runP`, `T.run`.
* `game_eq_den`: its strategy reading is `den T`; `reads_equiv`: two transformers it reads as
  are equivalent.
-/

public section

namespace Silmaril.Proofs.Wasm.JcoTool.KRead

open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.JcoTool.KRead

variable {σ τ : Type}

theorem drop_prefix_append {a b c : List Val} (hab : a <+: b) (hbc : b <+: c) :
    b.drop a.length ++ c.drop b.length = c.drop a.length := by
  obtain ⟨t, rfl⟩ := hab
  obtain ⟨u, rfl⟩ := hbc
  simp

theorem prefix_append_drop {a b : List Val} (h : a <+: b) : a ++ b.drop a.length = b := by
  obtain ⟨t, rfl⟩ := h
  simp

/-- **Feeding `ofObs`**: the input is remembered, the outputs are what `P` adds. -/
theorem ofObs_feed {P R : List Val → List Val} (hP : ∀ xs ys, P xs <+: P (xs ++ ys)) :
    ∀ (xs s : List Val), (ofObs P R).feed s xs = (s ++ xs, (P (s ++ xs)).drop (P s).length)
  | [], s => by simp [Tr.feed]
  | x :: xs, s => by
    have ih := ofObs_feed (R := R) hP xs (s ++ [x])
    have e : s ++ [x] ++ xs = s ++ x :: xs := by simp
    simp only [Tr.feed, ofObs, Bool.false_eq_true, ↓reduceIte]
    simp only [ofObs] at ih
    rw [ih, e, drop_prefix_append (hP s [x]) (by rw [← e]; exact hP (s ++ [x]) xs)]

theorem ofObs_runP {P R : List Val → List Val} (hP : ∀ xs ys, P xs <+: P (xs ++ ys))
    (h0 : P [] = []) (xs : List Val) : (ofObs P R).runP xs = P xs := by
  simp only [Tr.runP]
  rw [show (ofObs P R).init = [] from rfl, ofObs_feed hP xs [], h0]
  simp

theorem ofObs_run {P R : List Val → List Val} (hP : ∀ xs ys, P xs <+: P (xs ++ ys))
    (h0 : P [] = []) (hR : ∀ xs, P xs <+: R xs) (xs : List Val) : (ofObs P R).run xs = R xs := by
  simp only [Tr.run]
  rw [show (ofObs P R).init = [] from rfl, ofObs_feed hP xs [], h0]
  simp only [List.nil_append, List.length_nil, List.drop_zero]
  exact prefix_append_drop (hR xs)

/-- **`ofObs T.runP T.run` is equivalent to `T`.** -/
theorem ofObs_equiv (T : Tr σ Val Val) : (ofObs T.runP T.run).Equiv T := by
  have hP : ∀ xs ys, T.runP xs <+: T.runP (xs ++ ys) := Tr.runP_mono T
  have h0 : T.runP [] = [] := rfl
  intro xs
  exact ⟨ofObs_runP hP h0 xs, ofObs_run hP h0 (Tr.runP_le_run T) xs⟩

theorem reads_wholeF {O : Obs} {T : Tr σ Val Val} (h : O.Reads T) : O.wholeF = T.run := by
  funext xs
  have hex : ∃ ys, O.whole xs ys := ⟨_, ((h xs (T.run xs)).1).2 rfl⟩
  simp only [Obs.wholeF, hex, ↓reduceDIte]
  exact ((h xs _).1).1 (Classical.choose_spec hex)

theorem reads_partF {O : Obs} {T : Tr σ Val Val} (h : O.Reads T) : O.partF = T.runP := by
  funext xs
  have hex : ∃ ys, O.part xs ys := ⟨_, ((h xs (T.runP xs)).2).2 rfl⟩
  simp only [Obs.partF, hex, ↓reduceDIte]
  exact ((h xs _).2).1 (Classical.choose_spec hex)

/-- **The strategy reading of an observation that reads as `T` is `den T`.** -/
theorem game_eq_den {O : Obs} {T : Tr σ Val Val} (h : O.Reads T) :
    O.game = Algebra.StreamGame.den T := by
  rw [Obs.game, reads_partF h, reads_wholeF h]
  exact Algebra.StreamGame.den_congr (ofObs_equiv T)

/-- Two transformers one observation reads as are equivalent. -/
theorem reads_equiv {O : Obs} {T : Tr σ Val Val} {U : Tr τ Val Val} (hT : O.Reads T)
    (hU : O.Reads U) : T.Equiv U := fun xs =>
  ⟨(hU xs _).2.1 ((hT xs _).2.2 rfl), (hU xs _).1.1 ((hT xs _).1.2 rfl)⟩

end Silmaril.Proofs.Wasm.JcoTool.KRead
