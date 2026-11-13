module

public import Silmaril.Wasm.Models.FXAsyncPC.Defs
public import Mathlib.Data.List.Forall2

/-!
# Lock-step runs of deterministic machines, and list relations

* `ResRel R`: two step results are both `next` with `R`-related configurations, or both stop
  with the same outcome;
* **`beh_eq_of_lock`**: if `R`-related configurations always step to `ResRel R`-related results,
  then `R`-related configurations have the same behaviours (`R` need not be a function);
* `Forall₂` facts for the heap: lookup, `set` and append keep pointwise relations.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncPC

open Silmaril.Wasm.Models.FXAsync

variable {C D V : Type}

/-- Related step results: both continue with related configurations, or both stop alike. -/
inductive ResRel (R : C → D → Prop) : Res C V → Res D V → Prop where
  | next {c : C} {d : D} (h : R c d) : ResRel R (.next c) (.next d)
  | stop (o : Outcome V) : ResRel R (.stop o) (.stop o)

theorem runN_lock {s : C → Res C V} {t : D → Res D V} {R : C → D → Prop}
    (hstep : ∀ x y, R x y → ResRel R (s x) (t y)) (n : Nat) :
    ∀ x y, R x y → ResRel R (runN s n x) (runN t n y) := by
  induction n with
  | zero => exact fun x y h => .next h
  | succ n ih =>
    intro x y h
    have hs := hstep x y h
    revert hs
    simp only [runN]
    generalize s x = a
    generalize t y = b
    intro hs
    cases hs with
    | next h' => exact ih _ _ h'
    | stop o => exact .stop o

theorem lock_stop {R : C → D → Prop} {a : Res C V} {b : Res D V} (h : ResRel R a b)
    (o : Outcome V) : a = .stop o ↔ b = .stop o := by
  cases h with
  | next _ => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  | stop o' => exact ⟨fun h => by cases h; rfl, fun h => by cases h; rfl⟩

theorem lock_next {R : C → D → Prop} {a : Res C V} {b : Res D V} (h : ResRel R a b) :
    (∃ c, a = .next c) ↔ ∃ d, b = .next d := by
  cases h with
  | next _ => exact ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩⟩
  | stop o => exact ⟨fun ⟨_, h⟩ => (by cases h), fun ⟨_, h⟩ => (by cases h)⟩

/-- **Equal behaviours under a lock-step relation of deterministic machines.** -/
theorem beh_eq_of_lock {s : C → Res C V} {t : D → Res D V} {R : C → D → Prop}
    (hstep : ∀ x y, R x y → ResRel R (s x) (t y)) {x : C} {y : D} (hxy : R x y) :
    beh s x = beh t y := by
  have hrun := fun n => runN_lock hstep n x y hxy
  ext b
  constructor
  · rintro (⟨n, o, h, rfl⟩ | ⟨rfl, hdiv⟩)
    · exact .inl ⟨n, o, (lock_stop (hrun n) o).1 h, rfl⟩
    · exact .inr ⟨rfl, fun n => (lock_next (hrun n)).1 (hdiv n)⟩
  · rintro (⟨n, o, h, rfl⟩ | ⟨rfl, hdiv⟩)
    · exact .inl ⟨n, o, (lock_stop (hrun n) o).2 h, rfl⟩
    · exact .inr ⟨rfl, fun n => (lock_next (hrun n)).2 (hdiv n)⟩

/-! ## Pointwise relations on lists -/

variable {α β : Type} {S : α → β → Prop}

theorem forall₂_getElem? {l : List α} {l' : List β} (h : List.Forall₂ S l l') :
    ∀ k : Nat, Option.Rel S l[k]? l'[k]? := by
  induction h with
  | nil => intro k; simp only [List.getElem?_nil]; exact .none
  | cons hab _ ih =>
    intro k
    cases k with
    | zero => exact .some hab
    | succ k => simpa only [List.getElem?_cons_succ] using ih k

theorem forall₂_set {l : List α} {l' : List β} (h : List.Forall₂ S l l') {a : α} {b : β}
    (hab : S a b) : ∀ k : Nat, List.Forall₂ S (l.set k a) (l'.set k b) := by
  induction h with
  | nil => intro k; simp only [List.set_nil]; exact .nil
  | cons hxy _ ih =>
    intro k
    cases k with
    | zero => exact .cons hab (by assumption)
    | succ k => exact .cons hxy (ih k)

theorem forall₂_append_one {l : List α} {l' : List β} (h : List.Forall₂ S l l') {a : α} {b : β}
    (hab : S a b) : List.Forall₂ S (l ++ [a]) (l' ++ [b]) :=
  List.rel_append h (.cons hab .nil)

theorem forall₂_reverse {l : List α} {l' : List β} (h : List.Forall₂ S l l') :
    List.Forall₂ S l.reverse l'.reverse :=
  List.forall₂_reverse_iff.2 h

end Silmaril.Proofs.Wasm.Models.FXAsyncPC
