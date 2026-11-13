module

public import Mathlib.Data.List.Forall2

/-!
# Pointwise relations on lists, for heaps and buffers

Lookup, `set`, append and reverse keep `List.Forall₂`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.RelSim

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
  | cons hxy htl ih =>
    intro k
    cases k with
    | zero => exact .cons hab htl
    | succ k => exact .cons hxy (ih k)

theorem forall₂_append_one {l : List α} {l' : List β} (h : List.Forall₂ S l l') {a : α} {b : β}
    (hab : S a b) : List.Forall₂ S (l ++ [a]) (l' ++ [b]) :=
  List.rel_append h (.cons hab .nil)

theorem forall₂_reverse {l : List α} {l' : List β} (h : List.Forall₂ S l l') :
    List.Forall₂ S l.reverse l'.reverse :=
  List.forall₂_reverse_iff.2 h

end Silmaril.Proofs.Wasm.FX.Asyncify.RelSim
