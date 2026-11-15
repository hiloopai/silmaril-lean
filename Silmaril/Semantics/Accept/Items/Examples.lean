module

public import Silmaril.Semantics.Accept.Items.Thms

/-! # Item sequences: worked examples and regression tests

A JSON-Lines-shaped setting, kept generic: items are byte strings (`List UInt8`), an item's
length is `List.length`, and the whole file counts each item plus one separator byte. The item
specification is a stand-in (`nonempty`); concrete JSON validity lives in the format
developments. Every `example` is checked when the library builds.
-/

@[expose] public section

namespace Silmaril.Accept.ItemsExamples

open Silmaril.Accept

/-- Item length. -/
abbrev itemLen (x : List UInt8) : ℕ := x.length

/-- Weight in the whole file: the item and its newline. -/
abbrev lineWeight (x : List UInt8) : ℕ := x.length + 1

/-- Stand-in item specification. -/
def nonempty : Set (List UInt8) := {x | x ≠ []}

/-- Its checker. -/
def isNonempty (x : List UInt8) : Bool := !x.isEmpty

theorem isNonempty_decides : Decides isNonempty nonempty := fun x => by
  cases x <;> simp [isNonempty, nonempty]

/-- A file of a thousand one-byte items has per-item length `1` … -/
example : List.replicate 1000 [0x30] ∈ itemsWithin itemLen 1 := fun y hy => by
  rw [List.eq_of_mem_replicate hy]; simp

/-- … but whole-file length `2000`: per-item and whole-file bounds differ. -/
example : List.replicate 1000 [0x30] ∉ totalWithin lineWeight 1999 := fun h => by
  have h' : totalWeight lineWeight (List.replicate 1000 [0x30]) ≤ 1999 := h
  rw [totalWeight_replicate] at h'; exact absurd h' (by decide)

/-- No per-item bound gives a whole-file bound. -/
example (m : ℕ) : ¬ itemsWithin itemLen 1 ⊆ totalWithin lineWeight m :=
  itemsWithin_not_subset_totalWithin (x := [0x30]) (by simp) (by simp) m

/-- A whole-file bound does give a per-item bound. -/
example : totalWithin lineWeight 4096 ⊆ itemsWithin itemLen 4096 :=
  totalWithin_subset_itemsWithin fun _ => Nat.le_succ _

/-- An item checker lifts to whole files, with no bound on their length … -/
example : Decides (fun s => s.all isNonempty) (everyItem nonempty) :=
  isNonempty_decides.everyItem

/-- … and a checker correct only on items of length at most `n` is correct on every file of
such items, of any total length. -/
example (n : ℕ) (c : List UInt8 → Bool) (h : DecidesOn (within itemLen n) c nonempty) :
    DecidesOn (itemsWithin itemLen n) (fun s => s.all c) (everyItem nonempty) :=
  h.itemsWithin

/-- Infinite item sequences: per-item membership is membership of every finite prefix. -/
example (s : Cslib.ωSequence (List UInt8)) :
    s ∈ everyItemω nonempty ↔ ∀ n, s.take n ∈ everyItem nonempty :=
  mem_everyItemω_iff_take

/-- Mathlib's Kleene star is flattening of item lists. -/
example (L : Language UInt8) : (KStar.kstar L : Language UInt8) =
    List.flatten '' everyItem (L : Set (List UInt8)) := kstar_eq_image_flatten L

end Silmaril.Accept.ItemsExamples
