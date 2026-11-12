module

public import Silmaril.Proofs.Data.SepList.Dll
public import Silmaril.Data.Cells.Thms

/-!
# List segments inside a larger fragment: the frame of a block step

A data structure's fragment is often a concatenation of blocks (one list per bin). A generic
lemma about one block (`dllPushFront`, `dllUnlink`, …) lifts to the whole fragment when its
stores go to slots of the block or of fresh cells: the other blocks are framed
(`Frag.holds_block_step`). `dll_bytes`: a `dll`'s bytes are its nodes' slots' bytes, so the
lists' slot separation follows from the fragment's.
-/

@[expose] public section

namespace Silmaril.Data

/-- **Frame through stores**: a fragment apart from every store holds after them. -/
theorem Frag.holds_storeAll_frame : ∀ {v : MemView} {G st : Frag},
    (∀ c ∈ G, ∀ d ∈ st, c.Apart d) → G.Holds v → G.Holds (v.storeAll st)
  | _, _, [], _, h => h
  | v, G, d :: ds, hap, h => by
    rw [MemView.storeAll_cons]
    refine Frag.holds_storeAll_frame (fun c hc d' hd' => hap c hc d' (List.mem_cons_of_mem _ hd'))
      fun c hc => (Cell.holds_store_apart (hap c hc d (List.mem_cons_self ..))).2 (h c hc)

/-- **A block step in context**: `P ++ D ++ Q` holds and is separated with the fresh cells `X`;
the stores turn `D` into `D'` and go to slots of `D ++ X`. Then `P ++ D' ++ Q` holds after them. -/
theorem Frag.holds_block_step {v : MemView} {P D Q D' X st : Frag}
    (hS : Frag.Sep (P ++ D ++ Q ++ X)) (hf : (P ++ D ++ Q).Holds v) (hD' : D'.Holds (v.storeAll st))
    (hslot : ∀ d ∈ st, ∃ e ∈ D ++ X, e.addr = d.addr ∧ e.width = d.width) :
    (P ++ D' ++ Q).Holds (v.storeAll st) := by
  have hS1 : Frag.Sep (P ++ (D ++ (Q ++ X))) := by simpa only [List.append_assoc] using hS
  have hS2 : Frag.Sep ((P ++ D) ++ (Q ++ X)) := by simpa only [List.append_assoc] using hS
  have hQX := (Frag.sep_append.1 hS2).2.1
  have hP : (∀ c ∈ P, ∀ d ∈ st, c.Apart d) := by
    intro c hc d hd
    obtain ⟨e, he, h1, h2⟩ := hslot d hd
    refine ((Frag.sep_append.1 hS1).2.2 c hc e ?_).of_eq rfl rfl h1.symm h2.symm
    rcases List.mem_append.1 he with he | he
    · exact List.mem_append_left _ he
    · exact List.mem_append_right _ (List.mem_append_right _ he)
  have hQ : (∀ c ∈ Q, ∀ d ∈ st, c.Apart d) := by
    intro c hc d hd
    obtain ⟨e, he, h1, h2⟩ := hslot d hd
    rcases List.mem_append.1 he with he | he
    · exact ((Frag.sep_append.1 hS2).2.2 e (List.mem_append_right _ he) c
        (List.mem_append_left _ hc)).symm.of_eq rfl rfl h1.symm h2.symm
    · exact ((Frag.sep_append.1 hQX).2.2 c hc e he).of_eq rfl rfl h1.symm h2.symm
  have hPs := Frag.holds_storeAll_frame hP fun c hc => hf c (by simp [hc])
  have hQs := Frag.holds_storeAll_frame hQ fun c hc => hf c (by simp [hc])
  intro c hc
  simp only [List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · exact hPs c hc
  · exact hD' c hc
  · exact hQs c hc

/-- Cells whose bytes are disjoint are apart. -/
theorem Cell.apart_of_bytes {c d : Cell}
    (h : ∀ a ∈ List.range' c.addr c.width, a ∉ List.range' d.addr d.width) : c.Apart d :=
  fun a h1 h2 h3 h4 => h a (List.mem_range'.2 ⟨a - c.addr, by omega, by omega⟩)
    (List.mem_range'.2 ⟨a - d.addr, by omega, by omega⟩)

end Silmaril.Data

namespace Silmaril.Data.SepList

open Silmaril.Data

theorem node_bytes (K : Links) (x : Nat) :
    (K.node x 0 0).bytes = List.range' (x + K.fd) K.ws ++ List.range' (x + K.bk) K.ws := by
  simp [Links.node, Frag.bytes]

theorem dseg_bytes (K : Links) : ∀ (p : Nat) (l : List Nat) (n : Nat),
    (dseg K p l n).bytes = (K.slots l).bytes
  | _, [], _ => rfl
  | p, x :: xs, n => by
    rw [slots_cons, Frag.bytes_append, node_bytes]
    show Frag.bytes (_ :: _ :: dseg K x xs n) = _
    rw [Frag.bytes_cons, Frag.bytes_cons, dseg_bytes K x xs n, List.append_assoc]

/-- **A `dll`'s bytes are its nodes' slots' bytes** (sentinel first). -/
theorem dll_bytes (K : Links) (s : Nat) (l : List Nat) :
    (dll K s l).bytes = (K.slots (s :: l)).bytes := by
  rw [slots_cons, Frag.bytes_append, node_bytes]
  show Frag.bytes (_ :: _ :: dseg K s l s) = _
  rw [Frag.bytes_cons, Frag.bytes_cons, dseg_bytes, List.append_assoc]

end Silmaril.Data.SepList
