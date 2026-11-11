module

public import Silmaril.Wasm.Tools.Wast.Lex.Defs
public import Silmaril.Wasm.Tools.Wast.Syntax.Thms
import Silmaril.Proofs.Wasm.Tools.Wast.LexAppend
import Silmaril.Proofs.Wasm.Tools.Wast.Blank

/-!
# `.wast` reading: soundness for the WAT lexical grammar

`read` returns positioned trees only when their erasure is what silmaril-lean's executable
WAT lexer and bracketer (`Wat.sexpWatFullExec?`, sound by `Wat.sexpWat_of_fullExec`)
produce, on the input itself or, when that lexer cannot read some annotation payload, on
the input with its annotations blanked (`blankAnnots`). So the S-expressions every
subcommand works on are, provably, a parse of the text by the formal lexical grammar
`Wat.sexpWat .core3` (Core 3.0 profile):

* `read_sound`: `read s = .ok (ps, true) → sexpWat3 s (doc (ps.map erase))`;
* `read_sound_blanked`: the same for the annotation-blanked text when the flag is `false`;
* `read_script_sound`: with the script reader, the text spells `doc sc.toSExps`, the print
  of the script (`Silmaril.Wasm.Tools.Wast.Script.print_read`).

* `chunkCheck_sound` (in `Silmaril.Proofs.Wasm.Tools.Wast.LexAppend`, from the concatenation lemma
  `sexpWat_append`: the grammar is closed under concatenation after a line feed): the
  chunk-by-chunk check that `read` runs first is sound, so both theorems above cover it;
* `blankAnnots_only_annotations`: `blankAnnots` keeps the size, and every byte it changes
  becomes a space, was not a line break, and lies in a range that starts with `(@` and that
  the annotation scanner `annotEnd` closes.

Not proved: that every range `annotEnd` accepts is an annotation of the grammar
(`SpaceItem.annot`: a balanced token sequence), so that the blanked text and the text spell
the same document; and the byte positions of `PNode` (they only feed `line` numbers and
module source slices, which are tested).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast

open Silmaril.Formats Silmaril.Formats.SExpEncoding

theorem PNode.eraseList_eq (xs : List PNode) : PNode.eraseList xs = listOf (xs.map PNode.erase) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [PNode.eraseList, ih, listOf]

/-- The whole-text check is sound. -/
theorem readCheck_true {xs : List PNode} {s : String} (h : readCheck xs s = some true) :
    Wat.sexpWat .core3 s (doc (xs.map PNode.erase)) := by
  unfold readCheck at h
  split at h
  · rename_i heq
    have hw := Wat.sexpWat_of_fullExec heq
    rwa [PNode.eraseList_eq] at hw
  · split at h
    · split at h <;> simp at h
    · simp at h

theorem readCheck_false {xs : List PNode} {s : String} (h : readCheck xs s = some false) :
    ∃ s', String.fromUTF8? (blankAnnots s.toUTF8) = some s' ∧
      Wat.sexpWat .core3 s' (doc (xs.map PNode.erase)) := by
  unfold readCheck at h
  split at h
  · simp at h
  · split at h
    · rename_i s' hs'
      split at h
      · rename_i heq
        have hw := Wat.sexpWat_of_fullExec heq
        rw [PNode.eraseList_eq] at hw
        exact ⟨s', hs', hw⟩
      · simp at h
    · simp at h

/-- The chunked check is sound (`LexAppend.chunkCheck_sound`). -/
theorem readChunked_sound {b : ByteArray} {s : String} {xs ps : List PNode}
    (h : readChunked b s xs = some ps) : Wat.sexpWat .core3 s (doc (ps.map PNode.erase)) := by
  unfold readChunked at h
  split at h
  · split at h
    · cases h
      exact LexAppend.chunkCheck_sound (by assumption)
    · simp at h
  · simp at h

theorem readWhole_true {s : String} {xs ps : List PNode}
    (h : read.readWhole s xs = .ok (ps, true)) : Wat.sexpWat .core3 s (doc (ps.map PNode.erase)) := by
  unfold read.readWhole at h
  split at h
  · rename_i flag hflag
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact readCheck_true hflag
  · split at h <;> simp at h

theorem readWhole_false {s : String} {xs ps : List PNode}
    (h : read.readWhole s xs = .ok (ps, false)) :
    ∃ s', String.fromUTF8? (blankAnnots s.toUTF8) = some s' ∧
      Wat.sexpWat .core3 s' (doc (ps.map PNode.erase)) := by
  unfold read.readWhole at h
  split at h
  · rename_i flag hflag
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact readCheck_false hflag
  · split at h <;> simp at h

theorem readBlanked_true {s : String} {xs ps : List PNode}
    (h : read.readBlanked s xs = .ok (ps, true)) : Wat.sexpWat .core3 s (doc (ps.map PNode.erase)) := by
  unfold read.readBlanked at h
  split at h
  · simp at h
  · exact readWhole_true h

theorem readBlanked_false {s : String} {xs ps : List PNode}
    (h : read.readBlanked s xs = .ok (ps, false)) :
    ∃ s', String.fromUTF8? (blankAnnots s.toUTF8) = some s' ∧
      Wat.sexpWat .core3 s' (doc (ps.map PNode.erase)) := by
  unfold read.readBlanked at h
  split at h
  · rename_i ps' hb
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨s', hs', hc⟩ := Option.bind_eq_some_iff.1 hb
    exact ⟨s', hs', readChunked_sound hc⟩
  · exact readWhole_false h

/-- **Soundness of reading**, checked branch. -/
theorem read_sound {s : String} {ps : List PNode} (h : read s = .ok (ps, true)) :
    Wat.sexpWat .core3 s (doc (ps.map PNode.erase)) := by
  unfold read at h
  split at h
  · simp at h
  · unfold read.readFrom at h
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact readChunked_sound (by assumption)
    · exact readBlanked_true h

/-- **Soundness of reading**, annotation-blanked branch. -/
theorem read_sound_blanked {s : String} {ps : List PNode} (h : read s = .ok (ps, false)) :
    ∃ s', String.fromUTF8? (blankAnnots s.toUTF8) = some s' ∧
      Wat.sexpWat .core3 s' (doc (ps.map PNode.erase)) := by
  unfold read at h
  split at h
  · simp at h
  · unfold read.readFrom at h
    split at h
    · simp at h
    · exact readBlanked_false h

/-- **A script read from text is spelled by the text**: the input is a parse, by the WAT
lexical grammar, of the print of the script. -/
theorem read_script_sound {s : String} {ps : List PNode} {sc : Script}
    (h : read s = .ok (ps, true)) (hs : Script.ofSExps? (ps.map PNode.erase) = some sc) :
    sc.toSExps = ps.map PNode.erase ∧ Wat.sexpWat .core3 s (doc sc.toSExps) := by
  have hp : sc.toSExps = ps.map PNode.erase := Script.print_read hs
  exact ⟨hp, hp ▸ read_sound h⟩

/-- **`blankAnnots` blanks only (scanner-recognized) annotations**, keeping line breaks. -/
theorem blankAnnots_only_annotations (s : ByteArray) :
    (blankAnnots s).size = s.size ∧ ∀ k, (blankAnnots s).get! k = s.get! k ∨
      ((blankAnnots s).get! k = 32 ∧ s.get! k ≠ 10 ∧ s.get! k ≠ 13 ∧
        ∃ i j, i ≤ k ∧ k < j ∧ byteAt s i = 40 ∧ byteAt s (i + 1) = 64 ∧
          annotEnd s i (s.size + 1) 1 (i + 2) = .ok j) :=
  blankAnnots_blanked s

end Silmaril.Wasm.Tools.Wast
