module

public import Silmaril.Elf.Facts.Defs

/-! # Facts: uniqueness, frame, compound

PROVED (no `sorry`, no new axiom):

* `parses_unique`: a file has at most one parse;
* `Lookup.unique`, `SymbolAt.unique`: facts are functions of the file;
* `lookup_frame`, `symbolAt_frame`, `needed_frame`, `relocs_frame`: every AST-level fact holds of
  `G` as soon as `G` parses to the same AST as `F` (with `Task.parse_frame`, whatever its code
  bytes);
* `binds_iff`, `Binds.lookup`, `Binds.code`: `Binds` is the conjunction of a lookup fact and
  a contents fact;
* `lookup_of_index`: a lookup fact from the index, given `Task.index_lookup_sound` and
  `Task.gnu_eq_scan` (the index builder's theorems).
-/

@[expose] public section

namespace Silmaril.Elf

open Silmaril.X86.Link (Blob)

theorem parses_unique {F : Blob} {A B : File} (hA : Parses F A) (hB : Parses F B) : A = B :=
  Option.some.inj (hA.symm.trans hB)

theorem Lookup.unique {F : Blob} {sel : Sel} {d e : Option Def}
    (h₁ : Lookup F sel d) (h₂ : Lookup F sel e) : d = e := by
  obtain ⟨A, hA, hd⟩ := h₁
  obtain ⟨B, hB, he⟩ := h₂
  cases parses_unique hA hB
  exact Option.some.inj (hd.symm.trans he)

theorem SymbolAt.unique {F : Blob} {t : Table} {i : Nat} {s s' : Silmaril.Formats.ELF.ObjectSymbol}
    (h₁ : SymbolAt F t i s) (h₂ : SymbolAt F t i s') : s = s' := by
  obtain ⟨A, hA, hs⟩ := h₁
  obtain ⟨B, hB, hs'⟩ := h₂
  cases parses_unique hA hB
  exact Option.some.inj (hs.symm.trans hs')

/-- **Lookup frame**: a lookup fact depends only on the parse. -/
theorem lookup_frame {F G : Blob} {A : File} (hF : Parses F A) (hG : Parses G A)
    {sel : Sel} {d : Option Def} : Lookup F sel d ↔ Lookup G sel d := by
  constructor
  · rintro ⟨B, hB, h⟩; cases parses_unique hF hB; exact ⟨A, hG, h⟩
  · rintro ⟨B, hB, h⟩; cases parses_unique hG hB; exact ⟨A, hF, h⟩

theorem symbolAt_frame {F G : Blob} {A : File} (hF : Parses F A) (hG : Parses G A)
    {t : Table} {i : Nat} {s : Silmaril.Formats.ELF.ObjectSymbol} :
    SymbolAt F t i s ↔ SymbolAt G t i s := by
  constructor
  · rintro ⟨B, hB, h⟩; cases parses_unique hF hB; exact ⟨A, hG, h⟩
  · rintro ⟨B, hB, h⟩; cases parses_unique hG hB; exact ⟨A, hF, h⟩

theorem needed_frame {F G : Blob} {A : File} (hF : Parses F A) (hG : Parses G A)
    {ns : List Silmaril.Formats.ELF.NameBytes} : Needed F ns ↔ Needed G ns := by
  constructor
  · rintro ⟨B, hB, h⟩; cases parses_unique hF hB; exact ⟨A, hG, h⟩
  · rintro ⟨B, hB, h⟩; cases parses_unique hG hB; exact ⟨A, hF, h⟩

theorem relocs_frame {F G : Blob} {A : File} (hF : Parses F A) (hG : Parses G A)
    {sel : File.RelocSel} {rs : List File.Reloc} : Relocs F sel rs ↔ Relocs G sel rs := by
  constructor
  · rintro ⟨B, hB, h⟩; cases parses_unique hF hB; exact ⟨A, hG, h⟩
  · rintro ⟨B, hB, h⟩; cases parses_unique hG hB; exact ⟨A, hF, h⟩

/-- **Lookup never depends on code bytes** (given the parse builder's `Task.parse_frame`). -/
theorem lookup_code_frame (frame : Task.parse_frame) {F G : Blob} {A : File} (hF : Parses F A)
    (hav : AvoidsCode F A) (hlen : F.len = G.len)
    (hout : ∀ o w, (∀ s ∈ A.codeSpans, s.off + s.len ≤ o ∨ o + w ≤ s.off) →
      Silmaril.Elf.Link.DynElf.blobRead F o w = Silmaril.Elf.Link.DynElf.blobRead G o w)
    {sel : Sel} {d : Option Def} : Lookup F sel d ↔ Lookup G sel d :=
  lookup_frame hF (frame F G A hF hav hlen hout)

theorem binds_iff {F : Blob} {sel : Sel} {v : Nat} {code : List (BitVec 8)} :
    Binds F sel v code ↔
      (∃ d, Lookup F sel (some d) ∧ d.value = v ∧ d.ifunc = false ∧ d.abs = false) ∧
        CodeAt F v code := Iff.rfl

theorem Binds.lookup {F : Blob} {sel : Sel} {v : Nat} {code : List (BitVec 8)}
    (h : Binds F sel v code) :
    ∃ d, Lookup F sel (some d) ∧ d.value = v ∧ d.ifunc = false ∧ d.abs = false := h.1

theorem Binds.code {F : Blob} {sel : Sel} {v : Nat} {code : List (BitVec 8)}
    (h : Binds F sel v code) : CodeAt F v code := h.2

/-- **A dynamic lookup fact from the index**: on a well-formed hash table, what the index
answers is what ld.so's walk finds (excluding `SHN_ABS`, as `Sel.dyn` does). -/
theorem lookup_of_index (hix : Task.index_lookup_sound) (hgs : Task.gnu_eq_scan)
    {F : Blob} {A : File} {ix : Index} (hF : Parses F A) (hok : A.GnuHashOk)
    (hb : Index.build A = some ix) {r : Ref} {d : Def}
    (hl : ix.lookup r false = some (some d)) (habs : d.abs = false) :
    Lookup F (.dyn r) (some d) := by
  refine ⟨A, hF, ?_⟩
  have h1 := hix A ix hb r false
  rw [hl, ← hgs A hok r false] at h1
  have h2 : A.lookupDef r false = some (some d) := by
    unfold File.lookupDef; exact h1.symm
  simp [File.select, File.selectDyn, h2, habs]

end Silmaril.Elf
