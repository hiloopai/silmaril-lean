module

public import Silmaril.Elf.Index.Defs

/-! # Lookup reads only the lookup tables

`File.LookupView A` is the part of the metadata a lookup reads: `.dynsym`, the GNU hash table,
`.gnu.version`, `.gnu.version_d`, `.symtab`, whether there is a `.symtab`, and whether there is
a `PT_DYNAMIC`. Two files with the same view have the same lookups (`select_frame`, `lookupDef_frame`,
`symtabFind_frame`) and the same index (`build_frame`). No code byte, no relocation, no other
section is read (code is not in the AST at all: a code section's body is a `Span`).
-/

public section

namespace Silmaril.Elf

open Silmaril.Formats.ELF (NameBytes ObjectSymbol)

namespace File

theorem verdefOf_frame {A B : File} (h : A.verdefs = B.verdefs) (n : Nat) :
    A.verdefOf n = B.verdefOf n := by
  simp only [verdefOf, h]

theorem checkMatch_frame {A B : File} (hd : A.dynsyms = B.dynsyms) (hv : A.versyms = B.versyms)
    (hvd : A.verdefs = B.verdefs) (r : Ref) (plt : Bool) (i : Nat) :
    A.checkMatch r plt i = B.checkMatch r plt i := by
  simp only [checkMatch, hd, hv, verdefOf_frame hvd]

theorem chainWalk_frame {A B : File} (hc : ∀ r plt i, A.checkMatch r plt i = B.checkMatch r plt i)
    (g : GnuHash) (r : Ref) (plt : Bool) (h : Nat) :
    ∀ fuel i, A.chainWalk g r plt h fuel i = B.chainWalk g r plt h fuel i
  | 0, _ => rfl
  | fuel + 1, i => by
    simp only [chainWalk, hc, chainWalk_frame hc g r plt h fuel]

end File

/-- **What a lookup reads**: `.dynsym`, the GNU hash table, `.gnu.version`, `.gnu.version_d`,
`.symtab`, whether there is a `.symtab`, and whether there is a `PT_DYNAMIC`. -/
def File.LookupView (A : File) :
    List ObjectSymbol × Option GnuHash × Option (List Nat) × List Verdef × List ObjectSymbol ×
      Bool × Bool :=
  (A.dynsyms, A.gnuHashTab, A.versyms, A.verdefs, A.symbols .symtab,
    (A.sectionOfType SHT_SYMTAB).isSome, A.isDynamic)

namespace File

variable {A B : File} (h : A.LookupView = B.LookupView)
include h

theorem lookupView_parts : A.dynsyms = B.dynsyms ∧ A.gnuHashTab = B.gnuHashTab ∧
    A.versyms = B.versyms ∧ A.verdefs = B.verdefs ∧ A.symbols .symtab = B.symbols .symtab ∧
    (A.sectionOfType SHT_SYMTAB).isSome = (B.sectionOfType SHT_SYMTAB).isSome ∧
    A.isDynamic = B.isDynamic := by
  simpa [LookupView] using h

theorem gnuLookup_frame (r : Ref) (plt : Bool) : A.gnuLookup r plt = B.gnuLookup r plt := by
  obtain ⟨hd, hg, hv, hvd, -⟩ := lookupView_parts h
  simp only [gnuLookup, hg, hd, chainWalk_frame (checkMatch_frame hd hv hvd)]

theorem scanLookup_frame (r : Ref) (plt : Bool) : A.scanLookup r plt = B.scanLookup r plt := by
  obtain ⟨hd, hg, hv, hvd, -⟩ := lookupView_parts h
  have hc : A.checkMatch r plt = B.checkMatch r plt := funext (checkMatch_frame hd hv hvd r plt)
  simp only [scanLookup, hg, hd, hc]

theorem defAt_frame (i : Nat) : A.defAt i = B.defAt i := by
  obtain ⟨hd, -⟩ := lookupView_parts h
  simp only [defAt, hd]

theorem lookupDef_frame (r : Ref) (plt : Bool) : A.lookupDef r plt = B.lookupDef r plt := by
  simp only [lookupDef, gnuLookup_frame h, defAt_frame h]

theorem symtabFind_frame (n : NameBytes) : A.symtabFind n = B.symtabFind n := by
  obtain ⟨-, -, -, -, hs, hst, -⟩ := lookupView_parts h
  unfold symtabFind
  rw [hs]
  cases ha : A.sectionOfType SHT_SYMTAB <;> cases hb : B.sectionOfType SHT_SYMTAB <;>
    simp_all

/-- **Lookup frame (AST level)**: a selector denotes the same definition in two files with the
same lookup tables. -/
theorem select_frame (sel : Sel) : A.select sel = B.select sel := by
  obtain ⟨-, -, -, -, -, -, hdy⟩ := lookupView_parts h
  cases sel <;> simp only [select, selectDyn, lookupDef_frame h, symtabFind_frame h, hdy]

end File

namespace Index

/-- **Index frame**: the index of a file is a function of its lookup tables. -/
theorem build_frame {A B : File} (h : A.LookupView = B.LookupView) : build A = build B := by
  obtain ⟨hd, hg, hv, hvd, hs, hst, -⟩ := File.lookupView_parts h
  have ho : entryOf A = entryOf B := by
    funext i s vs; simp only [entryOf, File.verdefOf_frame hvd]
  have hf : ∀ i ss vs, entriesFrom A i ss vs = entriesFrom B i ss vs := by
    intro i ss
    induction ss generalizing i with
    | nil => intro vs; rfl
    | cons s ss ih => intro vs; simp only [entriesFrom, ho, ih]
  simp only [build, hd, hg, hv, hs, hst, hf]

end Index

end Silmaril.Elf
