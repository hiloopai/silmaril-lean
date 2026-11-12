module

public import Silmaril.Elf.Facts.Thms
public import Silmaril.Proofs.Elf.Index.Sound
public import Silmaril.Proofs.Elf.Index.Frame

/-! # The lookup index: soundness and frame

PROVED (standard axioms only; the three index `Task`s are discharged):

* `index_lookup_eq_scan`, `index_lookup_eq_lookupDef`: the index lookup (a search tree over
  name keys, then `check_match` in symbol order) is the declarative scan, and on a well-formed
  hash table ld.so's `lookupDef`;
* `task_index_lookup_sound : Task.index_lookup_sound`: `Index.lookup` answers the declarative
  lookup `scanLookup` (through `defAt`);
* `task_index_symtab_sound : Task.index_symtab_sound`: `Index.symtabFind` is `File.symtabFind`;
* `task_gnu_eq_scan : Task.gnu_eq_scan`: on a well-formed GNU hash table ld.so's walk computes
  the declarative lookup (`Silmaril.Elf.Lookup.Thms`);
* `lookup_of_index'`: a `Lookup` fact from the index, with no hypothesis beyond the parse, the
  per-file check `GnuHashOk` (decidable) and the index computation;
* `lookup_of_spec`: a `Lookup` fact straight from the specification (`A.select`, which runs the
  file's own GNU hash table: no well-formedness check needed);
* frame: `File.select_frame`, `File.lookupDef_frame`, `File.symtabFind_frame`,
  `Index.build_frame` (a lookup reads only `File.LookupView`: `.dynsym`, the GNU hash table, the
  version tables, `.symtab`), and `lookup_view_frame` (the same, for the facts on two files).
-/

@[expose] public section

namespace Silmaril.Elf

open Silmaril.X86.Link (Blob)

theorem task_index_lookup_sound : Task.index_lookup_sound := Index.lookup_sound

/-- **`index_lookup_eq_scan`**: the index lookup is the declarative scan (through `defAt`). -/
theorem index_lookup_eq_scan {A : File} {ix : Index} (hb : Index.build A = some ix)
    (r : Ref) (plt : Bool) :
    ix.lookup r plt = (do
      match ← A.scanLookup r plt with
      | none => pure none
      | some i => some <$> A.defAt i) :=
  Index.lookup_sound A ix hb r plt

/-- **The index lookup is ld.so's lookup** on a well-formed hash table. -/
theorem index_lookup_eq_lookupDef {A : File} {ix : Index} (hb : Index.build A = some ix)
    (hok : A.GnuHashOk) (r : Ref) (plt : Bool) : ix.lookup r plt = A.lookupDef r plt := by
  rw [index_lookup_eq_scan hb]
  unfold File.lookupDef
  rw [gnuLookup_eq_scanLookup hok]
  rcases A.scanLookup r plt with _ | _ | i <;> rfl

theorem task_index_symtab_sound : Task.index_symtab_sound := Index.symtab_sound

theorem task_gnu_eq_scan : Task.gnu_eq_scan := fun _ hok r plt => gnuLookup_eq_scanLookup hok r plt

/-- **A dynamic lookup fact from the index**, unconditionally. -/
theorem lookup_of_index' {F : Blob} {A : File} {ix : Index} (hF : Parses F A) (hok : A.GnuHashOk)
    (hb : Index.build A = some ix) {r : Ref} {d : Def}
    (hl : ix.lookup r false = some (some d)) (habs : d.abs = false) :
    Lookup F (.dyn r) (some d) :=
  lookup_of_index task_index_lookup_sound task_gnu_eq_scan hF hok hb hl habs

/-- **A static lookup fact from the index.** -/
theorem lookup_sym_of_index {F : Blob} {A : File} {ix : Index} (hF : Parses F A)
    (hb : Index.build A = some ix) {n : Silmaril.Formats.ELF.NameBytes} {d : Option Def}
    (hl : ix.symtabFind n = some d) : Lookup F (.sym n) d :=
  ⟨A, hF, by rw [File.select, ← Index.symtab_sound A ix hb n, hl]⟩

/-- **A lookup fact from the specification**: evaluate `A.select sel` (e.g. by `decide`). -/
theorem lookup_of_spec {F : Blob} {A : File} (hF : Parses F A) {sel : Sel} {d : Option Def}
    (h : A.select sel = some d) : Lookup F sel d := ⟨A, hF, h⟩

/-- **Lookup frame (file level)**: two files whose parses have the same lookup tables have the
same lookup facts, whatever else differs (code, data, relocations, other sections). -/
theorem lookup_view_frame {F G : Blob} {A B : File} (hF : Parses F A) (hG : Parses G B)
    (h : A.LookupView = B.LookupView) {sel : Sel} {d : Option Def} :
    Lookup F sel d ↔ Lookup G sel d := by
  constructor
  · rintro ⟨A', hA', hs⟩; cases parses_unique hF hA'
    exact ⟨B, hG, by rw [← File.select_frame h]; exact hs⟩
  · rintro ⟨B', hB', hs⟩; cases parses_unique hG hB'
    exact ⟨A, hF, by rw [File.select_frame h]; exact hs⟩

end Silmaril.Elf
