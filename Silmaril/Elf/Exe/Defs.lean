module

public import Silmaril.Elf.Bridge.Defs
public import Silmaril.Elf.Shapes.Defs

/-! # Executables: the loading chain and the facts of an executable

An executable (`ET_EXEC`, PIE, static PIE; `File.kind`) is read by the same parse as any other
object (`Silmaril.Elf.Parse`). This module adds what is specific to running one:

* **The loader's writes** (`slotPositions`): the addresses the loader relation
  `Dyn.ExeLoaded` writes in the executable's image, namely the `r_offset` of every RELA entry of
  `DT_RELA` and `DT_JMPREL` and, under lazy binding, `GOT[1]` and `GOT[2]` (`DT_PLTGOT + 8`,
  `+ 16`). `NoTextRelD F lazy` says that none of them touches a read-only `PT_LOAD` (no
  `DT_TEXTREL`). It is checked by the closed Boolean `noTextRel` (`noTextRelD_of_check`), one
  `decide +kernel` on the file (or on a sparse view through `run_sparse`).
* **The loading chain** `direct call ⊑ RoLoaded ⊑ ExeLoaded ⊑ Proc`.
  `Exe.Thms` proves `ExeLoaded → RoLoaded` under `NoTextRelD` and `ElfBind.Placement`
  (`roLoaded_of_exeLoaded`).
* **Executable facts by kind** (`InterpIs`, `ExeFacts`): the program interpreter, and the
  record of an executable's kind, entry point (`Silmaril.Elf.EntryIs`), interpreter and `DT_NEEDED`
  names (each a separate API fact).

The executable's loaders stay where they are: `Dyn.Loader.ExeLoaded` (dynamic: ld.so, a trusted
transcription) and `Silmaril.Process.LPS.ELFImage` (static `ET_EXEC`, silmaril-lean); the
relations are in `Exe.Thms` and `Silmaril.Elf.Bridge`.
-/

@[expose] public section

namespace Silmaril.Elf.Exe

open Silmaril.X86.Link (Blob)
open Silmaril.Formats.ELF (NameBytes)
open Silmaril.Elf.Link.DynElf (blobRead)
open Silmaril.Elf.Link.Dyn (finfo frun)
open Silmaril.Elf.Link.ElfBind (isLoad isRo)

/-! ## The loader's writes -/

/-- **The addresses the loader writes** in the image of `f` (headers `i`): `GOT[1]` and `GOT[2]`
under lazy binding (when there is a `DT_JMPREL` table), then the `r_offset`s of `DT_RELA` and
`DT_JMPREL`. `none` when the relocation tables cannot be read (then `ExeLoaded` is false). -/
def slotPositions (lazy : Bool) (f : Blob) (i : Silmaril.Elf.Link.DynElf.Elf.DynInfo) : Option (List Nat) :=
  match frun f (Silmaril.Elf.Link.DynElf.Elf.relas i) with
  | none => none
  | some (a, j) =>
    let got := if lazy ∧ j ≠ [] then (i.tag 3).map fun p => [p + 8, p + 16] else some []
    got.map fun g => g ++ a.map (·.off) ++ j.map (·.off)

/-- The 8 bytes at `p` miss every read-only `PT_LOAD` of `phs` (its memory extent). -/
def avoidsRo (phs : List Silmaril.Elf.Link.DynElf.Elf.Phdr) (p : Nat) : Bool :=
  phs.all fun ph => !(isLoad ph && isRo ph) || decide (p + 8 ≤ ph.vaddr ∨ ph.vaddr + ph.memsz ≤ p)

/-- **No loader write touches a read-only segment** of `f` (no text relocation; with `lazy`, the
lazily written `GOT[1]`, `GOT[2]` included). Vacuous when the headers or the relocation tables
cannot be read (the loader relation is then false). -/
def NoTextRelD (f : Blob) (lazy : Bool) : Prop :=
  ∀ i, finfo f = some i → ∀ ps, slotPositions lazy f i = some ps → ∀ p ∈ ps, avoidsRo i.phs p = true

/-- **The check of `NoTextRelD`**: one closed Boolean on the file. -/
def noTextRel (f : Blob) (lazy : Bool) : Bool :=
  match finfo f with
  | none => false
  | some i => match slotPositions lazy f i with
    | none => false
    | some ps => ps.all (avoidsRo i.phs)

/-! ## Executable facts by kind -/

/-- **The program interpreter of `F` is `n`** (`PT_INTERP`; `none`: a static executable or
static PIE, or a shared object). -/
def InterpIs (F : Blob) (n : Option NameBytes) : Prop := ∃ A, Parses F A ∧ A.interp = n

/-- **`F` is an executable**: of kind `exec`, `pie` or `staticPie`. -/
def _root_.Silmaril.Elf.Kind.isExe : Kind → Bool
  | .exec | .pie | .staticPie => true
  | _ => false

/-- **The facts an executable's loading uses**, in one record: its kind, entry, interpreter and
`DT_NEEDED` names (each a separate API fact; `ExeFacts.kindIs` etc.). -/
structure ExeFacts (F : Blob) where
  kind : Kind
  entry : Nat
  interp : Option NameBytes
  needed : List NameBytes
  kindIs : KindIs F kind
  entryIs : EntryIs F entry
  interpIs : InterpIs F interp
  neededIs : Needed F needed
  isExe : kind.isExe = true

/-- **A dynamically linked executable whose loading is in the scope of `Dyn.ExeLoaded`**: a PIE
(or a dynamic `ET_EXEC`) that needs `libc.so.6` through `ld-linux-x86-64.so.2`, with no
text relocation. -/
def DynExe (F : Blob) (lazy : Bool) : Prop :=
  (KindIs F .pie ∨ KindIs F .exec) ∧ InterpIs F (some (nameOf "/lib64/ld-linux-x86-64.so.2")) ∧
    NoTextRelD F lazy

end Silmaril.Elf.Exe
