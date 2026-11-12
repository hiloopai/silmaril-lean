module

public import Silmaril.Elf.Parse.Defs

/-! # A fast parse checker (`Silmaril.Elf.Check.file`)

`Silmaril.Elf.read` is the specification of the parse; run by the kernel it is slow on large files,
because it reads every name byte by byte (`DynElf.Elf.cstr`: about 47 s for the 3,156 dynamic
symbol names of glibc's `libc.so.6`). `Check.file r A` checks a **claimed** parse `A` (emitted
by an emitter) against a byte source `r` (the 4 KiB pages of an included file, a
sparse view, or the whole file):

* **names** are compared as one wide read each (`nameOk`: the `len + 1` bytes at the name's
  offset are the name and a NUL, and no byte of the name is NUL), never byte by byte;
* **symbols** are read as one 24-byte record each, their fields taken by shifts (`symOk`);
* the **hash tables** and `.gnu.version` are read one word per read (`wordsOk`, `gnuOk`,
  `hashOk`), without a reading program;
* every other component (header, program and section headers, the other section bodies, the
  loader's view) is checked by **running the specification's own sub-reader** on `r` and
  comparing with the claimed value, so nothing about those parts needs a separate proof.

Soundness (`Silmaril.Elf.Check.file_sound`, in `Thms`): if `r` answers as the file (`Sub r F`: every
read `r` answers, the file answers the same) and `file r A = true`, then `Parses F A`. The
checker is a Bool function for `decide +kernel`; it never calls `parse` and never forces the
whole-file number when `r` is a page reader.

It sits beside the specification (`Silmaril.Elf.Parse`), which stays the definition.
-/

@[expose] public section

namespace Silmaril.Elf.Check

open Silmaril.Formats.ELF (Header ProgramHeader SectionHeader Symbol NameBytes ObjectSymbol)
open Silmaril.Elf.Link.DynElf (Rd leVal blobRead)
open Silmaril.X86.Link (Blob)

/-- A byte source: `r o w` is the little-endian value of the `w` bytes at `o`, if available. -/
abbrev Src := Nat → Nat → Option Nat

/-- **`r` answers as the file `F`**: every read `r` answers, `F` answers the same. -/
def Sub (r : Src) (F : Blob) : Prop := ∀ o w v, r o w = some v → blobRead F o w = some v

/-- The field of `w` bytes at byte `k` of a record read as the number `v`. -/
def fld (v k w : Nat) : Nat := (v >>> (8 * k)) % 2 ^ (8 * w)

/-- The bytes of a name and its NUL, as one little-endian number. -/
def nameVal (n : NameBytes) : Nat := leVal (n.map BitVec.toNat ++ [0])

/-- **The NUL-terminated name at `o`, within `fuel` bytes, is `n`** (as `Parse.name o fuel`): one
wide read. -/
def nameOk (r : Src) (o fuel : Nat) (n : NameBytes) : Bool :=
  decide (n.length < fuel) && n.all (fun b => b.toNat != 0) && r o (n.length + 1) == some (nameVal n)

/-- The name at offset `i` of the string table `strs` is `n` (as `Parse.strAt strs i`). -/
def strAtOk (r : Src) (strs : SectionHeader) (i : Nat) (n : NameBytes) : Bool :=
  decide (i < strs.size) && nameOk r (strs.offset + i) (strs.size - i) n

/-- The symbol at `o`, named from `strs`, is `s` (as `Parse.symbol strs o`): one 24-byte read. -/
def symOk (r : Src) (strs : SectionHeader) (o : Nat) (s : ObjectSymbol) : Bool :=
  match r o 24 with
  | none => false
  | some v =>
    s.raw.name == fld v 0 4 && s.raw.info == fld v 4 1 && s.raw.other == fld v 5 1 &&
      s.raw.sectionIndex == fld v 6 2 && s.raw.value == fld v 8 8 && s.raw.size == fld v 16 8 &&
      strAtOk r strs s.raw.name s.name

/-- Symbols `i, i + 1, …` of a table at `o` are `es`. -/
def symsOk (r : Src) (strs : SectionHeader) (o : Nat) : Nat → List ObjectSymbol → Bool
  | _, [] => true
  | i, s :: es => symOk r strs (o + 24 * i) s && symsOk r strs o (i + 1) es

/-- Words `i, i + 1, …` of width `w` of an array at `o` are `xs` (as `Parse.records o w _ (Rd.le · w)`):
one read each, no reading program. -/
def wordsOk (r : Src) (o w : Nat) : Nat → List Nat → Bool
  | _, [] => true
  | i, x :: xs => r (o + w * i) w == some x && wordsOk r o w (i + 1) xs

/-- The GNU hash table of section `sh` is `g` (as `Parse.gnuHash sh`). -/
def gnuOk (r : Src) (sh : SectionHeader) (g : GnuHash) : Bool :=
  let o := sh.offset
  let head := 16 + 8 * g.bloom.length + 4 * g.nbuckets
  r o 4 == some g.nbuckets && r (o + 4) 4 == some g.symoffset && r (o + 8) 4 == some g.bloom.length &&
    r (o + 12) 4 == some g.bloomShift && decide (head ≤ sh.size) &&
    g.buckets.length == g.nbuckets && g.chain.length == (sh.size - head) / 4 &&
    wordsOk r (o + 16) 8 0 g.bloom && wordsOk r (o + 16 + 8 * g.bloom.length) 4 0 g.buckets &&
    wordsOk r (o + head) 4 0 g.chain

/-- The SysV hash table of section `sh` is `t` (as `Parse.sysvHash sh`). -/
def hashOk (r : Src) (sh : SectionHeader) (t : SysvHash) : Bool :=
  r sh.offset 4 == some t.buckets.length && r (sh.offset + 4) 4 == some t.chains.length &&
    wordsOk r (sh.offset + 8) 4 0 t.buckets &&
    wordsOk r (sh.offset + 8 + 4 * t.buckets.length) 4 0 t.chains

/-- The table selected by a symbol-table section type. -/
def tableOf (k : Nat) : Table := if k = SHT_SYMTAB then .symtab else .dynsym

/-- **The body of section `sh` is `b`** (as `Parse.body shs sh`): symbol tables by `symsOk`,
every other body by running the specification. -/
def bodyOk (r : Src) (shs : List SectionHeader) (sh : SectionHeader) (b : Body) : Bool :=
  if sh.kind = SHT_SYMTAB ∨ sh.kind = SHT_DYNSYM then
    match b, shs[sh.link]? with
    | .symbols t es, some strs =>
      sh.entrySize == 24 && t == tableOf sh.kind && es.length == sh.size / 24 &&
        symsOk r strs sh.offset 0 es
    | _, _ => false
  else if sh.kind = SHT_GNU_HASH then
    match b with
    | .gnuHash g => gnuOk r sh g
    | _ => false
  else if sh.kind = SHT_HASH then
    match b with
    | .hash t => hashOk r sh t
    | _ => false
  else if sh.kind = SHT_GNU_versym then
    match b with
    | .versym vs => vs.length == sh.size / 2 && wordsOk r sh.offset 2 0 vs
    | _ => false
  else (Parse.body shs sh).run r == some b

/-- **The sections are `secs`** (as `Parse.sections h (secs.map (·.header))`). -/
def sectionsOk (r : Src) (h : Header) (secs : List Section) : Bool :=
  let shs := secs.map (·.header)
  if secs.isEmpty then true
  else match shs[h.sectionNameIndex]? with
    | none => false
    | some names => secs.all fun s => strAtOk r names s.header.name s.name && bodyOk r shs s.header s.body

/-- **The checker**: `A` is the parse of the bytes `r` answers (soundness: `file_sound`). -/
def file (r : Src) (A : File) : Bool :=
  let h := A.header
  let phs := A.phdrs
  let dyn := A.dynamic
  let str := Parse.dynStr phs dyn
  Parse.header.run r == some h &&
    (Parse.phdrs h).run r == some phs &&
    (Parse.shdrs h).run r == some (A.sections.map (·.header)) &&
    sectionsOk r h A.sections &&
    (Parse.dynamic phs).run r == some dyn &&
    (Parse.interp phs).run r == some A.interp &&
    (((dyn.filter (·.tag == DT_NEEDED)).map (·.val)).mapM str).run r == some A.needed &&
    (Parse.optStr str ((dyn.find? (·.tag == DT_SONAME)).map (·.val))).run r == some A.soname &&
    (Parse.optStr str (((dyn.find? (·.tag == DT_RUNPATH)).orElse fun _ =>
      dyn.find? (·.tag == DT_RPATH)).map (·.val))).run r == some A.runpath

end Silmaril.Elf.Check
