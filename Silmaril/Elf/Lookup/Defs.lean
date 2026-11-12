module

public import Silmaril.Elf.Ast.Defs
public import Silmaril.X86.Link.Blob.Defs

/-! # Lookup semantics over the AST (the specification)

What a name **denotes** in a file, as functions of its metadata `File` only (never of its code
bytes; hence the frame theorem `Facts.lookup_frame`).

* **ld.so's dynamic lookup** in one object, `File.lookupDef`: glibc 2.39 `do_lookup_x` with
  `check_match` (`File.checkMatch`) over the GNU hash table (`File.gnuLookup`). It is the same
  algorithm as the reading program `Silmaril.Elf.Link.DynElf.Elf.lookupDef` (which reads the
  bytes through `DT_*` addresses), stated on the typed tables instead; the two agree on a file
  whose section and loader views agree (`DynConsistent`).
  As there, an unversioned reference meeting a non-default versioned definition (glibc's
  `num_versions` fallback) has no answer (`none`), so nothing is claimed about it.
* **The declarative lookup** `File.scanLookup`: the first hashed symbol (`i ≥ symoffset`) that
  `check_match` accepts. On a well-formed GNU hash table (`GnuHashOk`) the hash walk computes it
  (`Task.gnu_eq_scan`); the kernel-friendly index (`Silmaril.Elf.Index`) is proved against it.
* **Static selection** `File.symtabFind`: the first defined global or weak `STT_FUNC` or
  `STT_GNU_IFUNC` symbol of `.symtab` with the name (as `ElfBind.Elf.symtabFind`).
* **Selectors** `Sel` (as `ElfBind.Sel`): `.dyn r`, `.sym n`, `.fn r` (dynamic lookup if the
  file is dynamic, else static), and `File.select`.
* **Relocations** `File.relocs`: the relocations of the allocated (`SHF_ALLOC`) RELA, REL and
  RELR sections (what ld.so applies; RELR expanded), and of the non-allocated ones targeting a
  section (what a static linker applies), as one record type `Reloc`.

Scope (several objects, search order, interposition) is the loader's (`Dyn.Loader.resolveFrom`):
one object's lookup is the unit it is built from.
-/

@[expose] public section

namespace Silmaril.Elf

open Silmaril.Formats.ELF (Symbol Rela NameBytes ObjectSymbol)

/-! ## References, definitions, selectors -/

/-- A requested version, as `RESOLVE_MAP` passes it: name, ELF hash (`vna_hash`), hidden bit. -/
structure Ver where
  name : NameBytes
  hash : Nat
  hidden : Bool
  deriving DecidableEq, Repr

/-- A symbol reference: name, `STB_WEAK`, requested version. -/
structure Ref where
  name : NameBytes
  weak : Bool := false
  ver : Option Ver := none
  deriving DecidableEq, Repr

/-- A definition found by a lookup: the symbol's table index, `st_value`, `st_size`,
`STT_GNU_IFUNC`, `SHN_ABS`. -/
structure Def where
  index : Nat
  value : Nat
  size : Nat
  ifunc : Bool
  abs : Bool
  deriving DecidableEq, Repr

/-- How a function is found in a file (as `ElfBind.Sel`). -/
inductive Sel where
  /-- ld.so's lookup in `.dynsym`. -/
  | dyn (ref : Ref)
  /-- A defined global or weak function of `.symtab`. -/
  | sym (name : NameBytes)
  /-- `.dyn` if the file has `PT_DYNAMIC` and the lookup finds it, else `.sym`. -/
  | fn (ref : Ref)
  deriving DecidableEq, Repr

/-- The GNU hash of a name (`dl_new_hash`). -/
def gnuHashOf (s : NameBytes) : Nat := s.foldl (fun h c => (h * 33 + c.toNat) % 2 ^ 32) 5381

/-- The first index of `is` that `p` accepts; `none` when `p` has no answer before it. -/
def firstMatch (p : Nat → Option Bool) : List Nat → Option (Option Nat)
  | [] => some none
  | i :: is => do if ← p i then pure (some i) else firstMatch p is

namespace File

/-- `l_versions[ndx]` of a defining object: the hash and name of the non-base version
definition with index `ndx` (as `_dl_check_map_versions`; `DynElf.Elf.verdefAt`). -/
def verdefOf (A : File) (ndx : Nat) : Option (Nat × NameBytes) :=
  (A.verdefs.find? fun d => d.ndx % 0x8000 == ndx && d.flags % 2 == 0).bind fun d =>
    d.names.head?.map (d.hash, ·)

/-- **glibc's `check_match`** for `.dynsym` entry `i` (`plt`: a PLT reference). -/
def checkMatch (A : File) (r : Ref) (plt : Bool) (i : Nat) : Option Bool := do
  let s ← A.dynsyms[i]?
  let raw := s.raw
  if (raw.value = 0 ∧ raw.sectionIndex ≠ 0xfff1 ∧ raw.kind ≠ 6) ∨ (plt ∧ raw.sectionIndex = 0) then
    return false
  if raw.kind ∉ [0, 1, 2, 5, 6, 10] then return false
  if s.name ≠ r.name then return false
  match A.versyms with
  | none => return true
  | some vs =>
    let ndx ← vs[i]?
    match r.ver with
    | some v =>
      let vd := A.verdefOf (ndx % 0x8000)
      let same := match vd with
        | some (h, n) => h == v.hash && n == v.name
        | none => false
      let dh := match vd with
        | some (h, _) => h
        | none => 0
      if !same ∧ (v.hidden ∨ dh ≠ 0 ∨ ndx / 0x8000 % 2 = 1) then return false
      return true
    | none => if 3 ≤ ndx % 0x8000 then none else return true

/-- Walk a GNU hash chain from symbol `i` (as `DynElf.Elf.chainWalk`). -/
def chainWalk (A : File) (g : GnuHash) (r : Ref) (plt : Bool) (h : Nat) :
    Nat → Nat → Option (Option Nat)
  | 0, _ => none
  | fuel + 1, i => do
    let hv ← g.chain[i - g.symoffset]?
    if (hv ^^^ h) >>> 1 = 0 then
      if ← A.checkMatch r plt i then return some i
    if hv % 2 = 1 then return none
    A.chainWalk g r plt h fuel (i + 1)

/-- **ld.so's GNU-hash lookup in one object** (`do_lookup_x`; `DynElf.Elf.lookupIn`). -/
def gnuLookup (A : File) (r : Ref) (plt : Bool) : Option (Option Nat) := do
  let g ← A.gnuHashTab
  let bsz := g.bloom.length
  guard (0 < g.nbuckets ∧ 0 < bsz)
  let h := gnuHashOf r.name
  let word ← g.bloom[(h / 64) &&& (bsz - 1)]?
  if (word >>> (h % 64)) &&& (word >>> ((h >>> g.bloomShift) % 64)) &&& 1 = 0 then return none
  let bucket ← g.buckets[h % g.nbuckets]?
  if bucket = 0 then return none
  guard (g.symoffset ≤ bucket)
  A.chainWalk g r plt h (A.dynsyms.length + 1) bucket

/-- **The declarative lookup**: the first hashed symbol `check_match` accepts. -/
def scanLookup (A : File) (r : Ref) (plt : Bool) : Option (Option Nat) := do
  let g ← A.gnuHashTab
  firstMatch (A.checkMatch r plt) (List.range' g.symoffset (A.dynsyms.length - g.symoffset))

/-- The definition at `.dynsym` index `i`, if it is one (`STB_GLOBAL` or `STB_WEAK`). -/
def defAt (A : File) (i : Nat) : Option Def := do
  let s ← A.dynsyms[i]?
  guard (s.raw.binding = 1 ∨ s.raw.binding = 2)
  pure ⟨i, s.raw.value, s.raw.size, s.raw.kind == 10, s.raw.sectionIndex == 0xfff1⟩

/-- **The definition ld.so's lookup finds in `A`** (`DynElf.Elf.lookupDef`). -/
def lookupDef (A : File) (r : Ref) (plt : Bool) : Option (Option Def) := do
  match ← A.gnuLookup r plt with
  | none => pure none
  | some i => some <$> A.defAt i

/-- The definition `.symtab` entry `i` (symbol `s`) provides, if it is a defined (`st_shndx ≠ 0`)
global or weak (`STB_GLOBAL`, `STB_WEAK`) `STT_FUNC` or `STT_GNU_IFUNC` symbol. -/
def funcDef (si : ObjectSymbol × Nat) : Option Def :=
  if si.1.raw.sectionIndex ≠ 0 ∧ (si.1.raw.binding = 1 ∨ si.1.raw.binding = 2) ∧
      (si.1.raw.kind = 2 ∨ si.1.raw.kind = 10) then
    some ⟨si.2, si.1.raw.value, si.1.raw.size, si.1.raw.kind == 10, si.1.raw.sectionIndex == 0xfff1⟩
  else none

/-- **Static selection**: the first defined global or weak function named `n` in `.symtab`;
`none` without a `.symtab` (as `ElfBind.Elf.symtabFind`). -/
def symtabFind (A : File) (n : NameBytes) : Option (Option Def) := do
  let _ ← A.sectionOfType SHT_SYMTAB
  pure <| (A.symbols .symtab).zipIdx.findSome? fun si => if si.1.name = n then funcDef si else none

/-- `A` has a `PT_DYNAMIC` segment. -/
def isDynamic (A : File) : Bool := A.phdrs.any (·.kind == PT_DYNAMIC)

/-- The dynamic selection: `lookupDef`, excluding `SHN_ABS` definitions as `ElfBind.findDyn`
does. -/
def selectDyn (A : File) (r : Ref) : Option (Option Def) :=
  (A.lookupDef r false).map fun d => d.bind fun d => if d.abs then none else some d

/-- **The definition a selector denotes** (`ElfBind.Sel.find`). -/
def select (A : File) : Sel → Option (Option Def)
  | .dyn r => A.selectDyn r
  | .sym n => A.symtabFind n
  | .fn r => do
    let x ← if A.isDynamic then A.selectDyn r else pure none
    match x with
    | some d => pure (some d)
    | none => A.symtabFind r.name

/-! ## Agreement of the two views, well-formed hash tables -/

/-- The section of type `t` is at the file offset the dynamic tag `d` names. -/
def tagAt (A : File) (d t : Nat) : Prop :=
  match A.dynTag d, A.sectionOfType t with
  | none, none => True
  | some v, some (_, s) => A.vToOff v = some s.header.offset
  | _, _ => False

/-- **The section view and the loader's view agree** on every table the lookup and the
relocations read: `DT_SYMTAB`/`.dynsym`, `DT_STRTAB` is `.dynsym`'s string table,
`DT_GNU_HASH`, `DT_VERSYM`, `DT_VERDEF`, `DT_VERNEED`; and the `.dynamic` section holds the
`PT_DYNAMIC` entries. Decidable; checked per file. -/
def DynConsistent (A : File) : Prop :=
  A.tagAt 6 SHT_DYNSYM ∧ A.tagAt 0x6ffffef5 SHT_GNU_HASH ∧ A.tagAt 0x6ffffff0 SHT_GNU_versym ∧
    A.tagAt 0x6ffffffc SHT_GNU_verdef ∧ A.tagAt 0x6ffffffe SHT_GNU_verneed ∧
    (match A.sectionOfType SHT_DYNSYM, A.dynTag 5 with
      | some (_, s), some v => ∃ t ∈ A.sections[s.header.link]?, A.vToOff v = some t.header.offset
      | none, _ => True
      | _, none => False) ∧
    (match A.bodyOf SHT_DYNAMIC with
      | some (Body.dynamic es) => A.dynamic <+: es
      | _ => A.dynamic = [])

/-- The Bloom filter of `g` answers yes for the hash `h` (as `do_lookup_x` tests it). -/
def _root_.Silmaril.Elf.GnuHash.bloomYes (g : GnuHash) (h : Nat) : Bool :=
  match g.bloom[(h / 64) &&& (g.bloom.length - 1)]? with
  | some w => (w >>> (h % 64)) &&& (w >>> ((h >>> g.bloomShift) % 64)) &&& 1 == 1
  | none => false

/-- The per-symbol part of `GnuHash.wf`, one pass over the hashed symbols `ss` (from index `i`)
and their chain values `cs`, in a run started at `st`: each chain value is the symbol's hash
(bit 0 aside), the bucket of that hash is the start of the current run, and the Bloom filter
answers yes for it. A chain value with bit 0 set ends the run. -/
def _root_.Silmaril.Elf.GnuHash.runsOk (g : GnuHash) : Nat → Nat → List ObjectSymbol → List Nat → Bool
  | st, i, s :: ss, hv :: cs =>
    hv >>> 1 == gnuHashOf s.name >>> 1 &&
      g.buckets[gnuHashOf s.name % g.nbuckets]? == some st && g.bloomYes (gnuHashOf s.name) &&
      g.runsOk (if hv % 2 == 1 then i + 1 else st) (i + 1) ss cs
  | _, _, _, _ => true

/-- **A well-formed GNU hash table for the symbols `syms`**, checked in one linear pass:
`symoffset > 0` (bucket `0` means empty), `nbuckets` buckets (at least one), a non-empty Bloom
filter, every bucket `0` or a hashed symbol, one chain value per hashed symbol, the last run
ended (bit 0 of the last chain value set), and `runsOk`: the hashed symbols are grouped in runs,
one per bucket, as `ld` lays them out. -/
def _root_.Silmaril.Elf.GnuHash.wf (g : GnuHash) (syms : List ObjectSymbol) : Bool :=
  decide (0 < g.symoffset) && decide (0 < g.nbuckets) && decide (0 < g.bloom.length) &&
  g.buckets.length == g.nbuckets && g.symoffset + g.chain.length == syms.length &&
  g.buckets.all (fun b => b == 0 || decide (g.symoffset ≤ b ∧ b < syms.length)) &&
  (match g.chain.getLast? with
    | some hv => hv % 2 == 1
    | none => true) &&
  g.runsOk g.symoffset g.symoffset (syms.drop g.symoffset) g.chain

/-- **A well-formed GNU hash table** (`GnuHash.wf`; decidable). Under it `gnuLookup =
scanLookup` (`gnuLookup_eq_scanLookup`, `Silmaril.Elf.Lookup.Thms`). -/
def GnuHashOk (A : File) : Prop :=
  ∃ g, A.gnuHashTab = some g ∧ g.wf A.dynsyms = true

instance (A : File) : Decidable A.GnuHashOk :=
  match h : A.gnuHashTab with
  | none => isFalse fun ⟨_, hg, _⟩ => by rw [h] at hg; cases hg
  | some g =>
    if hw : g.wf A.dynsyms = true then isTrue ⟨g, h, hw⟩
    else isFalse fun ⟨g', hg, hw'⟩ => hw (by rw [h] at hg; cases hg; exact hw')

/-! ## Relocations -/

/-- **A relocation**, whatever its table: the place (`r_offset`), the type, the symbol index,
the addend (`none`: implicit, the word at the place), and the section it was read from. -/
structure Reloc where
  offset : Nat
  kind : Nat
  symbol : Nat
  addend : Option Int
  source : Nat
  deriving DecidableEq, Repr

/-- `R_X86_64_RELATIVE`, the type of an expanded RELR entry. -/
def R_X86_64_RELATIVE := 8

/-- Expand RELR words (`where`: the next place; `fuel`: the words left). -/
def relrExpand (src : Nat) : List Nat → Nat → List Reloc
  | [], _ => []
  | w :: ws, place =>
    if w % 2 = 0 then
      ⟨w, R_X86_64_RELATIVE, 0, none, src⟩ :: relrExpand src ws (w + 8)
    else
      ((List.range 63).filterMap fun b =>
        if (w >>> (b + 1)) % 2 = 1 then some ⟨place + 8 * b, R_X86_64_RELATIVE, 0, none, src⟩
        else none) ++ relrExpand src ws (place + 8 * 63)

/-- The relocations of section `i`. -/
def relocsOf (i : Nat) (s : Section) : List Reloc :=
  match s.body with
  | .relas es => es.map fun r => ⟨r.offset, r.relocationType, r.symbolIndex, some r.addend, i⟩
  | .rels es => es.map fun r => ⟨r.offset, r.relocationType, r.symbolIndex, none, i⟩
  | .relr ws => relrExpand i ws 0
  | _ => []

/-- Which relocations. -/
inductive RelocSel where
  /-- The dynamic relocations (allocated sections): what ld.so applies. -/
  | dynamic
  /-- The relocations of the non-allocated sections whose `sh_info` is section `i`: what a static
  linker applies to section `i` of a relocatable object. -/
  | forSection (i : Nat)
  deriving DecidableEq, Repr

/-- **The relocations a selector names**, in section order. -/
def relocs (A : File) : RelocSel → List Reloc
  | .dynamic => A.sections.zipIdx.flatMap fun (s, i) =>
      if s.header.flags / SHF_ALLOC % 2 = 1 then relocsOf i s else []
  | .forSection t => A.sections.zipIdx.flatMap fun (s, i) =>
      if s.header.flags / SHF_ALLOC % 2 = 0 ∧ s.header.info = t then relocsOf i s else []

end File

end Silmaril.Elf
