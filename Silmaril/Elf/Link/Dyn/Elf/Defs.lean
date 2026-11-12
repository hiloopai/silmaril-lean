module

public import Silmaril.X86.Link.Blob.Defs

/-! # Dynamic ELF objects, read through a byte oracle

The loader's view of an ELF64 x86-64 file (executable or shared object), read by small
**reading programs** `Rd α` (a free monad over `read offset width`), so that one soundness
theorem (`Rd.run_mono`, in `Thms`) covers every reader: a program that succeeds on a *sparse*
view of a file (a few byte ranges, `Chunk`s) succeeds with the same result on the whole file.
This is what lets a 2 MB `libc.so.6` be used through the few hundred bytes a symbol lookup
touches, without transcribing (or kernel-unfolding) the file.

Readers (all little-endian, ELF64, `e_machine = EM_X86_64`):

* `phdrs`, `dynEntries`, `DynInfo` (program headers, `PT_DYNAMIC` up to `DT_NULL`, and the
  tags a loader uses), `interp` (the `PT_INTERP` string), `needed` (`DT_NEEDED` names);
* `sym` (a `.dynsym` entry), `strIs` (a string comparison as **one** wide read), `cstr`;
* `gnuLookup`/`lookupIn`: **ld.so's GNU-hash symbol lookup** in one object, transcribed from
  glibc 2.39 `elf/dl-lookup.c` (`do_lookup_x` with `check_match`): the Bloom filter, the
  bucket, the chain walk, the symbol-type and value filters, the name comparison, and the
  version test against `l_versions` (built from `DT_VERDEF` as `_dl_check_map_versions`
  does). Two cases glibc handles that are **not modelled** make the reader fail (`Rd.fail`),
  so nothing is ever claimed about them: an unversioned reference meeting a non-default
  versioned definition (glibc's `num_versions` fallback), and an object without
  `DT_GNU_HASH`;
* `relas`, `refOf`: an object's `DT_RELA`/`DT_JMPREL` entries and, for each, the referencing
  symbol: name, binding and requested version (`DT_VERSYM` and `DT_VERNEED`, with the
  `vna_hash`/hidden bit glibc's `RESOLVE_MAP` passes on).

Nothing here is trusted except as the definition of the loader model (`Dyn.Loader`), whose
symbol resolution *is* `lookupIn` over the search scope: this file is the transcription of
ld.so's algorithm that the trust boundary names.
-/

@[expose] public section

namespace Silmaril.Elf.Link.DynElf

open Silmaril.X86.Link (Blob)

/-! ## Reading programs -/

/-- A reading program: finish, fail, or read `w` bytes (little-endian) at offset `o` and
continue with their value. -/
inductive Rd (α : Type) : Type where
  | pure : α → Rd α
  | fail : Rd α
  | read : Nat → Nat → (Nat → Rd α) → Rd α

namespace Rd

/-- Sequencing. -/
def bind {α β : Type} : Rd α → (α → Rd β) → Rd β
  | .pure a, f => f a
  | .fail, _ => .fail
  | .read o w k, f => .read o w fun v => bind (k v) f

instance : Monad Rd where
  pure := .pure
  bind := bind

/-- Run a program against a byte oracle `r o w` (`none`: not available). -/
def run {α : Type} (r : Nat → Nat → Option Nat) : Rd α → Option α
  | .pure a => some a
  | .fail => none
  | .read o w k => match r o w with
    | some v => run r (k v)
    | none => none

/-- Read `w` bytes at `o`. -/
def le (o w : Nat) : Rd Nat := .read o w .pure

/-- Continue only if `c` holds. -/
def guard (c : Prop) [Decidable c] : Rd Unit := if c then .pure () else .fail

def ofOption {α : Type} : Option α → Rd α
  | some a => .pure a
  | none => .fail

end Rd

/-! ## Byte sources -/

/-- A file as a whole (`Silmaril.X86.Link.Blob`): `Blob.readLEN`. -/
def blobRead (b : Blob) (o w : Nat) : Option Nat := Blob.readLEN b.n b.len o w

/-- A contiguous byte range of a file: `len` bytes at offset `off`, as one little-endian
number. -/
structure Chunk where
  off : Nat
  len : Nat
  n : Nat
  deriving DecidableEq, Repr

def Chunk.read (c : Chunk) (o w : Nat) : Option Nat :=
  if c.off ≤ o ∧ o + w ≤ c.off + c.len then some ((c.n >>> (8 * (o - c.off))) % 2 ^ (8 * w))
  else none

/-- A sparse view of a file: reads inside one chunk succeed, others fail. -/
def sparseRead : List Chunk → Nat → Nat → Option Nat
  | [], _, _ => none
  | c :: cs, o, w => match c.read o w with
    | some v => some v
    | none => sparseRead cs o w

/-- **The chunk is part of the file `b`**: it lies inside it and holds its bytes. -/
def Chunk.Of (b : Blob) (c : Chunk) : Prop :=
  c.off + c.len ≤ b.len ∧ c.n % 2 ^ (8 * c.len) = (b.n >>> (8 * c.off)) % 2 ^ (8 * c.len)

instance (b : Blob) (c : Chunk) : Decidable (c.Of b) := inferInstanceAs (Decidable (_ ∧ _))

/-- Every chunk is part of the file. -/
def ChunksOf (b : Blob) (cs : List Chunk) : Prop := ∀ c ∈ cs, c.Of b

/-! ## Little-endian helpers -/

/-- The little-endian value of a byte list. -/
def leVal : List Nat → Nat
  | [] => 0
  | x :: xs => x % 256 + 256 * leVal xs

/-- A name (symbol, version or library), as its bytes without the terminating NUL. -/
abbrev Name := List Nat

/-- The bytes of a string literal. -/
def nm (s : String) : Name := s.toList.map Char.toNat

-- The inner `Elf` (the loader's view of a file) repeats the region's name.
set_option linter.dupNamespace false

namespace Elf

def u8 (o : Nat) : Rd Nat := Rd.le o 1
def u16 (o : Nat) : Rd Nat := Rd.le o 2
def u32 (o : Nat) : Rd Nat := Rd.le o 4
def u64 (o : Nat) : Rd Nat := Rd.le o 8

/-- The string at `o` is `s`: the `s.length + 1` bytes there are `s` and a NUL (one read). -/
def strIs (o : Nat) (s : Name) : Rd Bool := do
  let v ← Rd.le o (s.length + 1)
  pure (v == leVal (s ++ [0]))

/-- The NUL-terminated string at `o`, at most `fuel` bytes (byte by byte). -/
def cstr (o : Nat) : Nat → Rd Name
  | 0 => .fail
  | fuel + 1 => do
    let c ← u8 o
    if c = 0 then pure [] else do
      let rest ← cstr (o + 1) fuel
      pure (c :: rest)

/-! ## Program headers and the dynamic section -/

/-- A program header (the fields a loader uses). -/
structure Phdr where
  kind : Nat
  flags : Nat
  off : Nat
  vaddr : Nat
  filesz : Nat
  memsz : Nat
  deriving DecidableEq, Repr

def phdr (o : Nat) : Rd Phdr := do
  let kind ← u32 o
  let flags ← u32 (o + 4)
  let off ← u64 (o + 8)
  let vaddr ← u64 (o + 16)
  let filesz ← u64 (o + 32)
  let memsz ← u64 (o + 40)
  pure ⟨kind, flags, off, vaddr, filesz, memsz⟩

/-- The ELF header checks (`ELFCLASS64`, `ELFDATA2LSB`, `EM_X86_64`) and the program headers. -/
def phdrs : Rd (List Phdr) := do
  Rd.guard ((← u32 0) = 0x464c457f)
  Rd.guard ((← u8 4) = 2)
  Rd.guard ((← u8 5) = 1)
  Rd.guard ((← u16 18) = 62)
  let phoff ← u64 32
  Rd.guard ((← u16 54) = 56)
  let num ← u16 56
  (List.range num).mapM fun i => phdr (phoff + 56 * i)

/-- The file offset of virtual address `v`, through the `PT_LOAD` that maps it from the file. -/
def vToOff (phs : List Phdr) (v : Nat) : Option Nat :=
  (phs.find? fun ph => ph.kind == 1 && ph.vaddr ≤ v && v < ph.vaddr + ph.filesz).map
    fun ph => v - ph.vaddr + ph.off

/-- `(d_tag, d_val)` entries from offset `o`, at most `k`, up to `DT_NULL`. -/
def dynFrom (o : Nat) : Nat → Rd (List (Nat × Nat))
  | 0 => pure []
  | k + 1 => do
    let t ← u64 o
    if t = 0 then pure [] else do
      let v ← u64 (o + 8)
      let rest ← dynFrom (o + 16) k
      pure ((t, v) :: rest)

/-- The `PT_DYNAMIC` entries. -/
def dynEntries (phs : List Phdr) : Rd (List (Nat × Nat)) := do
  let d ← Rd.ofOption (phs.find? (·.kind == 2))
  dynFrom d.off (d.filesz / 16)

/-- What the loader reads from an object before relocating it. -/
structure DynInfo where
  phs : List Phdr
  dyn : List (Nat × Nat)
  deriving DecidableEq, Repr

def dynInfo : Rd DynInfo := do
  let phs ← phdrs
  let dyn ← dynEntries phs
  pure ⟨phs, dyn⟩

/-- The value of the first dynamic entry with tag `t`. -/
def DynInfo.tag (d : DynInfo) (t : Nat) : Option Nat := (d.dyn.find? (·.1 == t)).map (·.2)

/-- The file offset of the address in tag `t`. -/
def DynInfo.tagOff (d : DynInfo) (t : Nat) : Option Nat := (d.tag t).bind (vToOff d.phs)

/-- `DT_` tags used here. -/
def DT_NEEDED := 1
def DT_PLTRELSZ := 2
def DT_STRTAB := 5
def DT_SYMTAB := 6
def DT_RELA := 7
def DT_RELASZ := 8
def DT_INIT := 12
def DT_FINI := 13
def DT_SONAME := 14
def DT_JMPREL := 23
def DT_INIT_ARRAY := 25
def DT_FINI_ARRAY := 26
def DT_INIT_ARRAYSZ := 27
def DT_FINI_ARRAYSZ := 28
def DT_FLAGS := 30
def DT_RELR := 36
def DT_GNU_HASH := 0x6ffffef5
def DT_VERSYM := 0x6ffffff0
def DT_FLAGS_1 := 0x6ffffffb
def DT_VERDEF := 0x6ffffffc
def DT_VERDEFNUM := 0x6ffffffd
def DT_VERNEED := 0x6ffffffe
def DT_VERNEEDNUM := 0x6fffffff

/-- Eager binding requested by the object: `DF_BIND_NOW` in `DT_FLAGS` or `DF_1_NOW` in
`DT_FLAGS_1`. -/
def DynInfo.bindNow (d : DynInfo) : Bool :=
  ((d.tag DT_FLAGS).getD 0) / 8 % 2 == 1 || ((d.tag DT_FLAGS_1).getD 0) % 2 == 1

/-- The `PT_INTERP` string. -/
def interp (d : DynInfo) : Rd Name := do
  let ph ← Rd.ofOption (d.phs.find? (·.kind == 3))
  cstr ph.off ph.filesz

/-- A string of `DT_STRTAB`. -/
def DynInfo.str (d : DynInfo) (i : Nat) : Rd Name := do
  let s ← Rd.ofOption (d.tagOff DT_STRTAB)
  cstr (s + i) 256

/-- The `DT_NEEDED` names, in order. -/
def needed (d : DynInfo) : Rd (List Name) :=
  ((d.dyn.filter (·.1 == DT_NEEDED)).map (·.2)).mapM d.str

/-! ## Symbols -/

/-- A `.dynsym` entry. -/
structure Sym where
  name : Nat
  info : Nat
  other : Nat
  shndx : Nat
  value : Nat
  deriving DecidableEq, Repr

def Sym.type (s : Sym) : Nat := s.info % 16
def Sym.bind (s : Sym) : Nat := s.info / 16

/-- Dynamic symbol `i`. -/
def sym (d : DynInfo) (i : Nat) : Rd Sym := do
  let t ← Rd.ofOption (d.tagOff DT_SYMTAB)
  let o := t + 24 * i
  let name ← u32 o
  let info ← u8 (o + 4)
  let other ← u8 (o + 5)
  let shndx ← u16 (o + 6)
  let value ← u64 (o + 8)
  pure ⟨name, info, other, shndx, value⟩

/-- A symbol version a reference asks for, as `RESOLVE_MAP` passes it to the lookup:
the version's name, its ELF hash (`vna_hash`) and the hidden bit (`vna_other & 0x8000`). -/
structure Ver where
  name : Name
  hash : Nat
  hidden : Bool
  deriving DecidableEq, Repr

/-- A symbol reference: the name, the binding (`STB_WEAK = 2`) and the requested version. -/
structure Ref where
  name : Name
  weak : Bool
  ver : Option Ver
  deriving DecidableEq, Repr

/-- `l_versions[ndx]` of a *defining* object, from `DT_VERDEF` (as `_dl_check_map_versions`):
the `vd_hash` and the file offset of the first `vda_name` of the non-base entry whose
`vd_ndx` is `ndx`; `none` for the base entry and the indices it does not define (their hash
is 0). `fuel` bounds the walk (`DT_VERDEFNUM`). -/
def verdefAt (d : DynInfo) (ndx : Nat) : Nat → Nat → Rd (Option (Nat × Nat))
  | 0, _ => pure none
  | fuel + 1, o => do
    let flags ← u16 (o + 2)
    let vndx ← u16 (o + 4)
    let hash ← u32 (o + 8)
    let aux ← u32 (o + 12)
    let next ← u32 (o + 16)
    if vndx % 0x8000 = ndx ∧ flags % 2 = 0 then do
      let vname ← u32 (o + aux)
      let s ← Rd.ofOption (d.tagOff DT_STRTAB)
      pure (some (hash, s + vname))
    else if next = 0 then pure none else verdefAt d ndx fuel (o + next)

/-- glibc's `check_match` for symbol `i` of an object (`plt`: the reference is a PLT
relocation, `ELF_RTYPE_CLASS_PLT`). -/
def checkMatch (d : DynInfo) (r : Ref) (plt : Bool) (i : Nat) : Rd Bool := do
  let s ← sym d i
  -- no value (and not absolute or TLS), or an undefined symbol for a PLT reference
  if (s.value = 0 ∧ s.shndx ≠ 0xfff1 ∧ s.type ≠ 6) ∨ (plt ∧ s.shndx = 0) then return false
  -- only STT_NOTYPE, OBJECT, FUNC, COMMON, TLS, GNU_IFUNC
  if s.type ∉ [0, 1, 2, 5, 6, 10] then return false
  let st ← Rd.ofOption (d.tagOff DT_STRTAB)
  if !(← strIs (st + s.name) r.name) then return false
  match d.tagOff DT_VERSYM with
  | none => return true
  | some vs =>
    let ndx ← u16 (vs + 2 * i)
    match r.ver with
    | some v =>
      -- `l_versions[ndx & 0x7fff]`: hash 0 when the index is not a non-base verdef entry
      let vd ← match d.tagOff DT_VERDEF with
        | some o => verdefAt d (ndx % 0x8000) ((d.tag DT_VERDEFNUM).getD 0) o
        | none => pure none
      let sameVersion ← match vd with
        | some (h, no) => if h = v.hash then strIs no v.name else pure false
        | none => pure false
      let dh := match vd with | some (h, _) => h | none => 0
      if !sameVersion ∧ (v.hidden ∨ dh ≠ 0 ∨ ndx / 0x8000 % 2 = 1) then return false
      return true
    | none =>
      -- a non-default version for an unversioned reference: glibc's fallback, not modelled
      if 3 ≤ ndx % 0x8000 then Rd.fail else return true

/-- The GNU hash of a name (`dl_new_hash`). -/
def gnuHash (s : Name) : Nat := s.foldl (fun h c => (h * 33 + c) % 2 ^ 32) 5381

/-- Walk a GNU hash chain from symbol `i`: entries whose hash matches go through
`checkMatch`; the walk ends at the entry with bit 0 set. -/
def chainWalk (d : DynInfo) (r : Ref) (plt : Bool) (h chain symoff : Nat) :
    Nat → Nat → Rd (Option Nat)
  | 0, _ => .fail
  | fuel + 1, i => do
    let hv ← u32 (chain + 4 * (i - symoff))
    if (hv ^^^ h) >>> 1 = 0 then
      if ← checkMatch d r plt i then return some i
    if hv % 2 = 1 then return none
    chainWalk d r plt h chain symoff fuel (i + 1)

/-- **Lookup of a reference in one object** (`do_lookup_x` for one map with a GNU hash
table): the index of the matching `.dynsym` entry, or `none`. -/
def lookupIn (d : DynInfo) (r : Ref) (plt : Bool) : Rd (Option Nat) := do
  let gh ← Rd.ofOption (d.tagOff DT_GNU_HASH)
  let nb ← u32 gh
  let symoff ← u32 (gh + 4)
  let bsz ← u32 (gh + 8)
  let shift ← u32 (gh + 12)
  Rd.guard (0 < nb ∧ 0 < bsz)
  let h := gnuHash r.name
  let word ← u64 (gh + 16 + 8 * ((h / 64) &&& (bsz - 1)))
  if (word >>> (h % 64)) &&& (word >>> ((h >>> shift) % 64)) &&& 1 = 0 then return none
  let bucket ← u32 (gh + 16 + 8 * bsz + 4 * (h % nb))
  if bucket = 0 then return none
  Rd.guard (symoff ≤ bucket)
  chainWalk d r plt h (gh + 16 + 8 * bsz + 4 * nb) symoff 100000 bucket

/-- A defining symbol found by `lookupIn`, with what relocation needs: `st_value`,
`STT_GNU_IFUNC`, `SHN_ABS`, and the binding. -/
structure Def where
  value : Nat
  ifunc : Bool
  abs : Bool
  deriving DecidableEq, Repr

def lookupDef (d : DynInfo) (r : Ref) (plt : Bool) : Rd (Option Def) := do
  match ← lookupIn d r plt with
  | none => pure none
  | some i =>
    let s ← sym d i
    -- STB_GLOBAL, STB_WEAK or STB_GNU_UNIQUE (10); other bindings are not definitions
    Rd.guard (s.bind = 1 ∨ s.bind = 2)
    pure (some ⟨s.value, s.type == 10, s.shndx == 0xfff1⟩)

/-! ## References and relocations -/

/-- The requested version of symbol `symidx` of an object (`DT_VERSYM` then `DT_VERNEED`):
the `vernaux` entry whose `vna_other & 0x7fff` is the index; `none` for indices 0 and 1 or a
zero `vna_hash`. -/
def verneedFind (d : DynInfo) (ndx : Nat) : Nat → Nat → Rd (Option Ver)
  | 0, _ => pure none
  | fuel + 1, o => do
    let cnt ← u16 (o + 2)
    let aux ← u32 (o + 8)
    let next ← u32 (o + 12)
    let found ← auxFind (o + aux) cnt
    match found with
    | some v => pure (some v)
    | none => if next = 0 then pure none else verneedFind d ndx fuel (o + next)
where
  auxFind (a : Nat) : Nat → Rd (Option Ver)
    | 0 => pure none
    | k + 1 => do
      let hash ← u32 a
      let other ← u16 (a + 6)
      let name ← u32 (a + 8)
      let next ← u32 (a + 12)
      if other % 0x8000 = ndx then do
        let n ← d.str name
        pure (if hash = 0 then none else some ⟨n, hash, other / 0x8000 % 2 = 1⟩)
      else if next = 0 then pure none else auxFind (a + next) k

/-- The reference made by symbol `symidx` of an object. -/
def refOf (d : DynInfo) (symidx : Nat) : Rd Ref := do
  let s ← sym d symidx
  let name ← d.str s.name
  let ver ← match d.tagOff DT_VERSYM, d.tagOff DT_VERNEED with
    | some vs, some vn => do
      let ndx ← u16 (vs + 2 * symidx)
      if ndx % 0x8000 < 2 then pure none
      else verneedFind d (ndx % 0x8000) ((d.tag DT_VERNEEDNUM).getD 0) vn
    | _, _ => pure none
  pure ⟨name, s.bind == 2, ver⟩

/-- A dynamic relocation: `r_offset`, the type, the symbol index and the addend. -/
structure Rela where
  off : Nat
  kind : Nat
  sym : Nat
  addend : Int
  deriving DecidableEq, Repr

def rela (o : Nat) : Rd Rela := do
  let off ← u64 o
  let info ← u64 (o + 8)
  let a ← u64 (o + 16)
  pure ⟨off, info % 2 ^ 32, info / 2 ^ 32, Silmaril.Formats.ELF.signed64 a⟩

/-- The `n` RELA entries at the address in tag `t`. -/
def relaTable (d : DynInfo) (t n : Nat) : Rd (List Rela) :=
  if n = 0 then pure [] else do
    let o ← Rd.ofOption (d.tagOff t)
    (List.range n).mapM fun i => rela (o + 24 * i)

/-- `DT_RELA` (`DT_RELASZ / 24` entries) and `DT_JMPREL` (`DT_PLTRELSZ / 24`). `DT_RELR` is
not read: an object with it is rejected. -/
def relas (d : DynInfo) : Rd (List Rela × List Rela) := do
  Rd.guard (d.tag DT_RELR = none)
  let a ← relaTable d DT_RELA ((d.tag DT_RELASZ).getD 0 / 24)
  let j ← relaTable d DT_JMPREL ((d.tag DT_PLTRELSZ).getD 0 / 24)
  pure (a, j)

/-- The words of an address table (`DT_INIT_ARRAY`, `DT_FINI_ARRAY`) as stored in the file. -/
def table (d : DynInfo) (t sz : Nat) : Rd (List Nat) :=
  match d.tag t with
  | none => pure []
  | some _ => do
    let o ← Rd.ofOption (d.tagOff t)
    (List.range ((d.tag sz).getD 0 / 8)).mapM fun i => u64 (o + 8 * i)

end Elf

end Silmaril.Elf.Link.DynElf
