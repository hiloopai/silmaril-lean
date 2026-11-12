module

public import Silmaril.Elf.Link.Dyn.Elf.Defs
public import Silmaril.X86.Ext.Semantics
public import Silmaril.X86.Ext.SymExec

/-! # The dynamic loader's effect on the executable: a specified relation (trusted)

What `execve` + `ld.so` leave in memory for the executable, as a **specified relation**
`ExeLoaded`, not a verified loader. It is the trusted model of the loader, and its parts are
transcriptions of glibc 2.39's `ld.so`:

* **Search scope** (`Scope`): the executable, then its `DT_NEEDED` closure in breadth-first order
  (`_dl_map_object_deps`). Which file a `DT_NEEDED` name opens (search paths, `ld.so.cache`) is
  an environment fact, not modelled: a scope is given as files with load bases.
* **Symbol resolution** (`resolveFrom`): the first object of the scope whose lookup
  (`Elf.lookupDef`, ld.so's `do_lookup_x`) finds a definition. `defAddr` is `SYMBOL_ADDRESS`
  (`l_addr + st_value`, or `st_value` for `SHN_ABS`), with an ifunc's choice given by `ifn`.
* **Relocation values** (`relocVal`, `sysdeps/x86_64/dl-machine.h`): `R_X86_64_RELATIVE`
  (`l_addr + r_addend`), `GLOB_DAT`/`JUMP_SLOT` (the resolved address; an unresolved weak
  reference is 0; addend 0 required), `IRELATIVE` (`ifn (l_addr + r_addend)`). Any other kind
  (`COPY`, `64`, `TPOFF64`, `DTPMOD64`, …) has no value here, so `ExeLoaded` is false for an
  executable that uses one: the model makes no claim about it.
* **Lazy binding** (`lazy = true`, allowed only without `DF_BIND_NOW`/`DF_1_NOW`): every
  `JUMP_SLOT` holds `l_addr` plus its file word (`elf_machine_lazy_rel`), `GOT[1]` is
  unconstrained (the link map) and `GOT[2]` is the resolver `resolver`
  (`elf_machine_runtime_setup`). `lazy = false` is `LD_BIND_NOW` or `DF_BIND_NOW`.
* **The image** (`ExeLoaded`): every byte of every `PT_LOAD` of the executable is mapped at
  `base + vaddr` with the segment's `PF_R`/`PF_X`, `PF_W` except on `PT_GNU_RELRO` pages
  (`_dl_protect_relro`: from the page of its start to the page of its end, rounded down), and
  holds its relocated value, its file byte, or 0 in `.bss`.

`R_X86_64_COPY` of an 8-byte object (`stdin`, `stdout`, `stderr` in a gcc PIE): `ld.so` copies the
object's initial value from the library; the model leaves the 8 bytes unconstrained (`.any`), and
what they hold is the library's guarantee.
Not modelled (no claim is made where they matter): `DT_RELR`, TLS relocations, other `COPY`s,
symbol interposition through `LD_PRELOAD` (a different scope), `dlopen`, `DT_TEXTREL`, pages
shared between two segments, the vDSO (not in the global scope), and the other objects'
images (their behaviour is what the import contracts state).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)

/-- An object of the link map: its file and its load base (`l_addr`). -/
structure Obj where
  file : Blob
  base : Word

def frun {α : Type} (f : Blob) (p : Rd α) : Option α := p.run (blobRead f)

def Obj.run {α : Type} (o : Obj) (p : Rd α) : Option α := frun o.file p

/-- What the loader reads from the object's headers. -/
def finfo (f : Blob) : Option Elf.DynInfo := frun f Elf.dynInfo

/-- **Symbol resolution** over a search scope (files in search order): `some (some (k, d))`
(found in object `k`), `some none` (no object defines it), `none` (the model has no answer:
a reader failed). Positions, not bases: the bases are applied by `Val.word`. -/
def resolveFrom (k : Nat) : List Blob → Elf.Ref → Bool → Option (Option (Nat × Elf.Def))
  | [], _, _ => some none
  | f :: fs, r, plt => do
    let i ← finfo f
    match ← frun f (Elf.lookupDef i r plt) with
    | some d => pure (some (k, d))
    | none => resolveFrom (k + 1) fs r plt

def resolve (scope : List Blob) := resolveFrom 0 scope

/-- A symbol resolver: what `resolve` computes for a scope, or a table of known results. -/
abbrev Resolver := Elf.Ref → Bool → Option (Option (Nat × Elf.Def))

/-- A slot value, relative to the load bases. -/
inductive Val where
  /-- `base_k + off` -/
  | addr (k : Nat) (off : Int)
  /-- an absolute value (`SHN_ABS`, or 0 for an unresolved weak reference) -/
  | abs (v : Nat)
  /-- what the ifunc resolver at `base_k + off` returns (`ifn`) -/
  | ifunc (k : Nat) (off : Int)
  /-- the lazy-binding resolver (`GOT[2]`) -/
  | resolver
  /-- unconstrained (`GOT[1]`, the link map) -/
  | any
  deriving DecidableEq, Repr

/-- `SYMBOL_ADDRESS`, relative: `l_addr + st_value` (or `st_value` for `SHN_ABS`), an ifunc
through its resolver. -/
def defVal (kd : Nat × Elf.Def) : Val :=
  if kd.2.abs then .abs kd.2.value
  else if kd.2.ifunc then .ifunc kd.1 kd.2.value else .addr kd.1 kd.2.value

/-- The value of a reference (an unresolved weak reference is 0; an unresolved strong
reference has no value: ld.so refuses to start the program). -/
def bindVal (R : Resolver) (r : Elf.Ref) (plt : Bool) : Option Val := do
  match ← R r plt with
  | some kd => pure (defVal kd)
  | none => if r.weak then some (.abs 0) else none

/-- `st_size` of dynamic symbol `i`. -/
def symSize (d : Elf.DynInfo) (i : Nat) : Rd Nat := do
  let t ← Rd.ofOption (d.tagOff Elf.DT_SYMTAB)
  Elf.u64 (t + 24 * i + 16)

/-- **The eager value of relocation `r`** of the executable (object 0, file `f`, headers `i`). -/
def relocVal (R : Resolver) (f : Blob) (i : Elf.DynInfo) (r : Elf.Rela) : Option Val :=
  if r.kind = 8 then some (.addr 0 r.addend)
  else if r.kind = 37 then some (.ifunc 0 r.addend)
  else if (r.kind = 6 ∨ r.kind = 7) ∧ r.addend = 0 then do
    let ref ← frun f (Elf.refOf i r.sym)
    bindVal R ref (r.kind = 7)
  else if r.kind = 5 ∧ r.addend = 0 ∧ frun f (symSize i r.sym) = some 8 then some .any
  else none

/-- The 8-byte word of the file at virtual address `v`. -/
def fileWord (f : Blob) (i : Elf.DynInfo) (v : Nat) : Option Nat := do
  let off ← Elf.vToOff i.phs v
  frun f (Elf.u64 off)

/-- **The slot table**: address-sized slots the loader writes, `(vaddr, value)`. -/
def slotsWith (R : Resolver) (lazy : Bool) (f : Blob) (i : Elf.DynInfo) :
    Option (List (Nat × Val)) := do
  let (a, j) ← frun f (Elf.relas i)
  let ra ← a.mapM fun r => (relocVal R f i r).map fun w => (r.off, w)
  let rj ← j.mapM fun r =>
    if lazy then
      if r.kind = 7 then (fileWord f i r.off).map fun w => (r.off, Val.addr 0 w)
      else none
    else (relocVal R f i r).map fun w => (r.off, w)
  let got ← if lazy ∧ j ≠ [] then
      (i.tag 3).map fun p => [(p + 8, Val.any), (p + 16, Val.resolver)]
    else some []
  pure (got ++ ra ++ rj)

/-- The loader's slot table for the executable, the head of `scope`. -/
def slots (scope : List Blob) := slotsWith (resolve scope)

/-- A slot value at the given bases: `some (some w)`, `some none` (unconstrained), `none` (no
value: an ifunc resolver without a choice, or a missing base). -/
def Val.word (bases : List Word) (ifn : Word → Option Word) (res : Word) : Val → Option (Option Word)
  | .addr k off => bases[k]?.map fun b => some (b + BitVec.ofInt 64 off)
  | .abs v => some (some (BitVec.ofNat 64 v))
  | .ifunc k off => (bases[k]?.bind fun b => ifn (b + BitVec.ofInt 64 off)).map some
  | .resolver => some (some res)
  | .any => some none

/-- An object with its headers and a table of lookup results (a cache: `Known.Ok` says the
table is right). -/
structure Known where
  file : Blob
  info : Elf.DynInfo
  facts : List (Elf.Ref × Bool × Option Elf.Def)

def Known.Ok (k : Known) : Prop :=
  finfo k.file = some k.info ∧ ∀ e ∈ k.facts, frun k.file (Elf.lookupDef k.info e.1 e.2.1) = some e.2.2

/-- Resolution from the tables (`none` when a table has no entry). -/
def resolveKFrom (k : Nat) : List (List (Elf.Ref × Bool × Option Elf.Def)) → Resolver
  | [], _, _ => some none
  | T :: Ts, r, p =>
    match (T.find? fun e => e.1 == r && e.2.1 == p) with
    | some (_, _, some d) => some (some (k, d))
    | some (_, _, none) => resolveKFrom (k + 1) Ts r p
    | none => none

def resolveK (Ts : List (List (Elf.Ref × Bool × Option Elf.Def))) := resolveKFrom 0 Ts

/-- Byte `k` (little-endian) of a word. -/
def wordByte (w : Word) (k : Nat) : Byte := BitVec.ofNat 8 (w.toNat >>> (8 * k))

/-- The byte the file gives at virtual address `v` of a `PT_LOAD` (0 past `p_filesz`). -/
def imageByte (f : Blob) (ph : Elf.Phdr) (v : Nat) : Option Byte :=
  if v < ph.vaddr + ph.filesz then (frun f (Elf.u8 (v - ph.vaddr + ph.off))).map (BitVec.ofNat 8)
  else some 0

/-- What the byte at `v` must hold: `some (some x)`, `some none` (unconstrained), or `none`
(no value in the model). -/
def expectedByte (f : Blob) (T : List (Nat × Option Word)) (ph : Elf.Phdr) (v : Nat) :
    Option (Option Byte) :=
  match T.find? (fun e => e.1 ≤ v ∧ v < e.1 + 8) with
  | some (s, some w) => some (some (wordByte w (v - s)))
  | some (_, none) => some none
  | none => (imageByte f ph v).map some

/-- `v` lies on a page that `PT_GNU_RELRO` makes read-only. -/
def inRelro (i : Elf.DynInfo) (v : Nat) : Bool :=
  i.phs.any fun ph => ph.kind == 0x6474e552 && ph.vaddr / 4096 * 4096 ≤ v &&
    v < (ph.vaddr + ph.memsz) / 4096 * 4096

/-- **The executable's post-load image** in `mem`, for headers `i` and slot table `T`:
every byte of every `PT_LOAD` mapped with its permissions, backed, and holding what
`expectedByte` says. -/
def ImageOk (o : Obj) (i : Elf.DynInfo) (T : List (Nat × Option Word)) (mem : Memory) : Prop :=
  ∀ ph ∈ i.phs, ph.kind = 1 → ∀ v, ph.vaddr ≤ v → v < ph.vaddr + ph.memsz →
    let a := (o.base + BitVec.ofNat 64 v).toNat
    o.base.toNat + v < 2 ^ 64 ∧
    mem.permits .read a = (ph.flags / 4 % 2 == 1) ∧
    mem.permits .execute a = (ph.flags % 2 == 1) ∧
    mem.permits .write a = (ph.flags / 2 % 2 == 1 && !inRelro i v) ∧
    ∃ e, expectedByte o.file T ph v = some e ∧ (mem.bytes.get? a).isSome ∧
      ∀ x, e = some x → mem.bytes.get? a = some x

/-- **The loader relation for the executable**, the head of the search scope `scope` (files
in search order) loaded at `bases`: its headers read, lazy binding only where allowed, its
slot table computed and placed at the bases, and its image in place. -/
def ExeLoaded (scope : List Blob) (bases : List Word) (ifn : Word → Option Word) (lazy : Bool)
    (res : Word) (mem : Memory) : Prop :=
  ∃ f b i D T, scope.head? = some f ∧ bases.head? = some b ∧ finfo f = some i ∧
    (lazy = true → i.bindNow = false) ∧ slots scope lazy f i = some D ∧
    D.mapM (fun e => (e.2.word bases ifn res).map fun w => (e.1, w)) = some T ∧
    ImageOk ⟨f, b⟩ i T mem

/-- **Loader fact: every object is mapped at a page-aligned base.** The kernel maps an `ET_DYN`
executable at `ELF_ET_DYN_BASE` plus a randomised offset, both multiples of the page size
(`load_elf_binary`, `ELF_PAGESTART`), and `ld.so` maps each library with `mmap`, whose results
are page-aligned. `ExeLoaded` describes the image relative to an arbitrary base and does not
say this. It is **trusted** (a fact about the loader, not read from the ELF); theorems that use
it (for instance SSE loads of the image's 16-byte-aligned constants) state the loader relation as
`ExeLoadedP`. The page size is 4096 (x86-64). -/
def PageBase (bases : List Word) : Prop := ∀ b ∈ bases, b.toNat % 4096 = 0

/-- **The loader relation with page-aligned bases**: `ExeLoaded` and the loader fact `PageBase`. -/
def ExeLoadedP (scope : List Blob) (bases : List Word) (ifn : Word → Option Word) (lazy : Bool)
    (res : Word) (mem : Memory) : Prop :=
  ExeLoaded scope bases ifn lazy res mem ∧ PageBase bases

end Silmaril.Elf.Link.Dyn
