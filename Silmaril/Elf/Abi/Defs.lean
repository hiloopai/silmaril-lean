module

public import Silmaril.Elf.Facts.Defs
public import Silmaril.Project.Shapes.Abi.Defs

/-!
# Standard problem shapes: ABI conformance of a function of an ELF file

`silmaril.shapes.elf.abi_conforms` is `silmaril.shapes.abi.conforms` with the code **bound to
the file** (`CodeOf`):

- the binding (`.symtab`, or ld.so's versioned lookup in `.dynsym`) looks up the header's name
  `f`, and finds a plain function at the code's entry (`st_value = base + off`) whose size is
  the code's extent (`st_size = len`);
- the symbol entry is an `STT_FUNC` named `f` (`STT_OBJECT`, `NOTYPE` and `GNU_IFUNC` symbols
  are rejected);
- a read-only executable `PT_LOAD` maps the code bytes, and read-only `PT_LOAD`s map the data;
- the code's image is the file's `PT_LOAD` ranges.

Two more facts complete the binding:

- **No relocation touches the code** (`Untouched`): the file is x86-64, and every dynamic
  relocation has a known per-type width (`relocWidth`: 4, 8 or 16 bytes; `COPY` and unknown
  types refused) and writes outside the code and its data.
- **Every load base** the file admits (`Placement`, of which there must be at least one): the
  rebased code (`Code.rebase`) conforms. For `ET_EXEC` that base is `0`. For `ET_DYN` no row claims conformance at
  link-time addresses.

Every one of these facts reads the file through the ELF specification (`Silmaril.Elf.Facts`).

An ELF symbol has a value and a size but **no C signature**. The prototype comes from the
header (`Conforms.declared`); the symbol only locates the code. A row is three separate
statements:

1. the function is present (`Lookup`, `SymbolAt`);
2. the code is the file's (`CodeAt`, `MappedAt`, `Untouched`);
3. the code conforms on the machine model `M` (`Conforms`).

The header shapes are:

- `silmaril.shapes.elf.abi_header_sat_partial`. The claimed functions (at least one) each
  have a row. An `absent` exclusion is absent from every symbol table of the file in any
  version (`Absent`: an API version gap). An `unclaimed` one is a function present in the
  file (`Present`). The coverage is checked against the header.
- `silmaril.shapes.elf.abi_header_sat_available`. The same with no `unclaimed` declaration and
  every claimed function total: every function of the header the file provides. `absent`
  declarations (version gaps, checked absent from the file) are allowed and are listed with the
  row: this is **not** satisfaction of the whole header.
- `silmaril.shapes.elf.abi_header_sat_complete`. Available, with nothing absent: every
  declaration is claimed or refused by the ABI's lowering (whole-header satisfaction, for the
  surface the ABI expresses).

A partial row is never displayed as header satisfaction: it says nothing about the excluded
declarations.

A header shared by several binaries (zlib's `zlib.h` for a static build and for a
distribution's `libz.so.1`) gives one set of rows **per binary**. The header and the specs are
the same values; the files, bindings (versions) and code differ.
-/

@[expose] public section

namespace Silmaril.Elf.Abi

open Silmaril.Elf
open Silmaril.Machine.Abi.Conformance
open Silmaril.X86.Link (Blob)
open Silmaril.Elf.Link.DynElf (blobRead)

/-- **How a function is found in the file**: in `.symtab`, or by ld.so's lookup in `.dynsym`
with a requested version. The name is always the header's (`Binding.sel`). -/
inductive Binding where
  | symtab
  | dynsym (ver : Option Ver)
  deriving DecidableEq, Repr

/-- The selector for the function `f`. -/
def Binding.sel (b : Binding) (f : String) : Sel :=
  match b with
  | .symtab => .sym (nameOf f)
  | .dynsym ver => .dyn ⟨nameOf f, false, ver⟩

/-- The symbol table the binding reads. -/
def Binding.table : Binding → Table
  | .symtab => .symtab
  | .dynsym _ => .dynsym

/-- `ph` is a `PT_LOAD` mapping `[v, v + len)` from the file, readable and not writable. -/
def roSeg (v len : Nat) (ph : Silmaril.Formats.ELF.ProgramHeader) : Bool :=
  ph.kind == PT_LOAD && ph.flags / 2 % 2 == 0 && ph.flags / 4 % 2 == 1 &&
    decide (ph.virtualAddress ≤ v) && decide (v + len ≤ ph.virtualAddress + ph.fileSize)

/-- **`F` maps `bytes` read-only at `v`** (any read-only `PT_LOAD`, as `CodeAt` for code). -/
def MappedAt (F : Blob) (v : Nat) (bytes : List (BitVec 8)) : Prop :=
  ∃ A, Parses F A ∧ ∃ ph, A.phdrs.find? (roSeg v bytes.length) = some ph ∧
    blobRead F (ph.offset + (v - ph.virtualAddress)) bytes.length = some (Blob.valueLE bytes)

/-- **The code is the function `f` of `F`** (at link-time addresses): the binding's lookup finds a
plain function at the entry with the code's extent, the symbol entry it found is an `STT_FUNC`
named `f` (not an `STT_OBJECT`, `NOTYPE` or `GNU_IFUNC`), the file maps the code bytes and the
data, and the code's image is the file's `PT_LOAD` ranges. -/
def CodeOf (F : Blob) (b : Binding) (f : String) (c : Code) : Prop :=
  (∃ d, Lookup F (b.sel f) (some d) ∧ d.value = c.base.toNat + c.off ∧ d.size = c.len ∧
    d.ifunc = false ∧ d.abs = false ∧
    ∃ s, SymbolAt F b.table d.index s ∧ s.name = nameOf f ∧ s.kind = 2) ∧
  CodeAt F c.base.toNat c.bytes ∧
  (∀ d ∈ c.data, MappedAt F d.1.toNat d.2) ∧
  ∃ A, Parses F A ∧ c.image = A.loads.map fun ph => (BitVec.ofNat 64 ph.virtualAddress, ph.memorySize)

/-- `EM_X86_64`: relocation type numbers below are x86-64's. -/
def EM_X86_64 : Nat := 62

/-- **The bytes an x86-64 dynamic relocation of type `k` writes** at its offset (the field of the
x86-64 psABI's relocation table, x86-psABIs/x86-64-ABI@e1ce0983 §4.4.1; `TLSDESC` is two words,
§"Thread-Local Storage Descriptors"). Every other type is `none`, and a relocation of it counts as
touching everything (`Untouched`): `R_X86_64_COPY` (5, writes the destination symbol's
`st_size`), the link-time-only types, and unknown numbers.

| width | types |
| --- | --- |
| 0 | `NONE` (0) |
| 4 | `PC32` (2), `32` (10), `32S` (11), `TPOFF32` (23) |
| 8 | `64` (1), `GLOB_DAT` (6), `JUMP_SLOT` (7), `RELATIVE` (8), `DTPMOD64` (16), `DTPOFF64` (17), `TPOFF64` (18), `PC64` (24), `IRELATIVE` (37), `RELATIVE64` (38) |
| 16 | `TLSDESC` (36) |
-/
def relocWidth : Nat → Option Nat
  | 0 => some 0
  | 2 | 10 | 11 | 23 => some 4
  | 1 | 6 | 7 | 8 | 16 | 17 | 18 | 24 | 37 | 38 => some 8
  | 36 => some 16
  | _ => none

/-- `[o, o + w)` misses `[v, v + n)`. -/
def Misses (o w v n : Nat) : Prop := o + w ≤ v ∨ v + n ≤ o

/-- **No dynamic relocation patches the code or its data**: the file is x86-64, and every dynamic
relocation (what ld.so applies, RELR entries expanded) has a known width (`relocWidth`) and
writes `[offset, offset + width)` outside the code bytes and outside each data range. A
relocation of unknown or symbol-dependent width (`COPY`) is refused. -/
def Untouched (F : Blob) (c : Code) : Prop :=
  ∃ A, Parses F A ∧ A.header.machine = EM_X86_64 ∧ ∀ r ∈ A.relocs .dynamic, ∃ w,
    relocWidth r.kind = some w ∧ Misses r.offset w c.base.toNat c.bytes.length ∧
    ∀ d ∈ c.data, Misses r.offset w d.1.toNat d.2.length

/-- **`f` is absent from `F`**: no symbol table (`.symtab`, `.dynsym`, any version) has a
defined symbol named `f`. -/
def Absent (F : Blob) (f : String) : Prop :=
  ∃ A, Parses F A ∧ ∀ t, ∀ s ∈ A.symbols t, s.name = nameOf f → s.raw.sectionIndex = 0

/-- **`f` is present in `F`**: some symbol table defines a function (`STT_FUNC` or
`STT_GNU_IFUNC`) named `f`. -/
def Present (F : Blob) (f : String) : Prop :=
  ∃ A, Parses F A ∧ ∃ t, ∃ s ∈ A.symbols t, s.name = nameOf f ∧ s.raw.sectionIndex ≠ 0 ∧
    (s.kind = 2 ∨ s.kind = 10)

/-- **The function `f` of the ELF file `F` conforms to the ABI `A` on the machine `M`**, as the
header `hdr` declares it: the code is the file's (`CodeOf`, at link-time addresses), no dynamic
relocation patches it (`Untouched`), the file admits some load base (so the next conjunct is not
vacuous), and at **every load base the file admits** (`Placement`: `0` for `ET_EXEC`,
page-aligned for `ET_DYN`) the rebased code conforms. -/
@[problem "silmaril.shapes.elf.abi_conforms"
  (title := "A function of an ELF file conforms to a versioned ABI on a restricted x86-64 machine model (FP, vector and control state carried by the model, not proved), as its C header declares it")]
def AbiConforms (A : AbiDef) (M : Mach) (mode : Mode) (hdr : HeaderSrc) (f : String)
    (p : A.V.Proto) (F : Blob) (b : Binding) (c : Code) (frame : Nat) (S : CallSpec A.V p) : Prop :=
  CodeOf F b f c ∧ Untouched F c ∧ (∃ base, Placement F base) ∧
    ∀ base, Placement F base → Conforms A M mode hdr f p (c.rebase base) frame S

/-- **The ELF file `F` satisfies a part of the header `hdr`** (partial): at least one function is
claimed; the coverage is checked against the header; every `absent` declaration is absent from
the file and every `unclaimed` one is present; every claimed function is a conforming function of
the file. -/
@[problem "silmaril.shapes.elf.abi_header_sat_partial"
  (title := "PARTIAL: an ELF file satisfies the claimed part of a C header under a versioned ABI, on a restricted x86-64 machine model")]
def AbiHeaderSatPartial (A : AbiDef) (M : Mach) (hdr : HeaderSrc) (cov : Coverage) (F : Blob)
    (bind : String → Binding) (impl : String → Option (Impl A)) : Prop :=
  cov.claimed ≠ [] ∧ cov.check A hdr = true ∧
  (∀ f why, (f, Exclusion.absent why) ∈ cov.excluded → Absent F f) ∧
  (∀ f why, (f, Exclusion.unclaimed why) ∈ cov.excluded → Present F f) ∧
  ∀ f ∈ cov.claimed, ∃ i, impl f = some i ∧
    AbiConforms A M i.mode hdr f i.proto F (bind f) i.code i.frame i.spec

/-- **The ELF file `F` satisfies every function of the header it provides** (available):
partial satisfaction with no `unclaimed` declaration and every claimed function total. Absent
declarations (checked absent from the file: a version gap) are allowed. -/
@[problem "silmaril.shapes.elf.abi_header_sat_available"
  (title := "An ELF file satisfies every function of a C header it provides (absent functions allowed as version gaps), total, under a versioned ABI, on a restricted x86-64 machine model")]
def AbiHeaderSatAvailable (A : AbiDef) (M : Mach) (hdr : HeaderSrc) (cov : Coverage) (F : Blob)
    (bind : String → Binding) (impl : String → Option (Impl A)) : Prop :=
  AbiHeaderSatPartial A M hdr cov F bind impl ∧ cov.available = true ∧
    ∀ f ∈ cov.claimed, ∃ i, impl f = some i ∧ i.mode = .total

/-- **The ELF file `F` satisfies the whole header `hdr`** (complete): available satisfaction
with no `absent` declaration; every declaration is claimed or refused by the ABI. -/
@[problem "silmaril.shapes.elf.abi_header_sat_complete"
  (title := "An ELF file satisfies a whole C header (every declaration the ABI lowers is present and conforming, total) under a versioned ABI, on a restricted x86-64 machine model")]
def AbiHeaderSatComplete (A : AbiDef) (M : Mach) (hdr : HeaderSrc) (cov : Coverage) (F : Blob)
    (bind : String → Binding) (impl : String → Option (Impl A)) : Prop :=
  AbiHeaderSatAvailable A M hdr cov F bind impl ∧ cov.complete = true

end Silmaril.Elf.Abi

end

silmaril instance silmaril.shapes.elf.abi_conforms.sysv_int_open
    (title := "abi_conforms, System V AMD64 INTEGER fragment, on the open machine model (Open)") :=
  silmaril.shapes.elf.abi_conforms (A := Silmaril.Machine.Abi.Conformance.sysvInt)
    (M := Silmaril.X86.Open.isa)
silmaril instance silmaril.shapes.elf.abi_conforms.sysv_int_open9
    (title := "abi_conforms, System V AMD64 INTEGER fragment, on the open machine model (Open9)") :=
  silmaril.shapes.elf.abi_conforms (A := Silmaril.Machine.Abi.Conformance.sysvInt)
    (M := Silmaril.X86.Open9.isa)
silmaril instance silmaril.shapes.elf.abi_header_sat_partial.sysv_int_open
    (title := "abi_header_sat_partial, System V AMD64 INTEGER fragment, on the open machine model (Open)") :=
  silmaril.shapes.elf.abi_header_sat_partial (A := Silmaril.Machine.Abi.Conformance.sysvInt)
    (M := Silmaril.X86.Open.isa)
silmaril instance silmaril.shapes.elf.abi_header_sat_available.sysv_int_open
    (title := "abi_header_sat_available, System V AMD64 INTEGER fragment, on the open machine model (Open)") :=
  silmaril.shapes.elf.abi_header_sat_available (A := Silmaril.Machine.Abi.Conformance.sysvInt)
    (M := Silmaril.X86.Open.isa)
silmaril instance silmaril.shapes.elf.abi_header_sat_complete.sysv_int_open
    (title := "abi_header_sat_complete, System V AMD64 INTEGER fragment, on the open machine model (Open)") :=
  silmaril.shapes.elf.abi_header_sat_complete (A := Silmaril.Machine.Abi.Conformance.sysvInt)
    (M := Silmaril.X86.Open.isa)
