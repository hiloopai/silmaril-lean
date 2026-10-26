module

public import Silmaril.X86.Decompile.CfgPropose

/-!
# Transcriptions of compiled machine code

A *transcription* is what `tools/x86-lift` emits for a piece of compiled code:
the bytes, the instruction listing with addresses and lengths, the function
partition, one control-flow graph per function, how each block is left, the
relocations that patch the bytes and the constants the code reads, together
with a description of the binary they came from (sections, load segments,
symbols, entry point) and its SHA-256 pin.

The lifter is written in Rust on top of iced-x86, and **nothing it produces is
trusted**. A generated module states one equation,

```
transcript.verify = true
```

closed by kernel reduction (`decide`), and `Transcript.verify_sound` turns it
into the facts a proof needs:

* the bytes decode, under the model's own decoder `Ext.decode`, to *exactly*
  the transcribed listing (`Region.decode region fuel = .ok listing`) — so the
  listing is a theorem about the bytes, and the rest of
  `Silmaril.X86.Decompile.Region` (coverage, fetch, address chaining) applies;
* `Decompile.check` accepts the function partition, so `check_sound_step` and
  `check_sound_run` apply;
* `Decompile.checkCfg` accepts every control-flow graph, and each one is the
  graph `CfgPropose.ofFunction` computes — the Rust CFG builder and the Lean
  leader algorithm agree;
* every recorded block exit is the terminator's `Decoded.edges` (so calls,
  returns and traps are named);
* every relocation's field lies inside one listed instruction.

## Trust boundary

* **Checked by the kernel:** everything `verify` covers, above.
* **Trusted (data):** that the transcribed bytes are the bytes of the named
  file. The generated module records the file's SHA-256 and the SHA-256 of the
  lifted byte range; a module that also embeds the bytes elsewhere (as
  `Silmaril.Crypto.X86.Sha256O2.Image` does) links them with an `rfl`
  equation. Re-deriving the bytes from the file inside Lean is the job of the
  ELF reader (`Silmaril.Formats.ELF`) and a verified decoder.
* **Trusted (proposal metadata):** the image description — section names,
  symbol table, relocation list, entry point. These are recorded, not checked:
  a relocation the lifter failed to report is a relocation `verify` never sees.
  The function partition and CFGs, by contrast, are checked.

## Scope and reuse

The structures below are deliberately not specific to one function: a
transcription can hold a whole `.text` (several functions with NOP padding,
relocated calls to external symbols) and the image description carries load
segments and an entry point, which is what a whole-executable statement needs.
The instruction type is x86's `Ext.Instr` because `Region`/`Decoded` are; an
RV64 transcription would reuse `Image`, `Reloc` and `Blob` unchanged and
replace the listing and checker with the RV64 model's.
-/

@[expose] public section

namespace Silmaril.X86.Lift

open Silmaril.X86 (Byte Reg)
open Silmaril.X86.Decompile

/-! ## The binary a transcription came from -/

/-- The instruction set. -/
inductive Arch where
  | x86_64 | riscv64
  deriving DecidableEq, Repr

/-- What kind of file the bytes came from. -/
inductive FileKind where
  /-- An ELF relocatable object: sections are unlinked and start at 0. -/
  | relocatable
  /-- An ELF executable. -/
  | executable
  /-- An ELF shared object or position-independent executable. -/
  | shared
  /-- Raw bytes at a caller-chosen base. -/
  | raw
  deriving DecidableEq, Repr

/-- Where the bytes came from: a display path, the SHA-256 of the whole file
(lower-case hex) and its size. -/
structure Provenance where
  path : String
  sha256 : String
  size : Nat
  kind : FileKind
  arch : Arch
  deriving DecidableEq, Repr

/-- Read/write/execute permissions. -/
structure Perm where
  read : Bool
  write : Bool
  exec : Bool
  deriving DecidableEq, Repr

/-- An allocated section. In a relocatable object every section starts at
address 0, so an address is meaningful only together with a section name. -/
structure Section where
  name : String
  addr : Nat
  size : Nat
  perm : Perm
  deriving DecidableEq, Repr

/-- A `PT_LOAD` program header of an executable. -/
structure LoadSegment where
  vaddr : Nat
  memSize : Nat
  fileSize : Nat
  fileOffset : Nat
  perm : Perm
  deriving DecidableEq, Repr

/-- What a symbol names. -/
inductive SymbolKind where
  | func | object | section | file | other
  deriving DecidableEq, Repr

/-- A symbol-table entry. `sect` is the section name, or `"*UND*"`. -/
structure Symbol where
  name : String
  sect : String
  addr : Nat
  size : Nat
  kind : SymbolKind
  global : Bool
  deriving DecidableEq, Repr

/-- Relocation types (x86-64 psABI names; others by number). -/
inductive RelocKind where
  /-- `R_X86_64_PC32`: `S + A - P`, 32 bits. -/
  | pc32
  /-- `R_X86_64_PLT32`: `L + A - P`, 32 bits. -/
  | plt32
  /-- `R_X86_64_GOTPCREL` and its relaxable variants. -/
  | gotpcrel
  /-- `R_X86_64_64`: `S + A`. -/
  | abs64
  /-- `R_X86_64_32`: `S + A`, zero-extended. -/
  | abs32
  /-- `R_X86_64_32S`: `S + A`, sign-extended. -/
  | abs32s
  /-- Any other type, by its ELF number. -/
  | other (type : Nat)
  deriving DecidableEq, Repr

/-- One relocation: the `width`-byte field at `field` in section `sect` is
patched with a value computed from `symbol` and `addend`. `insn` is the address
of the listed instruction that contains the field. -/
structure Reloc where
  sect : String
  field : Nat
  width : Nat
  kind : RelocKind
  symbol : String
  addend : Int
  insn : Nat
  deriving DecidableEq, Repr

/-- A named data object, with its bytes. -/
structure Blob where
  name : String
  sect : String
  addr : Nat
  bytes : List Byte
  deriving DecidableEq, Repr

/-- The binary a transcription came from. -/
structure Image where
  provenance : Provenance
  entry : Option Nat
  sections : List Section
  segments : List LoadSegment
  symbols : List Symbol
  deriving DecidableEq, Repr

/-! ## Transcriptions -/

/-- A scaled index register; the `RSP` side condition is discharged by
`decide` at each use, which keeps generated listings readable. -/
def ix (r : Reg) (scale : BitVec 2) (h : r ≠ .rsp := by decide) : Ext.Index := ⟨r, scale, h⟩

/-- A transcription. See the module documentation. -/
structure Transcript where
  /-- The binary the bytes came from. -/
  image : Image
  /-- The lifted bytes and their address. -/
  region : Region
  /-- SHA-256 (lower-case hex) of `region.bytes`. -/
  regionSha256 : String
  /-- Decoding fuel; `region.bytes.length` always suffices. -/
  fuel : Nat
  /-- The instructions, with addresses and lengths. -/
  listing : List Decoded
  /-- The functions of the region, NOP padding, relocated calls. -/
  partition : Partition
  /-- One control-flow graph per function, in the order of
  `partition.funcs`. -/
  cfgs : List CfgSpec
  /-- How each block is left: block start, and the terminator's edges
  (fall-through, jump, branch, call, return or trap). -/
  exits : List (Nat × List Edge)
  /-- The relocations whose fields lie in the region. -/
  relocs : List Reloc
  /-- Data objects the code reads. -/
  constants : List Blob
  deriving Repr

namespace Transcript

/-- The bytes decode to exactly the listing. -/
def decodes (t : Transcript) : Bool :=
  match t.region.decode t.fuel with
  | .ok ds => ds == t.listing
  | .error _ => false

/-- The recorded block exits are the terminators' edges. -/
def exitsMatch (t : Transcript) : Bool :=
  t.exits == (t.cfgs.flatMap CfgSpec.blocks).map fun b =>
    (b.start, ((at? t.listing b.terminator).map Decoded.edges).getD [])

/-- Every relocation's field lies inside the listed instruction it names. -/
def relocsPlaced (t : Transcript) : Bool :=
  t.relocs.all fun r =>
    match at? t.listing r.insn with
    | some d => decide (d.addr < r.field ∧ r.field + r.width ≤ d.addr + d.size)
    | none => false

/-- `checkCfg` accepts the graph, and it is the leader algorithm's graph. -/
def cfgOk (acc : Accepted) (c : CfgSpec) : Bool :=
  (match checkCfg acc c with | .ok _ => true | .error _ => false) &&
    CfgPropose.ofFunction acc c.func == c

/-- **The check.** Kernel-reducible; a generated module closes
`t.verify = true` by `decide`. -/
def verify (t : Transcript) : Bool :=
  t.decodes && t.exitsMatch && t.relocsPlaced &&
    t.cfgs.map CfgSpec.func == t.partition.funcs &&
    match check t.region t.partition t.fuel with
    | .ok acc => t.cfgs.all (cfgOk acc)
    | .error _ => false

/-- What a successful check establishes. -/
structure Verified (t : Transcript) : Prop where
  /-- The model's decoder reads the bytes as exactly the listing. -/
  decode : t.region.decode t.fuel = .ok t.listing
  /-- The partition checker accepts, and every CFG is accepted and is the
  leader algorithm's. -/
  accepted : ∃ acc, check t.region t.partition t.fuel = .ok acc ∧
    ∀ c ∈ t.cfgs, (∃ cc, checkCfg acc c = .ok cc) ∧ CfgPropose.ofFunction acc c.func = c
  /-- One CFG per function, in order. -/
  funcs : t.cfgs.map CfgSpec.func = t.partition.funcs
  /-- The recorded exits are the terminators' edges. -/
  exits : t.exits = (t.cfgs.flatMap CfgSpec.blocks).map fun b =>
    (b.start, ((at? t.listing b.terminator).map Decoded.edges).getD [])
  /-- Each relocation's field lies inside the instruction it names. -/
  relocs : ∀ r ∈ t.relocs, ∃ d, at? t.listing r.insn = some d ∧
    d.addr < r.field ∧ r.field + r.width ≤ d.addr + d.size

theorem verify_sound {t : Transcript} (h : t.verify = true) : t.Verified := by
  simp only [verify, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hdec, hexit⟩, hrel⟩, hfun⟩, hchk⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [decodes] at hdec
    split at hdec
    · rename_i ds hds
      rw [hds, beq_iff_eq.mp hdec]
    · cases hdec
  · split at hchk
    · rename_i acc hacc
      refine ⟨acc, hacc, fun c hc => ?_⟩
      have hc' := List.all_eq_true.mp hchk c hc
      simp only [cfgOk, Bool.and_eq_true, beq_iff_eq] at hc'
      obtain ⟨hok, hprop⟩ := hc'
      refine ⟨?_, hprop⟩
      split at hok
      · rename_i cc hcc
        exact ⟨cc, hcc⟩
      · cases hok
    · cases hchk
  · exact beq_iff_eq.mp hfun
  · exact beq_iff_eq.mp hexit
  · intro r hr
    have := List.all_eq_true.mp hrel r hr
    split at this
    · rename_i d hd
      exact ⟨d, hd, of_decide_eq_true this⟩
    · cases this

/-- The listing really is the model's reading of the bytes, in the `Option`
form the rest of `Decompile.Region` uses. -/
theorem Verified.decode? {t : Transcript} (h : t.Verified) :
    t.region.decode? t.fuel = some t.listing := by
  simp only [Region.decode?, h.decode]
  rfl

/-- The bytes are exactly the canonical encodings of the listed instructions. -/
theorem Verified.covers {t : Transcript} (h : t.Verified) :
    t.region.bytes = (t.listing.map fun d => Ext.encode d.instr).flatten :=
  (Region.decode?_covers h.decode?).symm

end Transcript

end Silmaril.X86.Lift
