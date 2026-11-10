module

public import Silmaril.Formats.ELF.Link.Defs

/-! # A checked x86-64 static RELA relocation profile

Instantiates the shared ELF AST linker `Silmaril.Formats.ELF.Link.link`, with no PLT/GOT
synthesis or relaxation. This is section linking, not an ELF executable writer or an ISA proof.

Kinds: `R_X86_64_64` (1), `PC32` (2), `PLT32` (4), `32` (10), `32S` (11).
`value r = S + A - P` for PC32/PLT32 and `S + A` otherwise; `Fits` is the range check;
`PLT32` resolves directly to the unique non-interposable definition, as in a static link.
Unsupported kinds and failed range or bounds checks are explicit residuals. `staticObject`
rejects weak, COMMON, IFUNC and TLS symbols and section groups even when unreferenced.
`link`/`linkBytes` instantiate the shared linker.

Supported build profile: `-fno-pic -no-pie` (plus `--no-relax` for `ld`), static, no
TLS/IFUNC/`.init_array`. Anything else is an explicit rejection.

`Checks` holds two small relocatable objects (a caller of `f` and its callee) that the
theorems in `Thms.lean` link and reject in controlled ways.
-/

@[expose] public section

namespace Silmaril.X86.Linking.Relocation

open Formats.ELF Formats.ELF.Link

def accepts (header : Header) : Bool :=
  header.machine == 62 && header.flags == 0 && header.osABI == 0 && header.abiVersion == 0

/-- The only kinds in this profile: 64, PC32, PLT32, 32 and 32S. -/
def supported (kind : Nat) : Prop := kind = 1 ∨ kind = 2 ∨ kind = 4 ∨ kind = 10 ∨ kind = 11

instance (kind : Nat) : Decidable (supported kind) := inferInstanceAs (Decidable (_ ∨ _))

def width (kind : Nat) : Nat := if kind = 1 then 8 else 4

/-- S+A-P for PC32/PLT32; S+A for the absolute kinds. -/
def value (r : ResolvedRelocation) : Int :=
  (r.symbolValue : Int) + r.addend - (if r.kind = 2 ∨ r.kind = 4 then (r.place : Int) else 0)

/-- This deliberately strict subset rejects absolute64 arithmetic wraparound.
32S accepts signed integer expressions; high unsigned representatives of negative
64-bit addresses are outside the profile. -/
def Fits (kind : Nat) (v : Int) : Prop :=
  if kind = 1 then 0 ≤ v ∧ v < 2 ^ 64
  else if kind = 10 then 0 ≤ v ∧ v < 2 ^ 32
  else -(2 ^ 31) ≤ v ∧ v < 2 ^ 31

instance (kind : Nat) (v : Int) : Decidable (Fits kind v) := by unfold Fits; infer_instance

def encodeLE : Nat → Nat → List (BitVec 8)
  | 0, _ => []
  | n + 1, v => BitVec.ofNat 8 v :: encodeLE n (v / 256)

def decodeLE : List (BitVec 8) → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * decodeLE rest

def encoded (kind : Nat) (v : Int) : Bytes :=
  (encodeLE (width kind) (v % (256 ^ width kind)).toNat).toArray

inductive Error where
  | unsupportedKind (kind : Nat)
  | invalidAddress
  | overflow (kind : Nat) (value : Int)
  | outOfBounds (offset width available : Nat)
  deriving DecidableEq, Repr

/-- A reusable diagnostic operation; the shared linker consumes its Option view. -/
def patch (r : ResolvedRelocation) (bytes : Bytes) : Except Error Patch :=
  if ¬ supported r.kind then .error (.unsupportedKind r.kind)
  else if ¬ (r.place < 2 ^ 64 ∧ r.symbolValue < 2 ^ 64) then .error .invalidAddress
  else if ¬ Fits r.kind (value r) then .error (.overflow r.kind (value r))
  else if ¬ (r.offset + width r.kind ≤ bytes.size) then
    .error (.outOfBounds r.offset (width r.kind) bytes.size)
  else .ok ⟨r.offset, encoded r.kind (value r)⟩

def relocate : Relocator := fun _ r bytes => (patch r bytes).toOption

/-- Reject selection/linkage mechanisms this static profile does not implement,
including unreferenced weak/COMMON/IFUNC/TLS symbols and section groups. -/
def staticObject (object : ObjectFile) : Bool :=
  object.symbols.all (fun symbol => symbol.binding ≤ 1 && symbol.kind ≤ 4 &&
    symbol.raw.other == 0 && (symbol.raw.sectionIndex < object.sections.length ||
      symbol.raw.sectionIndex == 0xfff1)) &&
  object.sections.all (fun part => part.header.kind != 17 &&
    (part.header.flags &&& 0x400) == 0)

/-- Checked linking of the shared section/symbol/relocation AST. -/
def link (objects : List ObjectFile) (layout : Layout) (absolute : AbsoluteSymbols := []) :
    Option (List LinkedSection) := do
  guard (objects.all staticObject)
  Formats.ELF.Link.link accepts relocate objects layout absolute

/-- The same operation on complete ET_REL byte inputs; parse failures remain failures. -/
def linkBytes (objects : List Bytes) (layout : Layout) (absolute : AbsoluteSymbols := []) :
    Option (List LinkedSection) := do
  let parsed ← objects.mapM readObject
  link parsed layout absolute

end Silmaril.X86.Linking.Relocation

namespace Silmaril.X86.Linking.Checks

open Formats.ELF Formats.ELF.Link Relocation

def header : Header := ⟨0, 0, 1, 62, 1, 0, 0, 0, 0, 64, 0, 0, 64, 2, 0⟩
def nullPart : ObjectSection := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, [], #[]⟩
def callerPart : ObjectSection := ⟨⟨0, 1, 6, 0, 0, 4, 0, 0, 4, 0⟩, [], #[0, 0, 0, 0]⟩
def calleePart : ObjectSection := ⟨⟨0, 1, 6, 0, 0, 1, 0, 0, 1, 0⟩, [], #[0x90]⟩
def nullSymbol : ObjectSymbol := ⟨⟨0, 0, 0, 0, 0, 0⟩, []⟩
def undefined : ObjectSymbol := ⟨⟨0, 16, 0, 0, 0, 0⟩, [102]⟩
def defined : ObjectSymbol := ⟨⟨0, 18, 0, 1, 0, 1⟩, [102]⟩
def caller : ObjectFile := ⟨header, [nullPart, callerPart], [nullSymbol, undefined], [⟨1, 0, 1, 2, 0⟩]⟩
def callee : ObjectFile := ⟨header, [nullPart, calleePart], [nullSymbol, defined], []⟩
def layout : Layout := [⟨⟨0, 1⟩, 0x1000⟩, ⟨⟨1, 1⟩, 0x1020⟩]

end Silmaril.X86.Linking.Checks
