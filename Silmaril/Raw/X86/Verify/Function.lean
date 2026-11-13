module

public import Silmaril.Semantics.CPort.Formats.ELF.Extract.Defs
/-! # A checked, deliberately small ELF function boundary

The external generator proposes bytes and proof terms. This module independently
selects a unique named function from an x86-64 relocatable ELF object. The first
profile rejects *all* relocations targeting the function's section: relocation
widths and link-time edits are outside this boundary, including edits which
start before the symbol and overlap it.

`VerifiedFunction` binds a separately reviewed contract to the selected bytes.
It says nothing about process startup or loading a linked executable. Artifact
hash annotations are reproduction metadata; these equalities check the actual
embedded bytes.
-/

@[expose] public section

namespace Silmaril.X86.Verify

open Formats.ELF

/-- Select exactly one defined, nonempty STT_FUNC in an allocated executable
PROGBITS section, with no relocation targeting that section. -/
def selectFunction (object : ObjectFile) (name : NameBytes) : Option (List (BitVec 8)) := do
  guard (object.header.machine = X86_64.machine)
  let [symbol] := object.symbols.filter (fun symbol => symbol.name == name) | none
  guard (symbol.kind = 2 ∧ 0 < symbol.raw.size ∧ 0 < symbol.raw.sectionIndex)
  let owner ← object.sections[symbol.raw.sectionIndex]?
  guard (owner.header.kind = 1 ∧ owner.header.flags &&& 6 = 6)
  guard (object.relocations.all (fun relocation =>
    relocation.targetSection != symbol.raw.sectionIndex))
  let bytes ← object.symbolData symbol
  pure bytes.toList

/-- Parse and extract from the complete ELF, rather than trusting the
generator's symbol table, offsets, or disassembly. -/
def readFunction (raw : Bytes) (name : NameBytes) : Option (List (BitVec 8)) := do
  let object ← readObject raw
  selectFunction object name

/-- Compose an opaque parser certificate with a small extraction certificate. -/
theorem readFunction_of_object {raw : Bytes} {name : NameBytes} {object : ObjectFile}
    {code : List (BitVec 8)} (parsed : readObject raw = some object)
    (selected : selectFunction object name = some code) :
    readFunction raw name = some code := by
  simp only [readFunction, parsed, bind, Option.bind]
  exact selected

/-- A fixed artifact/symbol boundary together with a contract about precisely
the extracted code. A verifier must choose the contract independently of the
untrusted generator. -/
def VerifiedFunction (raw : Bytes) (name : NameBytes) (code : List (BitVec 8))
    (contract : List (BitVec 8) → Prop) : Prop :=
  readFunction raw name = some code ∧ contract code

/-- Kernel reduction only. Larger artifacts can supply compositional
`ObjectCertificates` proofs through `readFunction_of_object` instead. -/
macro "certify_function" : tactic => `(tactic| first | rfl | decide +kernel)

end Silmaril.X86.Verify
