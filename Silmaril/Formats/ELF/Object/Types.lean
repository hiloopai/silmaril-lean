module

public import Silmaril.Formats.ELF.Types

/-! Data-only semantic ELF records. No reader, machine model, or artifact proofs. -/
@[expose] public section
namespace Silmaril.Formats.ELF

abbrev NameBytes := List (BitVec 8)

structure ObjectSection where
  header : SectionHeader
  name : NameBytes
  /-- NOBITS sections allocate memory but supply no file bytes. -/
  data : Bytes
  deriving DecidableEq, Repr

structure ObjectSymbol where
  raw : Symbol
  name : NameBytes
  deriving DecidableEq, Repr

def ObjectSymbol.binding (symbol : ObjectSymbol) : Nat := symbol.raw.info / 16
def ObjectSymbol.kind (symbol : ObjectSymbol) : Nat := symbol.raw.info % 16

structure ObjectRelocation where
  targetSection : Nat
  offset : Nat
  symbol : Nat
  kind : Nat
  addend : Int
  deriving DecidableEq, Repr

structure ObjectFile where
  header : Header
  sections : List ObjectSection
  symbols : List ObjectSymbol
  relocations : List ObjectRelocation
  deriving DecidableEq, Repr

end Silmaril.Formats.ELF
