module
public import Silmaril.Formats.Json.Defs
public import Silmaril.Formats.Binary.Thms
public import Silmaril.Raw.Formats.Json.Parser
@[expose] public section
namespace Silmaril.Formats.Json

/-- Parse a complete UTF-8 JSON or JSON5 document with a lossless CST. -/
def parseCst? (dialect : Dialect) (bytes : Bytes) : Option Cst := do
  let (ast, tokens) ← Internal.decode dialect bytes
  concrete? bytes ast tokens

/-- Full RFC string grammar (including lone surrogate escapes), ordered
members, duplicate names, and exact finite decimal numbers. -/
def parseDecimal? (dialect : Dialect) (bytes : Bytes) : Option (Ast Decimal) := do
  let (ast, _) ← Internal.decode dialect bytes
  mapNumbers? (fun | .finite d => some d | _ => none) ast

def parse? : Bytes → Option (Ast Decimal) := parseDecimal? .rfc8259

def parseJsonc? : Bytes → Option (Ast Decimal) := parseDecimal? .jsonc

def parseJson5? (bytes : Bytes) : Option (Ast Number) :=
  (Internal.decode .json5 bytes).map Prod.fst

/-- A simpler exact-integer model, accepting precisely integral decimal values.
For example `1e2` denotes the same integer as `100`. -/
def parseInteger? (bytes : Bytes) : Option (Ast Int) :=
  (parse? bytes).bind (mapNumbers? Decimal.toInt?)

abbrev IsJsonSlice := IsSlice parse?

/-- Syntactic validity of a CST is separate from its lossless byte partition. -/
def IsCst (dialect : Dialect) (cst : Cst) : Prop :=
  Internal.decode dialect cst.source = some (cst.ast, cst.events)

theorem parseCst?_sound {dialect : Dialect} {bytes : Bytes} {cst : Cst}
    (h : parseCst? dialect bytes = some cst) : cst.source = bytes ∧ IsCst dialect cst := by
  unfold parseCst? at h
  cases hd : Internal.decode dialect bytes with
  | none => simp [hd] at h
  | some pair =>
    obtain ⟨ast, tokens⟩ := pair
    simp only [hd] at h
    change concrete? bytes ast tokens = some cst at h
    obtain ⟨hs, ha, ht⟩ := concrete?_fields h
    exact ⟨hs, by simpa only [IsCst, hs, ha, ht] using hd⟩

end Silmaril.Formats.Json
