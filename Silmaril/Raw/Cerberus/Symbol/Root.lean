module

/-! # Cerberus locations, identifiers and symbols

The types of Cerberus's `frontend/model/loc.lem` and `frontend/model/symbol.lem`
at commit `b3e11ea334e95359907d4abf9194f0e7fedc6c6a`. Only types are ported; the
fresh-symbol generators and printers are not. `Silmaril.Cerberus.Names` maps each
Cerberus name to its Silmaril name.

## Equality

Lem's equality on identifiers compares only their text (`idEqual`), and its
equality on symbols compares only the digest and the number (`symbolEqual`).
Lean's derived `=` is structural, so it also compares locations and symbol
descriptions. Wherever Cerberus compares identifiers or symbols with `=`, the
port compares their `key`s instead: `a.key = b.key` is Lem's equality, and it is
decidable. `Silmaril.Cerberus.Map` keys its bindings the same way.
-/

@[expose] public section

namespace Silmaril.Cerberus

/-- A source location. Lem leaves `Loc.t` abstract; these are the four forms of
the OCaml `Cerb_location.t` that the wire format carries, without cursors. -/
inductive Loc where
  | unknown
  | other (description : String)
  | point (file : String) (line column : Int)
  | region (startFile : String) (startLine startColumn : Int)
      (endFile : String) (endLine endColumn : Int)
  deriving DecidableEq, Repr

/-- A C identifier and where it occurs. -/
structure Identifier where
  loc : Loc
  name : String
  deriving DecidableEq, Repr

/-- What Lem's equality on identifiers compares: the text, not the location. -/
def Identifier.key (x : Identifier) : String := x.name

/-- The digest identifying a translation unit. Lem leaves it abstract. Cerberus
uses the 16-byte MD5 digest (`Digest.t`) of the C file, and the empty digest for
its standard library.

TODO: once Core files live in the content-addressed store, this becomes the
repository's 32-byte content ID (SHA-256 or BLAKE3). -/
structure Digest where
  bytes : List UInt8
  deriving DecidableEq, Repr

/-- What a symbol was created for; Cerberus uses it only for printing. -/
inductive SymbolDescription where
  | none
  | unnamedTag : Loc → SymbolDescription
  | id : String → SymbolDescription
  | cnId : String → SymbolDescription
  | objectAddress : String → SymbolDescription
  | return_
  | funArgValue : String → SymbolDescription
  | funArg : Loc → Nat → SymbolDescription
  deriving DecidableEq, Repr

/-- A symbolic name: the translation unit's digest, a number unique within it,
and a description for printing. -/
structure Sym where
  digest : Digest
  number : Nat
  description : SymbolDescription
  deriving DecidableEq, Repr

/-- What Lem's equality and ordering on symbols compare: the digest and the
number, not the description. Compare symbols with `a.key = b.key`, never with
`a = b`, wherever Cerberus compares them: environment and label lookups,
substitution, and struct, union and enum tags inside types. -/
def Sym.key (s : Sym) : Digest × Nat := (s.digest, s.number)

theorem Sym.key_eq_iff {s t : Sym} :
    s.key = t.key ↔ s.digest = t.digest ∧ s.number = t.number := by
  simp [Sym.key]

theorem Identifier.key_eq_iff {x y : Identifier} : x.key = y.key ↔ x.name = y.name :=
  Iff.rfl

/-- The origin of an allocation, carried by `create` actions. -/
inductive Prefix where
  | source : Loc → List Sym → Prefix
  | funArg : Loc → Digest → Int → Prefix
  | stringLiteral : Loc → Digest → Prefix
  | compoundLiteral : Loc → Digest → Prefix
  | malloc
  | temporaryLifetime : Loc → Digest → Prefix
  | other : String → Prefix
  deriving DecidableEq, Repr

end Silmaril.Cerberus
