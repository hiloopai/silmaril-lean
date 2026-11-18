module

public import Silmaril.Formats.Json.Defs

/-!
# Lean-NDJSON: the lean4export 3.1.0 export format, as typed events

`lean4export` (format version **3.1.0**) writes a Lean environment fragment as newline-delimited
JSON: a metadata object, then one record per line. Names, universe levels and expressions are
**tables**: a record `{"in": i, …}` defines name `i`, `{"il": i, …}` level `i`, `{"ie": i, …}`
expression `i`, and records refer to earlier entries by these ids, so shared subterms are written
once. Name `0` (anonymous) and level `0` (zero) are implicit; expression ids start at `0`.
Declarations (`axiom`, `def`, `thm`, `opaque`, `quot`, and `inductive` blocks with their
constructors and recursors) refer to the tables.

This module is the typed shape of those records (`Event`), the keys each record defines
(`Event.keys`) and the keys it refers to (`Event.references`). Decoding is `…LeanNDJSON.Decode`
and reference validation `…LeanNDJSON.Validate`.

**Provenance.** The event types, the strict decoder and the reference validator are adapted from
the moria project's Lean-NDJSON decoder, with attribution; this port adds the `quot` records and
the `inductive` blocks (types, constructors, recursors) that real exports contain.

**Not supported** (decoding fails): `mdata` expressions (lean4export omits them unless run with
`--export-mdata`), and any record shape or field outside format 3.1.0.
-/

@[expose] public section

namespace Silmaril.Formats.LeanNDJSON

/-- The tables records define entries of. -/
inductive Table where
  | name | level | expr | declaration
  deriving DecidableEq, Repr

/-- A table entry: a table and an id. Declarations are keyed by their name's id. -/
structure Key where
  table : Table
  index : Nat
  deriving DecidableEq, Repr

inductive BinderInfo where
  | default | implicit | strictImplicit | instImplicit
  deriving DecidableEq, Repr

/-- A name: a string or a number after a prefix name. -/
inductive NameNode where
  | str (parent : Nat) (value : String)
  | num (parent value : Nat)
  deriving DecidableEq, Repr

/-- A universe level, over earlier levels and names. -/
inductive LevelNode where
  | succ (level : Nat)
  | max (left right : Nat)
  | imax (left right : Nat)
  | param (name : Nat)
  deriving DecidableEq, Repr

/-- An expression, over earlier expressions, levels and names. -/
inductive ExprNode where
  | bvar (index : Nat)
  | sort (level : Nat)
  | const (name : Nat) (levels : List Nat)
  | app (function argument : Nat)
  | lam (name type body : Nat) (info : BinderInfo)
  | forallE (name type body : Nat) (info : BinderInfo)
  | letE (name type value body : Nat) (nondep : Bool)
  | proj (typeName index target : Nat)
  /-- A natural-number literal, in decimal. -/
  | natVal (value : String)
  | strVal (value : String)
  deriving DecidableEq, Repr

inductive Safety where
  | safeCode | unsafeCode | partialCode
  deriving DecidableEq, Repr

inductive Hints where
  | opaque | abbrev | regular (height : Nat)
  deriving DecidableEq, Repr

inductive QuotKind where
  | type | ctor | lift | ind
  deriving DecidableEq, Repr

/-- One inductive type of a block. -/
structure InductiveType where
  name : Nat
  levelParams : List Nat
  type : Nat
  numParams : Nat
  numIndices : Nat
  all : List Nat
  ctors : List Nat
  numNested : Nat
  isRec : Bool
  isUnsafe : Bool
  isReflexive : Bool
  deriving DecidableEq, Repr

/-- One constructor of a block. -/
structure Constructor where
  name : Nat
  levelParams : List Nat
  type : Nat
  induct : Nat
  cidx : Nat
  numParams : Nat
  numFields : Nat
  isUnsafe : Bool
  deriving DecidableEq, Repr

/-- One recursor rule: a constructor, its number of fields, the right-hand side. -/
structure RecursorRule where
  ctor : Nat
  nfields : Nat
  rhs : Nat
  deriving DecidableEq, Repr

/-- One recursor of a block. -/
structure Recursor where
  name : Nat
  levelParams : List Nat
  type : Nat
  all : List Nat
  numParams : Nat
  numIndices : Nat
  numMotives : Nat
  numMinors : Nat
  rules : List RecursorRule
  k : Bool
  isUnsafe : Bool
  deriving DecidableEq, Repr

/-- A declaration record. -/
inductive Declaration where
  | axiomCode (name : Nat) (levelParams : List Nat) (type : Nat) (isUnsafe : Bool)
  | definitionCode (name : Nat) (levelParams : List Nat) (type value : Nat)
      (hints : Hints) (safety : Safety) (all : List Nat)
  | theoremCode (name : Nat) (levelParams : List Nat) (type value : Nat) (all : List Nat)
  | opaqueCode (name : Nat) (levelParams : List Nat) (type value : Nat) (isUnsafe : Bool)
      (all : List Nat)
  | quot (name : Nat) (levelParams : List Nat) (type : Nat) (kind : QuotKind)
  /-- A (mutual) inductive block with its constructors and recursors. -/
  | inductive (types : List InductiveType) (ctors : List Constructor) (recs : List Recursor)
  deriving DecidableEq, Repr

/-- A record after the metadata line. -/
inductive Event where
  | name (index : Nat) (node : NameNode)
  | level (index : Nat) (node : LevelNode)
  | expr (index : Nat) (node : ExprNode)
  | declaration (node : Declaration)
  deriving DecidableEq, Repr

/-- The names a declaration record declares. -/
def Declaration.names : Declaration → List Nat
  | .axiomCode n .. | .definitionCode n .. | .theoremCode n .. | .opaqueCode n ..
  | .quot n .. => [n]
  | .inductive ts cs rs => ts.map (·.name) ++ cs.map (·.name) ++ rs.map (·.name)

/-- The table entries a record defines. -/
def Event.keys : Event → List Key
  | .name i _ => [⟨.name, i⟩]
  | .level i _ => [⟨.level, i⟩]
  | .expr i _ => [⟨.expr, i⟩]
  | .declaration d => d.names.map (⟨.declaration, ·⟩)

def NameNode.references : NameNode → List Key
  | .str p _ | .num p _ => [⟨.name, p⟩]

def LevelNode.references : LevelNode → List Key
  | .succ l => [⟨.level, l⟩]
  | .max a b | .imax a b => [⟨.level, a⟩, ⟨.level, b⟩]
  | .param n => [⟨.name, n⟩]

def ExprNode.references : ExprNode → List Key
  | .bvar _ | .natVal _ | .strVal _ => []
  | .sort l => [⟨.level, l⟩]
  | .const n ls => ⟨.name, n⟩ :: ls.map (⟨.level, ·⟩)
  | .app f a => [⟨.expr, f⟩, ⟨.expr, a⟩]
  | .lam n t b _ | .forallE n t b _ => [⟨.name, n⟩, ⟨.expr, t⟩, ⟨.expr, b⟩]
  | .letE n t v b _ => [⟨.name, n⟩, ⟨.expr, t⟩, ⟨.expr, v⟩, ⟨.expr, b⟩]
  | .proj n _ s => [⟨.name, n⟩, ⟨.expr, s⟩]

/-- Names in a list. -/
def nameKeys (ns : List Nat) : List Key := ns.map (⟨.name, ·⟩)

def InductiveType.references (t : InductiveType) : List Key :=
  nameKeys (t.name :: t.levelParams ++ t.all ++ t.ctors) ++ [⟨.expr, t.type⟩]

def Constructor.references (c : Constructor) : List Key :=
  nameKeys (c.name :: c.induct :: c.levelParams) ++ [⟨.expr, c.type⟩]

def Recursor.references (r : Recursor) : List Key :=
  nameKeys (r.name :: r.levelParams ++ r.all ++ r.rules.map (·.ctor)) ++
    ⟨.expr, r.type⟩ :: r.rules.map (⟨.expr, ·.rhs⟩)

def Declaration.references : Declaration → List Key
  | .axiomCode n ps t _ | .quot n ps t _ => nameKeys (n :: ps) ++ [⟨.expr, t⟩]
  | .definitionCode n ps t v _ _ all | .theoremCode n ps t v all | .opaqueCode n ps t v _ all =>
    nameKeys (n :: ps ++ all) ++ [⟨.expr, t⟩, ⟨.expr, v⟩]
  | .inductive ts cs rs =>
    ts.flatMap (·.references) ++ cs.flatMap (·.references) ++ rs.flatMap (·.references)

def Event.references : Event → List Key
  | .name _ n => n.references
  | .level _ l => l.references
  | .expr _ e => e.references
  | .declaration d => d.references

end Silmaril.Formats.LeanNDJSON
