module

public import Silmaril.Cerberus.Names.Defs
public import Silmaril.Semantics.CPort.Encoding.TaggedCodec.Defs
public meta import Silmaril.Cerberus.Schema.Reflect.Defs

/-! # Constructor tags from the Cerberus name map

`tag% Type.constructor` resolves a Silmaril constructor and reads its Lem name
from `Names.types`. Unrenamed constructors retain their names. `recordTag% Type`
reads the unqualified Lem record name. Both elaborate to string literals, so
there is no name-map search during encoding or decoding. Changing `Names`
rebuilds the codecs; a missing entry or a non-constructor is an elaboration error.
`alt% Type.constructor fields`, `leaf% Type.constructor` and
`leafPair% Type.constructor` derive the tag and result constructor from the
same reference. `recordAlt% Type.mk fields` does the same for record tags.
The generic constructor syntax unpacks fields in constructor order; codec
encoder obligations check against these alternatives. Payload codecs still
specify wire field grouping and order explicitly.
The OCaml-backed locations, memory values and document header use the fixed
`$` tags specified by the wire contract.
-/

public meta section

namespace Silmaril.Cerberus.Codec

open Lean Elab Term Meta

private def nameEntry (type : Lean.Name) : TermElabM Names.TypeName := do
  let entries : List Names.TypeName ← reduceEval (mkConst ``Names.types)
  let some entry := entries.find? (·.silmaril == type)
    | throwError "no Cerberus name entry for {type}"
  return entry

elab "tag% " ctor:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo ctor
  let .ctorInfo info ← getConstInfo name | throwError "{name} is not a constructor"
  let entry ← nameEntry info.induct
  let short := name.getString!
  let tag := (entry.renames.find? (·.2 == short)).map Prod.fst |>.getD short
  return toExpr tag

elab "recordTag% " type:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo type
  unless isStructure (← getEnv) name do throwError "{name} is not a record"
  let entry ← nameEntry name
  return toExpr (entry.cerberus.splitOn "." |>.getLast!)

open Silmaril.TaggedCodec

/-- A payload alternative with its tag and constructor bound together. -/
macro "alt% " ctor:ident fields:term:max : term =>
  `(ctorAlt% $ctor (tag% $ctor) $fields)

/-- A nullary alternative with its tag and constructor bound together. -/
macro "leaf% " ctor:ident : term => `(ctorLeaf% $ctor (tag% $ctor))

/-- A nullary entry for `ofLeaves`, with its tag and constructor bound together. -/
macro "leafPair% " ctor:ident : term => `(ctorPair% $ctor (tag% $ctor))

/-- A record alternative identified by its constructor alone. -/
elab "recordAlt% " ctor:ident fields:term:max : term <= expectedType => do
  let info ← constructorInfo ctor
  let type := mkIdent info.induct
  elabTerm (← `(ctorAlt% $ctor (recordTag% $type) $fields)) expectedType

end Silmaril.Cerberus.Codec
