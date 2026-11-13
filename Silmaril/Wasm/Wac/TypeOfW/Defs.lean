module

public import Silmaril.Wasm.Wac.TypeOf.Defs

/-!
# WAC: the kinds `TypeOf` infers, against the world decoder

`TypeOf.typeOf` infers a package's type by replaying a component's sections; `Bridge.pkgOfWorld`
reads the type off the component's *world* (its component type declarations, the reading of
`decodePkg`, whose agreement with the WIT encoder is `Bridge.DecodeAnon.decode_encode_anon` and
its companions). Both use the same decoder steps (`decExtern`, `decDefType`, `decAlias`).

A component is **world-shaped** when every section is a declaration of a world or has no
component-level type: imports, type definitions, type and instance-export aliases, core types,
exports with a type ascription, and custom sections, core modules and core instances.
`worldDecls ss` reads such sections as the world's declarations (`none` on any other section);
`worldSecs ds` writes declarations as sections. `TypeOf.runDecl` is the inference step of one
declaration.

`Silmaril.Wasm.Wac.TypeOfW.Thms`: `typeOf_world`, on a world-shaped component whose declarations
the world decoder reads (`pkgOfWorld ds = .ok r`), `typeOf` infers exactly `r`, kinds included.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.TypeOf

open Silmaril.Wasm Silmaril.Wasm.Component.Binary

/-- The aliases on which the inference and the world decoder take the same step: type aliases,
aliases of instance exports that are instances, and core aliases. -/
def AliasOk (a : Alias) : Prop :=
  a.sort = .type ∨ (a.sort = .instance ∧ ∃ i n, a.target = .export i n) ∨ ∃ k, a.sort = .core k

/-- A declaration both sides read the same way. -/
def DeclOk : ComponentDecl → Prop
  | .inst (.alias a) => AliasOk a
  | _ => True

/-- The declarations of a world-shaped section. -/
def secDecls : Section → Option (List ComponentDecl)
  | .imports xs => some (xs.map fun i => .import i.name i.desc)
  | .types xs => some (xs.map fun t => .inst (.type t))
  | .coreTypes xs => some (xs.map fun t => .inst (.coreType t))
  | .aliases xs => some (xs.map fun a => .inst (.alias a))
  | .exports xs => xs.mapM fun e => e.desc.map fun d => .inst (.export e.name d)
  | .custom .. | .coreModule _ | .coreInstances _ => some []
  | _ => none

/-- **The world of a world-shaped component**: its sections read as declarations. -/
def worldDecls (ss : List Section) : Option (List ComponentDecl) :=
  (ss.mapM secDecls).map List.flatten

/-- The sort of an item described by `d`. -/
def descSort : ExternDesc → ItemSort
  | .coreModule _ => .core .module
  | .func _ => .func
  | .value _ => .value
  | .type _ => .type
  | .component _ => .component
  | .instance _ => .instance

/-- A declaration as a section (an export of the item `0` of its sort, with the declared
type as ascription). -/
def declSec : ComponentDecl → Section
  | .import n d => .imports [⟨n, d⟩]
  | .inst (.type t) => .types [t]
  | .inst (.coreType t) => .coreTypes [t]
  | .inst (.alias a) => .aliases [a]
  | .inst (.export n d) => .exports [⟨n, ⟨descSort d, 0⟩, some d⟩]

/-- **A world written as a component**, one declaration per section. -/
def worldSecs (ds : List ComponentDecl) : List Section := ds.map declSec

/-- The inference step of one declaration. -/
def runDecl : ComponentDecl → TM Unit
  | .import n d => import_ ⟨n, d⟩
  | .inst (.type t) => type_ t
  | .inst (.coreType _) => pure ()
  | .inst (.alias a) => alias_ a
  | .inst (.export n d) => export_ ⟨n, ⟨descSort d, 0⟩, some d⟩

end Silmaril.Wasm.Wac.TypeOf
