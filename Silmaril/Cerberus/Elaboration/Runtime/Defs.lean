module

public import Silmaril.Cerberus.Elaboration.Construction.Defs

/-! Left-to-right runtime lookup from `translation_aux.lem:15–57` at Cerberus
`b3e11ea334e95359907d4abf9194f0e7fedc6c6a`. Inputs deliberately retain ordered
symbol representatives: the imported semantic-key `Map` forgets descriptions
and upstream iteration order. A caller using a runtime export must supply its
actual binding order. This interface does not reconstruct that order from `Map`.
-/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Runtime
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Construction

abbrev Binding := Sym × FunDecl Codec.wireModel Unit Unit

def firstMatching {α : Type} (predicate : α → Bool) : List α → Option α
  | [] => none
  | value :: rest => if predicate value then some value else firstMatching predicate rest

/-- Only `SD_Id` matches; a CN identifier with identical text does not. -/
def hasName (name : String) (symbol : Sym) : Bool :=
  match symbol.description with
  | .id text => text == name
  | _ => false

def fetchSymbol (symbols : List Sym) (name : String) : Except String Sym :=
  match firstMatching (hasName name) symbols with
  | some symbol => .ok symbol
  | none => .error ("[Translate_aux.fetch_stdlib_symbol] `" ++ name ++
      "' is required to be defined by the Core standard library.")

/-- The first named binding must be a pure Core function. A procedure does not
cause a search for a later function. Upstream adds no arity/type check here. -/
def standardCall (bindings : List Binding) (name : String) (arguments : List Pure) :
    Except String Pure :=
  match firstMatching (fun binding => hasName name binding.1) bindings with
  | some (symbol, .function _ _ _) => .ok (call (.sym symbol) arguments)
  | _ => .error ("[Translate_effect.E.mk_stdcall] `" ++ name ++ "' is not a Core standard function.")

end Silmaril.Cerberus.Elaboration.Runtime
