module

public import Silmaril.Wasm.Component.Binary.Defs
public import Silmaril.Wasm.Component.Binary.Encode.Defs

/-!
# Names of async functions in WIT encodings

The verified WIT encoder (`Silmaril.Wasm.Wit.Binary`) names an async function `[async]f` (and
`[async method]r.f`, `[async static]r.f`), the mangling of an earlier draft of the Component
Model's async ABI. wit-component 0.262.0 (wasm-tools 1.262.0) writes the plain names (`f`,
`[method]r.f`, `[static]r.f`) and marks the function *type* async, which the verified encoder
also does; wasm-tools 1.262.0 rejects the old names (`[async]process` is not a valid extern
name). This module renames them in an encoded component:

* `fixName`: the name rewrite; `fixDef`, `fixCDs`, `fixIDs`: in every component and instance
  type, nested;
* `fixAst`: in the type, import and export sections;
* `fixBytes`: parse, rename and encode again, **only** when the bytes contain `[async`; other
  bytes are returned unchanged (`fixBytes_of_not`), so outputs without async functions
  keep the encoder's bytes and the theorems about them.

Used on the outputs of `wasm-wac encode-wit` and of type-only documents.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.AsyncNames

open Silmaril.Wasm.Component.Binary

/-- The plain name of an async function. -/
def fixName (s : String) : String :=
  if s.startsWith "[async]" then s.drop 7 |>.toString
  else if s.startsWith "[async method]" then "[method]" ++ (s.drop 14).toString
  else if s.startsWith "[async static]" then "[static]" ++ (s.drop 14).toString
  else s

def fixEN (n : ExternName) : ExternName := { n with name := fixName n.name }

mutual
def fixDef : DefType → DefType
  | .component ds => .component (fixCDs ds)
  | .instance ds => .instance (fixIDs ds)
  | d => d
def fixID : InstanceDecl → InstanceDecl
  | .type t => .type (fixDef t)
  | .export n d => .export (fixEN n) d
  | x => x
def fixIDs : List InstanceDecl → List InstanceDecl
  | [] => []
  | x :: r => fixID x :: fixIDs r
def fixCDs : List ComponentDecl → List ComponentDecl
  | [] => []
  | .import n d :: r => .import (fixEN n) d :: fixCDs r
  | .inst i :: r => .inst (fixID i) :: fixCDs r
end

def fixDefs : List DefType → List DefType
  | [] => []
  | d :: r => fixDef d :: fixDefs r

def fixSection : Section → Section
  | .types xs => .types (fixDefs xs)
  | .imports xs => .imports (xs.map fun i => { i with name := fixEN i.name })
  | .exports xs => .exports (xs.map fun e => { e with name := fixEN e.name })
  | s => s

def fixAst (a : Ast) : Ast := .mk (a.sections.map fixSection)

/-- Do the bytes contain `[async`? -/
def hasAsync (b : ByteArray) : Bool :=
  let pat := "[async".toUTF8
  (List.range (b.size + 1 - pat.size)).any fun i =>
    (List.range pat.size).all fun j => b.get! (i + j) == pat.get! j

/-- **Plain names for async functions**: the bytes again with the names rewritten, when they
contain `[async` and parse; otherwise unchanged. -/
def fixBytes (b : ByteArray) : ByteArray :=
  if hasAsync b then
    match parse b with
    | .ok a => (encode (fixAst a)).getD b
    | .error _ => b
  else b

theorem fixBytes_of_not {b : ByteArray} (h : hasAsync b = false) : fixBytes b = b := by
  simp [fixBytes, h]

end Silmaril.Wasm.Wac.AsyncNames
