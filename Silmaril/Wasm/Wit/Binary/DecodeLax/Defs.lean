module

public import Silmaril.Wasm.Wit.Binary.Embed.Defs

/-!
# Embedded worlds with async functions named as wit-component 0.262 names them

`Silmaril.Wasm.Wit.Binary.Decode` reads an async function only under an async name (`[async]f`,
`[async method]r.f`, `[async static]r.f`) and rejects an async function type under a plain
name (`name and type disagree on async`). wit-component 0.262.0 (`wasm-tools component embed`
1.262.0) writes the plain name `f` with an async function type: the asyncness is in the type
only. This module reads both:

* `normDecls` walks the declarations of a component or instance type, tracks which type
  indices are async function types (every declaration that allocates a type index: type
  definitions, type aliases, type imports and type exports), and gives each function import or
  export of an async type the async form of its name (`asyncName`), in nested component and
  instance types too. Names already in the async form are unchanged, so the normalization is
  idempotent and leaves wasm-wit's own encoding as it is.
* `decodeWorldTypeLax` / `extractWorldTypeLax`: the normalization, then the decoder of
  `Silmaril.Wasm.Wit.Binary.Custom` (`decodeWorldTypeSections`), unchanged.
* `decodeWorldFull`: the same, keeping more: the world's declarations as written (for
  `wasm-jco`, which copies them into the component it emits) and the bodies of the world's
  interface imports and exports, which the decoder's `World` refers to by name only.

The decoder itself is not modified (it is imported by the WIT tools and their theorems).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary

open Silmaril.Wasm.Component.Binary

/-! ## Async names -/

/-- The async form of a function name: `f ↦ [async]f`, `[method]r.f ↦ [async method]r.f`,
`[static]r.f ↦ [async static]r.f`; names already async (or constructors, never async) are
unchanged. -/
def asyncName (n : String) : String :=
  let cs := n.toList
  if (dropPrefix? pAsync cs).isSome || (dropPrefix? pAsyncMethod cs).isSome ||
      (dropPrefix? pAsyncStatic cs).isSome then n
  else match dropPrefix? pMethod cs with
    | some r => String.ofList (pAsyncMethod ++ r)
    | none => match dropPrefix? pStatic cs with
      | some r => String.ofList (pAsyncStatic ++ r)
      | none => if cs.head? = some '[' then n else String.ofList (pAsync ++ cs)

/-- Rename an async function's name. -/
def normName (async : Bool) (e : ExternName) : ExternName :=
  if async then { e with name := asyncName e.name } else e

/-- Whether a type definition is an async function type. -/
def defIsAsyncFunc : DefType → Bool
  | .func f => f.async
  | _ => false

/-- Whether an extern description allocates a type index. -/
def descIsType : ExternDesc → Bool
  | .type _ => true
  | _ => false

/-! ## Normalizing component and instance types

`tys` lists, for every type index of the scope so far, whether it is an async function type. -/

mutual
/-- A type definition with its nested component and instance types normalized. -/
def normDefType : DefType → DefType
  | .component ds => .component (normCompDecls [] ds)
  | .instance ds => .instance (normInstDecls [] ds)
  | t => t

/-- The declarations of an instance type. -/
def normInstDecls (tys : List Bool) : List InstanceDecl → List InstanceDecl
  | [] => []
  | .type t :: ds => .type (normDefType t) :: normInstDecls (tys ++ [defIsAsyncFunc t]) ds
  | .alias a :: ds =>
    .alias a :: normInstDecls (if a.sort = .type then tys ++ [false] else tys) ds
  | .export n d :: ds =>
    match d with
    | .func k => .export (normName (tys.getD k false) n) d :: normInstDecls tys ds
    | _ => .export n d :: normInstDecls (if descIsType d then tys ++ [false] else tys) ds
  | .coreType t :: ds => .coreType t :: normInstDecls tys ds

/-- The declarations of a component type. -/
def normCompDecls (tys : List Bool) : List ComponentDecl → List ComponentDecl
  | [] => []
  | .import n d :: ds =>
    match d with
    | .func k => .import (normName (tys.getD k false) n) d :: normCompDecls tys ds
    | _ => .import n d :: normCompDecls (if descIsType d then tys ++ [false] else tys) ds
  | .inst (.type t) :: ds => .inst (.type (normDefType t)) :: normCompDecls (tys ++ [defIsAsyncFunc t]) ds
  | .inst (.alias a) :: ds =>
    .inst (.alias a) :: normCompDecls (if a.sort = .type then tys ++ [false] else tys) ds
  | .inst (.export n d) :: ds =>
    match d with
    | .func k => .inst (.export (normName (tys.getD k false) n) d) :: normCompDecls tys ds
    | _ => .inst (.export n d) :: normCompDecls (if descIsType d then tys ++ [false] else tys) ds
  | .inst (.coreType t) :: ds => .inst (.coreType t) :: normCompDecls tys ds
end

/-- The sections of a `component-type` payload, normalized. -/
def normSections : List Section → List Section :=
  List.map fun
    | .types ts => .types (ts.map normDefType)
    | s => s

/-! ## Decoding -/

/-- `decodeWorldType`, reading async functions under plain names too. -/
def decodeWorldTypeLax (b : ByteArray) :
    Except String (PackageName × String × World × StringEncoding) := do
  match parse b with
  | .ok (.mk ss) => decodeWorldTypeSections (normSections ss)
  | .error _ => throw "malformed component"

/-- `extractWorldType`, reading async functions under plain names too. -/
def extractWorldTypeLax (m : ByteArray) :
    Except String (PackageName × String × World × StringEncoding) := do
  decodeWorldTypeLax (← extractPayload m)

/-- A world with what `wasm-jco` needs besides the decoded `World`. -/
structure WorldFull where
  pkg : PackageName
  name : String
  world : World
  encoding : StringEncoding
  /-- The declarations of the world's component type, as written (not normalized). -/
  decls : List ComponentDecl
  /-- The world's imports and exports with the bodies of their interfaces. -/
  imports : List DItem
  exports : List DItem

/-- Decode a `component-type` payload, keeping the declarations and interface bodies. -/
def decodeWorldFull (b : ByteArray) : Except String WorldFull := do
  match parse b with
  | .ok (.mk ss) =>
    match ss with
    | .custom "wit-component-encoding" _ :: .types [.component top] :: _ =>
      let (p, n, w, se) ← decodeWorldTypeSections (normSections ss)
      match top with
      | [.inst (.type (.component wds)), _] =>
        let s ← compSteps {} (normCompDecls [] wds)
        pure ⟨p, n, w, se, wds, s.imports, s.exports⟩
      | _ => throw "malformed world wrapper"
    | _ => throw "malformed component-type payload"
  | .error _ => throw "malformed component"

/-- The full world a core module embeds. -/
def extractWorldFull (m : ByteArray) : Except String WorldFull := do
  decodeWorldFull (← extractPayload m)

end Silmaril.Wasm.Wit.Binary
