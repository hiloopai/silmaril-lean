module

public import Silmaril.Wasm.Wac.Bridge.ComposeXV.Defs
public import Silmaril.Wasm.Wac.Embed.Defs
public import Silmaril.Wasm.Wac.Splice.Defs
public import Silmaril.Wasm.Component.Binary.Encode.Defs
public import Silmaril.Wasm.Perf.Splice.Defs

/-!
# WAC: compositions as component binaries (`wasm-wac compose --wasm`, `wasm-wac plug`)

The pipeline of `wasm-wac compose` (`Bridge.composeWatXV`: text, `ofDocX`, elaboration with
validation, `Bridge.encode`) stops at the component AST (`composeAst`), and that AST is
written as a component binary by the verified encoder of `Silmaril.Wasm.Component.Binary`
(`composeWasm`):

* with `embed = false` the packages stay imports `unlocked-dep=<ns:name>`
  (`wac compose --import-dependencies`);
* with `embed = true` every package is defined inside the composition (`Embed.embed`, the
  default of `wac compose`), from the components read from the dependency directory, so the
  binary runs on its own.

`Silmaril.Wasm.Wac.Emit.Thms` states the entry-point theorem `composeWasm_correct`: the bytes
parse back to the (embedded) encoding of the elaborated composition graph, which lowers to the
graph's direct translation, and its denotation in the component IR is that of the graph, so
equivalent packages give equivalent compositions (`composeWasm_congr`).

**`plug`.** `wac plug SOCKET --plug P₁ … --plug Pₙ` (wac-graph's `plug`, wac `5a7480c`):
each plug that exports a name the socket imports is instantiated, its matching exports are
the socket's arguments of the same name, the other imports of plugs and socket are promoted,
and every export of the socket is exported. `plugDoc` writes this as a WAC document over the
package keys `plug:socket`, `plug:p0`, … (`plugKey`); `wasm-wac plug` composes it with
`composeWasm`, so `composeWasm_correct` is its correctness theorem too. A plug that matches
no import is an error, as in wac (`no plug matched`); when several plugs export the same
name the last one is the argument (wac sets the argument again).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Emit

open Silmaril.Wasm
open Silmaril.Wasm.Component.Binary

/-- The nominal table the encoder sees. -/
def nomOf (noms : List (String × Bridge.NomTable)) (d : FuncAlias.Document) : Bridge.NomTable :=
  Bridge.docNom d.forget ++ noms.flatMap (·.2)

/-- The validation tables. -/
def tablesOf (noms : List (String × Bridge.NomTable)) (d : FuncAlias.Document) : Valid.Tables :=
  { doc := Bridge.docNom d.forget, pkgs := noms }

/-- Elaborate and validate, with the tool's error messages. -/
def elabGraph (env : PkgEnv) (noms : List (String × Bridge.NomTable)) (d : FuncAlias.Document) :
    Except String CGraph :=
  match Bridge.elabDocXV (tablesOf noms d) env d with
  | .ok g => .ok g
  | .error (.elab e) => .error s!"elaboration: {reprStr e}"
  | .error (.valid e) => .error s!"validation: {reprStr e}"

/-- **The composition as a component AST** (the pipeline of `Bridge.composeWatXV` before
printing). -/
def composeAst (env : PkgEnv) (noms : List (String × Bridge.NomTable)) (d : FuncAlias.Document) :
    Except String Ast := do
  let g ← elabGraph env noms d
  Bridge.encode (nomOf noms d) g

/-- Embed the packages when asked. -/
def finish (pkgs : List (String × Ast)) (embed : Bool) (c : Ast) : Ast :=
  if embed then Embed.embed (Embed.table pkgs) c else c

/-- The component binary of an AST, by the verified encoder. -/
def toBytes (c : Ast) : Except String ByteArray :=
  match encode c with
  | some b => .ok b
  | none => .error "the composition has a number or length of 2^32 or more"

/-- **`wasm-wac compose --wasm`**: the composition as a component binary; `pkgs` are the
packages' components by key (only read when `embed`). -/
def composeWasm (env : PkgEnv) (noms : List (String × Bridge.NomTable))
    (pkgs : List (String × Ast)) (embed : Bool) (d : FuncAlias.Document) :
    Except String ByteArray := do
  let c ← composeAst env noms d
  toBytes (finish pkgs embed c)

/-- **`wasm-wac compose --wasm`, as the tool runs it**: the packages' bytes `raw` (by key)
are spliced in unchanged (`Splice.splice`), so packages outside the binary AST (async
built-ins) can be embedded too. On packages whose bytes are canonical encodings this is
`composeWasm … true` (`Emit.composeWasmRaw_eq`). -/
def composeWasmRaw (env : PkgEnv) (noms : List (String × Bridge.NomTable))
    (raw : List (String × ByteArray)) (d : FuncAlias.Document) : Except String ByteArray := do
  let c ← composeAst env noms d
  match Silmaril.Wasm.Perf.Splice.spliceF (Splice.table raw) c with
  | some b => .ok b
  | none => .error "the composition has a number or length of 2^32 or more"

/-- A package type from a WIT package with one world (`wasm-wit encode`, `wasm-tools
component wit --wasm`): the world's imports and exports. Used for packages the component
binary AST cannot read (their declared type, trusted; the output is validated by
`wasm-tools validate` in the tests). -/
def pkgOfWitWorld (b : ByteArray) : Except String (PkgType × Bridge.NomTable) := do
  let (p, nom) ← Bridge.decodePkg b
  match p.defs.filterMap (fun | (_, .type (.comp _ is es)) => some (is, es) | _ => none) with
  | [(is, es)] => pure ({ imports := is, exports := es }, nom)
  | _ => throw "the WIT package does not have exactly one world"

/-! ## Plug -/

/-- The package key of the socket. -/
def socketKey : String := "plug:socket"

/-- The package key of plug `i`. -/
def plugKey (i : Nat) : String := s!"plug:p{i}"

/-- A WAC string literal. -/
def lit (s : String) : String := "\"" ++ s ++ "\""

/-- The names of the socket's imports that plug `exps` satisfies. -/
def matched (socket : PkgType) (exps : Externs) : List String :=
  (exps.map (·.1)).filter fun n => (socket.imports.lookup n).isSome

/-- The plugs that match, with their index and matched names. -/
def usedPlugs (socket : PkgType) (plugs : List PkgType) : List (Nat × List String) :=
  (plugs.zipIdx.map fun (p, i) => (i, matched socket p.exports)).filter (!·.2.isEmpty)

/-- The argument of each satisfied socket import: the last plug exporting it. -/
def plugArgs (used : List (Nat × List String)) : List (String × Nat) :=
  let all := used.flatMap fun (i, ns) => ns.map (·, i)
  (all.map (·.1)).eraseDups.map fun n => (n, ((all.filter (·.1 == n)).getLast?.map (·.2)).getD 0)

/-- **The WAC document of `wac plug`.** -/
def plugDoc (socket : PkgType) (plugs : List PkgType) : Except String String := do
  let used := usedPlugs socket plugs
  if used.isEmpty then throw "no plug matched an import of the socket"
  let unused := (plugs.zipIdx.filter fun (p, _) => (matched socket p.exports).isEmpty).map (·.2)
  if !unused.isEmpty then throw s!"plug {unused} matched no import of the socket"
  let lets := used.map fun (i, _) => s!"let p{i} = new {plugKey i} \{ ... };"
  let args := (plugArgs (used)).map fun (n, i) => s!"{lit n}: p{i}[{lit n}], "
  let sock := s!"let socket = new {socketKey} \{ {String.join args}... };"
  let exps := socket.exports.map fun (n, _) => s!"export socket[{lit n}];"
  pure (String.intercalate "\n" (["package plug:composition;"] ++ lets ++ [sock] ++ exps) ++ "\n")

/-- The package environment of a plug document. -/
def plugEnv (socket : PkgType) (plugs : List PkgType) : PkgEnv :=
  (socketKey, socket) :: plugs.zipIdx.map fun (p, i) => (plugKey i, p)

end Silmaril.Wasm.Wac.Emit
