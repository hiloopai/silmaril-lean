module

public import Silmaril.Wasm.Wac.EndToEndR.Defs
public import Silmaril.Wasm.Wac.NameAttrs.Defs
public import Silmaril.Wasm.Wac.TypeOfX.Defs

/-!
# `wasm-tools compose` (deprecated upstream) mapped to `wasm-wac`

Upstream's `compose` is `wasm-compose`'s `ComponentComposer`: starting from the root component,
every **instance import** `n` of an instantiated component is satisfied, in breadth-first order,

1. by an instance export named `n` of a definition component (`-d`), else
2. by an instance of the component found as `n.wasm`/`n.wat` in the root's directory or a
   search path (`-p`), instantiated once per name, whose own imports are then processed; the
   import takes the whole instance when its type is a subtype of the import's, else a
   compatible export of it, else the composition fails; else
3. it stays an import of the composition (refused with `--no-imports`).

The composition exports the root instance's exports. This module keeps that resolution as data
(`Inst`, `Target`: who satisfies each import, decided in the CLI layer from the files, with the
choice of `argTarget`) and maps the resolved graph to a **WAC document** (`wacText`): one
`let` per instance in dependency order (`order`), arguments by import name, `...` for the
imports left open, and `export root...;`. `wasm-wac`'s verified pipeline composes it
(`compose`: `EndToEndR.composeTextF`, else `composeTextR`, then `NameAttrs.patch`), as
`wasm-wac compose --wasm` does.

Not upstream's encoder: the bytes differ (wac's layout); parity is the component's WIT and
validity (tests in `tools/wasm-tools/tests/component/compose.sh`). Configuration files (`-c`,
`config.yml`: explicit dependencies, instantiations and their arguments) are read by a YAML
subset (`parseConfig`); `import-components: true` is refused by the CLI layer.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Compose

open Silmaril.Wasm.Wac (Kind Externs PkgType)

/-- What satisfies an import: instance `i` (whole, or its export `e`), or the instance export
`e` of definition `d`. -/
inductive Target where
  | inst (i : Nat) (exp : Option String)
  | defn (d : Nat) (exp : String)
  deriving Repr, DecidableEq, Inhabited

/-- An instance of the composition: the package key of its component and its arguments. -/
structure Inst where
  key : String
  args : List (String × Target)
  deriving Repr, Inhabited

/-- How an instance with exports `es` satisfies an import of kind `k`: whole when its type is a
subtype (`none`), else its first export at a subtype (`some e`). -/
def argTarget (es : Externs) (k : Kind) : Option (Option String) :=
  if Wac.sub (.inst none es) k then some none
  else match es.find? (fun (_, k') => Wac.sub k' k) with
    | some (e, _) => some (some e)
    | none => none

/-- The instances an instance's arguments use. -/
def Inst.deps (x : Inst) : List Nat :=
  x.args.filterMap fun
    | (_, .inst i _) => some i
    | _ => none

/-- Instances in dependency order (each after the instances it uses), by repeated selection
with fuel; `none` on a cycle. -/
def order (xs : List Inst) : Option (List Nat) :=
  let rec go : Nat → List Nat → List Nat → Option (List Nat)
    | _, done, [] => some done
    | 0, _, _ => none
    | fuel + 1, done, todo =>
      match todo.find? (fun i => ((xs.getD i default).deps.all (done.contains ·))) with
      | some i => go fuel (done ++ [i]) (todo.erase i)
      | none => none
  go (xs.length + 1) [] (List.range xs.length)

/-- A WAC string literal. -/
def lit (s : String) : String := "\"" ++ s ++ "\""

def instVar (i : Nat) : String := s!"i{i}"
def defVar (d : Nat) : String := s!"d{d}"

def targetExpr : Target → String
  | .inst i none => instVar i
  | .inst i (some e) => instVar i ++ "[" ++ lit e ++ "]"
  | .defn d e => defVar d ++ "[" ++ lit e ++ "]"

/-- The definitions an instance's arguments use. -/
def usedDefs (xs : List Inst) : List Nat :=
  (xs.flatMap fun x => x.args.filterMap fun
    | (_, .defn d _) => some d
    | _ => none).eraseDups

/-- **The WAC document** of a resolved composition: definitions used (`defKeys`), the instances
in dependency order, the root (instance 0) exported (when it has exports: wac rejects a
spread of nothing). -/
def wacText (xs : List Inst) (defKeys : List String) (rootExports : Bool := true) :
    Except String String := do
  let ord ← match order xs with
    | some o => pure o
    | none => throw "the instantiation graph has a cycle"
  let defs := (usedDefs xs).map fun d =>
    s!"let {defVar d} = new {defKeys.getD d ""} \{ ... };\n"
  let lets := ord.map fun i =>
    let x := xs.getD i default
    let args := x.args.map fun (n, t) => lit n ++ ": " ++ targetExpr t ++ ", "
    s!"let {instVar i} = new {x.key} \{ " ++ String.join args ++ "... };\n"
  pure ("package wasm-tools:composition;\n\n" ++ String.join defs ++ String.join lets ++
    (if rootExports then s!"\nexport {instVar 0}...;\n" else ""))

/-- The package key of instance or definition number `i`. -/
def instKey (i : Nat) : String := s!"compose:c{i}"
def defKey (d : Nat) : String := s!"compose:def{d}"

/-- **The composition**: the WAC document composed by `wasm-wac`'s pipeline against the
components' bytes `raw` (by package key). -/
def compose (src : String) (raw : List (String × ByteArray)) : Except String ByteArray := do
  let (b, _, _) ← match Wac.EndToEndR.composeTextF src raw with
    | .ok r => pure r
    | .error _ => Wac.EndToEndR.composeTextR src raw
  pure (Wac.NameAttrs.patch (raw.map (·.2)) b)

/-! ## Configuration files (`-c`, `config.yml`)

The subset of YAML that wasm-compose's configuration uses: block maps by indentation
(`key: value`, `key:` then a nested block; a key ends at the first `: ` or a final `:`, so keys
like `example:service/logging@0.1.0` are read whole), flow lists `[a, 'b']`, plain or quoted
scalars, `#` comments. -/

/-- A YAML node of the subset. -/
inductive YNode where
  | scalar (s : String)
  | list (xs : List String)
  | map (kvs : List (String × YNode))
  deriving Inhabited

/-- A scalar without its quotes. -/
def unquote (s : String) : String :=
  let s := s.trimAscii.toString
  if s.length ≥ 2 && ((s.startsWith "'" && s.endsWith "'") || (s.startsWith "\"" && s.endsWith "\"")) then
    ((s.drop 1).dropEnd 1).toString
  else s

/-- A value: a flow list or a scalar. -/
def yValue (v : String) : YNode :=
  let v := v.trimAscii.toString
  if v.startsWith "[" && v.endsWith "]" then
    .list ((((v.drop 1).dropEnd 1).toString.splitOn ",").map unquote |>.filter (· ≠ ""))
  else .scalar (unquote v)

/-- The lines of a document: indentation, key, value (empty for a nested block). -/
def yLines (t : String) : List (Nat × String × String) :=
  (t.splitOn "\n").filterMap fun l =>
    let body := l.trimAsciiStart.toString
    if body.isEmpty || body.startsWith "#" then none
    else
      let ind := l.length - body.length
      let body := body.trimAsciiEnd.toString
      match body.splitOn ": " with
      | k :: v :: rest => some (ind, k, ": ".intercalate (v :: rest))
      | _ => if body.endsWith ":" then some (ind, (body.dropEnd 1).toString, "") else none

/-- The block of lines at indentation greater than `ind`, as a map; the rest. -/
def yBlock : Nat → Nat → List (Nat × String × String) → List (String × YNode) × List (Nat × String × String)
  | 0, _, ls => ([], ls)
  | fuel + 1, ind, ls =>
    match ls with
    | (i, k, v) :: rest =>
      if i ≤ ind then ([], ls)
      else
        let (node, rest) :=
          if v.isEmpty then
            let (kvs, rest') := yBlock fuel i rest
            (YNode.map kvs, rest')
          else (yValue v, rest)
        -- the siblings: the following keys of this block
        let (more, rest) := yBlock fuel ind rest
        ((k, node) :: more, rest)
    | [] => ([], [])

/-- Parse a configuration document. -/
def yParse (t : String) : List (String × YNode) :=
  let ls := yLines t
  (yBlock (ls.length + 1) 0 (ls.map fun (i, k, v) => (i + 1, k, v))).1

def YNode.str? : YNode → Option String
  | .scalar s => some s
  | _ => none

def YNode.list? : YNode → List String
  | .list xs => xs
  | .scalar s => [s]
  | _ => []

def YNode.kvs : YNode → List (String × YNode)
  | .map kvs => kvs
  | _ => []

/-- An explicit instantiation argument: the instance and the export of it. -/
structure ConfigArg where
  instance_ : String
  exp : Option String := none

/-- wasm-compose's `Config` (the fields this implementation reads). -/
structure Config where
  definitions : List String := []
  searchPaths : List String := []
  importComponents : Bool := false
  disallowImports : Bool := false
  skipValidation : Bool := false
  dependencies : List (String × String) := []
  instantiations : List (String × Option String × List (String × ConfigArg)) := []
  deriving Inhabited

def yBool (n : Option YNode) : Bool := (n.bind YNode.str?) == some "true"

/-- **The configuration** of a `config.yml` text. -/
def parseConfig (t : String) : Config :=
  let top := yParse t
  let get (k : String) : Option YNode := top.lookup k
  { definitions := ((get "definitions").map YNode.list?).getD []
    searchPaths := ((get "search-paths").map YNode.list?).getD []
    importComponents := yBool (get "import-components")
    disallowImports := yBool (get "disallow-imports")
    skipValidation := yBool (get "skip-validation")
    dependencies := (((get "dependencies").map YNode.kvs).getD []).filterMap fun (n, v) =>
      match v with
      | .scalar p => some (n, p)
      | .map kvs => ((kvs.lookup "path").bind YNode.str?).map (n, ·)
      | _ => none
    instantiations := (((get "instantiations").map YNode.kvs).getD []).map fun (n, v) =>
      let kvs := v.kvs
      let args := ((kvs.lookup "arguments").map YNode.kvs).getD []
      (n, (kvs.lookup "dependency").bind YNode.str?, args.map fun (a, x) =>
        match x with
        | .scalar i => (a, ⟨i, none⟩)
        | .map m => (a, ⟨((m.lookup "instance").bind YNode.str?).getD a, (m.lookup "export").bind YNode.str?⟩)
        | _ => (a, ⟨a, none⟩)) }

/-- `Config::dependency_name`: the component an instance instantiates. -/
def Config.dependencyName (c : Config) (inst : String) : String :=
  (((c.instantiations.find? (·.1 == inst)).bind (·.2.1))).getD inst

/-- The explicit arguments of an instance. -/
def Config.arguments (c : Config) (inst : String) : List (String × ConfigArg) :=
  ((c.instantiations.find? (·.1 == inst)).map (·.2.2)).getD []

end Silmaril.Wasm.Tools.Component.Compose
