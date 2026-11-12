module

public import Silmaril.Wasm.Component.Wat.Ids.Defs
public import Silmaril.Wasm.Component.Binary.Encode.Defs
public import Silmaril.Wasm.Binaryen.Exe.Encode
public import Silmaril.Wasm.Binaryen.Toolkit.WatSource
public import Silmaril.Formats.SExp.EncodingWatFullLexer

/-!
# Component WAT as people write it: the abbreviations of the text format

`Wat.read` reads the spelling `wasmprinter` writes (numeric indices, every type defined by its
own `type` item, core modules as bytes); `Wat.readIds` adds symbolic identifiers `$x`. Hand-written
component WAT, such as the fixtures of wac's test suite, also uses the **abbreviations** of the
component text format (`Explainer.md`, component-model `8505ba7`), which the `wast` crate
expands before encoding. This module expands them at the level of S-expressions, then resolves
identifiers (`Wat.resolve`) and reads the result (`Wat.ofSexp`):

* **inline types in descriptors**: `(import "n" (func (param "x" u32)))`,
  `(import "n" (instance (export "f" (func))))`, `(component …)` likewise, in components and in
  component and instance types (also in `export` declarations of types): the type is defined by
  a new item `(type $watx-tN …)` just before the import or export, and the descriptor refers to
  it, `(func (type $watx-tN))` — the expansion of `wast` (an inline type use adds a type
  definition to the type index space before the item);
* **inline imports**: `(instance $x? (import "n") …)`, `(func … (import "n") …)`,
  `(component …)`, `(type …)`, `(value …)` are the import `(import "n" (instance $x? …))`;
* **inline exports**: `(type $x? (export "n") … T)` (any sort, one or more `(export "n")`) is the
  item without them, followed by `(export "n" (type $x))` for each (a fresh binder when it has
  none);
* **core modules in text**: `(core module $x? field…)` is assembled by silmaril's WAT parser
  and verified encoder (`Silmaril.Formats.SExpEncoding.Wat.sexpWatFullExec?`,
  `Silmaril.Wasm.Binaryen.Toolkit.Wat.parseSupported?`,
  `Silmaril.Wasm.Binaryen.Exe.encodeModule?`) to `(core module $x? binary "…")`.

`readX s` is `Wat.read s` whenever that succeeds (`readX_of_read`): on the printer's spelling
nothing changes, and every theorem about `Wat.read` (`read_print`) still describes what is read.
`parseWatX` is `Wit.Tool.parseWat` with `readX` (`parseWatX_of_parseWat`, in `WatX.Thms`); the WAC tool reads
`.wat` packages with it.

Not covered: inline types inside `canon` definitions and `alias` items, `(export "n")` on
items of component or instance types (they are declarations already), inline module types of
`core module` imports.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.WatX

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Wat

/-- The expansion monad: a counter for fresh identifiers, and failure. -/
abbrev SM := StateT Nat Option

/-- A fresh identifier `$watx-tN`. -/
def fresh : SM String := modifyGet fun n => ("$watx-t" ++ String.ofList (natChars n), n + 1)

/-- A leading binder of an item body. -/
def splitId : List Sexp → Option String × List Sexp
  | .atom a :: r => if isId a then (some a, r) else (none, .atom a :: r)
  | r => (none, r)

/-- The binder as a list (empty when absent). -/
def idL : Option String → List Sexp
  | some a => [.atom a]
  | none => []

/-- The sorts whose descriptors may carry an inline type. -/
def inlineSort (k : String) : Bool := k == "func" || k == "instance" || k == "component"

/-- A descriptor body that refers to a type: `(type i)` alone. -/
def isTypeUse : List Sexp → Bool
  | [.list (.atom "type" :: _)] => true
  | _ => false

/-- An inline export `(export "n")` (a name and nothing else, possibly with a version
attribute list). -/
def isInlineExport : Sexp → Bool
  | .list [.atom "export", .str _] => true
  | _ => false

/-- An inline import `(import "n")`. -/
def isInlineImport : Sexp → Bool
  | .list [.atom "import", .str _] => true
  | _ => false

/-- The name of an inline export or import. -/
def inlineName : Sexp → Sexp
  | .list [_, n] => n
  | s => s

/-- Split the last element of a list. -/
def splitLast : List Sexp → Option (List Sexp × Sexp)
  | [] => none
  | [x] => some ([], x)
  | x :: r => (splitLast r).map fun p => (x :: p.1, p.2)

/-- Remove the annotations `(@…)` among the fields of a core module (`(@producers …)`, which
`wasmprinter` writes and silmaril's parser does not read; the producers section is dropped). -/
def dropAnnots (fs : List Sexp) : List Sexp :=
  fs.filter fun
    | .list (.atom a :: _) => a.toList.head? != some '@'
    | _ => true

/-- Assemble a core module written in text with silmaril's parser and encoder: the bytes. -/
def asmCore (fields : List Sexp) : Option (List UInt8) := do
  let t := Sexp.print (.list (.atom "module" :: dropAnnots fields))
  let x ← Silmaril.Formats.SExpEncoding.Wat.sexpWatFullExec? .core3 t
  let m ← Silmaril.Wasm.Binaryen.Toolkit.Wat.parseSupported? x
  match Silmaril.Wasm.Binaryen.Exe.encodeModule? m with
  | .ok bs => some bs
  | .error _ => none

/-- An import or export name: `"n"`, or the older spelling `(interface "n")`. -/
def plainName : List Sexp → List Sexp
  | .list [.atom "interface", n] :: r => n :: r
  | r => r

/-- The heads of value type definitions that may be written inline where a value type is
expected. -/
def valHead (k : String) : Bool :=
  k == "tuple" || k == "list" || k == "option" || k == "result" || k == "record" ||
    k == "variant" || k == "flags" || k == "enum" || k == "own" || k == "borrow" ||
    k == "stream" || k == "future" || k == "map" || k == "error-context"

/-- The component sorts of inline aliases `(S i "n")`. -/
def aliasSort (k : String) : Bool :=
  k == "func" || k == "instance" || k == "component" || k == "type" || k == "value"

/-- The core sorts of inline aliases `(core S i "n")`. -/
def coreAliasSort (k : String) : Bool :=
  k == "func" || k == "table" || k == "memory" || k == "global" || k == "module" ||
    k == "instance" || k == "type" || k == "tag"

mutual
/-- A value type: an inline definition is hoisted into a new type item (the items to insert,
and the reference). -/
def hoistVT : Nat → Sexp → SM (List Sexp × Sexp)
  | 0, _ => failure
  | n + 1, .list (.atom k :: r) =>
    if valHead k then do
      let (pre, d) ← hoistDef n (.list (.atom k :: r))
      let g ← fresh
      pure (pre ++ [.list [.atom "type", .atom g, d]], .atom g)
    else pure ([], .list (.atom k :: r))
  | _ + 1, s => pure ([], s)
/-- Value types in order. -/
def hoistVTs : Nat → List Sexp → SM (List Sexp × List Sexp)
  | 0, _ => failure
  | _ + 1, [] => pure ([], [])
  | n + 1, x :: r => do
    let (p, x') ← hoistVT n x
    let (q, r') ← hoistVTs n r
    pure (p ++ q, x' :: r')
/-- The value types in the parts of a definition (`field`, `case`, `param`, `result`,
`error`): the last element of each part. -/
def hoistParts : Nat → List Sexp → SM (List Sexp × List Sexp)
  | 0, _ => failure
  | _ + 1, [] => pure ([], [])
  | n + 1, x :: r => do
    let (p, x') ← match x with
      | .list (.atom k :: ys) =>
        if k == "field" || k == "case" || k == "param" || k == "result" || k == "error" then
          match splitLast ys with
          | some (init, .list l) =>
            match l with
            | .atom "refines" :: _ => pure ([], x)
            | _ => do
              let (p, t) ← hoistVT n (.list l)
              pure (p, .list (.atom k :: init ++ [t]))
          | _ => pure ([], x)
        else do
          let (p, t) ← hoistVT n x
          pure (p, t)
      | _ => pure ([], x)
    let (q, r') ← hoistParts n r
    pure (p ++ q, x' :: r')
/-- A type definition with inline value types hoisted out of its parts. -/
def hoistDef : Nat → Sexp → SM (List Sexp × Sexp)
  | 0, _ => failure
  | n + 1, .list (.atom k :: r) =>
    if k == "own" || k == "borrow" || k == "enum" || k == "flags" then
      pure ([], .list (.atom k :: r))
    else if k == "tuple" || k == "list" || k == "option" || k == "stream" || k == "future" ||
        k == "map" then do
      let (p, r') ← hoistVTs n r
      pure (p, .list (.atom k :: r'))
    else if k == "result" then do
      -- `(result ok? (error err)?)`
      let (p, r') ← hoistParts n r
      pure (p, .list (.atom k :: r'))
    else if k == "record" || k == "variant" || k == "func" then do
      let (p, r') ← hoistParts n r
      pure (p, .list (.atom k :: r'))
    else pure ([], .list (.atom k :: r))
  | _ + 1, s => pure ([], s)
end

mutual
/-- Inline aliases `(S i "n")`, `(core S i "n")` in an item of a component: hoisted into
`alias` items before it. -/
def dAlias : Nat → Sexp → SM (List Sexp × Sexp)
  | 0, _ => failure
  | _ + 1, .list [.atom "core", .atom k, i, .str nm] =>
    if coreAliasSort k then do
      let g ← fresh
      pure ([.list [.atom "alias", .atom "core", .atom "export", i, .str nm,
        .list [.atom "core", .atom k, .atom g]]], .list [.atom "core", .atom k, .atom g])
    else pure ([], .list [.atom "core", .atom k, i, .str nm])
  | _ + 1, .list [.atom k, i, .str nm] =>
    if aliasSort k && (match i with | .atom _ => true | _ => false) then do
      let g ← fresh
      pure ([.list [.atom "alias", .atom "export", i, .str nm, .list [.atom k, .atom g]]],
        .list [.atom k, .atom g])
    else pure ([], .list [.atom k, i, .str nm])
  | n + 1, .list xs => do
    let (p, xs') ← dAliasL n xs
    pure (p, .list xs')
  | _ + 1, s => pure ([], s)
/-- `dAlias` on every element. -/
def dAliasL : Nat → List Sexp → SM (List Sexp × List Sexp)
  | 0, _ => failure
  | _ + 1, [] => pure ([], [])
  | n + 1, x :: r => do
    let (p, x') ← dAlias n x
    let (q, r') ← dAliasL n r
    pure (p ++ q, x' :: r')
end

mutual
/-- Expand the items of a scope (`inType`: a component or instance type). `n` is fuel. -/
def dItems : Nat → Bool → List Sexp → SM (List Sexp)
  | 0, _, _ => failure
  | _ + 1, _, [] => pure []
  | n + 1, inType, x :: r => do
    let xs ← dItem n inType x
    let rs ← dItems n inType r
    pure (xs ++ rs)
/-- Expand one item into the items it stands for. -/
def dItem : Nat → Bool → Sexp → SM (List Sexp)
  | 0, _, _ => failure
  | n + 1, _, .list (.atom "import" :: rest) => do
    let (init, d) ← StateT.lift (splitLast (plainName rest))
    let (pre, d') ← dDesc n d
    pure (pre ++ [.list (.atom "import" :: init ++ [d'])])
  | n + 1, true, .list (.atom "export" :: rest) => do
    let (init, d) ← StateT.lift (splitLast (plainName rest))
    let (pre, d') ← dDesc n d
    pure (pre ++ [.list (.atom "export" :: init ++ [d'])])
  | n + 1, true, .list (.atom "type" :: rest) => do
    let (b, body) := splitId rest
    match body with
    | [t] => do
      let (pre, t') ← dTypeDef n t
      pure (pre ++ [.list (.atom "type" :: idL b ++ [t'])])
    | _ => pure [.list (.atom "type" :: rest)]
  | _ + 1, false, .list (.atom "core" :: .atom "module" :: rest) =>
    let (b, body) := splitId rest
    match body with
    | .atom "binary" :: _ => pure [.list (.atom "core" :: .atom "module" :: rest)]
    | _ => do
      let bs ← StateT.lift (asmCore body)
      pure [.list (.atom "core" :: .atom "module" :: idL b ++ [.atom "binary", .str bs])]
  | n + 1, false, .list (.atom "export" :: rest) => do
    let (pre, x) ← dAlias n (.list (.atom "export" :: plainName rest))
    pure (pre ++ [x])
  | n + 1, false, .list (.atom k :: rest) =>
    if k == "func" || k == "instance" || k == "component" || k == "type" || k == "value" then
      let (b, body) := splitId rest
      let exps := body.takeWhile isInlineExport
      let body1 := body.dropWhile isInlineExport
      match body1 with
      | i :: body2 =>
        if isInlineImport i then do
          -- `(k $x? (export "n")* (import "m") …)`: the import, then the exports
          let a? ← if exps.isEmpty then pure b else match b with
            | some a => pure (some a)
            | none => do pure (some (← fresh))
          let imp ← dItem n false
            (.list [.atom "import", inlineName i, .list (.atom k :: idL a? ++ body2)])
          pure (imp ++ exps.map fun e => .list [.atom "export", inlineName e,
            .list [.atom k, .atom (a?.getD "")]])
        else plainItem n k b exps body1
      | [] => plainItem n k b exps body1
    else if k == "core" then do
      let (pre, x) ← dAlias n (.list (.atom k :: rest))
      pure (pre ++ [x])
    else pure [.list (.atom k :: rest)]
  | _ + 1, _, s => pure [s]
/-- An item `(k $x? body)` of a component (no inline import) with the inline exports
`exps`. -/
def plainItem : Nat → String → Option String → List Sexp → List Sexp → SM (List Sexp)
  | 0, _, _, _, _ => failure
  | n + 1, k, b, exps, body => do
    let (pre, body') ← if k == "type" then
        match body with
        | [t] => do let (p, t') ← dTypeDef n t; pure (p, [t'])
        | _ => pure ([], body)
      else if k == "component" then do pure ([], ← dItems n false body)
      else if k == "func" then
        -- `(func param* result* (canon lift …))`: the inline function type is defined first
        match splitLast body with
        | some (parts, c@(.list (.atom "canon" :: _))) =>
          if isTypeUse parts then dAliasL n body
          else do
            let (p, t) ← hoistDef n (.list (.atom "func" :: parts))
            let g ← fresh
            let (q, c') ← dAlias n c
            pure (p ++ [.list [.atom "type", .atom g, t]] ++ q, [.list [.atom "type", .atom g], c'])
        | _ => dAliasL n body
      else dAliasL n body
    if exps.isEmpty then pure (pre ++ [.list (.atom k :: idL b ++ body')])
    else do
      let a ← match b with
        | some a => pure a
        | none => fresh
      pure (pre ++ .list (.atom k :: .atom a :: body') ::
        exps.map fun e => .list [.atom "export", inlineName e, .list [.atom k, .atom a]])
/-- A descriptor `(k $x? body)`: the type items to insert before the item, and the
descriptor referring to them. -/
def dDesc : Nat → Sexp → SM (List Sexp × Sexp)
  | 0, _ => failure
  | n + 1, .list (.atom k :: rest) =>
    let (b, body) := splitId rest
    if inlineSort k && !isTypeUse body then do
      let (pre, t) ← dTypeDef n (.list (.atom k :: body))
      let g ← fresh
      pure (pre ++ [.list [.atom "type", .atom g, t]],
        .list (.atom k :: idL b ++ [.list [.atom "type", .atom g]]))
    else pure ([], .list (.atom k :: rest))
  | _ + 1, s => pure ([], s)
/-- A type definition: the declarations of instance and component types expanded, the
inline value types of value and function types hoisted (the items to insert before). -/
def dTypeDef : Nat → Sexp → SM (List Sexp × Sexp)
  | 0, _ => failure
  | n + 1, .list (.atom "instance" :: ds) => do
    pure ([], .list (.atom "instance" :: (← dItems n true ds)))
  | n + 1, .list (.atom "component" :: ds) => do
    pure ([], .list (.atom "component" :: (← dItems n true ds)))
  | n + 1, s => hoistDef n s
end

/-- The hexadecimal digits of a byte. -/
def hexByte (b : UInt8) : List Char := [Sexp.hexDigit (b.toNat / 16), Sexp.hexDigit (b.toNat % 16)]

mutual
/-- **Lexical clean-up** before the expansion: a quoted identifier `$"…"` (read as the atom `$`
and a string) becomes the identifier `$watx-q` followed by the hexadecimal bytes of the string
(an identifier of idchars); the name annotations `(@name "…")`
that `wasmprinter` writes next to binders are dropped (they carry no meaning for the
component; the `name` custom section is not rebuilt from them). -/
def clean : Sexp → Sexp
  | .list xs => .list (cleanL xs)
  | s => s
/-- `clean` on the elements of a list. -/
def cleanL : List Sexp → List Sexp
  | [] => []
  | .atom "$" :: .str bs :: r => .atom (String.ofList ("$watx-q".toList ++ bs.flatMap hexByte)) :: cleanL r
  | .list (.atom "@name" :: _) :: r => cleanL r
  | x :: r => clean x :: cleanL r
end

/-- Expand the abbreviations of a component. -/
def desugar : Sexp → Option Sexp
  | .list (.atom "component" :: r) =>
    let (b, body) := splitId r
    ((dItems (4 * Sexp.nodesL r + 4) false body).run' 0).map fun body' =>
      .list (.atom "component" :: idL b ++ body')
  | _ => none

/-- **Read component WAT with abbreviations and identifiers**: `Wat.read` when it succeeds,
else the abbreviations expanded (`desugar`), identifiers resolved (`resolve`), and read. -/
def readX (s : String) : Option Binary.Ast :=
  match Wat.read s with
  | some c => some c
  | none =>
    match Sexp.read s with
    | some [x] => desugar (clean x) >>= resolve >>= ofSexp
    | _ => none

/-- `Wit.Tool.parseWat` with `readX`. -/
def parseWatX (t : String) : Except String ByteArray :=
  match readX t with
  | none => .error "not component WAT this reader accepts"
  | some c => match Binary.encode c with
    | some b => .ok b
    | none => .error "a number or size exceeds 2^32"

theorem readX_of_read {s : String} {c : Binary.Ast} (h : Wat.read s = some c) :
    readX s = some c := by
  simp [readX, h]

end Silmaril.Wasm.Wac.WatX
