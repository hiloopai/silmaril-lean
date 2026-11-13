module

public import Silmaril.Wasm.Wit.Binary.Model.Defs

/-!
# WIT text of a binary package (wit-component's printer)

`printPackage p` is the WIT text `wasm-tools component wit` prints for the
*main* package of a WIT binary: a transcription of `WitPrinter` of
wit-component 0.263.0 (`src/printing.rs`, crates.io `.crate` sha256
`4189bd18…45bf7`, vcs `bytecodealliance/wasm-tools@7a2fa422`), functions
`print_package` (with `is_main`), `print_interface`, `print_types`,
`print_resource`, `print_function`, `print_world`, `print_world_item`,
`print_path_to_interface`, `print_type_name`, `declare_type`, `print_docs`,
`print_stability`, `escape_name`/`is_keyword` and the indentation of
`OutputToString`.

It is not proved to be anything: there is no WIT text parser to invert it. It is
checked byte for byte against wasm-tools 1.263.0 on the main packages of the
WASI 0.2.12 binaries (`tests/wasm-wit/differential.sh`). The dependency
packages wasm-tools prints after the main one (`package … { … }`) are not
printed: they are reconstructed by wit-parser's decoder from the types the
binary shows, a merge this model does not transcribe.

Model differences that do not show in the text: types are structural here
(wit-parser's anonymous type ids are not needed), a `use` is a type
`type x = ref` to a type of another interface, and a resource's functions are
those whose kind names it.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Binary.Print

open Silmaril.Wasm.Component.Binary (PrimValType)

/-! ## Output (`OutputToString`) -/

structure Out where
  indent : Nat := 0
  out : String := ""
  needsIndent : Bool := false

abbrev PM := StateM Out

def pushStr (s : String) : PM Unit := modify fun o => { o with out := o.out ++ s }

def indentIfNeeded : PM Unit := modify fun o =>
  if o.needsIndent then
    { o with out := o.out ++ String.join (List.replicate o.indent "  "), needsIndent := false }
  else o

def newline : PM Unit := modify fun o => { o with out := o.out.push '\n', needsIndent := true }

/-- `keyword`, `ty`, `param`, `case`, `str`: indent, then print. -/
def str (s : String) : PM Unit := do indentIfNeeded; pushStr s

def indentStart : PM Unit := do
  pushStr " {"
  modify fun o => { o with indent := o.indent + 1 }
  newline

def indentEnd : PM Unit := do
  modify fun o => { o with indent := o.indent - 1 }
  indentIfNeeded
  pushStr "}"
  newline

def semicolon : PM Unit := do pushStr ";"; newline

def doc (line : String) : PM Unit := do
  indentIfNeeded
  pushStr "///"
  if !line.isEmpty then pushStr " "; pushStr line
  newline

/-! ## Names -/

def keywords : List String :=
  ["use", "type", "func", "u8", "u16", "u32", "u64", "s8", "s16", "s32", "s64", "f32", "f64",
   "float32", "float64", "char", "resource", "record", "flags", "variant", "enum", "bool",
   "string", "option", "result", "future", "stream", "list", "own", "borrow", "_", "as",
   "from", "static", "interface", "tuple", "world", "import", "export", "package", "with",
   "include", "constructor", "error-context", "async", "map"]

/-- `escape_name`: keywords get a `%`. -/
def escape (n : String) : String := if keywords.contains n then "%" ++ n else n

def name (n : String) : PM Unit := str (escape n)

/-- Rust's `str::lines`: split at `\n`, no final empty line, `\r` before `\n` dropped. -/
def lines (s : String) : List String :=
  let ls := s.splitOn "\n"
  let ls := if s.endsWith "\n" || s.isEmpty then ls.dropLast else ls
  ls.map fun l => if l.endsWith "\r" then String.ofList l.toList.dropLast else l

def docs : Option String → PM Unit
  | none => pure ()
  | some d => (lines d).forM doc

def stability : Stability → PM Unit
  | .unknown => pure ()
  | .stable since dep => do
    str "@since"; str "("; str "version"; str " = "; name since; str ")"; newline
    deprecated dep
  | .unstable feature dep => do
    str "@unstable"; str "("; str "feature"; str " = "; str feature; str ")"; newline
    deprecated dep
where
  deprecated : Option String → PM Unit
    | none => pure ()
    | some v => do
      str "@deprecated"; str "("; str "version"; str " = "; name v; str ")"; newline

/-! ## Types -/

def prim : PrimValType → String
  | .bool => "bool" | .s8 => "s8" | .u8 => "u8" | .s16 => "s16" | .u16 => "u16"
  | .s32 => "s32" | .u32 => "u32" | .s64 => "s64" | .u64 => "u64" | .f32 => "f32"
  | .f64 => "f64" | .char => "char" | .string => "string" | .errorContext => "error-context"

/-- `print_type_name`. -/
partial def ty : Ty → PM Unit
  | .prim p => str (prim p)
  | .ref r => name r.name
  | .own r => name r.name
  | .borrow r => do str "borrow"; pushStr "<"; name r.name; pushStr ">"
  | .list t => do str "list"; pushStr "<"; ty t; pushStr ">"
  | .fixedList t n => do str "list"; pushStr "<"; ty t; pushStr s!", {n}"; pushStr ">"
  | .map k v => do str "map"; pushStr "<"; ty k; str ", "; ty v; pushStr ">"
  | .option t => do str "option"; pushStr "<"; ty t; pushStr ">"
  | .tuple ts => do
    str "tuple"; pushStr "<"
    ts.zipIdx.forM fun (t, i) => do if i > 0 then str ", "
                                     ty t
    pushStr ">"
  | .result none none => str "result"
  | .result (some o) none => do str "result"; pushStr "<"; ty o; pushStr ">"
  | .result none (some e) => do str "result"; pushStr "<"; str "_, "; ty e; pushStr ">"
  | .result (some o) (some e) => do str "result"; pushStr "<"; ty o; str ", "; ty e; pushStr ">"
  | .future none => pushStr "future"
  | .future (some t) => do pushStr "future<"; ty t; pushStr ">"
  | .stream none => pushStr "stream"
  | .stream (some t) => do pushStr "stream<"; ty t; pushStr ">"

/-- `declare_type` of a named type other than a resource. -/
def declare (td : TypeDef) : PM Unit :=
  match td.kind with
  | .record fs => do
    str "record"; str " "; name td.name; indentStart
    fs.forM fun f => do docs f.docs; name f.name; str ": "; ty f.ty; str ","; newline
    indentEnd
  | .variant cs => do
    str "variant"; str " "; name td.name; indentStart
    cs.forM fun c => do
      docs c.docs; name c.name
      match c.ty with
      | some t => do str "("; ty t; str ")"
      | none => pure ()
      str ","; newline
    indentEnd
  | .enum cs => do
    str "enum"; str " "; name td.name; indentStart
    cs.forM fun c => do docs c.docs; name c.name; str ","; newline
    indentEnd
  | .flags fs => do
    str "flags"; str " "; name td.name; indentStart
    fs.forM fun c => do docs c.docs; name c.name; str ","; newline
    indentEnd
  | .resource => pure ()
  | .type (.own r) => do
    str "type"; str " "; name td.name; str " = "
    str "own"; pushStr "<"; name r.name; pushStr ">"; semicolon
  | .type t => do str "type"; str " "; name td.name; str " = "; ty t; semicolon

/-! ## Functions -/

def isMethod : FuncKind → Bool
  | .method _ => true
  | _ => false

/-- `is_constructor_shorthand`: a constructor returning `own<Self>`. -/
def shorthand (f : Func) : Bool :=
  match f.kind, f.result with
  | .constructor r, some (.own ⟨.local, r'⟩) => r == r'
  | _, _ => false

/-- `print_function`. -/
def func (f : Func) : PM Unit := do
  if f.async then str "async"; str " "
  match f.kind with
  | .constructor _ => do str "constructor"; str "("
  | _ => do str "func"; str "("
  let ps := if isMethod f.kind then f.params.drop 1 else f.params
  ps.zipIdx.forM fun ((n, t), i) => do
    if i > 0 then str ", "
    name n; str ": "; ty t
  str ")"
  if !shorthand f then
    match f.result with
    | some t => do str " -> "; ty t
    | none => pure ()

/-- `print_resource`. -/
def resource (td : TypeDef) (fs : List Func) : PM Unit := do
  str "resource"; str " "; name td.name
  if fs.isEmpty then semicolon
  else
    indentStart
    fs.forM fun f => do
      docs f.docs; stability f.stability
      match f.kind with
      | .constructor _ => pure ()
      | .method _ => do name f.name; str ": "
      | .static _ => do name f.name; str ": "; str "static"; str " "
      | .freestanding => pure ()
      func f; semicolon
    indentEnd

/-! ## Interfaces and worlds -/

/-- `print_path_to_interface`. -/
def path (cur : PackageName) (i : IfaceName) : PM Unit :=
  if i.pkg = cur then name i.name
  else do
    name i.pkg.ns; str ":"; name i.pkg.name; str "/"; name i.name
    match i.pkg.version with
    | some v => name ("@" ++ v)
    | none => pure ()

/-- The interface a `use` type comes from, with the used name. -/
def useOf (td : TypeDef) : Option (IfaceName × String) :=
  match td.kind with
  | .type (.ref ⟨.iface i, n⟩) => some (i, n)
  | _ => none

/-- `new_item`: a blank line between items. -/
def newItem (any : Bool) : PM Bool := do
  if any then newline
  pure true

/-- `print_types` (`any` is `any_items`; returns it). -/
def types (cur : PackageName) (tds : List TypeDef) (funcs : List Func) (any : Bool) : PM Bool := do
  -- the `use`s, grouped by interface and stability
  let groups : List (IfaceName × Stability × List (String × String)) :=
    tds.foldl (init := []) fun gs td =>
      match useOf td with
      | none => gs
      | some (i, n) =>
        match gs.getLast? with
        | some (j, st, l) =>
          if j = i ∧ st = td.stability then gs.dropLast ++ [(j, st, l ++ [(td.name, n)])]
          else gs ++ [(i, td.stability, [(td.name, n)])]
        | none => [(i, td.stability, [(td.name, n)])]
  let mut any := any
  for (i, st, l) in groups do
    any := true
    stability st
    str "use"; str " "; path cur i; str ".{"
    for ((mine, other), k) in l.zipIdx do
      if k > 0 then str ", "
      if mine == other then name mine
      else do name other; str " "; str "as"; str " "; name mine
    str "}"; semicolon
  for td in tds.filter (useOf · |>.isNone) do
    any ← newItem any
    docs td.docs; stability td.stability
    match td.kind with
    | .resource => resource td (funcs.filter (·.kind.resource? == some td.name))
    | _ => declare td
  pure any

/-- `print_interface`. -/
def iface (cur : PackageName) (b : Interface) : PM Unit := do
  let mut any ← types cur b.types b.funcs false
  for f in b.funcs.filter (·.kind.resource?.isNone) do
    any ← newItem any
    docs f.docs; stability f.stability
    name f.name; str ": "; func f; semicolon

/-- `print_world_item` for interfaces and functions. -/
def worldItem (cur : PackageName) (kw : String) : WorldItem → PM Unit
  | .ifaceRef i d st => do
    docs d; stability st; str kw; str " "; path cur i; semicolon
  | .ifaceInline n b => do
    docs b.docs; stability b.stability; str kw; str " "
    name n; str ": "; str "interface"; indentStart; iface cur b; indentEnd
  | .func f => do
    docs f.docs; stability f.stability; str kw; str " "
    name f.name; str ": "; func f; semicolon
  | .type _ => pure ()

/-- `print_world`. -/
def world (cur : PackageName) (w : World) : PM Unit := do
  let mut any := false
  let mut tds : List TypeDef := []
  let mut rfuncs : List Func := []
  let mut fimports : List WorldItem := []
  for it in w.imports do
    match it with
    | .type td => tds := tds ++ [td]
    | .func f =>
      if f.kind.resource?.isSome then rfuncs := rfuncs ++ [f]
      else fimports := fimports ++ [it]
    | _ => do worldItem cur "import" it; any := true
  any ← types cur tds rfuncs any
  for it in fimports do
    worldItem cur "import" it
    any := true
  if !w.exports.isEmpty then
    let _ ← newItem any
  for it in w.exports do
    worldItem cur "export" it

/-- `print_package` of the main package. -/
def package (p : Package) : PM Unit := do
  docs p.docs
  str "package"; str " "; name p.name.ns; str ":"; name p.name.name
  match p.name.version with
  | some v => name ("@" ++ v)
  | none => pure ()
  semicolon; newline
  for (n, b) in p.interfaces do
    docs b.docs; stability b.stability
    str "interface"; str " "; name n
    indentStart; iface p.name b; indentEnd
    newline
  for (n, w) in p.worlds do
    docs w.docs; stability w.stability
    str "world"; str " "; name n
    indentStart; world p.name w; indentEnd

end Print

/-- The WIT text of a package, as `wasm-tools component wit` prints the main
package of its binary. -/
def printPackage (p : Package) : String := ((Print.package p).run {}).2.out

end Silmaril.Wasm.Wit.Binary
