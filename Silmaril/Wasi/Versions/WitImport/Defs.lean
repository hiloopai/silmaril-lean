module

public import Silmaril.Wasm.Wit.Tool.Source.Defs
public import Silmaril.Wasi.Theory.Defs

@[expose] public section

/-!
# WASI signatures through the WIT importer

The hand-written WASI interfaces of `Silmaril.Wasi.Versions` name their functions (`FnName`) and
type their answers by hand (`Random.ok2`, `P3.ok3`, …). This module reads the vendored WIT
(`specs/wasi/0.2.12`, `specs/wasi/0.3.2`) with the verified WIT front end of
`Silmaril.Wasm.Wit` (`Text.parse`, `Elab.elaborate`, through `Tool.parseText`) and turns the
elaborated packages into **signature tables**: a list of `FnName`s with their WIT signature
(`Binary.Sig`). `Silmaril.Wasi.Versions.WitImport.Tables` builds the tables at elaboration time
(the importer runs in the elaborator and its result is quoted); the theorems of
`Silmaril.Wasi.Versions.WitImport.Thms` compare them with the hand-written definitions.

## The glue (not verified)

The front end parses one document with one `package` header. WASI packages are directories of
files, of which only one carries the header, and some put doc comments on parameters. Before
the front end runs, this module

* `demoteParamDocs`: turns `///` doc comments *inside a parameter list* into `//` comments.
  wit-parser ignores doc comments there (parameters carry no docs), the Silmaril parser rejects
  them (a parser gap, see `docs/projects/wasm-wasi.md`, *Follow-up 3*);
* `withHeader`: prepends the package header of the directory to a file without one;
* `mergeDocs`: merges the documents of one package (their items concatenated in file order),
  as wit-parser merges the files of a package directory.

## Names and signatures

* `plainName f`: the canonical-ABI name *without* the async marker: `f`, `[method]r.f`,
  `[static]r.f`, `[constructor]r`. `Binary.Func.mangled` writes `[async]f`,
  `[async method]r.f` for async functions; the WASI theories observe async imports
  sync-lowered and name them without the marker (`P3.waitFor3`, `P3.openAt3`).
* `ifaceId ver p i`: `ns:pkg/i`, with `@version` when `ver` (the 0.3 names of
  `Silmaril.Wasi.Versions` carry the version, the 0.2 names do not).
* `table ver P`: the functions of the interfaces of `P` with their signatures; `drops ver P`:
  the `[resource-drop]r` functions of its resources.

## Typing

`tyOk t v`: the value `v` has the WIT type `t` in the value encoding of `Silmaril.Wasi.Theory`:
`list<T>`, `string` and `tuple<…>` are records, `option`/`result`/variants are variants,
handles (`own`, `borrow`, `stream`, `future`) are `u32`. Named types (`Binary.Ty.ref`) are not
resolved and accept every value. `witOk T`: an import answer is well typed when its function is
in the table `T` and its arguments have the WIT parameter types (other calls are
unconstrained, as in the hand-written theories).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Wit
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Binary (PrimValType)

/-! ## Preparing WIT text -/

/-- A line that starts (after spaces) with `//`. -/
def isCommentLine (l : String) : Bool := l.trimAsciiStart.toString.startsWith "//"

/-- A line that starts (after spaces) with `///`. -/
def isDocLine (l : String) : Bool := l.trimAsciiStart.toString.startsWith "///"

/-- Opened minus closed parentheses of a line. -/
def parenDelta (l : String) : Int :=
  l.toList.foldl (fun n c => if c = '(' then n + 1 else if c = ')' then n - 1 else n) 0

/-- One line of `demoteParamDocs`, with the parenthesis depth before it. -/
def demoteLine (acc : List String × Int) (l : String) : List String × Int :=
  if isCommentLine l then
    (acc.1 ++ [if acc.2 > 0 && isDocLine l then
      "//" ++ String.ofList (l.trimAsciiStart.toString.toList.drop 3) else l], acc.2)
  else (acc.1 ++ [l], acc.2 + parenDelta l)

/-- Doc comments inside parameter lists become plain comments. -/
def demoteParamDocs (t : String) : String :=
  "\n".intercalate ((t.splitOn "\n").foldl demoteLine ([], 0)).1

/-- The `package …;` line of a file, if any. -/
def headerOf (t : String) : Option String :=
  (t.splitOn "\n").find? fun l => l.startsWith "package "

/-- The text with the header `hdr` prepended unless it has one. -/
def withHeader (hdr t : String) : String :=
  if (headerOf t).isSome then t else hdr ++ "\n" ++ t

/-- A source file: the package header of its directory, a label and the text. -/
abbrev Src := String × String × String

/-- Parse a source file. -/
def parseSrc (s : Src) : Except String Document :=
  Tool.parseText s.2.1 (withHeader s.1 (demoteParamDocs s.2.2))

/-- The package names of a list of packages, first occurrences in order. -/
def pkgNames (ps : List Package) : List PackageName :=
  ps.foldl (fun acc p => if acc.contains p.name then acc else acc ++ [p.name]) []

/-- Merge the documents' packages of the same name (items in order). -/
def mergeDocs (ds : List Document) : List Package :=
  let ps := ds.flatMap Document.packages
  (pkgNames ps).map fun n =>
    let qs := ps.filter (·.name == n)
    { name := n, items := qs.flatMap (·.items), docs := (qs.head?.map (·.docs)).getD {} }

/-- **The importer**: the first package of the source files, elaborated in the universe of all
of them. -/
def importPkg (fs : List Src) : Except String Binary.Package := do
  let ds ← fs.mapM parseSrc
  let U := mergeDocs ds
  let P ← U.head?.elim (.error "no package") pure
  let (B, _) ← Elab.elaborate U P.name []
  pure B

/-! ## Names and signatures -/

/-- The canonical-ABI name of a function without the async marker. -/
def plainName (f : Binary.Func) : String := Binary.Func.mangled { f with async := false }

/-- `ns:pkg/iface`, with `@version` when `ver`. -/
def ifaceId (ver : Bool) (p : Binary.PackageName) (i : String) : String :=
  p.ns ++ ":" ++ p.name ++ "/" ++ i ++ (if ver then (p.version.map ("@" ++ ·)).getD "" else "")

/-- A signature table: functions with their WIT signatures. -/
abbrev Table := List (FnName × Binary.Sig)

/-- The functions of the interfaces of a package with their signatures. -/
def table (ver : Bool) (P : Binary.Package) : Table :=
  P.interfaces.flatMap fun x =>
    x.2.funcs.map fun f => (⟨ifaceId ver P.name x.1, plainName f⟩, f.sig)

/-- The `[resource-drop]r` functions of the resources of a package. -/
def drops (ver : Bool) (P : Binary.Package) : List FnName :=
  P.interfaces.flatMap fun x =>
    x.2.types.filterMap fun td =>
      match td.kind with
      | .resource => some ⟨ifaceId ver P.name x.1, "[resource-drop]" ++ td.name⟩
      | _ => none

/-- The functions of a table. -/
def names (T : Table) : List FnName := T.map Prod.fst

/-- The parameter and result types of a signature (parameter names and `async` forgotten). -/
def sigTypes (s : Binary.Sig) : List Binary.Ty × Option Binary.Ty :=
  (s.params.map Prod.snd, s.result)

/-! ## Typing -/

/-- A primitive WIT type. -/
def primOk : PrimValType → Val → Bool
  | .bool, .bool _ | .s8, .s8 _ | .u8, .u8 _ | .s16, .s16 _ | .u16, .u16 _
  | .s32, .s32 _ | .u32, .u32 _ | .s64, .s64 _ | .u64, .u64 _
  | .f32, .f32 _ | .f64, .f64 _ | .char, .char _ => true
  | .string, .record vs => vs.all fun | .char _ => true | _ => false
  | .errorContext, .u32 _ => true
  | _, _ => false

mutual
/-- `tyOk t v`: `v` has the WIT type `t` (named types unconstrained). -/
def tyOk : Binary.Ty → Val → Bool
  | .prim p, v => primOk p v
  | .ref _, _ => true
  | .list t, .record vs => tyAll t vs
  | .fixedList t n, .record vs => vs.length == n && tyAll t vs
  | .map k w, .record vs => pairsOk k w vs
  | .option _, .variant 0 none => true
  | .option t, .variant 1 (some v) => tyOk t v
  | .result a _, .variant 0 p => tyOpt a p
  | .result _ b, .variant 1 p => tyOpt b p
  | .tuple ts, .record vs => tysOk ts vs
  | .own _, .u32 _ | .borrow _, .u32 _ | .future _, .u32 _ | .stream _, .u32 _ => true
  | _, _ => false

/-- Every value has the type `t`. -/
def tyAll (t : Binary.Ty) : List Val → Bool
  | [] => true
  | v :: vs => tyOk t v && tyAll t vs

/-- A map: a list of key–value records. -/
def pairsOk (k w : Binary.Ty) : List Val → Bool
  | [] => true
  | .record [a, b] :: vs => tyOk k a && tyOk w b && pairsOk k w vs
  | _ :: _ => false

/-- The values have the types, one by one. -/
def tysOk : List Binary.Ty → List Val → Bool
  | [], [] => true
  | t :: ts, v :: vs => tyOk t v && tysOk ts vs
  | _, _ => false

/-- An optional payload of an optional type. -/
def tyOpt : Option Binary.Ty → Option Val → Bool
  | none, none => true
  | some t, some v => tyOk t v
  | _, _ => false
end

/-- The arguments of a call have the parameter types. -/
def argsOk (s : Binary.Sig) (a : List Val) : Bool := tysOk (s.params.map Prod.snd) a

/-- The answer of a call has the result type (`none`, a trap, is not well typed). -/
def resOk (s : Binary.Sig) : Option (List Val) → Bool
  | some vs => match s.result with
    | none => vs.isEmpty
    | some t => match vs with
      | [v] => tyOk t v
      | _ => false
  | none => false

/-- **WIT typing of import answers** for the functions of a table. -/
def witOk (T : Table) : WEv → Bool
  | .imp f a r => match T.lookup f with
    | some s => !argsOk s a || resOk s r
    | none => true
  | _ => true

/-- The WIT typing theory of a table. -/
def witTh (T : Table) : Silmaril.Wasm.Resource.Protocol Unit WEv := pointwise (witOk T)

end Silmaril.Wasi.Versions.WitImport
