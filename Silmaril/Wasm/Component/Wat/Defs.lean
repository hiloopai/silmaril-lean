module

public import Silmaril.Wasm.Component.Binary.Defs
public import Silmaril.Wasm.Component.Wat.Sexp.Defs

/-!
# Component WAT: the S-expression syntax of component binaries

A printer `Wat.print : Ast → String` and a reader `Wat.read : String → Option Ast`
between the component binary AST of `Silmaril.Wasm.Component.Binary` (component-model
`Binary.md` at `8505ba7`) and the component text format (`Explainer.md`), in the
spelling of `wasmprinter` 0.263.0 (`src/component.rs`, wasm-tools 1.263.0): one
S-expression per item, numeric indices, `(type (eq i))`, `(alias outer c i (type))`,
`(func (type t) (canon lift (core func f) …))` and so on.

The whole binary AST is covered: custom sections, core modules, core instances and
types (function and module types), component instances (`instantiate`/`with` and
inline exports), aliases (instance export, core instance export, outer), all type
definitions (value types, function types, component and instance types with their
declarations, resources), `canon` definitions, `start`, imports, exports and values.

## Silmaril-specific spellings

The component text format has no syntax for a few binary constructs; the printer uses:

* a core module, kept as bytes in the AST: `(core module binary "…")`;
* a value definition, kept as bytes: `(value <valtype> "…")`;
* a custom section: the annotation `(@custom "name" "data")` (placement annotations
  such as `(after …)` are not read). The reader also takes `wasmprinter`'s
  `(@producers (field "name" "version")*)` for the `producers` section.

## Normal form

Text has no section boundaries and no spelling of the redundant `nameattributes`
forms, so the round trip is up to `Wat.norm`:

* consecutive items of the same kind form one section (`group`), as the `wast`
  encoder does; empty vector sections disappear;
* a name with no attributes is spelled `0x00` (`NameForm.plain0`): `plain1` and
  `attrs []` become `plain0` (also as `wast` encodes them).

`Wat.read (Wat.print c) = some (Wat.norm c)` is
`Silmaril.Wasm.Component.Wat.read_print`.

Identifiers (`$x`) are not read: indices are numeric, as `wasmprinter` prints
them for components without a `name` section (it adds `(;i;)` comments, which the
reader skips).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Wat

open Silmaril.Wasm.Component.Binary

/-! ## Atoms -/

/-- A keyword. -/
abbrev kw (s : String) : Sexp := .atom s

/-- A decimal digit. -/
def digitChar (d : Nat) : Char := Char.ofNat (48 + d)

/-- The decimal digits of `n`. -/
def natChars (n : Nat) : List Char :=
  if n < 10 then [digitChar n] else natChars (n / 10) ++ [digitChar (n % 10)]
termination_by n
decreasing_by omega

/-- The value of a decimal digit. -/
def digitVal? (c : Char) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48) else none

/-- One step of reading decimal digits. -/
def digitStep (acc : Option Nat) (c : Char) : Option Nat :=
  acc.bind fun v => (digitVal? c).map (10 * v + ·)

/-- A non-empty run of decimal digits. -/
def parseNat : List Char → Option Nat
  | [] => none
  | c :: cs => (c :: cs).foldl digitStep (some 0)

/-- A natural number. -/
def num (n : Nat) : Sexp := .atom (String.ofList (natChars n))

def num? : Sexp → Option Nat
  | .atom s => parseNat s.toList
  | _ => none

/-- A name: a string literal of its UTF-8 bytes. -/
def nm (s : String) : Sexp := .str s.toUTF8.data.toList

def nm? : Sexp → Option String
  | .str bs => String.fromUTF8? ⟨bs.toArray⟩
  | _ => none

/-- Raw bytes as a string literal. -/
def bytesS (b : ByteArray) : Sexp := .str b.data.toList

def bytes? : Sexp → Option ByteArray
  | .str bs => some ⟨bs.toArray⟩
  | _ => none

/-- Read every element. -/
def mapO {α : Type} (f : Sexp → Option α) : List Sexp → Option (List α)
  | [] => some []
  | s :: ss => do
    let a ← f s
    let as ← mapO f ss
    pure (a :: as)

/-! ## Printer -/

namespace P

def coreSort : CoreSort → Sexp
  | .func => kw "func" | .table => kw "table" | .memory => kw "memory"
  | .global => kw "global" | .tag => kw "tag" | .type => kw "type"
  | .module => kw "module" | .instance => kw "instance"

/-- A sort, as the keywords of its group: `core func`, `func`, `type`, … -/
def sort : ItemSort → List Sexp
  | .core s => [kw "core", coreSort s]
  | .func => [kw "func"] | .value => [kw "value"] | .type => [kw "type"]
  | .component => [kw "component"] | .instance => [kw "instance"]

def sortIdx (x : SortIdx) : Sexp := .list (sort x.sort ++ [num x.idx])

def coreSortIdx (x : CoreSortIdx) : Sexp := .list [coreSort x.sort, num x.idx]

def attr : Attribute → Sexp
  | .implements s => .list [kw "implements", nm s]
  | .versionSuffix s => .list [kw "version-suffix", nm s]
  | .externalId s => .list [kw "external-id", nm s]

/-- A name and its attributes. -/
def name (n : ExternName) : List Sexp :=
  nm n.name :: match n.form with
    | .attrs as => as.map attr
    | _ => []

def coreInstance : CoreInstanceExpr → Sexp
  | .instantiate m args =>
    .list [kw "core", kw "instance", .list (kw "instantiate" :: num m ::
      args.map fun a => .list [kw "with", nm a.1, .list [kw "instance", num a.2]])]
  | .exports es =>
    .list (kw "core" :: kw "instance" ::
      es.map fun e => .list [kw "export", nm e.1, coreSortIdx e.2])

def inst : InstanceExpr → Sexp
  | .instantiate c args =>
    .list [kw "instance", .list (kw "instantiate" :: num c ::
      args.map fun a => .list [kw "with", nm a.1, sortIdx a.2])]
  | .exports es =>
    .list (kw "instance" :: es.map fun e => .list (kw "export" :: name e.1 ++ [sortIdx e.2]))

def alias_ (a : Alias) : Sexp :=
  match a.target with
  | .export i n => .list [kw "alias", kw "export", num i, nm n, .list (sort a.sort)]
  | .coreExport i n =>
    .list [kw "alias", kw "core", kw "export", num i, nm n, .list (sort a.sort)]
  | .outer c i => .list [kw "alias", kw "outer", num c, num i, .list (sort a.sort)]

def coreValType : CoreValType → Sexp
  | .i32 => kw "i32" | .i64 => kw "i64" | .f32 => kw "f32" | .f64 => kw "f64"
  | .v128 => kw "v128" | .funcref => kw "funcref" | .externref => kw "externref"

def limits (l : Binary.Limits) : List Sexp := num l.min :: (l.max.map num).toList

def coreImportDesc : CoreImportDesc → Sexp
  | .func t => .list [kw "func", .list [kw "type", num t]]
  | .table t l => .list (kw "table" :: limits l ++ [coreValType t])
  | .memory l => .list (kw "memory" :: limits l)
  | .global t m => .list [kw "global", if m then .list [kw "mut", coreValType t] else coreValType t]
  | .tag t => .list [kw "tag", .list [kw "type", num t]]

def coreFuncType (t : CoreFuncType) : Sexp :=
  .list (kw "func" ::
    ((if t.params = [] then [] else [.list (kw "param" :: t.params.map coreValType)]) ++
     (if t.results = [] then [] else [.list (kw "result" :: t.results.map coreValType)])))

def moduleDecl : ModuleDecl → Sexp
  | .import m n d => .list [kw "import", nm m, nm n, coreImportDesc d]
  | .type t => .list [kw "type", coreFuncType t]
  | .alias c i => .list [kw "alias", kw "outer", num c, num i, .list [kw "type"]]
  | .export n d => .list [kw "export", nm n, coreImportDesc d]

def coreType : CoreType → Sexp
  | .func t => coreFuncType t
  | .module ds => .list (kw "module" :: ds.map moduleDecl)

def prim : PrimValType → Sexp
  | .bool => kw "bool" | .s8 => kw "s8" | .u8 => kw "u8" | .s16 => kw "s16"
  | .u16 => kw "u16" | .s32 => kw "s32" | .u32 => kw "u32" | .s64 => kw "s64"
  | .u64 => kw "u64" | .f32 => kw "f32" | .f64 => kw "f64" | .char => kw "char"
  | .string => kw "string" | .errorContext => kw "error-context"

def valType : Binary.ValType → Sexp
  | .prim p => prim p
  | .idx i => num i

def defValType : DefValType → Sexp
  | .prim p => prim p
  | .record fs => .list (kw "record" :: fs.map fun f => .list [kw "field", nm f.1, valType f.2])
  | .variant cs => .list (kw "variant" :: cs.map fun c =>
      .list (kw "case" :: nm c.1 :: (c.2.map valType).toList))
  | .list t => .list [kw "list", valType t]
  | .tuple ts => .list (kw "tuple" :: ts.map valType)
  | .flags ls => .list (kw "flags" :: ls.map nm)
  | .enum ls => .list (kw "enum" :: ls.map nm)
  | .option t => .list [kw "option", valType t]
  | .result ok err => .list (kw "result" :: ((ok.map valType).toList ++
      (err.map fun e => .list [kw "error", valType e]).toList))
  | .own i => .list [kw "own", num i]
  | .borrow i => .list [kw "borrow", num i]
  | .fixedList t n => .list [kw "list", valType t, num n]
  | .stream t => .list (kw "stream" :: (t.map valType).toList)
  | .future t => .list (kw "future" :: (t.map valType).toList)
  | .map k v => .list [kw "map", valType k, valType v]

def funcType (f : Binary.FuncType) : Sexp :=
  .list (kw "func" :: ((if f.async then [kw "async"] else []) ++
    f.params.map (fun p => .list [kw "param", nm p.1, valType p.2]) ++
    (f.result.map fun r => .list [kw "result", valType r]).toList))

def externDesc : ExternDesc → Sexp
  | .coreModule i => .list [kw "core", kw "module", .list [kw "type", num i]]
  | .func i => .list [kw "func", .list [kw "type", num i]]
  | .value (.eq i) => .list [kw "value", .list [kw "eq", num i]]
  | .value (.type (.idx i)) => .list [kw "value", .list [kw "type", num i]]
  | .value (.type (.prim p)) => .list [kw "value", prim p]
  | .type (.eq i) => .list [kw "type", .list [kw "eq", num i]]
  | .type .subResource => .list [kw "type", .list [kw "sub", kw "resource"]]
  | .component i => .list [kw "component", .list [kw "type", num i]]
  | .instance i => .list [kw "instance", .list [kw "type", num i]]

mutual
def defType : DefType → Sexp
  | .val d => defValType d
  | .func f => funcType f
  | .component ds => .list (kw "component" :: componentDecls ds)
  | .instance ds => .list (kw "instance" :: instanceDecls ds)
  | .resource rep dtor => .list (kw "resource" :: .list [kw "rep", coreValType rep] ::
      (dtor.map fun d => .list [kw "dtor", num d]).toList)

def instanceDecl : InstanceDecl → Sexp
  | .coreType t => .list [kw "core", kw "type", coreType t]
  | .type t => .list [kw "type", defType t]
  | .alias a => alias_ a
  | .export n d => .list (kw "export" :: name n ++ [externDesc d])

def componentDecl : ComponentDecl → Sexp
  | .import n d => .list (kw "import" :: name n ++ [externDesc d])
  | .inst d => instanceDecl d

def instanceDecls : List InstanceDecl → List Sexp
  | [] => []
  | d :: ds => instanceDecl d :: instanceDecls ds

def componentDecls : List ComponentDecl → List Sexp
  | [] => []
  | d :: ds => componentDecl d :: componentDecls ds
end

def canonOpt : CanonOpt → Sexp
  | .utf8 => kw "string-encoding=utf8"
  | .utf16 => kw "string-encoding=utf16"
  | .latin1utf16 => kw "string-encoding=latin1+utf16"
  | .memory i => .list [kw "memory", num i]
  | .realloc i => .list [kw "realloc", num i]
  | .postReturn i => .list [kw "post-return", num i]
  | .async => kw "async"
  | .callback i => .list [kw "callback", num i]

def canon : Canon → Sexp
  | .lift f opts t => .list [kw "func", .list [kw "type", num t],
      .list (kw "canon" :: kw "lift" :: .list [kw "core", kw "func", num f] :: opts.map canonOpt)]
  | .lower f opts => .list [kw "core", kw "func",
      .list (kw "canon" :: kw "lower" :: .list [kw "func", num f] :: opts.map canonOpt)]
  | .resourceNew t => .list [kw "core", kw "func", .list [kw "canon", kw "resource.new", num t]]
  | .resourceDrop t => .list [kw "core", kw "func", .list [kw "canon", kw "resource.drop", num t]]
  | .resourceRep t => .list [kw "core", kw "func", .list [kw "canon", kw "resource.rep", num t]]

def start (s : Start) : Sexp :=
  .list (kw "start" :: num s.func :: (s.args.map fun a => .list [kw "value", num a]) ++
    List.replicate s.results (.list [kw "result", .list [kw "value"]]))

def import_ (i : Binary.Import) : Sexp := .list (kw "import" :: name i.name ++ [externDesc i.desc])

def export_ (e : Binary.Export) : Sexp :=
  .list (kw "export" :: name e.name ++ sortIdx e.item :: (e.desc.map externDesc).toList)

def value (v : Value) : Sexp := .list [kw "value", valType v.type, bytesS v.bytes]

mutual
/-- The items of a section. -/
def section_ : Section → List Sexp
  | .custom n d => [.list [kw "@custom", nm n, bytesS d]]
  | .coreModule b => [.list [kw "core", kw "module", kw "binary", bytesS b]]
  | .coreInstances xs => xs.map coreInstance
  | .coreTypes xs => xs.map fun t => .list [kw "core", kw "type", coreType t]
  | .component c => [.list (kw "component" :: ast c)]
  | .instances xs => xs.map inst
  | .aliases xs => xs.map alias_
  | .types xs => xs.map fun t => .list [kw "type", defType t]
  | .canons xs => xs.map canon
  | .start s => [start s]
  | .imports xs => xs.map import_
  | .exports xs => xs.map export_
  | .values xs => xs.map value

def sections : List Section → List Sexp
  | [] => []
  | s :: ss => section_ s ++ sections ss

/-- The items of a component. -/
def ast : Ast → List Sexp
  | .mk ss => sections ss
end

end P

/-! ## Reader -/

namespace R

def coreSort : Sexp → Option CoreSort
  | .atom "func" => some .func | .atom "table" => some .table | .atom "memory" => some .memory
  | .atom "global" => some .global | .atom "tag" => some .tag | .atom "type" => some .type
  | .atom "module" => some .module | .atom "instance" => some .instance | _ => none

/-- A sort at the head of a list, and the rest. -/
def sortPre : List Sexp → Option (ItemSort × List Sexp)
  | .atom "core" :: c :: rest => (coreSort c).map fun s => (.core s, rest)
  | .atom "func" :: rest => some (.func, rest)
  | .atom "value" :: rest => some (.value, rest)
  | .atom "type" :: rest => some (.type, rest)
  | .atom "component" :: rest => some (.component, rest)
  | .atom "instance" :: rest => some (.instance, rest)
  | _ => none

def sort (xs : List Sexp) : Option ItemSort :=
  match sortPre xs with
  | some (s, []) => some s
  | _ => none

def sortIdx : Sexp → Option SortIdx
  | .list xs => match sortPre xs with
    | some (s, [n]) => (num? n).map fun i => ⟨s, i⟩
    | _ => none
  | _ => none

def coreSortIdx : Sexp → Option CoreSortIdx
  | .list [c, n] => do
    let s ← coreSort c
    let i ← num? n
    pure ⟨s, i⟩
  | _ => none

def attr : Sexp → Option Attribute
  | .list [.atom "implements", s] => (nm? s).map .implements
  | .list [.atom "version-suffix", s] => (nm? s).map .versionSuffix
  | .list [.atom "external-id", s] => (nm? s).map .externalId
  | _ => none

/-- Attributes at the head of a list, and the rest. -/
def attrs : List Sexp → List Attribute × List Sexp
  | [] => ([], [])
  | s :: ss => match attr s with
    | some a => let p := attrs ss; (a :: p.1, p.2)
    | none => ([], s :: ss)

/-- A name and its attributes, and the rest. -/
def name : List Sexp → Option (ExternName × List Sexp)
  | s :: ss => (nm? s).map fun n =>
    let p := attrs ss
    (⟨n, if p.1 = [] then .plain0 else .attrs p.1⟩, p.2)
  | [] => none

def coreWith : Sexp → Option (String × Nat)
  | .list [.atom "with", n, .list [.atom "instance", i]] => do
    let a ← nm? n
    let b ← num? i
    pure (a, b)
  | _ => none

def coreExport : Sexp → Option (String × CoreSortIdx)
  | .list [.atom "export", n, x] => do
    let a ← nm? n
    let b ← coreSortIdx x
    pure (a, b)
  | _ => none

/-- The body of `(core instance …)`. -/
def coreInstance (ss : List Sexp) : Option CoreInstanceExpr :=
  match mapO coreExport ss with
  | some es => some (.exports es)
  | none => match ss with
    | [.list (.atom "instantiate" :: m :: args)] => do
      let mi ← num? m
      let as ← mapO coreWith args
      pure (.instantiate mi as)
    | _ => none

def with_ : Sexp → Option (String × SortIdx)
  | .list [.atom "with", n, x] => do
    let a ← nm? n
    let b ← sortIdx x
    pure (a, b)
  | _ => none

def inlineExport : Sexp → Option (ExternName × SortIdx)
  | .list (.atom "export" :: rest) => do
    let (n, r) ← name rest
    match r with
    | [x] => (sortIdx x).map fun i => (n, i)
    | _ => none
  | _ => none

/-- The body of `(instance …)`. -/
def inst (ss : List Sexp) : Option InstanceExpr :=
  match mapO inlineExport ss with
  | some es => some (.exports es)
  | none => match ss with
    | [.list (.atom "instantiate" :: c :: args)] => do
      let ci ← num? c
      let as ← mapO with_ args
      pure (.instantiate ci as)
    | _ => none

/-- The body of `(alias …)`. -/
def alias_ : List Sexp → Option Alias
  | [.atom "export", i, n, .list s] => do
    let a ← num? i
    let b ← nm? n
    let c ← sort s
    pure ⟨c, .export a b⟩
  | [.atom "core", .atom "export", i, n, .list s] => do
    let a ← num? i
    let b ← nm? n
    let c ← sort s
    pure ⟨c, .coreExport a b⟩
  | [.atom "outer", c, i, .list s] => do
    let a ← num? c
    let b ← num? i
    let d ← sort s
    pure ⟨d, .outer a b⟩
  | _ => none

def coreValType : Sexp → Option CoreValType
  | .atom "i32" => some .i32 | .atom "i64" => some .i64 | .atom "f32" => some .f32
  | .atom "f64" => some .f64 | .atom "v128" => some .v128 | .atom "funcref" => some .funcref
  | .atom "externref" => some .externref | _ => none

def typeUse : Sexp → Option Nat
  | .list [.atom "type", i] => num? i
  | _ => none

def coreImportDesc : Sexp → Option CoreImportDesc
  | .list [.atom "func", t] => (typeUse t).map .func
  | .list [.atom "table", a, t] => do
    let m ← num? a
    let v ← coreValType t
    pure (.table v ⟨m, none⟩)
  | .list [.atom "table", a, b, t] => do
    let m ← num? a
    let n ← num? b
    let v ← coreValType t
    pure (.table v ⟨m, some n⟩)
  | .list [.atom "memory", a] => (num? a).map fun m => .memory ⟨m, none⟩
  | .list [.atom "memory", a, b] => do
    let m ← num? a
    let n ← num? b
    pure (.memory ⟨m, some n⟩)
  | .list [.atom "global", .list [.atom "mut", t]] => (coreValType t).map fun v => .global v true
  | .list [.atom "global", t] => (coreValType t).map fun v => .global v false
  | .list [.atom "tag", t] => (typeUse t).map .tag
  | _ => none

/-- The body of a core `(func …)` type. -/
def coreFuncType : List Sexp → Option CoreFuncType
  | [] => some ⟨[], []⟩
  | [.list (.atom "param" :: ps)] => (mapO coreValType ps).map fun p => ⟨p, []⟩
  | [.list (.atom "result" :: rs)] => (mapO coreValType rs).map fun r => ⟨[], r⟩
  | [.list (.atom "param" :: ps), .list (.atom "result" :: rs)] => do
    let p ← mapO coreValType ps
    let r ← mapO coreValType rs
    pure ⟨p, r⟩
  | _ => none

def moduleDecl : Sexp → Option ModuleDecl
  | .list [.atom "import", m, n, d] => do
    let a ← nm? m
    let b ← nm? n
    let c ← coreImportDesc d
    pure (.import a b c)
  | .list [.atom "type", .list (.atom "func" :: t)] => (coreFuncType t).map .type
  | .list [.atom "alias", .atom "outer", c, i, .list [.atom "type"]] => do
    let a ← num? c
    let b ← num? i
    pure (.alias a b)
  | .list [.atom "export", n, d] => do
    let a ← nm? n
    let c ← coreImportDesc d
    pure (.export a c)
  | _ => none

def coreType : Sexp → Option CoreType
  | .list (.atom "func" :: t) => (coreFuncType t).map .func
  | .list (.atom "module" :: ds) => (mapO moduleDecl ds).map .module
  | _ => none

def prim : Sexp → Option PrimValType
  | .atom "bool" => some .bool | .atom "s8" => some .s8 | .atom "u8" => some .u8
  | .atom "s16" => some .s16 | .atom "u16" => some .u16 | .atom "s32" => some .s32
  | .atom "u32" => some .u32 | .atom "s64" => some .s64 | .atom "u64" => some .u64
  | .atom "f32" => some .f32 | .atom "f64" => some .f64 | .atom "char" => some .char
  | .atom "string" => some .string | .atom "error-context" => some .errorContext
  | _ => none

def valType (s : Sexp) : Option Binary.ValType :=
  match num? s with
  | some i => some (.idx i)
  | none => (prim s).map .prim

def field : Sexp → Option (String × Binary.ValType)
  | .list [.atom "field", n, t] => do
    let a ← nm? n
    let b ← valType t
    pure (a, b)
  | _ => none

def case : Sexp → Option (String × Option Binary.ValType)
  | .list [.atom "case", n] => (nm? n).map fun a => (a, none)
  | .list [.atom "case", n, t] => do
    let a ← nm? n
    let b ← valType t
    pure (a, some b)
  | _ => none

def optValType : List Sexp → Option (Option Binary.ValType)
  | [] => some none
  | [t] => (valType t).map some
  | _ => none

def resultBody : List Sexp → Option DefValType
  | [] => some (.result none none)
  | [.list [.atom "error", e]] => (valType e).map fun b => .result none (some b)
  | [t] => (valType t).map fun a => .result (some a) none
  | [t, .list [.atom "error", e]] => do
    let a ← valType t
    let b ← valType e
    pure (.result (some a) (some b))
  | _ => none

def defValType : Sexp → Option DefValType
  | .list (.atom "record" :: fs) => (mapO field fs).map .record
  | .list (.atom "variant" :: cs) => (mapO case cs).map .variant
  | .list [.atom "list", t] => (valType t).map .list
  | .list [.atom "list", t, n] => do
    let a ← valType t
    let b ← num? n
    pure (.fixedList a b)
  | .list (.atom "tuple" :: ts) => (mapO valType ts).map .tuple
  | .list (.atom "flags" :: ls) => (mapO nm? ls).map .flags
  | .list (.atom "enum" :: ls) => (mapO nm? ls).map .enum
  | .list [.atom "option", t] => (valType t).map .option
  | .list (.atom "result" :: r) => resultBody r
  | .list [.atom "own", i] => (num? i).map .own
  | .list [.atom "borrow", i] => (num? i).map .borrow
  | .list (.atom "stream" :: t) => (optValType t).map .stream
  | .list (.atom "future" :: t) => (optValType t).map .future
  | .list [.atom "map", k, v] => do
    let a ← valType k
    let b ← valType v
    pure (.map a b)
  | s => (prim s).map .prim

def param : Sexp → Option (String × Binary.ValType)
  | .list [.atom "param", n, t] => do
    let a ← nm? n
    let b ← valType t
    pure (a, b)
  | _ => none

/-- Parameters at the head of a list, and the rest. -/
def params : List Sexp → Option (List (String × Binary.ValType) × List Sexp)
  | (.list (.atom "param" :: p)) :: ss => do
    let a ← param (.list (.atom "param" :: p))
    let (ps, r) ← params ss
    pure (a :: ps, r)
  | ss => some ([], ss)

/-- The body of a component `(func …)` type after `async`. -/
def funcBody (async : Bool) (ss : List Sexp) : Option Binary.FuncType := do
  let (ps, r) ← params ss
  match r with
  | [] => pure ⟨ps, none, async⟩
  | [.list [.atom "result", t]] => (valType t).map fun v => ⟨ps, some v, async⟩
  | _ => none

/-- The body of a component `(func …)` type. -/
def funcType : List Sexp → Option Binary.FuncType
  | .atom "async" :: ss => funcBody true ss
  | ss => funcBody false ss

def externDesc : Sexp → Option ExternDesc
  | .list [.atom "core", .atom "module", t] => (typeUse t).map .coreModule
  | .list [.atom "func", t] => (typeUse t).map .func
  | .list [.atom "value", .list [.atom "eq", i]] => (num? i).map fun j => .value (.eq j)
  | .list [.atom "value", .list [.atom "type", i]] => (num? i).map fun j => .value (.type (.idx j))
  | .list [.atom "value", p] => (prim p).map fun q => .value (.type (.prim q))
  | .list [.atom "type", .list [.atom "eq", i]] => (num? i).map fun j => .type (.eq j)
  | .list [.atom "type", .list [.atom "sub", .atom "resource"]] => some (.type .subResource)
  | .list [.atom "component", t] => (typeUse t).map .component
  | .list [.atom "instance", t] => (typeUse t).map .instance
  | _ => none

/-- The rest of an import or export declaration: name, attributes, descriptor. -/
def nameDesc (ss : List Sexp) : Option (ExternName × ExternDesc) := do
  let (n, r) ← name ss
  match r with
  | [d] => (externDesc d).map fun e => (n, e)
  | _ => none

def resource : List Sexp → Option DefType
  | [.list [.atom "rep", t]] => (coreValType t).map fun r => .resource r none
  | [.list [.atom "rep", t], .list [.atom "dtor", d]] => do
    let r ← coreValType t
    let i ← num? d
    pure (.resource r (some i))
  | _ => none

mutual
def defType : Sexp → Option DefType
  | .list (.atom "func" :: ss) => (funcType ss).map .func
  | .list (.atom "component" :: ds) => (componentDecls ds).map .component
  | .list (.atom "instance" :: ds) => (instanceDecls ds).map .instance
  | .list (.atom "resource" :: ss) => resource ss
  | s => (defValType s).map .val

def instanceDecl : Sexp → Option InstanceDecl
  | .list [.atom "core", .atom "type", t] => (coreType t).map .coreType
  | .list [.atom "type", t] => (defType t).map .type
  | .list (.atom "alias" :: ss) => (alias_ ss).map .alias
  | .list (.atom "export" :: ss) => (nameDesc ss).map fun p => .export p.1 p.2
  | _ => none

def componentDecl : Sexp → Option ComponentDecl
  | .list (.atom "import" :: ss) => (nameDesc ss).map fun p => .import p.1 p.2
  | s => (instanceDecl s).map .inst

def instanceDecls : List Sexp → Option (List InstanceDecl)
  | [] => some []
  | s :: ss => do
    let d ← instanceDecl s
    let ds ← instanceDecls ss
    pure (d :: ds)

def componentDecls : List Sexp → Option (List ComponentDecl)
  | [] => some []
  | s :: ss => do
    let d ← componentDecl s
    let ds ← componentDecls ss
    pure (d :: ds)
end

def canonOpt : Sexp → Option CanonOpt
  | .atom "string-encoding=utf8" => some .utf8
  | .atom "string-encoding=utf16" => some .utf16
  | .atom "string-encoding=latin1+utf16" => some .latin1utf16
  | .list [.atom "memory", i] => (num? i).map .memory
  | .list [.atom "realloc", i] => (num? i).map .realloc
  | .list [.atom "post-return", i] => (num? i).map .postReturn
  | .atom "async" => some .async
  | .list [.atom "callback", i] => (num? i).map .callback
  | _ => none

def startValue : Sexp → Option Nat
  | .list [.atom "value", i] => num? i
  | _ => none

/-- Start arguments at the head of a list, and the rest. -/
def startArgs : List Sexp → Option (List Nat × List Sexp)
  | (.list [.atom "value", i]) :: ss => do
    let a ← num? i
    let (as, r) ← startArgs ss
    pure (a :: as, r)
  | ss => some ([], ss)

/-- The number of `(result (value))` items. -/
def startResults : List Sexp → Option Nat
  | [] => some 0
  | (.list [.atom "result", .list [.atom "value"]]) :: ss => (startResults ss).map (· + 1)
  | _ => none

def export_ (ss : List Sexp) : Option Binary.Export := do
  let (n, r) ← name ss
  match r with
  | [x] => (sortIdx x).map fun i => ⟨n, i, none⟩
  | [x, d] => do
    let i ← sortIdx x
    let e ← externDesc d
    pure ⟨n, i, some e⟩
  | _ => none

/-- Merge two adjacent sections of the same vector kind. -/
def merge : Section → Section → Option Section
  | .coreInstances a, .coreInstances b => some (.coreInstances (a ++ b))
  | .coreTypes a, .coreTypes b => some (.coreTypes (a ++ b))
  | .instances a, .instances b => some (.instances (a ++ b))
  | .aliases a, .aliases b => some (.aliases (a ++ b))
  | .types a, .types b => some (.types (a ++ b))
  | .canons a, .canons b => some (.canons (a ++ b))
  | .imports a, .imports b => some (.imports (a ++ b))
  | .exports a, .exports b => some (.exports (a ++ b))
  | .values a, .values b => some (.values (a ++ b))
  | _, _ => none

/-- Group consecutive sections of the same vector kind. -/
def group : List Section → List Section
  | [] => []
  | s :: ss => match group ss with
    | [] => [s]
    | t :: ts => match merge s t with
      | some u => u :: ts
      | none => s :: t :: ts

/-- The body of a `(core func (canon …))` item. -/
def coreCanon : List Sexp → Option Canon
  | .atom "lower" :: .list [.atom "func", f] :: opts => do
    let fi ← num? f
    let os ← mapO canonOpt opts
    pure (.lower fi os)
  | [.atom "resource.new", t] => (num? t).map .resourceNew
  | [.atom "resource.drop", t] => (num? t).map .resourceDrop
  | [.atom "resource.rep", t] => (num? t).map .resourceRep
  | _ => none

/-- Items starting with `core`. -/
def coreItem : List Sexp → Option Section
  | [.atom "module", .atom "binary", b] => (bytes? b).map .coreModule
  | .atom "instance" :: ss => (coreInstance ss).map fun x => .coreInstances [x]
  | [.atom "type", t] => (coreType t).map fun x => .coreTypes [x]
  | [.atom "func", .list (.atom "canon" :: ss)] => (coreCanon ss).map fun c => .canons [c]
  | _ => none

/-- The body of a `(func (type t) (canon lift …))` item. -/
def liftItem : List Sexp → Option Section
  | [t, .list (.atom "canon" :: .atom "lift" :: .list [.atom "core", .atom "func", f] :: opts)] =>
    do
    let ti ← typeUse t
    let fi ← num? f
    let os ← mapO canonOpt opts
    pure (.canons [.lift fi os ti])
  | _ => none

/-- The body of a `(start …)` item. -/
def startItem : List Sexp → Option Section
  | f :: ss => do
    let fi ← num? f
    let (as, r) ← startArgs ss
    let n ← startResults r
    pure (.start ⟨fi, as, n⟩)
  | [] => none

/-- The body of a `(@custom …)` item. -/
def customItem : List Sexp → Option Section
  | [n, d] => do
    let a ← nm? n
    let b ← bytes? d
    pure (.custom a b)
  | _ => none

/-- The body of a `(value …)` item. -/
def valueItem : List Sexp → Option Section
  | [t, b] => do
    let v ← valType t
    let d ← bytes? b
    pure (.values [⟨v, d⟩])
  | _ => none

/-- The body of a `(type …)` item. -/
def typeItem : List Sexp → Option Section
  | [t] => (defType t).map fun x => .types [x]
  | _ => none

/-- Unsigned LEB128 (for the `producers` payload). -/
def leb (n : Nat) : List UInt8 :=
  if n < 128 then [n.toUInt8] else (n % 128 + 128).toUInt8 :: leb (n / 128)
termination_by n
decreasing_by omega

/-- A name in a custom-section payload: its UTF-8 size, then its bytes. -/
def nameBytes (s : String) : List UInt8 := leb s.toUTF8.size ++ s.toUTF8.data.toList

/-- One value of `(@producers …)`: `(field "name" "version")`. -/
def producerValue : Sexp → Option (String × String × String)
  | .list [.atom f, n, v] => do
    let a ← nm? n
    let b ← nm? v
    pure (f, a, b)
  | _ => none

/-- Group consecutive values of one field. -/
def groupFields : List (String × String × String) → List (String × List (String × String))
  | [] => []
  | (f, n, v) :: rest => match groupFields rest with
    | (g, vs) :: fs => if f = g then (f, (n, v) :: vs) :: fs else (f, [(n, v)]) :: (g, vs) :: fs
    | [] => [(f, [(n, v)])]

/-- The body of `(@producers …)` (as `wasmprinter` prints the `producers`
section), as the custom section it stands for. This is read only: the printer
writes the section as `(@custom "producers" …)`. -/
def producersItem (ss : List Sexp) : Option Section := do
  let vs ← mapO producerValue ss
  let fs := groupFields vs
  let payload := leb fs.length ++ fs.flatMap fun f =>
    nameBytes f.1 ++ leb f.2.length ++ f.2.flatMap fun p => nameBytes p.1 ++ nameBytes p.2
  pure (.custom "producers" ⟨payload.toArray⟩)

/-- An item other than a nested component, by its head keyword. -/
def itemKw (k : String) (ss : List Sexp) : Option Section :=
  match k with
  | "@custom" => customItem ss
  | "@producers" => producersItem ss
  | "core" => coreItem ss
  | "func" => liftItem ss
  | "instance" => (inst ss).map fun x => .instances [x]
  | "alias" => (alias_ ss).map fun x => .aliases [x]
  | "type" => typeItem ss
  | "start" => startItem ss
  | "import" => (nameDesc ss).map fun p => .imports [⟨p.1, p.2⟩]
  | "export" => (export_ ss).map fun e => .exports [e]
  | "value" => valueItem ss
  | _ => none

mutual
/-- One item, as a section of one element. -/
def item : Sexp → Option Section
  | .list (.atom "component" :: ss) => (items ss).map fun xs => .component (.mk (group xs))
  | .list (.atom k :: ss) => itemKw k ss
  | _ => none

/-- Items, each as a section of one element. -/
def items : List Sexp → Option (List Section)
  | [] => some []
  | s :: ss => do
    let x ← item s
    let xs ← items ss
    pure (x :: xs)
end

end R

/-! ## Normal form -/

/-- A name without attributes is spelled `0x00`. -/
def normName (n : ExternName) : ExternName :=
  ⟨n.name, match n.form with
    | .attrs (a :: as) => .attrs (a :: as)
    | _ => .plain0⟩

def normInstance : InstanceExpr → InstanceExpr
  | .instantiate c args => .instantiate c args
  | .exports es => .exports (es.map fun e => (normName e.1, e.2))

def normDesc : ExternDesc → ExternDesc := id

mutual
def normDefType : DefType → DefType
  | .val d => .val d
  | .func f => .func f
  | .component ds => .component (normComponentDecls ds)
  | .instance ds => .instance (normInstanceDecls ds)
  | .resource r d => .resource r d

def normInstanceDecl : InstanceDecl → InstanceDecl
  | .coreType t => .coreType t
  | .type t => .type (normDefType t)
  | .alias a => .alias a
  | .export n d => .export (normName n) d

def normComponentDecl : ComponentDecl → ComponentDecl
  | .import n d => .import (normName n) d
  | .inst d => .inst (normInstanceDecl d)

def normInstanceDecls : List InstanceDecl → List InstanceDecl
  | [] => []
  | d :: ds => normInstanceDecl d :: normInstanceDecls ds

def normComponentDecls : List ComponentDecl → List ComponentDecl
  | [] => []
  | d :: ds => normComponentDecl d :: normComponentDecls ds
end

mutual
/-- A section, split into sections of one element (with normal names). -/
def normSection : Section → List Section
  | .custom n d => [.custom n d]
  | .coreModule b => [.coreModule b]
  | .coreInstances xs => xs.map fun x => .coreInstances [x]
  | .coreTypes xs => xs.map fun x => .coreTypes [x]
  | .component c => [.component (norm c)]
  | .instances xs => xs.map fun x => .instances [normInstance x]
  | .aliases xs => xs.map fun x => .aliases [x]
  | .types xs => xs.map fun x => .types [normDefType x]
  | .canons xs => xs.map fun x => .canons [x]
  | .start s => [.start s]
  | .imports xs => xs.map fun x => .imports [⟨normName x.name, x.desc⟩]
  | .exports xs => xs.map fun x => .exports [⟨normName x.name, x.item, x.desc⟩]
  | .values xs => xs.map fun x => .values [x]

def normSections : List Section → List Section
  | [] => []
  | s :: ss => normSection s ++ normSections ss

/-- **The normal form** of the text round trip: names without attributes are
spelled `0x00`, consecutive items of one kind form one section, recursively. -/
def norm : Ast → Ast
  | .mk ss => .mk (R.group (normSections ss))
end

/-! ## Entry points -/

/-- The S-expression of a component. -/
def toSexp (c : Ast) : Sexp := .list (kw "component" :: P.ast c)

/-- The component of an S-expression. -/
def ofSexp : Sexp → Option Ast
  | .list (.atom "component" :: ss) => (R.items ss).map fun xs => .mk (R.group xs)
  | _ => none

/-- Print a component as WAT. -/
def print (c : Ast) : String := Sexp.printAll [toSexp c]

/-- Read a component from WAT. -/
def read (s : String) : Option Ast :=
  match Sexp.read s with
  | some [x] => ofSexp x
  | _ => none

end Silmaril.Wasm.Component.Wat
