module

public import Silmaril.Wasm.Text.Core.Instructions
public import Silmaril.Wasm.Text.Core.FunctionalInstrs
public import Silmaril.Wasm.Modules
public import Silmaril.Formats.SExp.EncodingWat

/-!
# Core 3.0 text format: modules (SpecTec `6.4-text.modules`)

* `DeclT I x ds J uses` — `Tdecl_(I)`: one module field `x` denotes a list of
  declarations `ds` (several when inline import/export, inline `(data …)` or
  inline `(elem …)` abbreviations are used) and contributes the identifier
  context `J`.
* `ModuleT x m` — `Tmodule` (plain and abbreviated): the identifier context
  `I'` of the whole module is the concatenation of the contributions of all
  fields (plus implicitly inserted function types), every field is read in
  `I'` (`Idctxt_ok I'`), imports precede definitions (`$ordered`), and the
  module is assembled from the declarations.
* `watSyntax : EncRel SExp Module` and **`Encodes := sexpWat3 ⨾ watSyntax`**
  (`Silmaril.Wasm.Wat.Encodes`), with its UTF-8 byte version.

Choices made precise where SpecTec is informal (see `Silmaril.Wasm.Text.Core.Modules`):

* **Implicit type definitions** (TODO(5) in `6.2-text.types.spectec`): a type
  use `param* result*` without `(type x)` refers to the first singleton
  `(rec (sub final (func …)))` definition of that function type; if there is
  none among the explicit definitions, one is appended after all explicit
  type definitions, in order of first use in the *unfolded* instruction
  sequence (`implicitTypes`): `Folded.plain` records the operands' uses
  before the operator's own (post-order), matching wabt's resolution over the
  unfolded instructions.  The 1.0/Lime1 relations use the same order.
* **Self references of abbreviations**: inline exports, inline `(data …)` and
  inline `(elem …)` expand to declarations referring to the entity being
  defined through a fresh identifier; here they refer to it by position
  (`Decl.exportSelf`, `Decl.dataSelf`, `Decl.elemSelf`, resolved by
  `resolve`).
* **Inline export order**: several inline
  exports of one entity are exported in *textual* order (`selfExports`), as
  the reference interpreter (`parser.mly`, `inline_export table_fields` and
  siblings), the 1.0 REC and the 2.0 prose do.  This deliberately departs from
  the literal SpecTec equation `(func id? (export nm) dots) ≡ (func id' dots)
  (export nm …)`, which can only peel the first export and place it after the
  entity, so that the expansion yields the exports in *reverse* textual order
  (see the upstream TODO at `6.4-text.modules.spectec` L195-196).
* `(table id? tt)` without an initializer is the abbreviation with
  `(ref.null ht)`; the plain form requires a non-empty initializer (SpecTec
  also derives the empty initializer, which never validates).  SpecTec
  ambiguity, resolved as the reference interpreter does.
* **Inline element segments of tables**:
  SpecTec's `Telemtable_/abbrev`
  reads the body of `(table … rt (elem …))` as a `Telemlist_`, which demands a
  leading `func` or reftype; the reference interpreter (`parser.mly`
  `table_fields`) and the 2.0 REC instead take a bare list of function indices
  (`DeclT.tableElemFuncs`, possibly empty) or a non-empty bare list of element
  expressions (`DeclT.tableElemExprs`), and reject `(elem func x*)` and
  `(elem rt e*)` there.  Both forms give the segment the table's reftype `rt`,
  as the interpreter does.  The expression list must
  be non-empty, as in the interpreter, whose grammar parses `(elem)` as the
  empty index list; both readings would give the same declarations anyway.
-/

@[expose] public section

namespace Silmaril.Wasm.Text.Core

open Silmaril Silmaril.Formats.SExpEncoding Silmaril.Wasm

/-! ## Declarations -/

/-- Module declarations (`decl`), with self-referential forms produced by
abbreviations. -/
inductive Decl where
  | type (rt : RecType)
  | import_ (im : Import)
  | tag (t : TagType)
  | global (g : Global)
  | mem (m : MemoryType)
  | table (t : Table)
  | func (f : Func)
  | data (d : Data)
  | elem (e : Elem)
  | start (x : FuncIdx)
  | export_ (e : Export)
  /-- Export the most recently declared entity. -/
  | exportSelf (name : String)
  /-- An active data segment at offset `0` of the most recently declared memory. -/
  | dataSelf (addr : AddrType) (bytes : List UInt8)
  /-- An active element segment at offset `0` of the most recently declared table. -/
  | elemSelf (addr : AddrType) (type : RefType) (init : List Expr)

/-- Entity index spaces whose members can be imported. -/
inductive Space where
  | tag | global | mem | table | func
  deriving DecidableEq, Repr

def externSpace : ExternType → Space
  | .tag _ => .tag
  | .global _ => .global
  | .memory _ => .mem
  | .table _ => .table
  | .func _ => .func

/-- The entity space a declaration adds to, if any. -/
def Decl.space? : Decl → Option Space
  | .import_ im => some (externSpace im.type)
  | .tag _ => some .tag
  | .global _ => some .global
  | .mem _ => some .mem
  | .table _ => some .table
  | .func _ => some .func
  | _ => none

/-- Is this a definition (not an import) of an entity? -/
def Decl.isDefinition : Decl → Bool
  | .tag _ | .global _ | .mem _ | .table _ | .func _ => true
  | _ => false

def Decl.isImport : Decl → Bool
  | .import_ _ => true
  | _ => false

/-- `$ordered`: no import follows a definition of a tag, global, memory, table
or function. -/
def Ordered (ds : List Decl) : Prop :=
  ∀ i j (hi : i < ds.length) (hj : j < ds.length), i < j →
    ds[j].isImport = true → ds[i].isDefinition = false

/-- A typed index from a natural number (indices are below `2^32` in valid
modules; larger counts wrap). -/
def mkIdx {k : IndexKind} (n : Nat) : Wasm.Idx k := ⟨⟨n % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩

def externIdxOf (sp : Space) (i : Nat) : ExternIdx :=
  match sp with
  | .tag => .tag (mkIdx i)
  | .global => .global (mkIdx i)
  | .mem => .memory (mkIdx i)
  | .table => .table (mkIdx i)
  | .func => .func (mkIdx i)

/-- The constant `0` of an address type. -/
def zeroOffset (addr : AddrType) : Expr := [.intConst addr.intType 0]

/-- Resolve self references, tracking per-space counts and the most recent entity. -/
def resolveAux (count : Space → Nat) (last : Option (Space × Nat)) : List Decl → List Decl
  | [] => []
  | .exportSelf n :: ds =>
      (match last with
        | some (sp, i) => [Decl.export_ ⟨n, externIdxOf sp i⟩]
        | none => []) ++ resolveAux count last ds
  | .dataSelf addr bs :: ds =>
      (match last with
        | some (.mem, i) => [Decl.data ⟨⟨bs.toArray⟩, .active (mkIdx i) (zeroOffset addr)⟩]
        | _ => []) ++ resolveAux count last ds
  | .elemSelf addr rt es :: ds =>
      (match last with
        | some (.table, i) => [Decl.elem ⟨rt, es, .active (mkIdx i) (zeroOffset addr)⟩]
        | _ => []) ++ resolveAux count last ds
  | d :: ds =>
      match d.space? with
      | some sp =>
          d :: resolveAux (fun s => if s = sp then count s + 1 else count s) (some (sp, count sp)) ds
      | none => d :: resolveAux count last ds

def resolve (ds : List Decl) : List Decl := resolveAux (fun _ => 0) none ds

/-- `$typesd`, `$importsd`, … : assemble the module from resolved declarations
and the implicitly inserted function types. -/
def build (ds : List Decl) (implicit : List FuncType) : Module where
  types := ds.filterMap (fun | .type rt => some rt | _ => none) ++ implicit.map funcRec
  imports := ds.filterMap (fun | .import_ im => some im | _ => none)
  tags := ds.filterMap (fun | .tag t => some t | _ => none)
  globals := ds.filterMap (fun | .global g => some g | _ => none)
  memories := ds.filterMap (fun | .mem m => some m | _ => none)
  tables := ds.filterMap (fun | .table t => some t | _ => none)
  funcs := ds.filterMap (fun | .func f => some f | _ => none)
  data := ds.filterMap (fun | .data d => some d | _ => none)
  elems := ds.filterMap (fun | .elem e => some e | _ => none)
  start := (ds.filterMap (fun | .start x => some x | _ => none)).head?
  exports := ds.filterMap (fun | .export_ e => some e | _ => none)

/-- Start declarations (at most one is allowed). -/
def startCount (ds : List Decl) : Nat := (ds.filter (fun | .start _ => true | _ => false)).length

/-! ## Implicit type definitions -/

/-- Keep the first occurrence of each function type. -/
def firstOccurrences (fts : List FuncType) : List FuncType :=
  fts.foldl (fun acc ft => if ft ∈ acc then acc else acc ++ [ft]) []

/-- Function types used through the type-use abbreviation that have no
explicit singleton definition, in order of first use in the unfolded
instruction sequence. -/
def implicitTypes (explicit : List (Option (RecType × Nat))) (uses : List FuncType) :
    List FuncType :=
  (firstOccurrences uses).filter (fun ft => some (funcRec ft, 0) ∉ explicit)

/-- The identifier context contributed by the implicit type definitions. -/
def implicitCtx (implicit : List FuncType) : IdCtx where
  types := implicit.map fun _ => none
  fields := implicit.map fun _ => []
  typedefs := implicit.map fun ft => some (funcRec ft, 0)

/-! ## Module fields -/

/-- Inline exports `(export nm)*`, as names in textual order. -/
def ExportsT (xs : List SExp) (names : List String) : Prop :=
  List.Forall₂ (fun x n => ∃ nx, x = L [K "export", nx] ∧ Name nx n) xs names

/-- The self-exports produced by inline exports, in textual order (deviation
from the literal SpecTec expansion order, see the module docstring). -/
def selfExports (names : List String) : List Decl := names.map .exportSelf

/-- An inline import `(import nm₁ nm₂)`. -/
def InlineImportT (x : SExp) (n₁ n₂ : String) : Prop :=
  ∃ a b, x = L [K "import", a, b] ∧ Name a n₁ ∧ Name b n₂

/-- `Tlocal_(I)` (base and abbreviation). -/
def LocalT (I : IdCtx) (x : SExp) (ls : List (ValType × Option String)) : Prop :=
  (∃ n tx t, x = L [K "local", .atom (.id n), tx] ∧ ValTypeT I tx t ∧ ls = [(t, some n)]) ∨
    ∃ txs ts, x = L (K "local" :: txs) ∧ List.Forall₂ (ValTypeT I) txs ts ∧
      ls = ts.map (·, none)

/-- `Tdatastring`. -/
def DataStringT (xs : List SExp) (bs : List UInt8) : Prop :=
  ∃ bss, List.Forall₂ (fun x b => x = .atom (.str b)) xs bss ∧ bs = bss.flatten

/-- `Tmemuse_(I)` (with the abbreviation `eps ≡ (memory 0)`). -/
def MemUseT (I : IdCtx) (xs : List SExp) (m : MemIdx) : Prop :=
  (xs = [] ∧ m.toNat = 0) ∨ ∃ x, xs = [L [K "memory", x]] ∧ Idx I.mems x m

/-- `Ttableuse_(I)` (with the abbreviation `eps ≡ (table 0)`). -/
def TableUseT (I : IdCtx) (xs : List SExp) (t : TableIdx) : Prop :=
  (xs = [] ∧ t.toNat = 0) ∨ ∃ x, xs = [L [K "table", x]] ∧ Idx I.tables x t

/-- `Toffsetexpr_(I)` (with the abbreviation by a single folded instruction). -/
def OffsetT (I : IdCtx) (x : SExp) (e : Expr) (uses : List FuncType) : Prop :=
  (∃ xs, x = L (K "offset" :: xs) ∧ ExprT I xs e uses) ∨ Folded I x e uses

/-- `Telemexpr_(I)` (with the abbreviation by a single folded instruction). -/
def ElemExprT (I : IdCtx) (x : SExp) (e : Expr) (uses : List FuncType) : Prop :=
  (∃ xs, x = L (K "item" :: xs) ∧ ExprT I xs e uses) ∨ Folded I x e uses

/-- `Telemlist_(I)` (with the abbreviation `func x*`). -/
def ElemListT (I : IdCtx) (xs : List SExp) (rt : RefType) (es : List Expr)
    (uses : List FuncType) : Prop :=
  (∃ rx exs uss, xs = rx :: exs ∧ RefTypeT I rx rt ∧
      List.Forall₂ (fun x (p : Expr × List FuncType) => ElemExprT I x p.1 p.2) exs
        (es.zip uss) ∧ es.length = uss.length ∧ es.length < 2 ^ 32 ∧ uses = uss.flatten) ∨
    ∃ fxs fs, xs = K "func" :: fxs ∧ List.Forall₂ (Idx I.funcs) fxs fs ∧ fs.length < 2 ^ 32 ∧
      rt = ⟨false, .abstract .func⟩ ∧ es = fs.map (fun f => [.refFunc f]) ∧ uses = []

/-- `Texternidx_(I)`. -/
def ExternIdxT (I : IdCtx) (x : SExp) (e : ExternIdx) : Prop :=
  (∃ y i, x = L [K "tag", y] ∧ Idx I.tags y i ∧ e = .tag i) ∨
  (∃ y i, x = L [K "global", y] ∧ Idx I.globals y i ∧ e = .global i) ∨
  (∃ y i, x = L [K "memory", y] ∧ Idx I.mems y i ∧ e = .memory i) ∨
  (∃ y i, x = L [K "table", y] ∧ Idx I.tables y i ∧ e = .table i) ∨
  ∃ y i, x = L [K "func", y] ∧ Idx I.funcs y i ∧ e = .func i

/-- Pages needed for inline data (`$ceilz(|b*| / 64 Ki)`). -/
def pagesFor (n : Nat) : Nat := (n + 65535) / 65536

/-- Limits `[n .. n]`. -/
def exactLimits (n : Nat) : Limits :=
  ⟨⟨n % 2 ^ 64, Nat.mod_lt _ (by decide)⟩, some ⟨n % 2 ^ 64, Nat.mod_lt _ (by decide)⟩⟩

/-- `Tdecl_(I)`: a module field, the declarations it denotes, the identifier
context it contributes and the function types it uses implicitly. -/
inductive DeclT (I : IdCtx) : SExp → List Decl → IdCtx → List FuncType → Prop where
  | type {x : SExp} {rt : RecType} {J : IdCtx} : RecTypeT I x rt J →
      DeclT I x [.type rt]
        { J with typedefs := (List.range rt.types.length).map fun i => some (rt, i) } []
  | import_ {a b xt : SExp} {n₁ n₂ : String} {et : ExternType} {J : IdCtx} {u : List FuncType} :
      Name a n₁ → Name b n₂ → ExternTypeT I xt et J u →
      DeclT I (L [K "import", a, b, xt]) [.import_ ⟨n₁, n₂, et⟩] J u
  | tag {ix ex rest : List SExp} {id : Option String} {names : List String} {t : TagType}
      {u : List FuncType} : IdOpt ix id → ExportsT ex names → TagTypeT I rest t u →
      DeclT I (L (K "tag" :: (ix ++ ex ++ rest))) (.tag t :: selfExports names)
        { tags := [id] } u
  | tagImport {ix ex rest : List SExp} {imp : SExp} {id : Option String} {names : List String}
      {n₁ n₂ : String} {t : TagType} {u : List FuncType} : IdOpt ix id → ExportsT ex names →
      InlineImportT imp n₁ n₂ → TagTypeT I rest t u →
      DeclT I (L (K "tag" :: (ix ++ ex ++ imp :: rest)))
        (.import_ ⟨n₁, n₂, .tag t⟩ :: selfExports names) { tags := [id] } u
  | global {ix ex body : List SExp} {gx : SExp} {id : Option String} {names : List String}
      {g : GlobalType} {e : Expr} {u : List FuncType} : IdOpt ix id → ExportsT ex names →
      GlobalTypeT I gx g → ExprT I body e u →
      DeclT I (L (K "global" :: (ix ++ ex ++ gx :: body)))
        (.global ⟨g, e⟩ :: selfExports names) { globals := [id] } u
  | globalImport {ix ex : List SExp} {imp gx : SExp} {id : Option String} {names : List String}
      {n₁ n₂ : String} {g : GlobalType} : IdOpt ix id → ExportsT ex names →
      InlineImportT imp n₁ n₂ → GlobalTypeT I gx g →
      DeclT I (L (K "global" :: (ix ++ ex ++ [imp, gx])))
        (.import_ ⟨n₁, n₂, .global g⟩ :: selfExports names) { globals := [id] } []
  | mem {ix ex rest : List SExp} {id : Option String} {names : List String} {m : MemoryType} :
      IdOpt ix id → ExportsT ex names → MemTypeT rest m →
      DeclT I (L (K "memory" :: (ix ++ ex ++ rest))) (.mem m :: selfExports names)
        { mems := [id] } []
  | memImport {ix ex rest : List SExp} {imp : SExp} {id : Option String} {names : List String}
      {n₁ n₂ : String} {m : MemoryType} : IdOpt ix id → ExportsT ex names →
      InlineImportT imp n₁ n₂ → MemTypeT rest m →
      DeclT I (L (K "memory" :: (ix ++ ex ++ imp :: rest)))
        (.import_ ⟨n₁, n₂, .memory m⟩ :: selfExports names) { mems := [id] } []
  | memData {ix ex ax strs : List SExp} {id : Option String} {names : List String}
      {addr : AddrType} {bs : List UInt8} : IdOpt ix id → ExportsT ex names → AddrTypeT ax addr →
      DataStringT strs bs →
      DeclT I (L (K "memory" :: (ix ++ ex ++ ax ++ [L (K "data" :: strs)])))
        (.mem ⟨addr, exactLimits (pagesFor bs.length)⟩ :: .dataSelf addr bs :: selfExports names)
        { mems := [id], datas := [none] } []
  | table {ix ex tx body : List SExp} {id : Option String} {names : List String}
      {tt : TableType} {e : Expr} {u : List FuncType} : IdOpt ix id → ExportsT ex names →
      TableTypeT I tx tt → body ≠ [] → ExprT I body e u →
      DeclT I (L (K "table" :: (ix ++ ex ++ tx ++ body))) (.table ⟨tt, e⟩ :: selfExports names)
        { tables := [id] } u
  | tableNull {ix ex tx : List SExp} {id : Option String} {names : List String}
      {tt : TableType} : IdOpt ix id → ExportsT ex names → TableTypeT I tx tt →
      DeclT I (L (K "table" :: (ix ++ ex ++ tx)))
        (.table ⟨tt, [.refNull tt.element.heap]⟩ :: selfExports names) { tables := [id] } []
  | tableImport {ix ex rest : List SExp} {imp : SExp} {id : Option String} {names : List String}
      {n₁ n₂ : String} {tt : TableType} : IdOpt ix id → ExportsT ex names →
      InlineImportT imp n₁ n₂ → TableTypeT I rest tt →
      DeclT I (L (K "table" :: (ix ++ ex ++ imp :: rest)))
        (.import_ ⟨n₁, n₂, .table tt⟩ :: selfExports names) { tables := [id] } []
  | tableElemFuncs {ix ex ax fxs : List SExp} {rx : SExp} {id : Option String}
      {names : List String} {addr : AddrType} {r : RefType} {fs : List FuncIdx} :
      IdOpt ix id → ExportsT ex names → AddrTypeT ax addr → RefTypeT I rx r →
      List.Forall₂ (Idx I.funcs) fxs fs → fs.length < 2 ^ 32 →
      DeclT I (L (K "table" :: (ix ++ ex ++ ax ++ [rx, L (K "elem" :: fxs)])))
        (.table ⟨⟨addr, exactLimits fs.length, r⟩, [.refNull r.heap]⟩ ::
          .elemSelf addr r (fs.map (fun f => [.refFunc f])) :: selfExports names)
        { tables := [id], elems := [none] } []
  | tableElemExprs {ix ex ax exs : List SExp} {rx : SExp} {id : Option String}
      {names : List String} {addr : AddrType} {r : RefType} {es : List Expr}
      {uss : List (List FuncType)} :
      IdOpt ix id → ExportsT ex names → AddrTypeT ax addr → RefTypeT I rx r → exs ≠ [] →
      List.Forall₂ (fun x (p : Expr × List FuncType) => ElemExprT I x p.1 p.2) exs
        (es.zip uss) → es.length = uss.length → es.length < 2 ^ 32 →
      DeclT I (L (K "table" :: (ix ++ ex ++ ax ++ [rx, L (K "elem" :: exs)])))
        (.table ⟨⟨addr, exactLimits es.length, r⟩, [.refNull r.heap]⟩ ::
          .elemSelf addr r es :: selfExports names)
        { tables := [id], elems := [none] } uss.flatten
  | func {ix ex tu lx body : List SExp} {id : Option String} {names : List String}
      {t : TypeIdx} {params : List (Option String)} {locs : List (ValType × Option String)}
      {e : Expr} {u₁ u₂ : List FuncType} : IdOpt ix id → ExportsT ex names →
      TypeUseT I tu t params u₁ → Concat (LocalT I) lx locs →
      (I ++ { locals := params ++ locs.map Prod.snd }).Ok →
      ExprT (I ++ { locals := params ++ locs.map Prod.snd }) body e u₂ →
      DeclT I (L (K "func" :: (ix ++ ex ++ tu ++ lx ++ body)))
        (.func ⟨t, locs.map Prod.fst, e⟩ :: selfExports names) { funcs := [id] } (u₁ ++ u₂)
  | funcImport {ix ex tu : List SExp} {imp : SExp} {id : Option String} {names : List String}
      {n₁ n₂ : String} {t : TypeIdx} {params : List (Option String)} {u : List FuncType} :
      IdOpt ix id → ExportsT ex names → InlineImportT imp n₁ n₂ → TypeUseT I tu t params u →
      DeclT I (L (K "func" :: (ix ++ ex ++ imp :: tu)))
        (.import_ ⟨n₁, n₂, .func t⟩ :: selfExports names) { funcs := [id] } u
  | dataPassive {ix strs : List SExp} {id : Option String} {bs : List UInt8} :
      IdOpt ix id → DataStringT strs bs →
      DeclT I (L (K "data" :: (ix ++ strs))) [.data ⟨⟨bs.toArray⟩, .passive⟩] { datas := [id] } []
  | dataActive {ix mu strs : List SExp} {ox : SExp} {id : Option String} {m : MemIdx} {e : Expr}
      {bs : List UInt8} {u : List FuncType} : IdOpt ix id → MemUseT I mu m → OffsetT I ox e u →
      DataStringT strs bs →
      DeclT I (L (K "data" :: (ix ++ mu ++ ox :: strs)))
        [.data ⟨⟨bs.toArray⟩, .active m e⟩] { datas := [id] } u
  | elemPassive {ix el : List SExp} {id : Option String} {rt : RefType} {es : List Expr}
      {u : List FuncType} : IdOpt ix id → ElemListT I el rt es u →
      DeclT I (L (K "elem" :: (ix ++ el))) [.elem ⟨rt, es, .passive⟩] { elems := [id] } u
  | elemActive {ix tu el : List SExp} {ox : SExp} {id : Option String} {t : TableIdx}
      {e : Expr} {rt : RefType} {es : List Expr} {u u' : List FuncType} :
      IdOpt ix id → TableUseT I tu t → OffsetT I ox e u → ElemListT I el rt es u' →
      DeclT I (L (K "elem" :: (ix ++ tu ++ ox :: el)))
        [.elem ⟨rt, es, .active t e⟩] { elems := [id] } (u ++ u')
  | elemDeclare {ix el : List SExp} {id : Option String} {rt : RefType} {es : List Expr}
      {u : List FuncType} : IdOpt ix id → ElemListT I el rt es u →
      DeclT I (L (K "elem" :: (ix ++ K "declare" :: el))) [.elem ⟨rt, es, .declarative⟩]
        { elems := [id] } u
  | elemFuncs {ix : List SExp} {ox : SExp} {fxs : List SExp} {id : Option String} {e : Expr}
      {fs : List FuncIdx} {u : List FuncType} :
      IdOpt ix id → OffsetT I ox e u → List.Forall₂ (Idx I.funcs) fxs fs → fs.length < 2 ^ 32 →
      DeclT I (L (K "elem" :: (ix ++ ox :: fxs)))
        [.elem ⟨⟨false, .abstract .func⟩, fs.map (fun f => [.refFunc f]), .active ⟨0⟩ e⟩]
        { elems := [id] } u
  | start {x : SExp} {f : FuncIdx} : Idx I.funcs x f → DeclT I (L [K "start", x]) [.start f] {} []
  | export_ {nx xi : SExp} {n : String} {e : ExternIdx} : Name nx n → ExternIdxT I xi e →
      DeclT I (L [K "export", nx, xi]) [.export_ ⟨n, e⟩] {} []

/-- One field's reading: declarations, contributed context, implicit uses. -/
abbrev FieldOut := List Decl × IdCtx × List FuncType

/-- `Tmodule` (plain `(module id? decl*)` and abbreviated `decl*`), read from a
document. -/
def ModuleT (x : SExp) (m : Module) : Prop :=
  ∃ (fields : List SExp) (outs : List FieldOut) (I : IdCtx),
    ((∃ ix id, x = doc [L (K "module" :: (ix ++ fields))] ∧ IdOpt ix id) ∨ x = doc fields) ∧
    List.Forall₂ (fun f (o : FieldOut) => DeclT I f o.1 o.2.1 o.2.2) fields outs ∧
    let J := IdCtx.concat (outs.map (·.2.1))
    let ds := outs.flatMap (·.1)
    let implicit := implicitTypes J.typedefs (outs.flatMap (·.2.2))
    I = J ++ implicitCtx implicit ∧ I.Ok ∧ Ordered ds ∧ startCount ds ≤ 1 ∧
    m = build (resolve ds) implicit

/-! ## The encoding relations -/

/-- WAT syntax: S-expression documents to Core 3.0 modules. -/
def watSyntax : EncRel SExp Module := ModuleT

/-- **Core 3.0 WAT text**: `sexpWat3 ⨾ watSyntax`. -/
def Encodes : EncRel String Module := Formats.SExpEncoding.Wat.sexpWat3 ⨾ watSyntax

/-- UTF-8 bytes of Core 3.0 WAT text (the pushforward along UTF-8). -/
def EncodesBytes : EncRel (List UInt8) Module := Encodes.push Unicode.utf8

theorem encodesBytes_eq_comp :
    EncodesBytes = Formats.SExpEncoding.Wat.sexpWatBytes .core3 ⨾ watSyntax :=
  EncRel.push_comp _ _ _

/-! ## Functionality of module fields (helpers) -/

theorem exportsT_mem {xs : List SExp} {ns : List String} (h : ExportsT xs ns) :
    ∀ x ∈ xs, HeadKw "export" x :=
  forall₂_mem_left (fun _ _ h => by obtain ⟨nx, rfl, -⟩ := h; exact ⟨_, rfl⟩) h

theorem exportsT_functional {xs : List SExp} {ns ns' : List String} (h : ExportsT xs ns)
    (h' : ExportsT xs ns') : ns = ns' := by
  refine forall₂_functional (fun x n n' hn hn' => ?_) h h'
  obtain ⟨nx, rfl, h1⟩ := hn
  obtain ⟨nx', e, h2⟩ := hn'
  simp only [L_inj, List.cons.injEq, and_true, true_and] at e; subst e
  exact name_functional h1 h2

/-- Splitting `id? (export nm)*` off the items of a module field. -/
theorem ix_ex_split {ix ex r ix' ex' r' : List SExp} {id id' : Option String}
    {ns ns' : List String} (hix : IdOpt ix id) (hex : ExportsT ex ns) (hix' : IdOpt ix' id')
    (hex' : ExportsT ex' ns') (hr : NotP IdAtom r) (hr2 : NotP (HeadKw "export") r)
    (hr' : NotP IdAtom r') (hr2' : NotP (HeadKw "export") r')
    (e : ix ++ ex ++ r = ix' ++ ex' ++ r') :
    ix = ix' ∧ id = id' ∧ ex = ex' ∧ ns = ns' ∧ r = r' := by
  simp only [List.append_assoc] at e
  obtain ⟨rfl, e1⟩ := munch (idOpt_mem hix) (idOpt_mem hix')
    (notP_append (fun x hx => not_idAtom_of_headKw (exportsT_mem hex x hx)) hr)
    (notP_append (fun x hx => not_idAtom_of_headKw (exportsT_mem hex' x hx)) hr') e
  obtain ⟨rfl, rfl⟩ := munch (exportsT_mem hex) (exportsT_mem hex') hr2 hr2' e1
  exact ⟨rfl, idOpt_functional hix hix', rfl, exportsT_functional hex hex', rfl⟩

theorem inlineImportT_head {x : SExp} {n₁ n₂ : String} (h : InlineImportT x n₁ n₂) :
    HeadKw "import" x := by
  obtain ⟨a, b, rfl, -⟩ := h; exact ⟨_, rfl⟩

theorem inlineImportT_functional {x : SExp} {n₁ n₂ n₁' n₂' : String} (h : InlineImportT x n₁ n₂)
    (h' : InlineImportT x n₁' n₂') : n₁ = n₁' ∧ n₂ = n₂' := by
  obtain ⟨a, b, rfl, ha, hb⟩ := h
  obtain ⟨a', b', e, ha', hb'⟩ := h'
  simp only [L_inj, List.cons.injEq, and_true, true_and] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨name_functional ha ha', name_functional hb hb'⟩

theorem notP_headKw {P : SExp → Prop} {s : String} {x : SExp} {t : List SExp}
    (h : HeadKw s x) (hP : ∀ y, HeadKw s y → ¬ P y) : NotP P (x :: t) := notP_cons (hP x h)

theorem headKw_not_headKw {s t : String} (hst : s ≠ t) : ∀ y, HeadKw s y → ¬ HeadKw t y :=
  fun _ h => headKw_ne hst h

theorem localT_head {I : IdCtx} {x : SExp} {ls : List (ValType × Option String)}
    (h : LocalT I x ls) : HeadKw "local" x := by
  rcases h with ⟨n, tx, t, rfl, -⟩ | ⟨txs, ts, rfl, -⟩ <;> exact ⟨_, rfl⟩

theorem localT_functional {I : IdCtx} (hT : Distinct I.types) {x : SExp}
    {ls ls' : List (ValType × Option String)} (h : LocalT I x ls) (h' : LocalT I x ls') :
    ls = ls' := by
  rcases h with ⟨n, tx, t, rfl, ht, rfl⟩ | ⟨txs, ts, rfl, hts, rfl⟩ <;>
    rcases h' with ⟨n', tx', t', e, ht', rfl⟩ | ⟨txs', ts', e, hts', rfl⟩
  · simp only [L_inj, List.cons.injEq, Formats.SExp2.atom.injEq, Atom.id.injEq, and_true,
      true_and] at e
    obtain ⟨rfl, rfl⟩ := e; rw [valTypeT_functional hT ht ht']
  · simp only [L_inj, List.cons.injEq, true_and] at e; subst e
    cases hts' with | cons h _ => exact absurd h not_valTypeT_id
  · simp only [L_inj, List.cons.injEq, true_and] at e; subst e
    cases hts with | cons h _ => exact absurd h not_valTypeT_id
  · simp only [L_inj, List.cons.injEq, true_and] at e; subst e
    rw [forall₂_functional (R := ValTypeT I) (fun _ _ _ h h' => valTypeT_functional hT h h')
      hts hts']

theorem dataStringT_mem {xs : List SExp} {bs : List UInt8} (h : DataStringT xs bs) :
    ∀ x ∈ xs, ∃ b, x = .atom (.str b) := by
  obtain ⟨bss, h, -⟩ := h
  exact forall₂_mem_left (fun x b h => ⟨b, h⟩) h

theorem dataStringT_functional {xs : List SExp} {bs bs' : List UInt8} (h : DataStringT xs bs)
    (h' : DataStringT xs bs') : bs = bs' := by
  obtain ⟨bss, h, rfl⟩ := h
  obtain ⟨bss', h', rfl⟩ := h'
  obtain rfl := forall₂_functional (R := fun (x : SExp) (b : List UInt8) => x = .atom (.str b))
    (fun x b b' hb hb' => by rw [hb] at hb'; simpa using hb') h h'
  rfl

theorem memUseT_mem {I : IdCtx} {xs : List SExp} {m : MemIdx} (h : MemUseT I xs m) :
    ∀ x ∈ xs, HeadKw "memory" x := by
  rcases h with ⟨rfl, -⟩ | ⟨x, rfl, -⟩
  · simp
  · intro y hy; simp only [List.mem_singleton] at hy; subst hy; exact ⟨_, rfl⟩

theorem memUseT_functional {I : IdCtx} (hM : Distinct I.mems) {xs : List SExp} {m m' : MemIdx}
    (h : MemUseT I xs m) (h' : MemUseT I xs m') : m = m' := by
  rcases h with ⟨rfl, h1⟩ | ⟨x, rfl, h1⟩ <;> rcases h' with ⟨e, h2⟩ | ⟨x', e, h2⟩
  · exact Wasm.Idx.toNat_injective (h1.trans h2.symm)
  · simp at e
  · simp at e
  · simp only [List.cons.injEq, L_inj, and_true, true_and] at e; subst e
    exact idx_functional hM h1 h2

theorem tableUseT_mem {I : IdCtx} {xs : List SExp} {t : TableIdx} (h : TableUseT I xs t) :
    ∀ x ∈ xs, HeadKw "table" x := by
  rcases h with ⟨rfl, -⟩ | ⟨x, rfl, -⟩
  · simp
  · intro y hy; simp only [List.mem_singleton] at hy; subst hy; exact ⟨_, rfl⟩

theorem tableUseT_functional {I : IdCtx} (hTb : Distinct I.tables) {xs : List SExp}
    {t t' : TableIdx} (h : TableUseT I xs t) (h' : TableUseT I xs t') : t = t' := by
  rcases h with ⟨rfl, h1⟩ | ⟨x, rfl, h1⟩ <;> rcases h' with ⟨e, h2⟩ | ⟨x', e, h2⟩
  · exact Wasm.Idx.toNat_injective (h1.trans h2.symm)
  · simp at e
  · simp at e
  · simp only [List.cons.injEq, L_inj, and_true, true_and] at e; subst e
    exact idx_functional hTb h1 h2

/-- An item that is a `(kw …)` list with a reserved keyword is not a folded instruction. -/
theorem not_folded_headKw {I : IdCtx} {s : String} (hs : s ∈ reservedKws) {x : SExp} {e : Expr}
    {u : List FuncType} (hx : HeadKw s x) (h : Folded I x e u) : False := by
  obtain ⟨s', ys, rfl, hs'⟩ := folded_shape h
  exact isStart_not_headKw hs (.inr ⟨s', ys, rfl, hs'⟩) hx

/-- Offsets and element expressions: `(kw instr*)` or one folded instruction. -/
theorem wrapped_functional {I I' : IdCtx} {kw : String} (hkw : kw ∈ reservedKws) {x : SExp}
    {e e' : Expr} {u u' : List FuncType} (hT : Distinct I.types) (hE : TypesEq I I')
    (h : (∃ xs, x = L (K kw :: xs) ∧ ExprT I xs e u) ∨ Folded I x e u)
    (h' : (∃ xs, x = L (K kw :: xs) ∧ ExprT I' xs e' u') ∨ Folded I' x e' u') :
    u = u' ∧ (I = I' → I.Ok → e = e') := by
  rcases h with ⟨xs, rfl, h⟩ | h <;> rcases h' with ⟨xs', e1, h'⟩ | h'
  · simp only [L_inj, List.cons.injEq, true_and] at e1; subst e1
    exact ⟨instrs_uses hT hE h h', fun hI hok => by subst hI; exact (instrs_functional' hok h h').1⟩
  · exact (not_folded_headKw hkw ⟨_, rfl⟩ h').elim
  · subst e1; exact (not_folded_headKw hkw ⟨_, rfl⟩ h).elim
  · exact ⟨folded_uses hT hE h h', fun hI hok => by subst hI; exact (folded_functional' hok h h').1⟩

theorem wrapped_isList {I : IdCtx} {kw : String} {x : SExp} {e : Expr} {u : List FuncType}
    (h : (∃ xs, x = L (K kw :: xs) ∧ ExprT I xs e u) ∨ Folded I x e u) :
    ∃ s ys, x = L (K s :: ys) ∧ (s = kw ∨ InstrKw s) := by
  rcases h with ⟨xs, rfl, -⟩ | h
  · exact ⟨_, _, rfl, .inl rfl⟩
  · obtain ⟨s, ys, rfl, hs⟩ := folded_shape h; exact ⟨_, _, rfl, .inr hs⟩

theorem elemListT_cases {I : IdCtx} {xs : List SExp} {rt : RefType} {es : List Expr}
    {u : List FuncType} (h : ElemListT I xs rt es u) :
    ∃ y ys, xs = y :: ys ∧ ((∃ r, RefTypeT I y r) ∨ y = K "func") := by
  rcases h with ⟨rx, exs, uss, rfl, hr, -⟩ | ⟨fxs, fs, rfl, -⟩
  · exact ⟨_, _, rfl, .inl ⟨_, hr⟩⟩
  · exact ⟨_, _, rfl, .inr rfl⟩

theorem zip_unique {α β : Type} {as as' : List α} {bs bs' : List β} (h : as.length = bs.length)
    (h' : as'.length = bs'.length) (e : as.zip bs = as'.zip bs') : as = as' ∧ bs = bs' := by
  have h1 := List.unzip_zip h
  have h2 := List.unzip_zip h'
  rw [e] at h1
  rw [h1] at h2
  simp only [Prod.mk.injEq] at h2
  exact ⟨h2.1, h2.2⟩

theorem elemExprs_functional {I I' : IdCtx} (hT : Distinct I.types) (hE : TypesEq I I')
    {exs : List SExp} {es es' : List Expr} {uss uss' : List (List FuncType)}
    (h : List.Forall₂ (fun x (p : Expr × List FuncType) => ElemExprT I x p.1 p.2) exs (es.zip uss))
    (hl : es.length = uss.length)
    (h' : List.Forall₂ (fun x (p : Expr × List FuncType) => ElemExprT I' x p.1 p.2) exs
      (es'.zip uss'))
    (hl' : es'.length = uss'.length) :
    uss = uss' ∧ (I = I' → I.Ok → es = es') := by
  -- by induction on the items
  have key : ∀ {exs : List SExp} {ps ps' : List (Expr × List FuncType)},
      List.Forall₂ (fun x (p : Expr × List FuncType) => ElemExprT I x p.1 p.2) exs ps →
      List.Forall₂ (fun x (p : Expr × List FuncType) => ElemExprT I' x p.1 p.2) exs ps' →
      ps.map Prod.snd = ps'.map Prod.snd ∧ (I = I' → I.Ok → ps = ps') := by
    intro exs ps ps' h h'
    induction h generalizing ps' with
    | nil => cases h'; exact ⟨rfl, fun _ _ => rfl⟩
    | cons hx _ ih =>
        cases h' with
        | cons hx' hr' =>
            obtain ⟨hu, he⟩ := wrapped_functional (kw := "item") (by decide) hT hE hx hx'
            obtain ⟨hu1, he1⟩ := ih hr'
            refine ⟨by simp [hu, hu1], fun hI hok => ?_⟩
            rw [he1 hI hok, Prod.ext (he hI hok) hu]
  obtain ⟨hu, he⟩ := key h h'
  have lu : (es.zip uss).map Prod.snd = uss := by
    rw [← List.unzip_snd, List.unzip_zip hl]
  have lu' : (es'.zip uss').map Prod.snd = uss' := by
    rw [← List.unzip_snd, List.unzip_zip hl']
  refine ⟨by rw [← lu, ← lu', hu], fun hI hok => ?_⟩
  exact (zip_unique hl hl' (he hI hok)).1

theorem elemListT_functional {I I' : IdCtx} (hT : Distinct I.types) (hE : TypesEq I I')
    {xs : List SExp} {rt rt' : RefType} {es es' : List Expr} {u u' : List FuncType}
    (h : ElemListT I xs rt es u) (h' : ElemListT I' xs rt' es' u') :
    u = u' ∧ (I = I' → I.Ok → rt = rt' ∧ es = es') := by
  rcases h with ⟨rx, exs, uss, rfl, hr, hex, hl, -, rfl⟩ | ⟨fxs, fs, rfl, hfs, -, rfl, rfl, rfl⟩ <;>
    rcases h' with ⟨rx', exs', uss', e, hr', hex', hl', -, rfl⟩ |
      ⟨fxs', fs', e, hfs', -, rfl, rfl, rfl⟩
  · simp only [List.cons.injEq] at e; obtain ⟨rfl, rfl⟩ := e
    obtain ⟨hu, he⟩ := elemExprs_functional hT hE hex hl hex' hl'
    refine ⟨by rw [hu], fun hI hok => ?_⟩
    subst hI
    exact ⟨refTypeT_functional hT hr hr', he rfl hok⟩
  · simp only [List.cons.injEq] at e; obtain ⟨rfl, -⟩ := e
    rcases refTypeT_shape hr with h | ⟨s, e, hs⟩
    · exact absurd h headKw_K
    · simp only [K_inj] at e; subst e; exact absurd hs (by decide)
  · simp only [List.cons.injEq] at e; obtain ⟨rfl, -⟩ := e
    rcases refTypeT_shape hr' with h | ⟨s, e, hs⟩
    · exact absurd h headKw_K
    · simp only [K_inj] at e; subst e; exact absurd hs (by decide)
  · simp only [List.cons.injEq, true_and] at e; subst e
    refine ⟨rfl, fun hI hok => ?_⟩
    subst hI
    rw [forall₂_functional (R := Idx I.funcs)
      (fun _ _ _ h h' => idx_functional hok.2.2.2.2.2.1 h h') hfs hfs']
    exact ⟨rfl, rfl⟩

theorem externIdxT_functional {I : IdCtx} (hI : I.Ok) {x : SExp} {e e' : ExternIdx}
    (h : ExternIdxT I x e) (h' : ExternIdxT I x e') : e = e' := by
  obtain ⟨hT, hTg, hG, hM, hTb, hF, hD, hE, hL, hLb, hFl⟩ := hI
  rcases h with ⟨y, i, rfl, hi, rfl⟩ | ⟨y, i, rfl, hi, rfl⟩ | ⟨y, i, rfl, hi, rfl⟩ |
      ⟨y, i, rfl, hi, rfl⟩ | ⟨y, i, rfl, hi, rfl⟩ <;>
    rcases h' with ⟨y', i', e, hi', rfl⟩ | ⟨y', i', e, hi', rfl⟩ | ⟨y', i', e, hi', rfl⟩ |
      ⟨y', i', e, hi', rfl⟩ | ⟨y', i', e, hi', rfl⟩
  all_goals simp at e
  all_goals subst e
  · rw [idx_functional hTg hi hi']
  · rw [idx_functional hG hi hi']
  · rw [idx_functional hM hi hi']
  · rw [idx_functional hTb hi hi']
  · rw [idx_functional hF hi hi']

/-! ### Item classes of module fields -/

/-- Items that are neither identifiers nor inline exports. -/
def FieldOk (x : SExp) : Prop := ¬ IdAtom x ∧ ¬ HeadKw "export" x

/-- The rest of a module field after `id? (export nm)*`. -/
def RestOk (r : List SExp) : Prop := NotP IdAtom r ∧ NotP (HeadKw "export") r

theorem fieldOk_K {s : String} : FieldOk (K s) := ⟨not_idAtom_K, headKw_K⟩

theorem fieldOk_headKw {s : String} {x : SExp} (h : HeadKw s x) (hs : s ≠ "export") : FieldOk x :=
  ⟨not_idAtom_of_headKw h, headKw_ne hs h⟩

theorem fieldOk_isStart {x : SExp} (h : IsStart x) : FieldOk x :=
  ⟨isStart_not_idAtom h, isStart_not_headKw (by decide) h⟩

theorem restOk_nil : RestOk [] := ⟨notP_nil, notP_nil⟩

theorem restOk_cons {x : SExp} {t : List SExp} (h : FieldOk x) : RestOk (x :: t) :=
  ⟨notP_cons h.1, notP_cons h.2⟩

theorem restOk_append {xs r : List SExp} (h : ∀ x ∈ xs, FieldOk x) (hr : RestOk r) :
    RestOk (xs ++ r) :=
  ⟨notP_append (fun x hx => (h x hx).1) hr.1, notP_append (fun x hx => (h x hx).2) hr.2⟩

theorem restOk_instrs {I : IdCtx} {body : List SExp} {e : Expr} {u : List FuncType}
    (h : Instrs I body e u) : RestOk body :=
  ⟨notP_instrs_nil (fun _ h => (fieldOk_isStart h).1) h,
    notP_instrs_nil (fun _ h => (fieldOk_isStart h).2) h⟩

theorem fieldOk_tuList {x : SExp} (h : TUList x) : FieldOk x := by
  rcases h with h | h | h <;> exact fieldOk_headKw h (by decide)

theorem restOk_typeUse {I : IdCtx} {xs : List SExp} {x : TypeIdx} {ls : List (Option String)}
    {u : List FuncType} (h : TypeUseT I xs x ls u) : RestOk xs := by
  simpa using restOk_append (r := []) (fun x hx => fieldOk_tuList (typeUseT_mem h x hx)) restOk_nil

theorem fieldOk_globalType {I : IdCtx} {x : SExp} {g : GlobalType} (h : GlobalTypeT I x g) :
    FieldOk x := by
  rcases globalTypeT_shape h with h | h | ⟨s, rfl⟩
  · exact fieldOk_headKw h (by decide)
  · exact fieldOk_headKw h (by decide)
  · exact fieldOk_K

theorem fieldOk_refType {I : IdCtx} {x : SExp} {r : RefType} (h : RefTypeT I x r) : FieldOk x := by
  rcases refTypeT_shape h with h | ⟨s, rfl, -⟩
  · exact fieldOk_headKw h (by decide)
  · exact fieldOk_K

theorem memType_fieldOk {xs : List SExp} {m : MemoryType} (h : MemTypeT xs m) :
    ∀ x ∈ xs, FieldOk x := by
  intro x hx; obtain ⟨s, rfl⟩ := memTypeT_mem h x hx; exact fieldOk_K

theorem addrType_fieldOk {xs : List SExp} {a : AddrType} (h : AddrTypeT xs a) :
    ∀ x ∈ xs, FieldOk x := by
  intro x hx; rcases addrTypeT_mem h x hx with rfl | rfl <;> exact fieldOk_K

theorem tableType_fieldOk {I : IdCtx} {xs : List SExp} {t : TableType} (h : TableTypeT I xs t) :
    xs ≠ [] ∧ ∀ x ∈ xs, FieldOk x := by
  obtain ⟨ax, lx, rx, a, l, r, rfl, ha, hl, hr, -⟩ := h
  refine ⟨by simp, fun x hx => ?_⟩
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with (hx | hx) | rfl
  · exact addrType_fieldOk ha x hx
  · obtain ⟨t, rfl, -⟩ := (limitsT_mem hl).2 x hx; exact fieldOk_K
  · exact fieldOk_refType hr

theorem restOk_append_ne {xs r : List SExp} (hne : xs ≠ []) (h : ∀ x ∈ xs, FieldOk x) :
    RestOk (xs ++ r) := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x xs => exact restOk_cons (h x (by simp))

/-- Splitting `id? (export nm)*`. -/
theorem ix_ex_split' {ix ex r ix' ex' r' : List SExp} {id id' : Option String}
    {ns ns' : List String} (hix : IdOpt ix id) (hex : ExportsT ex ns) (hix' : IdOpt ix' id')
    (hex' : ExportsT ex' ns') (hr : RestOk r) (hr' : RestOk r')
    (e : ix ++ (ex ++ r) = ix' ++ (ex' ++ r')) :
    ix = ix' ∧ id = id' ∧ ex = ex' ∧ ns = ns' ∧ r = r' :=
  ix_ex_split hix hex hix' hex' hr.1 hr.2 hr'.1 hr'.2 (by simpa only [List.append_assoc] using e)

theorem typeDefT_id_types {I I' : IdCtx} {x : SExp} {st st' : SubType} {id id' : Option String}
    {ns ns' : List (Option String)} (h : TypeDefT I x st id ns) (h' : TypeDefT I' x st' id' ns') :
    id = id' := by
  obtain ⟨ix, sx, rfl, hix, -⟩ := h
  obtain ⟨ix', sx', e, hix', -⟩ := h'
  simp only [L_inj, List.cons.injEq, true_and] at e
  obtain ⟨rfl, -⟩ := List.append_inj' e rfl
  exact idOpt_functional hix hix'


theorem forall₂_map_eq {α β γ δ : Type} {R : α → β → Prop} {R' : α → γ → Prop} {f : β → δ}
    {g : γ → δ} (hR : ∀ x a b, R x a → R' x b → f a = g b) :
    ∀ {xs : List α} {as : List β} {bs : List γ}, List.Forall₂ R xs as → List.Forall₂ R' xs bs →
      as.map f = bs.map g
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons h hs, .cons h' hs' => by
      simp only [List.map_cons, hR _ _ _ h h', forall₂_map_eq hR hs hs']

/-- The type names contributed by a recursive type are syntactic. -/
theorem recTypeT_types {I I' : IdCtx} {x : SExp} {rt rt' : RecType} {J J' : IdCtx}
    (h : RecTypeT I x rt J) (h' : RecTypeT I' x rt' J') : J.types = J'.types := by
  rcases h with ⟨dxs, defs, rfl, hd, -, -, rfl⟩ | ⟨st, id, ns, hd, -, rfl⟩ <;>
    rcases h' with ⟨dxs', defs', e, hd', -, -, rfl⟩ | ⟨st', id', ns', hd', -, rfl⟩
  · simp only [L_inj, List.cons.injEq, true_and] at e; subst e
    exact forall₂_map_eq
      (R := fun dx (d : SubType × Option String × List (Option String)) => TypeDefT I dx d.1 d.2.1 d.2.2)
      (R' := fun dx (d : SubType × Option String × List (Option String)) =>
        TypeDefT I' dx d.1 d.2.1 d.2.2)
      (f := fun (d : SubType × Option String × List (Option String)) => d.2.1)
      (g := fun (d : SubType × Option String × List (Option String)) => d.2.1)
      (fun _ _ _ h h' => typeDefT_id_types h h') hd hd'
  · exact absurd (typeDefT_head hd') (headKw_ne (by decide) ⟨_, rfl⟩)
  · subst e; exact absurd (typeDefT_head hd) (headKw_ne (by decide) ⟨_, rfl⟩)
  · simp [recCtx, typeDefT_id_types hd hd']

/-- Readings of external types in two contexts resolving types alike. -/
theorem externTypeT_uses {I I' : IdCtx} (hT : Distinct I.types) (hE : TypesEq I I') {x : SExp}
    {et et' : ExternType} {J J' : IdCtx} {u u' : List FuncType} (h : ExternTypeT I x et J u)
    (h' : ExternTypeT I' x et' J' u') : J = J' ∧ u = u' := by
  rcases h with ⟨ix, rest, id, t, rfl, hix, ⟨ls, ht⟩, rfl, rfl⟩ |
      ⟨ix, gx, id, g, rfl, hix, hg, rfl, rfl, rfl⟩ |
      ⟨ix, rest, id, m, rfl, hix, hm, rfl, rfl, rfl⟩ |
      ⟨ix, rest, id, t, rfl, hix, ht, rfl, rfl, rfl⟩ |
      ⟨ix, rest, id, t, ls, rfl, hix, ht, rfl, rfl⟩ <;>
    rcases h' with ⟨ix', rest', id', t', e, hix', ⟨ls', ht'⟩, rfl, rfl⟩ |
      ⟨ix', gx', id', g', e, hix', hg', rfl, rfl, rfl⟩ |
      ⟨ix', rest', id', m', e, hix', hm', rfl, rfl, rfl⟩ |
      ⟨ix', rest', id', t', e, hix', ht', rfl, rfl, rfl⟩ |
      ⟨ix', rest', id', t', ls', e, hix', ht', rfl, rfl⟩
  all_goals simp only [L_inj, List.cons.injEq, K_inj] at e
  all_goals first | (exact absurd e.1 (by decide)) | obtain ⟨-, e⟩ := e
  · obtain ⟨rfl, rfl, rfl⟩ := idOpt_split hix hix' (notIdHead_of_forall (typeUseT_notId ht))
      (notIdHead_of_forall (typeUseT_notId ht')) e
    exact ⟨rfl, typeUseT_uses hT hE ht ht'⟩
  · obtain ⟨rfl, rfl, -⟩ := idOpt_split hix hix' (notIdHead_cons (globalTypeT_notId hg))
      (notIdHead_cons (globalTypeT_notId hg')) e
    exact ⟨rfl, rfl⟩
  · have nid : ∀ {rest : List SExp} {m : MemoryType}, MemTypeT rest m → NotIdHead rest := by
      intro rest m hm
      exact notIdHead_of_forall fun x hx => by obtain ⟨s, rfl⟩ := memTypeT_mem hm x hx; simp
    obtain ⟨rfl, rfl, -⟩ := idOpt_split hix hix' (nid hm) (nid hm') e
    exact ⟨rfl, rfl⟩
  · obtain ⟨rfl, rfl, -⟩ := idOpt_split hix hix' (notIdHead_of_forall (tableTypeT_notId ht))
      (notIdHead_of_forall (tableTypeT_notId ht')) e
    exact ⟨rfl, rfl⟩
  · obtain ⟨rfl, rfl, rfl⟩ := idOpt_split hix hix' (notIdHead_of_forall (typeUseT_notId ht))
      (notIdHead_of_forall (typeUseT_notId ht')) e
    exact ⟨rfl, typeUseT_uses hT hE ht ht'⟩

theorem externTypeT_types {I : IdCtx} {x : SExp} {et : ExternType} {J : IdCtx}
    {u : List FuncType} (h : ExternTypeT I x et J u) : J.types = [] := by
  rcases h with ⟨_, _, _, _, -, -, -, -, rfl⟩ | ⟨_, _, _, _, -, -, -, -, rfl, -⟩ |
      ⟨_, _, _, _, -, -, -, -, rfl, -⟩ | ⟨_, _, _, _, -, -, -, -, rfl, -⟩ |
      ⟨_, _, _, _, _, -, -, -, -, rfl⟩ <;> rfl

theorem typesEq_append {I I' K K' : IdCtx} (hE : TypesEq I I') (hK : K.types = []) (hK' : K'.types = []) :
    TypesEq (I ++ K) (I' ++ K') := by
  intro x i
  change IdxIn (I.types ++ K.types) x i ↔ IdxIn (I'.types ++ K'.types) x i
  rw [hK, hK', List.append_nil, List.append_nil]; exact hE x i

theorem distinct_append_types {I K : IdCtx} (hT : Distinct I.types) (hK : K.types = []) :
    Distinct (I ++ K).types := by
  change Distinct (I.types ++ K.types); rw [hK, List.append_nil]; exact hT

/-- What two readings of one module field agree on: the type names always; the
contributed context and the implicitly used types when the contexts resolve
types alike; the declarations in one context with distinct names. -/
def DeclAgree (I I' : IdCtx) (ds : List Decl) (J : IdCtx) (u : List FuncType) (ds' : List Decl)
    (J' : IdCtx) (u' : List FuncType) : Prop :=
  J.types = J'.types ∧ (TypesEq I I' → Distinct I.types → J = J' ∧ u = u') ∧
    (I = I' → I.Ok → ds = ds')

theorem DeclAgree.mk' {I I' : IdCtx} {ds ds' : List Decl} {J J' : IdCtx}
    {u u' : List FuncType} (hJ : J = J') (hu : TypesEq I I' → Distinct I.types → u = u')
    (hds : I = I' → I.Ok → ds = ds') : DeclAgree I I' ds J u ds' J' u' :=
  ⟨by rw [hJ], fun hE hT => ⟨hJ, hu hE hT⟩, hds⟩

theorem restOk_imp {imp : SExp} {t : List SExp} {n₁ n₂ : String} (h : InlineImportT imp n₁ n₂) :
    RestOk (imp :: t) := restOk_cons (fieldOk_headKw (inlineImportT_head h) (by decide))

theorem not_tu_import {imp : SExp} {n₁ n₂ : String} (h : InlineImportT imp n₁ n₂) :
    ¬ TUList imp := by
  rintro (h' | h' | h') <;> exact headKw_ne (by decide) (inlineImportT_head h) h'

/-! ### Table types -/

theorem tableType_items {I : IdCtx} {xs : List SExp} {t : TableType} (h : TableTypeT I xs t) :
    ∀ x ∈ xs, (∃ s, x = K s) ∨ HeadKw "ref" x := by
  obtain ⟨ax, lx, rx, a, l, r, rfl, ha, hl, hr, -⟩ := h
  intro x hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with (hx | hx) | rfl
  · rcases addrTypeT_mem ha x hx with rfl | rfl <;> exact .inl ⟨_, rfl⟩
  · obtain ⟨t, rfl, -⟩ := (limitsT_mem hl).2 x hx; exact .inl ⟨_, rfl⟩
  · rcases refTypeT_shape hr with h | ⟨s, rfl, -⟩
    · exact .inr h
    · exact .inl ⟨_, rfl⟩

theorem tableType_ne {I : IdCtx} {xs : List SExp} {t : TableType} (h : TableTypeT I xs t) :
    xs ≠ [] := (tableType_fieldOk h).1

theorem refAbbrevKws_alpha : ∀ s ∈ refAbbrevKws, AlphaKw s ∧ s ≠ "i32" ∧ s ≠ "i64" := by
  decide +kernel

theorem refType_not_numTok {I : IdCtx} {x : SExp} {r : RefType} (h : RefTypeT I x r) :
    ¬ NumTok x := by
  rcases refTypeT_shape h with h | ⟨s, rfl, hs⟩
  · exact not_numTok_of_headKw h
  · exact not_numTok_K (refAbbrevKws_alpha s hs).1

theorem refType_not_addrTok {I : IdCtx} {x : SExp} {r : RefType} (h : RefTypeT I x r) :
    ¬ AddrTok x := by
  rcases refTypeT_shape h with ⟨ys, rfl⟩ | ⟨s, rfl, hs⟩
  · rintro (e | e) <;> simp at e
  · rintro (e | e) <;> simp only [K_inj] at e <;> subst e
    · exact (refAbbrevKws_alpha _ hs).2.1 rfl
    · exact (refAbbrevKws_alpha _ hs).2.2 rfl

theorem tableType_split {I I' : IdCtx} {tx tx' r r' : List SExp} {t t' : TableType}
    (h : TableTypeT I tx t) (h' : TableTypeT I' tx' t') (e : tx ++ r = tx' ++ r') :
    tx = tx' ∧ r = r' := by
  obtain ⟨ax, lx, rx, a, l, rt, rfl, ha, hl, hr, -⟩ := h
  obtain ⟨ax', lx', rx', a', l', rt', rfl, ha', hl', hr', -⟩ := h'
  simp only [List.append_assoc, List.cons_append] at e
  obtain ⟨rfl, e1⟩ := addr_limits_split ha hl ha' hl' e
  obtain ⟨rfl, e2⟩ := munch (P := NumTok) (limitsT_mem hl).2 (limitsT_mem hl').2
    (notP_cons (refType_not_numTok hr)) (notP_cons (refType_not_numTok hr')) e1
  simp only [List.cons.injEq] at e2
  obtain ⟨rfl, rfl⟩ := e2
  exact ⟨rfl, rfl⟩

theorem tableType_not_elem {I I' : IdCtx} {tx body ax' : List SExp} {rx' E' : SExp}
    {t : TableType} {a' : AddrType} {r' : RefType} (h : TableTypeT I tx t) (ha' : AddrTypeT ax' a')
    (hr' : RefTypeT I' rx' r') (e : tx ++ body = ax' ++ [rx', E']) : False := by
  obtain ⟨ax, lx, rx, a, l, rt, rfl, ha, hl, hr, -⟩ := h
  simp only [List.append_assoc] at e
  obtain ⟨hne, hnum⟩ := limitsT_mem hl
  obtain ⟨rfl, e1⟩ := munch (P := AddrTok) (addrTypeT_mem ha) (addrTypeT_mem ha')
    (by
      cases lx with
      | nil => exact absurd rfl hne
      | cons y ys => exact notP_cons (not_addrTok_of_numTok (hnum y (by simp))))
    (notP_cons (refType_not_addrTok hr')) e
  cases lx with
  | nil => exact hne rfl
  | cons y ys =>
      simp only [List.cons_append, List.cons.injEq] at e1
      obtain ⟨rfl, -⟩ := e1
      exact refType_not_numTok hr' (hnum _ (by simp))

theorem import_not_elem {I' : IdCtx} {imp : SExp} {rest ax' : List SExp} {rx' E' : SExp}
    {n₁ n₂ : String} {a' : AddrType} {r' : RefType} (himp : InlineImportT imp n₁ n₂)
    (ha' : AddrTypeT ax' a') (hr' : RefTypeT I' rx' r') (e : imp :: rest = ax' ++ [rx', E']) :
    False := by
  have hi := inlineImportT_head himp
  rcases ha' with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · simp only [List.nil_append, List.cons.injEq] at e
    obtain ⟨rfl, -⟩ := e
    rcases refTypeT_shape hr' with h | ⟨s, rfl, -⟩
    · exact headKw_ne (by decide) hi h
    · exact headKw_K hi
  · simp only [List.cons_append, List.cons.injEq] at e; obtain ⟨rfl, -⟩ := e; exact headKw_K hi
  · simp only [List.cons_append, List.cons.injEq] at e; obtain ⟨rfl, -⟩ := e; exact headKw_K hi

theorem tableType_not_import {I : IdCtx} {tx body rest : List SExp} {imp : SExp} {t : TableType}
    {n₁ n₂ : String} (h : TableTypeT I tx t) (himp : InlineImportT imp n₁ n₂)
    (e : tx ++ body = imp :: rest) : False := by
  have hi := inlineImportT_head himp
  cases tx with
  | nil => exact tableType_ne h rfl
  | cons y ys =>
      simp only [List.cons_append, List.cons.injEq] at e
      obtain ⟨rfl, -⟩ := e
      rcases tableType_items h y (by simp) with ⟨s, rfl⟩ | h'
      · exact headKw_K hi
      · exact headKw_ne (by decide) h' hi

/-- An element list does not start like a list of function indices. -/
theorem elemList_not_idx {I I' : IdCtx} {el : List SExp} {rt : RefType} {es : List Expr}
    {u : List FuncType} {fxs : List SExp} {fs : List FuncIdx} (h : ElemListT I el rt es u)
    (h' : List.Forall₂ (Idx I'.funcs) fxs fs) (e : el = fxs) : False := by
  obtain ⟨y, ys, rfl, hy⟩ := elemListT_cases h
  subst e
  cases h' with
  | cons hy' _ =>
      rcases hy with ⟨r, hr⟩ | rfl
      · rcases idx_shape hy' with h1 | h1
        · exact refType_not_numTok hr h1
        · exact (fieldOk_refType hr).1 h1
      · exact not_idx_K (s := "func") (by decide) hy'

theorem wrapped_not_refType {I I' : IdCtx} {kw : String} (_hkw : kw ∈ reservedKws)
    (hkw' : kw ≠ "ref") {x : SExp} {e : Expr} {u : List FuncType} {r : RefType}
    (h : (∃ xs, x = L (K kw :: xs) ∧ ExprT I xs e u) ∨ Folded I x e u) (hr : RefTypeT I' x r) :
    False := by
  obtain ⟨s, ys, rfl, hs⟩ := wrapped_isList h
  rcases refTypeT_shape hr with h1 | ⟨s', e1, -⟩
  · rw [headKw_L_iff] at h1; subst h1
    rcases hs with hs | hs
    · exact hkw' hs.symm
    · exact hs.not_reserved (by decide)
  · simp at e1

theorem wrapped_not_headKw {I : IdCtx} {kw s : String} (hs : s ∈ reservedKws) (hks : kw ≠ s)
    {x : SExp} {e : Expr} {u : List FuncType}
    (h : (∃ xs, x = L (K kw :: xs) ∧ ExprT I xs e u) ∨ Folded I x e u) : ¬ HeadKw s x := by
  obtain ⟨s', ys, rfl, hs'⟩ := wrapped_isList h
  rw [headKw_L_iff]; rintro rfl
  rcases hs' with hs' | hs'
  · exact hks hs'.symm
  · exact hs'.not_reserved hs

theorem elemList_head_not_wrapped {I I' : IdCtx} {el : List SExp} {rt : RefType}
    {es : List Expr} {u : List FuncType} {kw : String} (hkw : kw ∈ reservedKws) (hkw' : kw ≠ "ref")
    {x : SExp} {e : Expr} {u' : List FuncType} {t : List SExp} (h : ElemListT I el rt es u)
    (hx : (∃ xs, x = L (K kw :: xs) ∧ ExprT I' xs e u') ∨ Folded I' x e u') (eq : el = x :: t) :
    False := by
  obtain ⟨y, ys, rfl, hy⟩ := elemListT_cases h
  simp only [List.cons.injEq] at eq; obtain ⟨rfl, -⟩ := eq
  rcases hy with ⟨r, hr⟩ | rfl
  · exact wrapped_not_refType hkw hkw' hx hr
  · obtain ⟨s, ys, e1, -⟩ := wrapped_isList hx; simp at e1

theorem elemList_fieldOk {I : IdCtx} {el : List SExp} {rt : RefType} {es : List Expr}
    {u : List FuncType} (h : ElemListT I el rt es u) : NotP IdAtom el := by
  obtain ⟨y, ys, rfl, hy⟩ := elemListT_cases h
  rcases hy with ⟨r, hr⟩ | rfl
  · exact notP_cons (fieldOk_refType hr).1
  · exact notP_cons not_idAtom_K

theorem wrapped_notId {I : IdCtx} {kw : String} {x : SExp} {e : Expr} {u : List FuncType}
    (h : (∃ xs, x = L (K kw :: xs) ∧ ExprT I xs e u) ∨ Folded I x e u) : ¬ IdAtom x := by
  obtain ⟨s, ys, rfl, -⟩ := wrapped_isList h; exact not_idAtom_L

/-! ### Readings of one module field -/

set_option hygiene false in
/-- Close a goal relating two module fields with different keywords. -/
macro "decl_kw_contra" : tactic => `(tactic| first
  | (simp at hx; done)
  | (subst hx
     rcases recTypeT_head ‹RecTypeT _ _ _ _› with ⟨ys, e⟩ | ⟨ys, e⟩ <;>
       simp [L, K, kw, listOf] at e))

theorem tagRest {I : IdCtx} {rest : List SExp} {t : TagType} {u : List FuncType}
    (ht : TagTypeT I rest t u) : RestOk rest := by
  obtain ⟨ls, ht⟩ := ht; exact restOk_typeUse ht

theorem memRest {rest : List SExp} {m : MemoryType} (hm : MemTypeT rest m) : RestOk rest := by
  simpa using restOk_append (r := []) (memType_fieldOk hm) restOk_nil

theorem tableRest {I : IdCtx} {tx r : List SExp} {t : TableType} (h : TableTypeT I tx t) :
    RestOk (tx ++ r) := restOk_append_ne (tableType_ne h) (tableType_fieldOk h).2

theorem elemRest {I : IdCtx} {ax : List SExp} {a : AddrType} {rx E : SExp} {r : RefType}
    (ha : AddrTypeT ax a) (hr : RefTypeT I rx r) : RestOk (ax ++ [rx, E]) :=
  restOk_append (addrType_fieldOk ha) (restOk_cons (fieldOk_refType hr))

theorem dataRest {ax strs : List SExp} {a : AddrType} (ha : AddrTypeT ax a) :
    RestOk (ax ++ [L (K "data" :: strs)]) :=
  restOk_append (addrType_fieldOk ha) (restOk_cons (fieldOk_headKw ⟨_, rfl⟩ (by decide)))

theorem funcRest {I I₁ : IdCtx} {tu lx body : List SExp} {t : TypeIdx} {ps : List (Option String)}
    {u₁ u₂ : List FuncType} {locs : List (ValType × Option String)} {e : Expr}
    (htu : TypeUseT I tu t ps u₁) (hlx : Concat (LocalT I) lx locs) (hbody : Instrs I₁ body e u₂) :
    RestOk (tu ++ (lx ++ body)) := by
  exact restOk_append (fun x hx => fieldOk_tuList (typeUseT_mem htu x hx))
    (restOk_append (fun x hx => fieldOk_headKw
      (concat_mem (R := LocalT I) (fun _ _ h => localT_head h) hlx x hx) (by decide))
      (restOk_instrs hbody))

theorem idOpt_split' {ix ix' r r' : List SExp} {id id' : Option String} (h : IdOpt ix id)
    (h' : IdOpt ix' id') (hr : NotP IdAtom r) (hr' : NotP IdAtom r') (e : ix ++ r = ix' ++ r') :
    ix = ix' ∧ id = id' ∧ r = r' := by
  obtain ⟨rfl, rfl⟩ := munch (idOpt_mem h) (idOpt_mem h') hr hr' e
  exact ⟨rfl, idOpt_functional h h', rfl⟩

theorem notId_strs {strs : List SExp} {bs : List UInt8} (h : DataStringT strs bs) :
    NotP IdAtom strs :=
  notP_of_forall fun x hx => by
    obtain ⟨b, rfl⟩ := dataStringT_mem h x hx; rintro ⟨n, e⟩; simp at e

theorem notId_memOff {I : IdCtx} {mu strs : List SExp} {ox : SExp} {m : MemIdx} {e : Expr}
    {u : List FuncType} (hmu : MemUseT I mu m) (hox : OffsetT I ox e u) :
    NotP IdAtom (mu ++ ox :: strs) :=
  notP_append (fun x hx => not_idAtom_of_headKw (memUseT_mem hmu x hx)) (notP_cons (wrapped_notId hox))

theorem notId_tabOff {I : IdCtx} {tu el : List SExp} {ox : SExp} {t : TableIdx} {e : Expr}
    {u : List FuncType} (htu : TableUseT I tu t) (hox : OffsetT I ox e u) :
    NotP IdAtom (tu ++ ox :: el) :=
  notP_append (fun x hx => not_idAtom_of_headKw (tableUseT_mem htu x hx)) (notP_cons (wrapped_notId hox))

set_option maxHeartbeats 4000000 in
/-- Two readings of one module field agree. -/
theorem declT_agree {I : IdCtx} {x : SExp} {ds : List Decl} {J : IdCtx} {u : List FuncType}
    (h : DeclT I x ds J u) :
    ∀ {I' : IdCtx} {x' : SExp} {ds' : List Decl} {J' : IdCtx} {u' : List FuncType},
      DeclT I' x' ds' J' u' → x = x' → DeclAgree I I' ds J u ds' J' u' := by
  cases h with
  | type hr =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | type hr' =>
          subst hx
          have htypes := recTypeT_types hr hr'
          refine ⟨htypes, fun hE hT => ?_, fun hI hok => ?_⟩
          · rw [← recTypeT_eq hE] at hr'
            obtain ⟨rfl, rfl⟩ := recTypeT_functional hT hr hr'
            exact ⟨rfl, rfl⟩
          · subst hI
            obtain ⟨rfl, rfl⟩ := recTypeT_functional hok.1 hr hr'
            rfl
      | _ =>
          subst hx
          rcases recTypeT_head hr with ⟨ys, e⟩ | ⟨ys, e⟩ <;> simp [L, K, kw, listOf] at e
  | import_ ha hb hxt =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | import_ ha' hb' hxt' =>
          simp only [L_inj, List.cons.injEq, true_and, and_true] at hx
          obtain ⟨rfl, rfl, rfl⟩ :=
            (by simpa only [List.append_assoc] using hx)
          obtain rfl := name_functional ha ha'
          obtain rfl := name_functional hb hb'
          refine ⟨by rw [externTypeT_types hxt, externTypeT_types hxt'],
            fun hE hT => externTypeT_uses hT hE hxt hxt', fun hI hok => ?_⟩
          subst hI
          obtain ⟨rfl, -, -⟩ := externTypeT_functional hok.1 hxt hxt'
          rfl
      | _ => decl_kw_contra
  | tag hix hex ht =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | tag hix' hex' ht' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := ix_ex_split' hix hex hix' hex' (tagRest ht)
            (tagRest ht')
            (by simpa only [List.append_assoc] using hx)
          obtain ⟨ls, ht⟩ := ht; obtain ⟨ls', ht'⟩ := ht'
          refine DeclAgree.mk' rfl (fun hE hT => typeUseT_uses hT hE ht ht') (fun hI hok => ?_)
          subst hI
          obtain ⟨rfl, -, -⟩ := typeUseT_functional hok.1 ht ht'
          rfl
      | tagImport hix' hex' himp' ht' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (tagRest ht) (restOk_imp himp')
            (by simpa only [List.append_assoc] using hx)
          obtain ⟨ls, ht⟩ := ht
          exact (not_tu_import himp' (typeUseT_mem ht _ (by rw [e]; simp))).elim
      | _ => decl_kw_contra
  | tagImport hix hex himp ht =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | tag hix' hex' ht' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (restOk_imp himp) (tagRest ht')
            (by simpa only [List.append_assoc] using hx)
          obtain ⟨ls, ht'⟩ := ht'
          exact (not_tu_import himp (typeUseT_mem ht' _ (by rw [← e]; simp))).elim
      | tagImport hix' hex' himp' ht' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨rfl, rfl, rfl, rfl, e⟩ := ix_ex_split' hix hex hix' hex' (restOk_imp himp)
            (restOk_imp himp')
            (by simpa only [List.append_assoc] using hx)
          simp only [List.cons.injEq] at e; obtain ⟨rfl, rfl⟩ := e
          obtain ⟨rfl, rfl⟩ := inlineImportT_functional himp himp'
          obtain ⟨ls, ht⟩ := ht; obtain ⟨ls', ht'⟩ := ht'
          refine DeclAgree.mk' rfl (fun hE hT => typeUseT_uses hT hE ht ht') (fun hI hok => ?_)
          subst hI
          obtain ⟨rfl, -, -⟩ := typeUseT_functional hok.1 ht ht'
          rfl
      | _ => decl_kw_contra
  | global hix hex hg hbody =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | global hix' hex' hg' hbody' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨rfl, rfl, rfl, rfl, e⟩ := ix_ex_split' hix hex hix' hex'
            (restOk_cons (fieldOk_globalType hg)) (restOk_cons (fieldOk_globalType hg'))
            (by simpa only [List.append_assoc] using hx)
          simp only [List.cons.injEq] at e; obtain ⟨rfl, rfl⟩ := e
          refine DeclAgree.mk' rfl (fun hE hT => instrs_uses hT hE hbody hbody') (fun hI hok => ?_)
          subst hI
          rw [globalTypeT_functional hok.1 hg hg', (instrs_functional' hok hbody hbody').1]
      | globalImport hix' hex' himp' hg' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex'
            (restOk_cons (fieldOk_globalType hg)) (restOk_imp himp')
            (by simpa only [List.append_assoc] using hx)
          simp only [List.cons.injEq] at e; obtain ⟨rfl, -⟩ := e
          exfalso
          rcases globalTypeT_shape hg with h | h | ⟨s, e⟩
          · exact headKw_ne (by decide) h (inlineImportT_head himp')
          · exact headKw_ne (by decide) h (inlineImportT_head himp')
          · exact headKw_K (e ▸ inlineImportT_head himp')
      | _ => decl_kw_contra
  | globalImport hix hex himp hg =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | global hix' hex' hg' hbody' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex'
            (restOk_imp himp) (restOk_cons (fieldOk_globalType hg'))
            (by simpa only [List.append_assoc] using hx)
          simp only [List.cons.injEq] at e; obtain ⟨rfl, -⟩ := e
          exfalso
          rcases globalTypeT_shape hg' with h | h | ⟨s, e⟩
          · exact headKw_ne (by decide) h (inlineImportT_head himp)
          · exact headKw_ne (by decide) h (inlineImportT_head himp)
          · exact headKw_K (e ▸ inlineImportT_head himp)
      | globalImport hix' hex' himp' hg' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨rfl, rfl, rfl, rfl, e⟩ := ix_ex_split' hix hex hix' hex' (restOk_imp himp)
            (restOk_imp himp')
            (by simpa only [List.append_assoc] using hx)
          simp only [List.cons.injEq, and_true] at e; obtain ⟨rfl, rfl⟩ := e
          obtain ⟨rfl, rfl⟩ := inlineImportT_functional himp himp'
          refine DeclAgree.mk' rfl (fun _ _ => rfl) (fun hI hok => ?_)
          subst hI
          rw [globalTypeT_functional hok.1 hg hg']
      | _ => decl_kw_contra
  | mem hix hex hm =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | mem hix' hex' hm' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := ix_ex_split' hix hex hix' hex' (memRest hm)
            (memRest hm')
            (by simpa only [List.append_assoc] using hx)
          refine DeclAgree.mk' rfl (fun _ _ => rfl) (fun _ _ => ?_)
          rw [memTypeT_functional hm hm']
      | memImport hix' hex' himp' hm' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (memRest hm) (restOk_imp himp')
            (by simpa only [List.append_assoc] using hx)
          exfalso
          obtain ⟨s, hs⟩ := memTypeT_mem hm _ (by rw [e]; exact List.mem_cons_self)
          exact headKw_K (hs ▸ inlineImportT_head himp')
      | memData hix' hex' ha' hstr' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (memRest hm) (dataRest ha')
            (by simpa only [List.append_assoc] using hx)
          obtain ⟨s, hs⟩ := memTypeT_mem hm _
            (by rw [e]; exact List.mem_append_right _ (List.mem_singleton_self _))
          simp at hs
      | _ => decl_kw_contra
  | memImport hix hex himp hm =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | mem hix' hex' hm' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (restOk_imp himp) (memRest hm')
            (by simpa only [List.append_assoc] using hx)
          exfalso
          obtain ⟨s, hs⟩ := memTypeT_mem hm' _ (by rw [← e]; exact List.mem_cons_self)
          exact headKw_K (hs ▸ inlineImportT_head himp)
      | memImport hix' hex' himp' hm' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨rfl, rfl, rfl, rfl, e⟩ := ix_ex_split' hix hex hix' hex' (restOk_imp himp)
            (restOk_imp himp')
            (by simpa only [List.append_assoc] using hx)
          simp only [List.cons.injEq] at e; obtain ⟨rfl, rfl⟩ := e
          obtain ⟨rfl, rfl⟩ := inlineImportT_functional himp himp'
          refine DeclAgree.mk' rfl (fun _ _ => rfl) (fun _ _ => ?_)
          rw [memTypeT_functional hm hm']
      | memData hix' hex' ha' hstr' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (restOk_imp himp) (dataRest ha')
            (by simpa only [List.append_assoc] using hx)
          have hi := inlineImportT_head himp
          exfalso
          rcases ha' with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
            simp only [List.nil_append, List.cons_append, List.cons.injEq] at e <;>
            obtain ⟨rfl, -⟩ := e
          · exact headKw_ne (by decide) hi ⟨_, rfl⟩
          · exact headKw_K hi
          · exact headKw_K hi
      | _ => decl_kw_contra
  | memData hix hex ha hstr =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | mem hix' hex' hm' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (dataRest ha) (memRest hm')
            (by simpa only [List.append_assoc] using hx)
          obtain ⟨s, hs⟩ := memTypeT_mem hm' _ (by rw [← e]; exact List.mem_append_right _ (List.mem_singleton_self _))
          simp at hs
      | memImport hix' hex' himp' hm' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (dataRest ha) (restOk_imp himp')
            (by simpa only [List.append_assoc] using hx)
          have hi := inlineImportT_head himp'
          exfalso
          rcases ha with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
            simp only [List.nil_append, List.cons_append, List.cons.injEq] at e <;>
            obtain ⟨rfl, -⟩ := e
          · exact headKw_ne (by decide) hi ⟨_, rfl⟩
          · exact headKw_K hi
          · exact headKw_K hi
      | memData hix' hex' ha' hstr' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨rfl, rfl, rfl, rfl, e⟩ := ix_ex_split' hix hex hix' hex' (dataRest ha)
            (dataRest ha')
            (by simpa only [List.append_assoc] using hx)
          obtain ⟨rfl, e2⟩ := List.append_inj' e rfl
          simp only [List.cons.injEq, L_inj, true_and, and_true] at e2; subst e2
          refine DeclAgree.mk' rfl (fun _ _ => rfl) (fun _ _ => ?_)
          rw [addrTypeT_functional ha ha', dataStringT_functional hstr hstr']
      | _ => decl_kw_contra
  | table hix hex htt hne hbody =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | table hix' hex' htt' hne' hbody' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨rfl, rfl, rfl, rfl, e⟩ := ix_ex_split' hix hex hix' hex' (tableRest htt)
            (tableRest htt')
            (by simpa only [List.append_assoc] using hx)
          obtain ⟨rfl, rfl⟩ := tableType_split htt htt' e
          refine DeclAgree.mk' rfl (fun hE hT => instrs_uses hT hE hbody hbody') (fun hI hok => ?_)
          subst hI
          rw [tableTypeT_functional hok.1 htt htt', (instrs_functional' hok hbody hbody').1]
      | tableNull hix' hex' htt' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (tableRest htt)
            (by simpa using tableRest (r := []) htt')
            (by simpa only [List.append_assoc] using hx)
          obtain ⟨-, rfl⟩ := tableType_split (r' := []) htt htt' (by simpa using e)
          exact absurd rfl hne
      | tableImport hix' hex' himp' htt' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (tableRest htt) (restOk_imp himp')
            (by simpa only [List.append_assoc] using hx)
          exact (tableType_not_import htt himp' e).elim
      | tableElemFuncs hix' hex' ha' hr' _ _ =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (tableRest htt) (elemRest ha' hr')
            (by simpa only [List.append_assoc] using hx)
          exact (tableType_not_elem htt ha' hr' e).elim
      | tableElemExprs hix' hex' ha' hr' _ _ _ _ =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (tableRest htt) (elemRest ha' hr')
            (by simpa only [List.append_assoc] using hx)
          exact (tableType_not_elem htt ha' hr' e).elim
      | _ => decl_kw_contra
  | tableNull hix hex htt =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | table hix' hex' htt' hne' hbody' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex'
            (by simpa using tableRest (r := []) htt) (tableRest htt')
            (by simpa only [List.append_assoc] using hx)
          obtain ⟨-, e2⟩ := tableType_split (r := []) htt htt' (by simpa using e)
          exact absurd e2.symm hne'
      | tableNull hix' hex' htt' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := ix_ex_split' hix hex hix' hex'
            (by simpa using tableRest (r := []) htt) (by simpa using tableRest (r := []) htt')
            (by simpa only [List.append_assoc] using hx)
          refine DeclAgree.mk' rfl (fun _ _ => rfl) (fun hI hok => ?_)
          subst hI
          rw [tableTypeT_functional hok.1 htt htt']
      | tableImport hix' hex' himp' htt' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex'
            (by simpa using tableRest (r := []) htt) (restOk_imp himp')
            (by simpa only [List.append_assoc] using hx)
          exact (tableType_not_import (body := []) htt himp' (by simpa using e)).elim
      | tableElemFuncs hix' hex' ha' hr' _ _ =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex'
            (by simpa using tableRest (r := []) htt) (elemRest ha' hr')
            (by simpa only [List.append_assoc] using hx)
          exact (tableType_not_elem (body := []) htt ha' hr' (by simpa using e)).elim
      | tableElemExprs hix' hex' ha' hr' _ _ _ _ =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex'
            (by simpa using tableRest (r := []) htt) (elemRest ha' hr')
            (by simpa only [List.append_assoc] using hx)
          exact (tableType_not_elem (body := []) htt ha' hr' (by simpa using e)).elim
      | _ => decl_kw_contra
  | tableImport hix hex himp htt =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | table hix' hex' htt' _ _ =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (restOk_imp himp) (tableRest htt')
            (by simpa only [List.append_assoc] using hx)
          exact (tableType_not_import htt' himp e.symm).elim
      | tableNull hix' hex' htt' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (restOk_imp himp)
            (by simpa using tableRest (r := []) htt')
            (by simpa only [List.append_assoc] using hx)
          exact (tableType_not_import (body := []) htt' himp (by simpa using e.symm)).elim
      | tableImport hix' hex' himp' htt' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨rfl, rfl, rfl, rfl, e⟩ := ix_ex_split' hix hex hix' hex' (restOk_imp himp)
            (restOk_imp himp')
            (by simpa only [List.append_assoc] using hx)
          simp only [List.cons.injEq] at e; obtain ⟨rfl, rfl⟩ := e
          obtain ⟨rfl, rfl⟩ := inlineImportT_functional himp himp'
          refine DeclAgree.mk' rfl (fun _ _ => rfl) (fun hI hok => ?_)
          subst hI
          rw [tableTypeT_functional hok.1 htt htt']
      | tableElemFuncs hix' hex' ha' hr' _ _ =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (restOk_imp himp) (elemRest ha' hr')
            (by simpa only [List.append_assoc] using hx)
          exact (import_not_elem himp ha' hr' e).elim
      | tableElemExprs hix' hex' ha' hr' _ _ _ _ =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (restOk_imp himp) (elemRest ha' hr')
            (by simpa only [List.append_assoc] using hx)
          exact (import_not_elem himp ha' hr' e).elim
      | _ => decl_kw_contra
  | tableElemFuncs hix hex ha hr hfs hlen =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | table hix' hex' htt' _ _ =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (elemRest ha hr) (tableRest htt')
            (by simpa only [List.append_assoc] using hx)
          exact (tableType_not_elem htt' ha hr e.symm).elim
      | tableNull hix' hex' htt' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (elemRest ha hr)
            (by simpa using tableRest (r := []) htt') (by simpa only [List.append_assoc] using hx)
          exact (tableType_not_elem (body := []) htt' ha hr (by simpa using e.symm)).elim
      | tableImport hix' hex' himp' htt' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (elemRest ha hr) (restOk_imp himp')
            (by simpa only [List.append_assoc] using hx)
          exact (import_not_elem himp' ha hr e.symm).elim
      | tableElemFuncs hix' hex' ha' hr' hfs' _ =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨rfl, rfl, rfl, rfl, e⟩ := ix_ex_split' hix hex hix' hex' (elemRest ha hr)
            (elemRest ha' hr') (by simpa only [List.append_assoc] using hx)
          obtain ⟨rfl, e2⟩ := List.append_inj' e rfl
          simp only [List.cons.injEq, L_inj, true_and, and_true] at e2
          obtain ⟨rfl, rfl⟩ := e2
          refine DeclAgree.mk' rfl (fun _ _ => rfl) (fun hI hOk => ?_)
          subst hI
          rw [addrTypeT_functional ha ha', refTypeT_functional hOk.1 hr hr',
            forall₂_functional (R := Idx I.funcs)
              (fun _ _ _ h h' => idx_functional hOk.2.2.2.2.2.1 h h') hfs hfs']
      | tableElemExprs hix' hex' ha' hr' hne' hexs' _ _ =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨rfl, rfl, rfl, rfl, e⟩ := ix_ex_split' hix hex hix' hex' (elemRest ha hr)
            (elemRest ha' hr') (by simpa only [List.append_assoc] using hx)
          obtain ⟨rfl, e2⟩ := List.append_inj' e rfl
          simp only [List.cons.injEq, L_inj, true_and, and_true] at e2
          obtain ⟨-, rfl⟩ := e2
          exfalso
          obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne'
          obtain ⟨p, ps, hy, -, -⟩ := List.forall₂_cons_left_iff.mp hexs'
          obtain ⟨q, qs, hq, -, -⟩ := List.forall₂_cons_left_iff.mp hfs
          rcases idx_shape hq with h1 | h1
          · obtain ⟨s, zs, rfl, -⟩ := wrapped_isList hy; exact not_numTok_L h1
          · exact wrapped_notId hy h1
      | _ => decl_kw_contra
  | tableElemExprs hix hex ha hr hne hexs hl hlen =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | table hix' hex' htt' _ _ =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (elemRest ha hr) (tableRest htt')
            (by simpa only [List.append_assoc] using hx)
          exact (tableType_not_elem htt' ha hr e.symm).elim
      | tableNull hix' hex' htt' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (elemRest ha hr)
            (by simpa using tableRest (r := []) htt') (by simpa only [List.append_assoc] using hx)
          exact (tableType_not_elem (body := []) htt' ha hr (by simpa using e.symm)).elim
      | tableImport hix' hex' himp' htt' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (elemRest ha hr) (restOk_imp himp')
            (by simpa only [List.append_assoc] using hx)
          exact (import_not_elem himp' ha hr e.symm).elim
      | tableElemFuncs hix' hex' ha' hr' hfs' _ =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨rfl, rfl, rfl, rfl, e⟩ := ix_ex_split' hix hex hix' hex' (elemRest ha hr)
            (elemRest ha' hr') (by simpa only [List.append_assoc] using hx)
          obtain ⟨rfl, e2⟩ := List.append_inj' e rfl
          simp only [List.cons.injEq, L_inj, true_and, and_true] at e2
          obtain ⟨-, rfl⟩ := e2
          exfalso
          obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
          obtain ⟨p, ps, hy, -, -⟩ := List.forall₂_cons_left_iff.mp hexs
          obtain ⟨q, qs, hq, -, -⟩ := List.forall₂_cons_left_iff.mp hfs'
          rcases idx_shape hq with h1 | h1
          · obtain ⟨s, zs, rfl, -⟩ := wrapped_isList hy; exact not_numTok_L h1
          · exact wrapped_notId hy h1
      | tableElemExprs hix' hex' ha' hr' hne' hexs' hl' _ =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨rfl, rfl, rfl, rfl, e⟩ := ix_ex_split' hix hex hix' hex' (elemRest ha hr)
            (elemRest ha' hr') (by simpa only [List.append_assoc] using hx)
          obtain ⟨rfl, e2⟩ := List.append_inj' e rfl
          simp only [List.cons.injEq, L_inj, true_and, and_true] at e2
          obtain ⟨rfl, rfl⟩ := e2
          refine DeclAgree.mk' rfl (fun hE hT => by rw [(elemExprs_functional hT hE hexs hl hexs' hl').1])
            (fun hI hOk => ?_)
          subst hI
          rw [addrTypeT_functional ha ha', refTypeT_functional hOk.1 hr hr',
            (elemExprs_functional hOk.1 (TypesEq.refl _) hexs hl hexs' hl').2 rfl hOk]
      | _ => decl_kw_contra
  | func hix hex htu hlx hok hbody =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | func hix' hex' htu' hlx' hok' hbody' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨rfl, rfl, rfl, rfl, e⟩ := ix_ex_split' hix hex hix' hex' (funcRest htu hlx hbody)
            (funcRest htu' hlx' hbody') (by simpa only [List.append_assoc] using hx)
          have locMem : ∀ {K' : IdCtx} {lx : List SExp} {locs : List (ValType × Option String)},
              Concat (LocalT K') lx locs → ∀ x ∈ lx, HeadKw "local" x :=
            fun h => concat_mem (fun _ _ h => localT_head h) h
          obtain ⟨rfl, e1⟩ := munch (typeUseT_mem htu) (typeUseT_mem htu')
            (notP_append (fun x hx => notTU_headKw (by decide) (locMem hlx x hx))
              (notP_instrs_nil (fun _ h => isStart_not_tuList h) hbody))
            (notP_append (fun x hx => notTU_headKw (by decide) (locMem hlx' x hx))
              (notP_instrs_nil (fun _ h => isStart_not_tuList h) hbody')) e
          obtain ⟨rfl, rfl⟩ := munch (locMem hlx) (locMem hlx')
            (notP_instrs_nil (fun _ h => isStart_not_headKw (by decide) h) hbody)
            (notP_instrs_nil (fun _ h => isStart_not_headKw (by decide) h) hbody') e1
          refine DeclAgree.mk' rfl (fun hE hT => ?_) (fun hI hOk => ?_)
          · rw [typeUseT_uses hT hE htu htu',
              instrs_uses (distinct_append_types hT rfl) (typesEq_append hE rfl rfl) hbody hbody']
          · subst hI
            obtain ⟨rfl, rfl, -⟩ := typeUseT_functional hOk.1 htu htu'
            obtain rfl := concat_functional (R := LocalT I)
              (fun _ _ _ h h' => localT_functional hOk.1 h h') hlx hlx'
            rw [(instrs_functional' hok hbody hbody').1]
      | funcImport hix' hex' himp' htu' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (funcRest htu hlx hbody)
            (restOk_imp himp') (by simpa only [List.append_assoc] using hx)
          exfalso
          have hn : NotP (HeadKw "import") (_ ++ (_ ++ _)) :=
            notP_append (fun x hx h => by
                rcases typeUseT_mem htu x hx with h' | h' | h' <;> exact headKw_ne (by decide) h' h)
              (notP_append (fun x hx => headKw_ne (by decide)
                  (concat_mem (R := LocalT I) (fun _ _ h => localT_head h) hlx x hx))
                (notP_instrs_nil (fun _ h => isStart_not_headKw (by decide) h) hbody))
          rw [e] at hn
          exact hn _ rfl (inlineImportT_head himp')
      | _ => decl_kw_contra
  | funcImport hix hex himp htu =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | func hix' hex' htu' hlx' hok' hbody' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, -, -, e⟩ := ix_ex_split' hix hex hix' hex' (restOk_imp himp)
            (funcRest htu' hlx' hbody') (by simpa only [List.append_assoc] using hx)
          exfalso
          have hn : NotP (HeadKw "import") (_ ++ (_ ++ _)) :=
            notP_append (fun x hx h => by
                rcases typeUseT_mem htu' x hx with h' | h' | h' <;> exact headKw_ne (by decide) h' h)
              (notP_append (fun x hx => headKw_ne (by decide)
                  (concat_mem (R := LocalT I') (fun _ _ h => localT_head h) hlx' x hx))
                (notP_instrs_nil (fun _ h => isStart_not_headKw (by decide) h) hbody'))
          rw [← e] at hn
          exact hn _ rfl (inlineImportT_head himp)
      | funcImport hix' hex' himp' htu' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨rfl, rfl, rfl, rfl, e⟩ := ix_ex_split' hix hex hix' hex' (restOk_imp himp)
            (restOk_imp himp') (by simpa only [List.append_assoc] using hx)
          simp only [List.cons.injEq] at e; obtain ⟨rfl, rfl⟩ := e
          obtain ⟨rfl, rfl⟩ := inlineImportT_functional himp himp'
          refine DeclAgree.mk' rfl (fun hE hT => typeUseT_uses hT hE htu htu') (fun hI hOk => ?_)
          subst hI
          obtain ⟨rfl, -, -⟩ := typeUseT_functional hOk.1 htu htu'
          rfl
      | _ => decl_kw_contra
  | dataPassive hix hstr =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | dataPassive hix' hstr' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨rfl, rfl, rfl⟩ := idOpt_split' hix hix' (notId_strs hstr) (notId_strs hstr') hx
          refine DeclAgree.mk' rfl (fun _ _ => rfl) (fun _ _ => ?_)
          rw [dataStringT_functional hstr hstr']
      | dataActive hix' hmu' hox' hstr' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, e⟩ := idOpt_split' hix hix' (notId_strs hstr) (notId_memOff hmu' hox')
            (by simpa only [List.append_assoc] using hx)
          exfalso
          obtain ⟨s, ys, rfl, -⟩ := wrapped_isList hox'
          rcases hmu' with ⟨rfl, -⟩ | ⟨y, rfl, -⟩
          · obtain ⟨b, hb⟩ := dataStringT_mem hstr _ (by rw [e]; exact List.mem_cons_self)
            simp [L, listOf] at hb
          · obtain ⟨b, hb⟩ := dataStringT_mem hstr _ (by rw [e]; exact List.mem_cons_self)
            simp [L, listOf] at hb
      | _ => decl_kw_contra
  | dataActive hix hmu hox hstr =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | dataPassive hix' hstr' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, e⟩ := idOpt_split' hix hix' (notId_memOff hmu hox) (notId_strs hstr')
            (by simpa only [List.append_assoc] using hx)
          exfalso
          obtain ⟨s, ys, rfl, -⟩ := wrapped_isList hox
          rcases hmu with ⟨rfl, -⟩ | ⟨y, rfl, -⟩
          · obtain ⟨b, hb⟩ := dataStringT_mem hstr' _ (by rw [← e]; exact List.mem_cons_self)
            simp [L, listOf] at hb
          · obtain ⟨b, hb⟩ := dataStringT_mem hstr' _ (by rw [← e]; exact List.mem_cons_self)
            simp [L, listOf] at hb
      | dataActive hix' hmu' hox' hstr' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨rfl, rfl, e⟩ := idOpt_split' hix hix' (notId_memOff hmu hox) (notId_memOff hmu' hox')
            (by simpa only [List.append_assoc] using hx)
          obtain ⟨rfl, e1⟩ := munch (memUseT_mem hmu) (memUseT_mem hmu')
            (notP_cons (wrapped_not_headKw (s := "memory") (by decide) (by decide) hox))
            (notP_cons (wrapped_not_headKw (s := "memory") (by decide) (by decide) hox')) e
          simp only [List.cons.injEq] at e1; obtain ⟨rfl, rfl⟩ := e1
          refine DeclAgree.mk' rfl
            (fun hE hT => (wrapped_functional (kw := "offset") (by decide) hT hE hox hox').1)
            (fun hI hOk => ?_)
          subst hI
          rw [memUseT_functional hOk.2.2.2.1 hmu hmu',
            (wrapped_functional (kw := "offset") (by decide) hOk.1 (TypesEq.refl _) hox hox').2 rfl hOk,
            dataStringT_functional hstr hstr']
      | _ => decl_kw_contra
  | elemPassive hix hel =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | elemPassive hix' hel' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨rfl, rfl, rfl⟩ := idOpt_split' hix hix' (elemList_fieldOk hel)
            (elemList_fieldOk hel') hx
          refine DeclAgree.mk' rfl (fun hE hT => (elemListT_functional hT hE hel hel').1)
            (fun hI hOk => ?_)
          subst hI
          obtain ⟨rfl, rfl⟩ := (elemListT_functional hOk.1 (TypesEq.refl _) hel hel').2 rfl hOk
          rfl
      | elemActive hix' htu' hox' hel' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, e⟩ := idOpt_split' hix hix' (elemList_fieldOk hel) (notId_tabOff htu' hox')
            (by simpa only [List.append_assoc] using hx)
          exfalso
          rcases htu' with ⟨rfl, -⟩ | ⟨tx, rfl, -⟩
          · exact elemList_head_not_wrapped (kw := "offset") (by decide) (by decide) hel hox' e
          · obtain ⟨y, ys, rfl, hy⟩ := elemListT_cases hel
            simp only [List.singleton_append, List.cons.injEq] at e; obtain ⟨rfl, -⟩ := e
            rcases hy with ⟨r, hr⟩ | e1
            · rcases refTypeT_shape hr with h1 | ⟨s, e1, -⟩
              · exact headKw_ne (by decide) h1 ⟨_, rfl⟩
              · simp at e1
            · simp at e1
      | elemDeclare hix' hel' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, e⟩ := idOpt_split' hix hix' (elemList_fieldOk hel)
            (notP_cons not_idAtom_K) hx
          exfalso
          obtain ⟨y, ys, rfl, hy⟩ := elemListT_cases hel
          simp only [List.cons.injEq] at e; obtain ⟨rfl, -⟩ := e
          rcases hy with ⟨r, hr⟩ | e1
          · rcases refTypeT_shape hr with h1 | ⟨s, e1, hs⟩
            · exact headKw_K h1
            · simp only [K_inj] at e1; subst e1; exact absurd hs (by decide)
          · simp at e1
      | elemFuncs hix' hox' hfs' _ =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, e⟩ := idOpt_split' hix hix' (elemList_fieldOk hel)
            (notP_cons (wrapped_notId hox')) hx
          exact (elemList_head_not_wrapped (kw := "offset") (by decide) (by decide) hel hox' e).elim
      | _ => decl_kw_contra
  | elemActive hix htu hox hel =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | elemPassive hix' hel' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, e⟩ := idOpt_split' hix hix' (notId_tabOff htu hox) (elemList_fieldOk hel')
            (by simpa only [List.append_assoc] using hx)
          exfalso
          rcases htu with ⟨rfl, -⟩ | ⟨tx, rfl, -⟩
          · exact elemList_head_not_wrapped (kw := "offset") (by decide) (by decide) hel' hox e.symm
          · obtain ⟨y, ys, rfl, hy⟩ := elemListT_cases hel'
            simp only [List.singleton_append, List.cons.injEq] at e; obtain ⟨rfl, -⟩ := e
            rcases hy with ⟨r, hr⟩ | e1
            · rcases refTypeT_shape hr with h1 | ⟨s, e1, -⟩
              · exact headKw_ne (by decide) h1 ⟨_, rfl⟩
              · simp at e1
            · simp at e1
      | elemActive hix' htu' hox' hel' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨rfl, rfl, e⟩ := idOpt_split' hix hix' (notId_tabOff htu hox) (notId_tabOff htu' hox')
            (by simpa only [List.append_assoc] using hx)
          obtain ⟨rfl, e1⟩ := munch (tableUseT_mem htu) (tableUseT_mem htu')
            (notP_cons (wrapped_not_headKw (s := "table") (by decide) (by decide) hox))
            (notP_cons (wrapped_not_headKw (s := "table") (by decide) (by decide) hox')) e
          simp only [List.cons.injEq] at e1; obtain ⟨rfl, rfl⟩ := e1
          refine DeclAgree.mk' rfl (fun hE hT => by
              rw [(wrapped_functional (kw := "offset") (by decide) hT hE hox hox').1,
                (elemListT_functional hT hE hel hel').1])
            (fun hI hOk => ?_)
          subst hI
          obtain ⟨rfl, rfl⟩ := (elemListT_functional hOk.1 (TypesEq.refl _) hel hel').2 rfl hOk
          rw [tableUseT_functional hOk.2.2.2.2.1 htu htu',
            (wrapped_functional (kw := "offset") (by decide) hOk.1 (TypesEq.refl _) hox hox').2 rfl hOk]
      | elemDeclare hix' hel' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, e⟩ := idOpt_split' hix hix' (notId_tabOff htu hox) (notP_cons not_idAtom_K)
            (by simpa only [List.append_assoc] using hx)
          exfalso
          rcases htu with ⟨rfl, -⟩ | ⟨tx, rfl, -⟩
          · simp only [List.nil_append, List.cons.injEq] at e; obtain ⟨rfl, -⟩ := e
            obtain ⟨s, ys, e1, -⟩ := wrapped_isList hox; simp at e1
          · simp at e
      | elemFuncs hix' hox' hfs' _ =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, e⟩ := idOpt_split' hix hix' (notId_tabOff htu hox)
            (notP_cons (wrapped_notId hox')) (by simpa only [List.append_assoc] using hx)
          exfalso
          rcases htu with ⟨rfl, -⟩ | ⟨tx, rfl, -⟩
          · simp only [List.nil_append, List.cons.injEq] at e; obtain ⟨rfl, rfl⟩ := e
            exact elemList_not_idx hel hfs' rfl
          · simp only [List.singleton_append, List.cons.injEq] at e; obtain ⟨rfl, -⟩ := e
            exact wrapped_not_headKw (s := "table") (by decide) (by decide) hox' ⟨_, rfl⟩
      | _ => decl_kw_contra
  | elemDeclare hix hel =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | elemPassive hix' hel' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, e⟩ := idOpt_split' hix hix' (notP_cons not_idAtom_K)
            (elemList_fieldOk hel') hx
          exfalso
          obtain ⟨y, ys, rfl, hy⟩ := elemListT_cases hel'
          simp only [List.cons.injEq] at e; obtain ⟨rfl, -⟩ := e
          rcases hy with ⟨r, hr⟩ | e1
          · rcases refTypeT_shape hr with h1 | ⟨s, e1, hs⟩
            · exact headKw_K h1
            · simp only [K_inj] at e1; subst e1; exact absurd hs (by decide)
          · simp at e1
      | elemActive hix' htu' hox' hel' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, e⟩ := idOpt_split' hix hix' (notP_cons not_idAtom_K) (notId_tabOff htu' hox')
            (by simpa only [List.append_assoc] using hx)
          exfalso
          rcases htu' with ⟨rfl, -⟩ | ⟨tx, rfl, -⟩
          · simp only [List.nil_append, List.cons.injEq] at e; obtain ⟨rfl, -⟩ := e
            obtain ⟨s, ys, e1, -⟩ := wrapped_isList hox'; simp at e1
          · simp at e
      | elemDeclare hix' hel' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨rfl, rfl, e⟩ := idOpt_split' hix hix' (notP_cons not_idAtom_K)
            (notP_cons not_idAtom_K) hx
          simp only [List.cons.injEq, true_and] at e; subst e
          refine DeclAgree.mk' rfl (fun hE hT => (elemListT_functional hT hE hel hel').1)
            (fun hI hOk => ?_)
          subst hI
          obtain ⟨rfl, rfl⟩ := (elemListT_functional hOk.1 (TypesEq.refl _) hel hel').2 rfl hOk
          rfl
      | elemFuncs hix' hox' hfs' _ =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, e⟩ := idOpt_split' hix hix' (notP_cons not_idAtom_K)
            (notP_cons (wrapped_notId hox')) hx
          exfalso
          simp only [List.cons.injEq] at e; obtain ⟨rfl, -⟩ := e
          obtain ⟨s, ys, e1, -⟩ := wrapped_isList hox'; simp at e1
      | _ => decl_kw_contra
  | elemFuncs hix hox hfs hlen =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | elemPassive hix' hel' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, e⟩ := idOpt_split' hix hix' (notP_cons (wrapped_notId hox))
            (elemList_fieldOk hel') hx
          exact (elemList_head_not_wrapped (kw := "offset") (by decide) (by decide) hel' hox e.symm).elim
      | elemActive hix' htu' hox' hel' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, e⟩ := idOpt_split' hix hix' (notP_cons (wrapped_notId hox))
            (notId_tabOff htu' hox') (by simpa only [List.append_assoc] using hx)
          exfalso
          rcases htu' with ⟨rfl, -⟩ | ⟨tx, rfl, -⟩
          · simp only [List.nil_append, List.cons.injEq] at e; obtain ⟨rfl, rfl⟩ := e
            exact elemList_not_idx hel' hfs rfl
          · simp only [List.singleton_append, List.cons.injEq] at e; obtain ⟨rfl, -⟩ := e
            exact wrapped_not_headKw (s := "table") (by decide) (by decide) hox ⟨_, rfl⟩
      | elemDeclare hix' hel' =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨-, -, e⟩ := idOpt_split' hix hix' (notP_cons (wrapped_notId hox))
            (notP_cons not_idAtom_K) hx
          exfalso
          simp only [List.cons.injEq] at e; obtain ⟨rfl, -⟩ := e
          obtain ⟨s, ys, e1, -⟩ := wrapped_isList hox; simp at e1
      | elemFuncs hix' hox' hfs' _ =>
          simp only [L_inj, List.cons.injEq, true_and] at hx
          obtain ⟨rfl, rfl, e⟩ := idOpt_split' hix hix' (notP_cons (wrapped_notId hox))
            (notP_cons (wrapped_notId hox')) hx
          simp only [List.cons.injEq] at e; obtain ⟨rfl, rfl⟩ := e
          refine DeclAgree.mk' rfl
            (fun hE hT => (wrapped_functional (kw := "offset") (by decide) hT hE hox hox').1)
            (fun hI hOk => ?_)
          subst hI
          rw [(wrapped_functional (kw := "offset") (by decide) hOk.1 (TypesEq.refl _) hox hox').2 rfl hOk,
            forall₂_functional (R := Idx I.funcs)
              (fun _ _ _ h h' => idx_functional hOk.2.2.2.2.2.1 h h') hfs hfs']
      | _ => decl_kw_contra
  | start hf =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | start hf' =>
          simp only [L_inj, List.cons.injEq, true_and, and_true] at hx; subst hx
          refine DeclAgree.mk' rfl (fun _ _ => rfl) (fun hI hOk => ?_)
          subst hI
          rw [idx_functional hOk.2.2.2.2.2.1 hf hf']
      | _ => decl_kw_contra
  | export_ hn hxi =>
      intro I' x' ds' J' u' h' hx
      cases h' with
      | export_ hn' hxi' =>
          simp only [L_inj, List.cons.injEq, true_and, and_true] at hx
          obtain ⟨rfl, rfl⟩ := hx
          refine DeclAgree.mk' rfl (fun _ _ => rfl) (fun hI hOk => ?_)
          subst hI
          rw [name_functional hn hn', externIdxT_functional hOk hxi hxi']
      | _ => decl_kw_contra

/-! ### Whole modules -/

def fieldKws : List String :=
  ["type", "rec", "import", "tag", "global", "memory", "table", "func", "data", "elem", "start",
    "export"]

theorem declT_head {I : IdCtx} {x : SExp} {ds : List Decl} {J : IdCtx} {u : List FuncType}
    (h : DeclT I x ds J u) : ∃ s ys, x = L (K s :: ys) ∧ s ∈ fieldKws := by
  cases h with
  | type hr =>
      rcases recTypeT_head hr with ⟨ys, rfl⟩ | ⟨ys, rfl⟩
      · exact ⟨_, _, rfl, by decide⟩
      · exact ⟨_, _, rfl, by decide⟩
  | _ => exact ⟨_, _, rfl, by decide⟩

theorem fields_notId {I : IdCtx} {fields : List SExp} {outs : List FieldOut}
    (h : List.Forall₂ (fun f (o : FieldOut) => DeclT I f o.1 o.2.1 o.2.2) fields outs) :
    NotP IdAtom fields := by
  cases h with
  | nil => exact notP_nil
  | cons hf _ =>
      obtain ⟨s, ys, rfl, -⟩ := declT_head hf
      exact notP_cons not_idAtom_L

theorem concat_types (Js : List IdCtx) :
    (IdCtx.concat Js).types = (Js.map IdCtx.types).flatten := by
  induction Js with
  | nil => rfl
  | cons J Js ih =>
      change J.types ++ (IdCtx.concat Js).types = _
      rw [ih]; rfl

theorem append_implicit_types (J : IdCtx) (imp : List FuncType) :
    (J ++ implicitCtx imp).types = J.types ++ imp.map (fun _ => none) := rfl

theorem idxIn_pad {A : List (Option String)} {k k' : List FuncType} {x : SExp} {i : Nat} :
    IdxIn (A ++ k.map (fun _ => none)) x i ↔ IdxIn (A ++ k'.map (fun _ => none)) x i := by
  have key : ∀ {k k' : List FuncType} {n : String},
      (A ++ k.map (fun _ => none))[i]? = some (some n) →
      (A ++ k'.map (fun _ => none))[i]? = some (some n) := by
    intro k k' n h
    rcases Nat.lt_or_ge i A.length with hi | hi
    · rw [List.getElem?_append_left hi] at h ⊢; exact h
    · rw [List.getElem?_append_right hi] at h
      simp only [List.getElem?_map] at h
      cases e : k[i - A.length]? <;> simp [e] at h
  unfold IdxIn
  constructor
  · rintro (h | ⟨n, rfl, h⟩)
    · exact .inl h
    · exact .inr ⟨n, rfl, key h⟩
  · rintro (h | ⟨n, rfl, h⟩)
    · exact .inl h
    · exact .inr ⟨n, rfl, key h⟩

theorem module_fields {x : SExp} {fields fields' : List SExp} {outs outs' : List FieldOut}
    {I I' : IdCtx}
    (hF : List.Forall₂ (fun f (o : FieldOut) => DeclT I f o.1 o.2.1 o.2.2) fields outs)
    (hF' : List.Forall₂ (fun f (o : FieldOut) => DeclT I' f o.1 o.2.1 o.2.2) fields' outs')
    (h : (∃ ix id, x = doc [L (K "module" :: (ix ++ fields))] ∧ IdOpt ix id) ∨ x = doc fields)
    (h' : (∃ ix id, x = doc [L (K "module" :: (ix ++ fields'))] ∧ IdOpt ix id) ∨ x = doc fields') :
    fields = fields' := by
  have noModule : ∀ {K' : IdCtx} {fs : List SExp} {os : List FieldOut} {ys : List SExp},
      List.Forall₂ (fun f (o : FieldOut) => DeclT K' f o.1 o.2.1 o.2.2) fs os →
      fs = [L (K "module" :: ys)] → False := by
    intro K' fs os ys hF e
    subst e
    cases hF with
    | cons hf _ =>
        obtain ⟨s, zs, e, hs⟩ := declT_head hf
        simp only [L_inj, List.cons.injEq, K_inj] at e
        obtain ⟨rfl, -⟩ := e
        exact absurd hs (by decide)
  rcases h with ⟨ix, id, rfl, hix⟩ | rfl <;> rcases h' with ⟨ix', id', e, hix'⟩ | e
  · simp only [L_inj, List.cons.injEq, and_true, true_and] at e
    exact (idOpt_split' hix hix' (fields_notId hF) (fields_notId hF') e).2.2
  · simp only [L_inj] at e
    exact (noModule hF' e.symm).elim
  · simp only [L_inj] at e
    exact (noModule hF e).elim
  · simpa using e

/-! ## Functionality

Identifiers are erased by the reading (`Encodes` relates texts to *resolved*
modules, whose indices are numbers), so the relation is many-to-one
(`encodes_not_deterministic`).  What *is* functional is: the resolved module is
determined by the text.  This holds for a fixed identifier context at every
level (`plain_functional`, `instrs_functional`, `declT_functional`) and, for
whole modules, because the module's context is itself determined by its fields
(`watSyntax_functional`).  Without fixing the context, the same items denote
different instructions (`plain_context_dependent`). -/

/-- For a fixed context, a plain instruction is determined by its items. -/
theorem plain_functional {I : IdCtx} (hI : I.Ok) {xs : List SExp} {i i' : Instr}
    {u u' : List FuncType} (h : Plain I xs i u) (h' : Plain I xs i' u') : i = i' ∧ u = u' :=
  plain_functional' hI h h' rfl

/-- For a fixed context, an instruction sequence is determined by its items. -/
theorem instrs_functional {I : IdCtx} (hI : I.Ok) {xs : List SExp} {e e' : Expr}
    {u u' : List FuncType} (h : Instrs I xs e u) (h' : Instrs I xs e' u') : e = e' ∧ u = u' :=
  instrs_functional' hI h h'

/-- For a fixed context, a module field is determined by its items. -/
theorem declT_functional {I : IdCtx} (hI : I.Ok) {x : SExp} {ds ds' : List Decl}
    {J J' : IdCtx} {u u' : List FuncType} (h : DeclT I x ds J u) (h' : DeclT I x ds' J' u') :
    ds = ds' ∧ J = J' ∧ u = u' := by
  obtain ⟨-, hJu, hds⟩ := declT_agree h h' rfl
  obtain ⟨hJ, hu⟩ := hJu (TypesEq.refl I) hI.1
  exact ⟨hds rfl hI, hJ, hu⟩

/-- The same items read in different contexts can denote different
instructions: `call $f`. -/
theorem plain_context_dependent :
    ∃ (I I' : IdCtx) (xs : List SExp) (i i' : Instr) (u u' : List FuncType),
      Plain I xs i u ∧ Plain I' xs i' u' ∧ i ≠ i' := by
  refine ⟨{ funcs := [some "f"] }, { funcs := [none, some "f"] },
    [K "call", .atom (.id "f")], .call ⟨0⟩, .call ⟨1⟩, [], [],
    .call (.inr ⟨"f", rfl, rfl⟩), .call (.inr ⟨"f", rfl, rfl⟩), ?_⟩
  intro h
  simp only [Instr.call.injEq, Wasm.Idx.mk.injEq] at h
  exact absurd h (by decide)

/-- **The resolved module is determined by the S-expression document.** -/
theorem watSyntax_functional : watSyntax.Functional := by
  intro x m m' h h'
  obtain ⟨fields, outs, I, hform, hF, hI, hOk, -, -, rfl⟩ := h
  obtain ⟨fields', outs', I', hform', hF', hI', hOk', -, -, rfl⟩ := h'
  obtain rfl := module_fields hF hF' hform hform'
  -- the type names of the two contexts agree
  have htypes : (IdCtx.concat (outs.map (·.2.1))).types =
      (IdCtx.concat (outs'.map (·.2.1))).types := by
    rw [concat_types, concat_types, List.map_map, List.map_map]
    congr 1
    exact forall₂_map_eq (R := fun f (o : FieldOut) => DeclT I f o.1 o.2.1 o.2.2)
      (R' := fun f (o : FieldOut) => DeclT I' f o.1 o.2.1 o.2.2)
      (f := fun o : FieldOut => o.2.1.types) (g := fun o : FieldOut => o.2.1.types)
      (fun _ _ _ h h' => (declT_agree h h' rfl).1) hF hF'
  have hE : TypesEq I I' := by
    intro y i
    rw [hI, hI', append_implicit_types, append_implicit_types, htypes]
    exact idxIn_pad
  have hT : Distinct I.types := hOk.1
  -- hence the contributed contexts and implicitly used types agree
  have hJu : outs.map (·.2) = outs'.map (·.2) :=
    forall₂_map_eq (R := fun f (o : FieldOut) => DeclT I f o.1 o.2.1 o.2.2)
      (R' := fun f (o : FieldOut) => DeclT I' f o.1 o.2.1 o.2.2)
      (f := fun o : FieldOut => o.2) (g := fun o : FieldOut => o.2)
      (fun _ _ _ h h' => by
        obtain ⟨hJ, hu⟩ := (declT_agree h h' rfl).2.1 hE hT
        exact Prod.ext hJ hu) hF hF'
  have hJ : outs.map (·.2.1) = outs'.map (·.2.1) := by
    have := congrArg (List.map Prod.fst) hJu
    simpa only [List.map_map, Function.comp_def] using this
  have hU : outs.flatMap (·.2.2) = outs'.flatMap (·.2.2) := by
    have := congrArg (List.map Prod.snd) hJu
    simp only [List.map_map, Function.comp_def] at this
    rw [List.flatMap_def, List.flatMap_def]
    exact congrArg List.flatten this
  have hII : I = I' := by rw [hI, hI', hJ, hU]
  subst hII
  -- with one context, the fields read the same declarations
  have houts : outs = outs' := by
    refine forall₂_functional (fun f o o' h h' => ?_) hF hF'
    obtain ⟨-, hJu, hds⟩ := declT_agree h h' rfl
    obtain ⟨hJ, hu⟩ := hJu (TypesEq.refl I) hT
    exact Prod.ext (hds rfl hOk) (Prod.ext hJ hu)
  subst houts
  rfl

/-- **The resolved module is determined by the text.** -/
theorem encodes_functional : Encodes.Functional :=
  (Formats.SExpEncoding.Wat.sexpWat_functional _).comp watSyntax_functional

theorem encodesBytes_functional : EncodesBytes.Functional :=
  Unicode.functional_push_utf8 encodes_functional

/-- The S-expression of the empty module reads as the empty module. -/
theorem watSyntax_empty : watSyntax (doc [L [K "module"]]) {} := by
  refine ⟨[], [], IdCtx.concat [] ++ implicitCtx [], .inl ⟨[], none, rfl, .inl ⟨rfl, rfl⟩⟩,
    .nil, ?_⟩
  refine ⟨rfl, ?_, ?_, ?_, rfl⟩
  · refine ⟨List.nodup_nil, List.nodup_nil, List.nodup_nil, List.nodup_nil, List.nodup_nil,
      List.nodup_nil, List.nodup_nil, List.nodup_nil, List.nodup_nil, List.nodup_nil, ?_⟩
    intro f hf; exact (List.not_mem_nil hf).elim
  · intro i j hi; simp at hi
  · simp [startCount]

/-- `(module )`: the empty module with a space. -/
theorem sexpWat3_module_space : Formats.SExpEncoding.Wat.sexpWat3 "(module )"
    (doc [listOf [kw "module"]]) := by
  have hm : ∀ c ∈ ['m', 'o', 'd', 'u', 'l', 'e'], Formats.SExpEncoding.Wat.IsIdChar c := by decide
  have hid : Formats.SExpEncoding.Wat.IdRun ['m', 'o', 'd', 'u', 'l', 'e'] (.sym "module") :=
    Formats.SExpEncoding.Wat.IdRun.sym (cs := ['m', 'o', 'd', 'u', 'l', 'e']) (by simp) hm (by simp)
  have hlex : Formats.SExpEncoding.Wat.Lex .core3 true ['(', 'm', 'o', 'd', 'u', 'l', 'e', ' ', ')']
      [.lp, .atom (.sym "module"), .rp] := by
    refine Formats.SExpEncoding.Wat.Lex.step (s := []) (c := ['('])
      (rest := ['m', 'o', 'd', 'u', 'l', 'e', ' ', ')']) Formats.SExpEncoding.Wat.Space.nil rfl ?_ ?_
    · simp [Formats.SExpEncoding.Wat.Follow]
    refine Formats.SExpEncoding.Wat.Lex.step (s := []) (c := ['m', 'o', 'd', 'u', 'l', 'e'])
      (rest := [' ', ')']) Formats.SExpEncoding.Wat.Space.nil ⟨.idRun hid, by decide⟩ ?_ ?_
    · simp [Formats.SExpEncoding.Wat.Follow]; decide
    have hsp : Formats.SExpEncoding.Wat.Space .core3 [' '] :=
      Formats.SExpEncoding.Wat.Space.cons (a := [' ']) (b := [])
        (Formats.SExpEncoding.Wat.SpaceItem.char (by simp [Formats.SExpEncoding.Wat.IsSpaceChar]))
        Formats.SExpEncoding.Wat.Space.nil
    exact Formats.SExpEncoding.Wat.Lex.step (s := [' ']) (c := [')']) (rest := []) hsp rfl trivial
      (Formats.SExpEncoding.Wat.Lex.done Formats.SExpEncoding.Wat.Space.nil)
  refine ⟨[.lp, .atom (.sym "module"), .rp], hlex, [listOf [kw "module"]], ?_, rfl⟩
  have ht : Formats.SExpEncoding.Wat.Tree [.lp, .atom (.sym "module"), .rp] (listOf [kw "module"]) :=
    Formats.SExpEncoding.Wat.Tree.list (ts := [.atom (.sym "module")])
      (Formats.SExpEncoding.Wat.Trees.cons (a := [_]) (b := []) (Formats.SExpEncoding.Wat.Tree.atom _)
        Formats.SExpEncoding.Wat.Trees.nil)
  exact Formats.SExpEncoding.Wat.Trees.cons (b := []) ht Formats.SExpEncoding.Wat.Trees.nil

/-- Identifiers (and abbreviations, whitespace, …) are erased: `(module)` and
`(module )` denote the same module. -/
theorem encodes_not_deterministic : ¬ Encodes.Deterministic := by
  intro hD
  have h1 : Encodes "(module)" {} :=
    ⟨_, Formats.SExpEncoding.Wat.sexpWat_module .core3, watSyntax_empty⟩
  have h2 : Encodes "(module )" {} := ⟨_, sexpWat3_module_space, watSyntax_empty⟩
  exact absurd (hD h1 h2) (by decide)

/-- The empty module. -/
theorem encodes_empty : Encodes "(module)" {} :=
  ⟨_, Formats.SExpEncoding.Wat.sexpWat_module .core3, watSyntax_empty⟩

end Silmaril.Wasm.Text.Core

namespace Silmaril.Wasm.Wat

/-- **Core 3.0 WAT text** (`String` carrier), `sexpWat3 ⨾ watSyntax`. -/
abbrev Encodes : EncRel String Wasm.Module := Text.Core.Encodes

/-- Core 3.0 WAT text as UTF-8 bytes. -/
abbrev EncodesBytes : EncRel (List UInt8) Wasm.Module := Text.Core.EncodesBytes

end Silmaril.Wasm.Wat
