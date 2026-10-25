module

public import Silmaril.Wasm.Text.Values

/-!
# Core 3.0 text format: identifier contexts and types

Transcribes SpecTec `6.1-text.values` (identifier contexts, `Idctxt_ok`) and
`6.2-text.types`.  Every grammar `Tx_(I)` becomes a relation indexed by the
identifier context `I : IdCtx`, between the S-expression items it spans and
the abstract syntax it denotes (plus, where the grammar returns one, the
identifier context it contributes).

Productions spanning several items of a list (`Tlimits`, `Ttypeuse`, `Tid?`, …)
relate item *lists*; single-node productions relate one `SExp`.  Abbreviations
(`Tx/abbrev`) are additional constructors producing the same abstract syntax
as their expansion.

Type uses (`Ttypeuse_`) also return the list of function types used through
the `param*/result*` abbreviation (`uses`); the module grammar uses it to
insert the implicit type definitions that SpecTec leaves informal (TODO(5) in
`6.2-text.types.spectec`).
-/

@[expose] public section

namespace Silmaril.Wasm.Text.Core

open Silmaril Silmaril.Formats.SExpEncoding Silmaril.Wasm

/-! ## Identifier contexts (`idctxt`) -/

/-- `idctxt`: the names bound in each index space, field names per type, and
the type definitions (`_DEF rectype i`). -/
structure IdCtx where
  types : List (Option String) := []
  tags : List (Option String) := []
  globals : List (Option String) := []
  mems : List (Option String) := []
  tables : List (Option String) := []
  funcs : List (Option String) := []
  datas : List (Option String) := []
  elems : List (Option String) := []
  locals : List (Option String) := []
  labels : List (Option String) := []
  fields : List (List (Option String)) := []
  typedefs : List (Option (RecType × Nat)) := []

namespace IdCtx

/-- Composition of identifier contexts (`I ++ I'`), space by space. -/
def append (I J : IdCtx) : IdCtx where
  types := I.types ++ J.types
  tags := I.tags ++ J.tags
  globals := I.globals ++ J.globals
  mems := I.mems ++ J.mems
  tables := I.tables ++ J.tables
  funcs := I.funcs ++ J.funcs
  datas := I.datas ++ J.datas
  elems := I.elems ++ J.elems
  locals := I.locals ++ J.locals
  labels := I.labels ++ J.labels
  fields := I.fields ++ J.fields
  typedefs := I.typedefs ++ J.typedefs

instance : Append IdCtx := ⟨append⟩

/-- `$concat_idctxt`. -/
def concat (Is : List IdCtx) : IdCtx := Is.foldr (· ++ ·) {}

/-- `Idctxt_ok`: names are distinct within each index space and each type's
fields. -/
def Ok (I : IdCtx) : Prop :=
  Distinct I.types ∧ Distinct I.tags ∧ Distinct I.globals ∧ Distinct I.mems ∧
    Distinct I.tables ∧ Distinct I.funcs ∧ Distinct I.datas ∧ Distinct I.elems ∧
    Distinct I.locals ∧ Distinct I.labels ∧ ∀ f ∈ I.fields, Distinct f

end IdCtx

/-! ## Value types -/

/-- `Tnumtype`. -/
def numTypeKw : String → Option NumType
  | "i32" => some (.int .i32)
  | "i64" => some (.int .i64)
  | "f32" => some (.float .f32)
  | "f64" => some (.float .f64)
  | _ => none

/-- `Tabsheaptype`. -/
def absHeapKw : String → Option AbsHeapType
  | "any" => some .any
  | "eq" => some .eq
  | "i31" => some .i31
  | "struct" => some .struct
  | "array" => some .array
  | "none" => some .none
  | "func" => some .func
  | "nofunc" => some .nofunc
  | "exn" => some .exn
  | "noexn" => some .noexn
  | "extern" => some .extern
  | "noextern" => some .noextern
  | _ => none

/-- `Treftype_/abbrev`: `anyref` ≡ `(ref null any)`, … -/
def refAbbrevKw : String → Option AbsHeapType
  | "anyref" => some .any
  | "eqref" => some .eq
  | "i31ref" => some .i31
  | "structref" => some .struct
  | "arrayref" => some .array
  | "nullref" => some .none
  | "funcref" => some .func
  | "nullfuncref" => some .nofunc
  | "exnref" => some .exn
  | "nullexnref" => some .noexn
  | "externref" => some .extern
  | "nullexternref" => some .noextern
  | _ => none

/-- `Theaptype_(I)`. -/
def HeapTypeT (I : IdCtx) (x : SExp) (h : HeapType) : Prop :=
  (∃ s a, x = K s ∧ absHeapKw s = some a ∧ h = .abstract a) ∨
    ∃ i, Idx I.types x i ∧ h = .typeIdx i

/-- `Treftype_(I)`. -/
def RefTypeT (I : IdCtx) (x : SExp) (r : RefType) : Prop :=
  (∃ ht h, x = L [K "ref", ht] ∧ HeapTypeT I ht h ∧ r = ⟨false, h⟩) ∨
    (∃ ht h, x = L [K "ref", K "null", ht] ∧ HeapTypeT I ht h ∧ r = ⟨true, h⟩) ∨
    ∃ s a, x = K s ∧ refAbbrevKw s = some a ∧ r = ⟨true, .abstract a⟩

/-- `Tvaltype_(I)`. -/
def ValTypeT (I : IdCtx) (x : SExp) (t : ValType) : Prop :=
  (∃ s n, x = K s ∧ numTypeKw s = some n ∧ t = .num n) ∨ (x = K "v128" ∧ t = .vec .v128) ∨
    ∃ r, RefTypeT I x r ∧ t = .ref r

/-! ## Type definitions -/

/-- `Tstoragetype_(I)`. -/
def StorageTypeT (I : IdCtx) (x : SExp) (z : StorageType) : Prop :=
  (∃ t, ValTypeT I x t ∧ z = .val t) ∨ (x = K "i8" ∧ z = .packed .i8) ∨
    (x = K "i16" ∧ z = .packed .i16)

/-- `Tfieldtype_(I)`. -/
def FieldTypeT (I : IdCtx) (x : SExp) (f : FieldType) : Prop :=
  (∃ z, StorageTypeT I x z ∧ f = ⟨.const, z⟩) ∨
    ∃ zx z, x = L [K "mut", zx] ∧ StorageTypeT I zx z ∧ f = ⟨.var, z⟩

/-- `Tfield_(I)` (base and abbreviation): one item, several named fields. -/
def FieldT (I : IdCtx) (x : SExp) (fs : List (FieldType × Option String)) : Prop :=
  (∃ n fx f, x = L [K "field", .atom (.id n), fx] ∧ FieldTypeT I fx f ∧ fs = [(f, some n)]) ∨
    ∃ fxs ts, x = L (K "field" :: fxs) ∧ List.Forall₂ (FieldTypeT I) fxs ts ∧
      fs = ts.map (·, none)

/-- `Tparam_(I)` (base and abbreviation). -/
def ParamT (I : IdCtx) (x : SExp) (ps : List (ValType × Option String)) : Prop :=
  (∃ n tx t, x = L [K "param", .atom (.id n), tx] ∧ ValTypeT I tx t ∧ ps = [(t, some n)]) ∨
    ∃ txs ts, x = L (K "param" :: txs) ∧ List.Forall₂ (ValTypeT I) txs ts ∧
      ps = ts.map (·, none)

/-- `Tresult_(I)` (base and abbreviation). -/
def ResultT (I : IdCtx) (x : SExp) (ts : List ValType) : Prop :=
  ∃ txs, x = L (K "result" :: txs) ∧ List.Forall₂ (ValTypeT I) txs ts

/-- A sequence of items, each spelling a list, concatenated (`Tlist(TX)` for
productions with abbreviations yielding several elements). -/
def Concat {α : Type} (R : SExp → List α → Prop) (xs : List SExp) (as : List α) : Prop :=
  ∃ ass, List.Forall₂ R xs ass ∧ as = ass.flatten ∧ as.length < 2 ^ 32

/-- The empty concatenation. -/
theorem Concat.nil' {α : Type} {R : SExp → List α → Prop} : Concat R [] [] :=
  ⟨[], .nil, rfl, Nat.two_pow_pos 32⟩

/-- `Tcomptype_(I)`, with the field names it binds. -/
def CompTypeT (I : IdCtx) (x : SExp) (ct : CompositeType) (names : List (Option String)) :
    Prop :=
  (∃ fxs fs, x = L (K "struct" :: fxs) ∧ Concat (FieldT I) fxs fs ∧
      ct = .struct (fs.map Prod.fst) ∧ names = fs.map Prod.snd) ∨
    (∃ fx f, x = L [K "array", fx] ∧ FieldTypeT I fx f ∧ ct = .array f ∧ names = []) ∨
    ∃ pxs rxs ps rs, x = L (K "func" :: (pxs ++ rxs)) ∧ Concat (ParamT I) pxs ps ∧
      Concat (ResultT I) rxs rs ∧ ct = .func ⟨ps.map Prod.fst, rs⟩ ∧ names = []

/-- `Tsubtype_(I)` (base and the abbreviation `ct ≡ (sub final ct)`). -/
def SubTypeT (I : IdCtx) (x : SExp) (st : SubType) (names : List (Option String)) : Prop :=
  (∃ fin xs cx is ct, x = L (K "sub" :: (fin ++ xs ++ [cx])) ∧
      (fin = [] ∨ fin = [K "final"]) ∧ List.Forall₂ (Idx I.types) xs is ∧
      is.length < 2 ^ 32 ∧ CompTypeT I cx ct names ∧ st = ⟨fin ≠ [], is, ct⟩) ∨
    ∃ ct, CompTypeT I x ct names ∧ st = ⟨true, [], ct⟩

/-- `Ttypedef_(I)`: a subtype, the type name and the field names. -/
def TypeDefT (I : IdCtx) (x : SExp) (st : SubType) (id : Option String)
    (names : List (Option String)) : Prop :=
  ∃ ix sx, x = L (K "type" :: (ix ++ [sx])) ∧ IdOpt ix id ∧ SubTypeT I sx st names

/-- The identifier context contributed by a recursive type at type index `base`… is
determined by its definitions: `{TYPES id?*, FIELDS names*}`. -/
def recCtx (defs : List (SubType × Option String × List (Option String))) : IdCtx :=
  { types := defs.map (·.2.1), fields := defs.map (·.2.2) }

/-- `Trectype_(I)` (base and the abbreviation `typedef ≡ (rec typedef)`). -/
def RecTypeT (I : IdCtx) (x : SExp) (rt : RecType) (J : IdCtx) : Prop :=
  (∃ dxs defs, x = L (K "rec" :: dxs) ∧
      List.Forall₂ (fun dx (d : SubType × Option String × List (Option String)) =>
        TypeDefT I dx d.1 d.2.1 d.2.2) dxs defs ∧ defs.length < 2 ^ 32 ∧
      rt = ⟨defs.map Prod.fst⟩ ∧ J = recCtx defs) ∨
    ∃ st id names, TypeDefT I x st id names ∧ rt = ⟨[st]⟩ ∧ J = recCtx [(st, id, names)]

/-! ## External types -/

/-- `Taddrtype` (with the abbreviation `eps ≡ i32`). -/
def AddrTypeT (xs : List SExp) (a : AddrType) : Prop :=
  (xs = [] ∧ a = .i32) ∨ (xs = [K "i32"] ∧ a = .i32) ∨ (xs = [K "i64"] ∧ a = .i64)

/-- `Tlimits`. -/
def LimitsT (xs : List SExp) (l : Limits) : Prop :=
  (∃ nx n, xs = [nx] ∧ AtomU64 nx n ∧ l = ⟨n, none⟩) ∨
    ∃ nx mx n m, xs = [nx, mx] ∧ AtomU64 nx n ∧ AtomU64 mx m ∧ l = ⟨n, some m⟩

/-- `Tglobaltype_(I)`. -/
def GlobalTypeT (I : IdCtx) (x : SExp) (g : GlobalType) : Prop :=
  (∃ t, ValTypeT I x t ∧ g = ⟨.const, t⟩) ∨
    ∃ tx t, x = L [K "mut", tx] ∧ ValTypeT I tx t ∧ g = ⟨.var, t⟩

/-- `Tmemtype_(I)`. -/
def MemTypeT (xs : List SExp) (m : MemoryType) : Prop :=
  ∃ ax lx a l, xs = ax ++ lx ∧ AddrTypeT ax a ∧ LimitsT lx l ∧ m = ⟨a, l⟩

/-- `Ttabletype_(I)`. -/
def TableTypeT (I : IdCtx) (xs : List SExp) (t : TableType) : Prop :=
  ∃ ax lx rx a l r, xs = ax ++ lx ++ [rx] ∧ AddrTypeT ax a ∧ LimitsT lx l ∧ RefTypeT I rx r ∧
    t = ⟨a, l, r⟩

/-! ## Type uses -/

/-- The singleton recursive type `(rec (sub final (func ft)))`. -/
def funcRec (ft : FuncType) : RecType := ⟨[⟨true, [], .func ft⟩]⟩

/-- `I.TYPEDEFS[x] = _DEF (REC st*) i` with `st*[i]` a function subtype.

Erratum T4: the literal premise of
`Ttypeuse_(I)/base` demands `st*[i] = SUB FINAL (FUNC ft)`, i.e. a final type
*and* an empty supertype list, for an explicit `(type x)` use, which rejects
non-final types and final subtypes such as `(sub final $t (func))`; like the
reference interpreter and the existing `wat3!` quotation, any function subtype
is accepted here.  (The `SUB FINAL` with no supertypes required for implicit
uses, `Ttypeuse_(I)/abbrev`, is intended and kept: `funcRec`.) -/
def TypeDefIsFunc (I : IdCtx) (x : TypeIdx) (ft : FuncType) : Prop :=
  ∃ rt i fin sups, I.typedefs[x.toNat]? = some (some (rt, i)) ∧
    rt.types[i]? = some ⟨fin, sups, .func ft⟩

/-- `Ttypeuse_(I)`: the type index, the local names bound by the parameters, and
the function types used through the abbreviation (for implicit definitions).

`(type x)` may be followed by parameter and result clauses that are all empty,
`(param)` and `(result)`, which the abbreviations `(param t*) ≡ (param t)*` and
`(result t*) ≡ (result t)*` expand to nothing; the use then means `(type x)`
alone, whatever the arity of `x`.  SpecTec ambiguity (do the zero-type
abbreviations vanish before `Ttypeuse_` is matched?), resolved as the reference
interpreter does: it drops empty clauses (`parser.mly`, the `([], [])` case of
`callinstr_type_instr_list` and of `func_fields`). -/
def TypeUseT (I : IdCtx) (xs : List SExp) (x : TypeIdx) (locals : List (Option String))
    (uses : List FuncType) : Prop :=
  -- `(type x)`, possibly followed by empty `(param)`/`(result)` clauses
  (∃ tx pxs rxs ft, xs = L [K "type", tx] :: (pxs ++ rxs) ∧ Concat (ParamT I) pxs [] ∧
      Concat (ResultT I) rxs [] ∧ Idx I.types tx x ∧ TypeDefIsFunc I x ft ∧
      locals = List.replicate ft.params.length none ∧ uses = []) ∨
  -- `(type x) param* result*`
  (∃ tx pxs rxs ft ps rs, xs = L [K "type", tx] :: (pxs ++ rxs) ∧ Idx I.types tx x ∧
      TypeDefIsFunc I x ft ∧ Concat (ParamT I) pxs ps ∧ Concat (ResultT I) rxs rs ∧
      ft = ⟨ps.map Prod.fst, rs⟩ ∧ locals = ps.map Prod.snd ∧
      ({ locals := locals } : IdCtx).Ok ∧ uses = []) ∨
  -- abbreviation `param* result*`: the first matching singleton function type
  ∃ pxs rxs ps rs, xs = pxs ++ rxs ∧ Concat (ParamT I) pxs ps ∧ Concat (ResultT I) rxs rs ∧
    I.typedefs[x.toNat]? = some (some (funcRec ⟨ps.map Prod.fst, rs⟩, 0)) ∧
    (∀ j < x.toNat, I.typedefs[j]? ≠ some (some (funcRec ⟨ps.map Prod.fst, rs⟩, 0))) ∧
    locals = ps.map Prod.snd ∧ ({ locals := locals } : IdCtx).Ok ∧
    uses = [⟨ps.map Prod.fst, rs⟩]

/-- `(type x)` alone. -/
theorem TypeUseT.ofType {I : IdCtx} {tx : SExp} {x : TypeIdx} {ft : FuncType}
    (hx : Idx I.types tx x) (hft : TypeDefIsFunc I x ft) :
    TypeUseT I [L [K "type", tx]] x (List.replicate ft.params.length none) [] :=
  Or.inl ⟨tx, [], [], ft, rfl, Concat.nil', Concat.nil', hx, hft, rfl, rfl⟩

/-- `Ttagtype_(I)`. -/
def TagTypeT (I : IdCtx) (xs : List SExp) (t : TagType) (uses : List FuncType) : Prop :=
  ∃ locals, TypeUseT I xs t locals uses

/-- `Texterntype_(I)`: an external type and the context it contributes. -/
def ExternTypeT (I : IdCtx) (x : SExp) (et : ExternType) (J : IdCtx)
    (uses : List FuncType) : Prop :=
  (∃ ix rest id t, x = L (K "tag" :: (ix ++ rest)) ∧ IdOpt ix id ∧ TagTypeT I rest t uses ∧
      et = .tag t ∧ J = { tags := [id] }) ∨
  (∃ ix gx id g, x = L (K "global" :: (ix ++ [gx])) ∧ IdOpt ix id ∧ GlobalTypeT I gx g ∧
      et = .global g ∧ J = { globals := [id] } ∧ uses = []) ∨
  (∃ ix rest id m, x = L (K "memory" :: (ix ++ rest)) ∧ IdOpt ix id ∧ MemTypeT rest m ∧
      et = .memory m ∧ J = { mems := [id] } ∧ uses = []) ∨
  (∃ ix rest id t, x = L (K "table" :: (ix ++ rest)) ∧ IdOpt ix id ∧ TableTypeT I rest t ∧
      et = .table t ∧ J = { tables := [id] } ∧ uses = []) ∨
  ∃ ix rest id t locals, x = L (K "func" :: (ix ++ rest)) ∧ IdOpt ix id ∧
    TypeUseT I rest t locals uses ∧ et = .func t ∧ J = { funcs := [id] }

end Silmaril.Wasm.Text.Core
