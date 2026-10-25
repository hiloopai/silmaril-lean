module

public import Silmaril.Wasm.V2.Validation.Instructions
public import Silmaril.Wasm.V2.Modules

/-!
# WebAssembly 2.0 constant expressions and module validation

Transcribed from the official SpecTec source
`specification/wasm-2.0/6-typing.spectec`, sections `Constant Expressions`
(`6-typing:535-567`) and `Modules` (`6-typing:570-708`), together with
`specification/wasm-2.0/2-syntax-aux.spectec`, at WebAssembly/spec revision
`608711107b7f1edb13efd57b7d79b49477462d36` (see `specs/wasm/core-2.0.json`).
Line references of the form `6-typing:NN` point into that file; `1-syntax:NN`
into `specification/wasm-2.0/1-syntax.spectec`.

## `Instr_const/global.get` requires an *immutable* global

`6-typing:555-557` reads, character for character,

```
rule Instr_const/global.get:
  C |- (GLOBAL.GET x) CONST
  -- if C.GLOBALS[x] = t
```

The right-hand side is the bare metavariable `t`, and `var t : valtype`
(`1-syntax:187`). A `globaltype` is `mut valtype` (`1-syntax:167`) with
`syntax mut = MUT?` (`1-syntax:162`), so `C.GLOBALS[x] = t` says that the
*whole* global type is `eps t`: the `MUT` marker is absent and the global is
**immutable**. Contrast `Instr_ok/global.get` (`6-typing:386`), whose premise is
`C.GLOBALS[x] = mut t` with `mut` a bound metavariable, so *that* rule accepts a
global of either mutability; and `Instr_ok/global.set` (`6-typing:390`), whose
premise is `C.GLOBALS[x] = MUT t`, requiring a mutable one.

Cross-checked three ways, as the errata policy requires: the raw pinned file
(above), SpecTec's own notation (`syntax mut = MUT?`, so an omitted `mut` is
`eps`), and the reference interpreter together with the test suite —
`interpreter/valid/valid.ml:1039` is

```
| GlobalGet x -> let GlobalT (mut, _t) = global c x in mut = Cons
```

and `test/core/global.wast:376-378` is

```
(assert_invalid
  (module (global (import "test" "global-mut-i32") (mut i32)) (global i32 (global.get 0)))
  "constant expression required"
)
```

`InstrConst.globalGet` therefore carries `gt.mutability = .const`. This is a
faithful transcription, not a deviation.

Note also what 2.0 const expressions do **not** contain: there is no
`Instr_const/binop`, so the extended-constant `i32.add`/`i32.sub`/`i32.mul` of
Core 3.0 (`Silmaril/Wasm/Validation/Const.lean`) are not constant in 2.0, and
`is_const` in the pinned (3.0) interpreter is correspondingly more generous than
this file. The five 2.0 rules are exactly `const`, `vconst`, `ref.null`,
`ref.func`, `global.get`.

## `Module_ok`'s two contexts

`6-typing:682-708` builds **two** contexts and is careful about which judgment
sees which.

```
C  = {TYPES ft'*, FUNCS ift* ft*, GLOBALS igt* gt*, TABLES itt* tt*,
      MEMS imt* mt*, ELEMS rt*, DATAS OK^n}                       (6-typing:701)
C' = {TYPES ft'*, FUNCS ift* ft*, GLOBALS igt*, TABLES itt* tt*,
      MEMS imt* mt*}                                              (6-typing:703)
```

`C'` holds **only the imported globals** — a global initializer, an element
segment and a data segment can read imported globals but not globals defined by
the same module — and `C'` has no `ELEMS`, no `DATAS`, no `LOCALS`, no `LABELS`
and no `RETURN`. Globals, tables, memories, elements and data are checked under
`C'` (`6-typing:687-692`); functions, the start function and exports under `C`
(`6-typing:694-696`). Imports are checked under `{TYPES ft'*}` alone
(`6-typing:685`), so an import's own type may name only the module's types.

`ift*`, `igt*`, `itt*`, `imt*` are `$funcsxt`, `$globalsxt`, `$tablesxt`,
`$memsxt` of the import types (`6-typing:705-708`, `2-syntax-aux:51-70`), which
are `Silmaril.Wasm.V2.ExternType.{funcs,globals,tables,mems}`.

The data count `n` of `data^n` ties the segment list to `DATAS OK^n`; here that
is `datas := m.data.map fun _ => ()`.

2.0 bounds the number of memories but **not** the number of tables: the
`-- if |tt*| <= 1` premise that `wasm-1.0/6-typing.spectec:455` carries is gone
from `6-typing:698`, because multiple tables are the point of the
reference-types feature. No table bound is imposed here.

## Deviations

**Deviation (import descriptors).** This is decided deviation 2 of the
development, taken in `Silmaril/Wasm/V2/Modules.lean`: an `Import` carries an
`ImportDesc` whose function case is a `TypeIdx`, because `A-binary:139` says
`;; TODO: typeidx`. `ImportOk` resolves the descriptor against the module's own
types with `Silmaril.Wasm.V2.Module.importType?`, and the resolved `ExternType`
is SpecTec's `xt` unchanged. An unresolvable type index makes `importType?`
return `none`, so no `ExternType` exists and the import does not validate.

**Deviation (`C.REFS`).** Decided deviation 6. `6-typing` has no `REFS` context
field and `Module_ok` carries `;; TODO: refs` (`6-typing:681`), so the pinned
SpecTec 2.0 omits the `x \in C.REFS` premise that the W3C 2.0 prose puts on
`ref.func`. `Silmaril/Wasm/V2/Validation/Context.lean` adds the field and
`InstrOk.refFunc` checks it; this file must therefore *populate* it. We use the
only normative definition that exists, the one SpecTec introduced when the TODO
was discharged in 3.0:

```
syntax nonfuncs = global* mem* table* elem* export*
def $funcidx_nonfuncs(global* mem* table* elem* export*) =
  $funcidx_module(MODULE eps eps eps global* mem* table* eps eps elem* eps export*)
                                          (wasm-3.0/2.4-validation.modules.spectec:141-143)
-- if x* = $funcidx_nonfuncs(global* mem* table* elem* export*)
                                          (wasm-3.0/2.4-validation.modules.spectec:166)
```

Specialised to 2.0 syntax, where a `mem` is a bare `memtype` and a `table` a
bare `tabletype` and neither carries an initializer, this is exactly

* every function index free in a **global's initializer**,
* every function index free in an **element segment's** init expressions and in
  its **active offset**,
* every function index named by an **export**,

which is `funcIdxNonFuncs` below, and which matches
`Silmaril/Wasm/Validation/Modules.lean`'s `funcIdxNonFuncs` clause for clause.
Two boundary cases are worth stating explicitly, because the brief for this unit
guessed differently on one of them:

* **The start function is not in `REFS`.** `$funcidx_nonfuncs` does not take
  `start?`, and `interpreter/valid/valid.ml:1153` reads
  `let refs = Free.module_ ({m.it with funcs = []; start = None} @@ m.at)` —
  `start = None` deletes it. So `(start $f)` alone does *not* license
  `ref.func $f`.
* **Data segments are not in `$funcidx_nonfuncs`, but are in `Free.module_`.**
  The interpreter keeps `m.datas`, whose only expression is an active offset
  (`interpreter/syntax/free.ml:217`). The two readings agree on every module
  that can validate: a 2.0 active data offset must have type `I32`
  (`Datamode_ok/active`, `6-typing:632-635`) and the only `Instr_const` rules
  that mention a function index are `ref.func` (result `FUNCREF`) and
  `global.get`, so a well-typed offset contributes nothing. We follow the
  SpecTec set and omit data.

`Instr.freeFuncs` collects `CALL x` as well as `REF.FUNC x`, matching
`interpreter/syntax/free.ml:146` (`Call x | ReturnCall x -> funcs (idx x)`) and
`Silmaril/Wasm/Validation/Modules.lean`. In 2.0 no constant expression can
contain `CALL`, so this clause too is inert; it is kept for agreement with the
interpreter and because `freeFuncs` is defined on all of `Instr`.

**Deviation (disjoint export names).** `6-typing:699` is the comment
`;; -- TODO: disjoint export names`, so the pinned SpecTec 2.0 imposes no
constraint at all. The W3C 2.0 text requires export names to be pairwise
distinct, and the reference interpreter enforces it, at this pin in
`interpreter/valid/valid.ml:1143-1150`

```
let check_names (names : name list) at =
  ignore (
    List.fold_left (fun set name ->
      require (not (NameSet.mem name set)) at
        ("duplicate export name \"" ^ string_of_name name ^ "\"");
      NameSet.add name set
    ) NameSet.empty names
  )
```

called from `check_module` (`valid.ml:1170`), and historically (2.0 era) in
`check_export`, `require (not (NameSet.mem name set)) ex.at "duplicate export
name"`. `test/core/exports.wast` has twenty `assert_invalid` modules whose
expected failure is `"duplicate export name"` (lines 52, 56, 60, 64, 68, 72,
113, 117, 121, 125, 129, 168, 172, 176, 180, 184, 224, 233, 237, 241), and
`test/core/linking.wast` depends on names being unique when it resolves imports.
Core 3.0 SpecTec has the premise, `-- if $disjoint_(name, nm*)`
(`wasm-3.0/2.4-validation.modules.spectec:161`). We add it, as
`(m.exports.map Export.name).Nodup`. See `Silmaril.Wasm.V2.Validation`.

**Deviation (`|mt*| <= 1` counts imports too).** `6-typing:698` is
`-- if |mt*| <= 1`, where `mt*` is bound by `(Mem_ok: C' |- mem : mt)*`
(`6-typing:689`) and so ranges over the memories **defined** by the module. Read
literally, a module that imports one memory and defines another is well formed,
even though `C.MEMS = imt* mt*` then has length `2` and every memory instruction
is specified against `C.MEMS[0]` only.

Checked three ways. (i) The raw file: the binding occurrence of `mt*` is the
`Mem_ok` premise, and the imported memories are `imt*`, a different sequence,
introduced at `6-typing:708`. (ii) SpecTec's own notation: `wasm-1.0`'s
`Module_ok` has the same shape, `-- if |tt*| <= 1` and `-- if |mt*| <= 1`
(`wasm-1.0/6-typing.spectec:455-456`), also on the defined sequences — the same
reading, so this is systematic rather than a typo in one line. (iii) The
reference interpreter and the test suite. The pinned interpreter is the 3.0 one
and has no bound at all (multi-memory is a 3.0 feature), so the 2.0-era source
is the relevant witness; the check was deleted by commit `717177c7c`, whose
parent has, at the end of `check_module`,

```
  require (List.length c.tables <= 1) m.at
    "multiple tables are not allowed (yet)";
  require (List.length c.memories <= 1) m.at
    "multiple memories are not allowed (yet)"
```

where `c.memories` is `c0.memories @ List.map (fun mem -> mem.it.mtype) memories`
with `c0` the result of folding `check_import` — that is, **imports plus
definitions**. The same commit's parent has, in `test/core/memory.wast:8-9`,

```
(assert_invalid (module (memory 0) (memory 0)) "multiple memories")
(assert_invalid (module (memory (import "spectest" "memory") 0) (memory 0)) "multiple memories")
```

The second of these is precisely the module that `|mt*| <= 1` would admit. We
follow the reference interpreter and state the premise as
`C.mems.length <= 1`, i.e. `|imt* mt*| <= 1`. See `Silmaril.Wasm.V2.Validation`.

## Other points of care

* `Func_ok` (`6-typing:592-596`) carries `(if t =/= BOT)*` on the declared local
  types. `Silmaril.Wasm.V2.Func` stores locals as `List ValType`, which has no
  `BOT` alternative at all, so the premise is discharged by the representation
  and does not appear as a field. The body is checked in
  `C ++ {LOCALS t_1* t*, LABELS (t_2*), RETURN (t_2*)}`, which is
  `Context.withFuncFrame` with locals `ft.params ++ f.locals`.
* `Datamode_ok/active` (`6-typing:632`) is written `C |- ACTIVE 0 expr : OK`
  with a **literal** `0`: a 2.0 active data segment must target memory `0`. That
  is a separate premise from `C.MEMS[0] = mt`, and both are recorded.
* `Elemmode_ok/active` (`6-typing:621`) names the reference type `rt` once, in
  `C.TABLES[x] = lim rt` and in the conclusion, so the element segment's type
  must equal the table's element type **exactly**; 2.0 has no reference
  subtyping. Core 3.0 relaxes this to `Ref_sub`.
* `Table_ok` (`6-typing:604`) and `Mem_ok` (`6-typing:608`) have a context on
  the left of the turnstile but never use it, and in 2.0 a `table` *is* a
  `tabletype` and a `mem` *is* a `memtype`. `TableOk`/`MemOk` therefore take no
  context; they keep both the syntax and the assigned type, so that the
  judgment's arity and its determinism survive.
* `Start_ok` (`6-typing:640`) demands `C.FUNCS[x] = eps -> eps` on the nose: the
  start function takes no arguments and returns nothing.

No deviation beyond the four recorded above is taken in this file.
-/

@[expose] public section

namespace Silmaril.Wasm.V2.Validation

/-! ## Constant expressions

`Instr_const`, `Expr_const` and `Expr_ok_const` (`6-typing:535-567`). -/

/-- `Instr_const: context |- instr CONST` (`6-typing:539`), all five rules.

2.0 has no extended constant expressions: `Instr_const` lists exactly `CONST`,
`VCONST`, `REF.NULL`, `REF.FUNC` and `GLOBAL.GET`, and nothing else is
constant. -/
inductive InstrConst (C : Context) : Instr → Prop where
  /-- `Instr_const/const` (`6-typing:543`), integer case. -/
  | intConst (t : IntType) (c : BitVec t.width) : InstrConst C (.intConst t c)
  /-- `Instr_const/const` (`6-typing:543`), floating-point case. -/
  | floatConst (t : FloatType) (c : BitVec t.width) : InstrConst C (.floatConst t c)
  /-- `Instr_const/vconst` (`6-typing:546`). -/
  | vecConst (c : BitVec 128) : InstrConst C (.vecConst c)
  /-- `Instr_const/ref.null` (`6-typing:549`). -/
  | refNull (rt : RefType) : InstrConst C (.refNull rt)
  /-- `Instr_const/ref.func` (`6-typing:552`). The rule has no premise:
  `Instr_ok/ref.func` (`6-typing:294`) is what checks the index. -/
  | refFunc (x : FuncIdx) : InstrConst C (.refFunc x)
  /-- `Instr_const/global.get` (`6-typing:555`), whose premise
  `C.GLOBALS[x] = t` has a bare `valtype` on the right and therefore forces the
  `mut` component to be absent: the global must be **immutable**. See the module
  documentation for the three-way check. -/
  | globalGet {x : GlobalIdx} {gt : GlobalType}
      (hx : C.globals[x.toNat]? = some gt) (hmut : gt.mutability = .const) :
      InstrConst C (.globalGet x)

/-- `Expr_const: context |- expr CONST` (`6-typing:540`), whose single rule
(`6-typing:560`) is the iterated premise `(Instr_const: C |- instr CONST)*`. -/
def ExprConst (C : Context) (e : Expr) : Prop := ∀ i ∈ e, InstrConst C i

/-- `Expr_ok_const: context |- expr : valtype CONST` (`6-typing:541`), whose
single rule (`6-typing:564`) conjoins `Expr_ok` and `Expr_const`. The result
type is a *syntactic* `valtype`, so the expression has exactly one result and it
is not `BOT`. -/
structure ExprOkConst (C : Context) (e : Expr) (t : ValType) : Prop where
  /-- `Expr_ok: C |- expr : t` (`6-typing:566`). -/
  typed : ExprOk C e [CValType.val t]
  /-- `Expr_const: C |- expr CONST` (`6-typing:567`). -/
  const : ExprConst C e

@[simp] theorem exprConst_nil (C : Context) : ExprConst C [] := by
  intro i hi; exact absurd hi (by simp)

theorem ExprConst.cons {C : Context} {i : Instr} {e : Expr}
    (hi : InstrConst C i) (he : ExprConst C e) : ExprConst C (i :: e) := by
  intro j hj
  rcases List.mem_cons.1 hj with rfl | hj
  · exact hi
  · exact he j hj

/-! ## Free function indices

`$funcidx_nonfuncs` of `wasm-3.0/2.4-validation.modules.spectec:141-143`,
specialised to 2.0 syntax; this is what populates `Context.refs`. See the
module documentation. -/

/-- The function indices occurring in an instruction: `CALL x` and `REF.FUNC x`,
recursing through the bodies of `BLOCK`, `LOOP` and `IF`. This is
`$free_instr(instr).FUNCS`, i.e. `interpreter/syntax/free.ml:146` and `:171`. -/
def Instr.freeFuncs : Instr → List FuncIdx
  | .call x | .refFunc x => [x]
  | .block _ body | .loop _ body => body.attach.flatMap fun i => freeFuncs i.val
  | .if_ _ left right =>
      (left.attach.flatMap fun i => freeFuncs i.val) ++
        (right.attach.flatMap fun i => freeFuncs i.val)
  | _ => []
  termination_by instruction => sizeOf instruction
  decreasing_by
    all_goals exact Nat.lt_trans (List.sizeOf_lt_of_mem i.property) (by simp; omega)

/-- `$free_expr(expr).FUNCS`. -/
def Expr.freeFuncs (e : Expr) : List FuncIdx := e.flatMap Instr.freeFuncs

/-- `$funcidx_nonfuncs(global* mem* table* elem* export*)`, the `REFS` field of
`Module_ok`. A 2.0 `mem` and `table` carry no expression, so only globals,
element segments and exports contribute. See the module documentation for why
`start?` and `data*` are absent. -/
def funcIdxNonFuncs (m : Module) : List FuncIdx :=
  m.globals.flatMap (fun g => Expr.freeFuncs g.init) ++
    m.elems.flatMap (fun e => e.init.flatMap Expr.freeFuncs ++
      match e.mode with
        | .active _ off => Expr.freeFuncs off
        | .passive | .declare => []) ++
    m.exports.flatMap (fun e => match e.index with
      | .func x => [x]
      | .global _ | .table _ | .memory _ => [])

/-! ## Module definitions

`Type_ok`, `Func_ok`, `Global_ok`, `Table_ok`, `Mem_ok`, `Elem_ok`, `Data_ok`,
`Elemmode_ok`, `Datamode_ok`, `Start_ok` (`6-typing:574-642`). -/

/-- `Type_ok: |- TYPE ft : ft` (`6-typing:588`), with premise
`Functype_ok: |- ft : OK`. A `Silmaril.Wasm.V2.Module` stores the bare
`functype`, so the `TYPE` wrapper is implicit. -/
def TypeOk (ty : FuncType) (ft : FuncType) : Prop := ft = ty ∧ FuncType.Ok ty

instance (ty ft : FuncType) : Decidable (TypeOk ty ft) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `Func_ok: C |- FUNC x (LOCAL t)* expr : t_1* -> t_2*` (`6-typing:592`).

The premises are `C.TYPES[x] = t_1* -> t_2*`, the iterated `(if t =/= BOT)*`
— automatic here, since `Silmaril.Wasm.V2.ValType` has no `BOT` — and
`Expr_ok: C ++ {LOCALS t_1* t*, LABELS (t_2*), RETURN (t_2*)} |- expr : t_2*`,
which is `Context.withFuncFrame`. -/
inductive FuncOk (C : Context) : Func → FuncType → Prop where
  /-- `Func_ok` (`6-typing:592`). -/
  | mk {f : Func} {ft : FuncType}
      (hx : C.types[f.type.toNat]? = some ft)
      (hbody : ExprOk (C.withFuncFrame (ft.params ++ f.locals)
          (liftResult ft.results) (liftResult ft.results)) f.body (liftResult ft.results)) :
      FuncOk C f ft

/-- `Global_ok: C |- GLOBAL gt expr : gt` (`6-typing:598`), with premises
`Globaltype_ok: |- gt : OK`, `if gt = mut t`, and
`Expr_ok_const: C |- expr : t CONST`. The decomposition `gt = mut t` names the
value type, so the initializer is checked at `gt.value` whatever the
mutability. -/
def GlobalOk (C : Context) (g : Global) (gt : GlobalType) : Prop :=
  gt = g.type ∧ GlobalType.Ok gt ∧ ExprOkConst C g.init gt.value

/-- `Table_ok: C |- TABLE tt : tt` (`6-typing:604`), with premise
`Tabletype_ok: |- tt : OK`. The context is unused by the rule. -/
def TableOk (tab : TableType) (tt : TableType) : Prop := tt = tab ∧ TableType.Ok tab

instance (tab tt : TableType) : Decidable (TableOk tab tt) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `Mem_ok: C |- MEMORY mt : mt` (`6-typing:608`), with premise
`Memtype_ok: |- mt : OK`. The context is unused by the rule. -/
def MemOk (mem : MemoryType) (mt : MemoryType) : Prop := mt = mem ∧ MemoryType.Ok mem

instance (mem mt : MemoryType) : Decidable (MemOk mem mt) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `Elemmode_ok: context |- elemmode : reftype` (`6-typing:581`), its three
rules.

* `/active` (`6-typing:621`): `C.TABLES[x] = lim rt` with the **same** `rt` as
  the conclusion — exact equality of reference types, 2.0 has no reference
  subtyping — and `Expr_ok_const: C |- expr : I32 CONST` for the offset.
* `/passive` (`6-typing:626`) and `/declare` (`6-typing:629`): no premise, and
  the reference type is unconstrained. -/
inductive ElemModeOk (C : Context) : ElemMode → RefType → Prop where
  /-- `Elemmode_ok/active` (`6-typing:621`). -/
  | active {x : TableIdx} {off : Expr} {rt : RefType} {tt : TableType}
      (hx : C.tables[x.toNat]? = some tt) (hrt : tt.element = rt)
      (hoff : ExprOkConst C off .i32) :
      ElemModeOk C (.active x off) rt
  /-- `Elemmode_ok/passive` (`6-typing:626`). -/
  | passive {rt : RefType} : ElemModeOk C .passive rt
  /-- `Elemmode_ok/declare` (`6-typing:629`). -/
  | declare {rt : RefType} : ElemModeOk C .declare rt

/-- `Datamode_ok: context |- datamode : OK` (`6-typing:582`), its two rules.

`/active` (`6-typing:632`) is written `C |- ACTIVE 0 expr : OK` with a literal
memory index `0`, and additionally requires `C.MEMS[0] = mt`; `/passive`
(`6-typing:637`) has no premise. -/
inductive DataModeOk (C : Context) : DataMode → Prop where
  /-- `Datamode_ok/active` (`6-typing:632`). -/
  | active {x : MemIdx} {off : Expr} {mt : MemoryType}
      (hx : x.toNat = 0) (hmem : C.mems[0]? = some mt)
      (hoff : ExprOkConst C off .i32) :
      DataModeOk C (.active x off)
  /-- `Datamode_ok/passive` (`6-typing:637`). -/
  | passive : DataModeOk C .passive

/-- `Elem_ok: C |- ELEM rt expr* elemmode : rt` (`6-typing:612`), with premises
`(Expr_ok_const: C |- expr : rt CONST)*` and `Elemmode_ok: C |- elemmode : rt`.
The assigned reference type is the segment's own `rt`. -/
def ElemOk (C : Context) (e : Elem) (rt : RefType) : Prop :=
  rt = e.type ∧ (∀ ex ∈ e.init, ExprOkConst C ex (.ref rt)) ∧ ElemModeOk C e.mode rt

/-- `Data_ok: C |- DATA b* datamode : OK` (`6-typing:617`), whose only premise is
`Datamode_ok`. The bytes are unconstrained. -/
def DataOk (C : Context) (d : Data) : Prop := DataModeOk C d.mode

/-- `Start_ok: C |- START x : OK` (`6-typing:640`), whose premise is
`C.FUNCS[x] = eps -> eps`. -/
def StartOk (C : Context) (x : FuncIdx) : Prop := C.funcs[x.toNat]? = some ⟨[], []⟩

instance (C : Context) (x : FuncIdx) : Decidable (StartOk C x) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## Module im/exports

`Import_ok`, `Export_ok`, `Externidx_ok` (`6-typing:645-674`). -/

/-- `Import_ok: C |- IMPORT name_1 name_2 xt : xt` (`6-typing:651`), with premise
`Externtype_ok: |- xt : OK`.

Decided deviation 2: the syntactic descriptor carries a `TypeIdx` for function
imports, so the SpecTec `xt` is recovered by
`Silmaril.Wasm.V2.Module.importType?` against `C.TYPES`. At the single use site
(`6-typing:685`) `C` is `{TYPES ft'*}`. -/
def ImportOk (C : Context) (im : Import) (xt : ExternType) : Prop :=
  Module.importType? C.types im.desc = some xt ∧ ExternType.Ok xt

instance (C : Context) (im : Import) (xt : ExternType) : Decidable (ImportOk C im xt) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `Externidx_ok: context |- externidx : externtype` (`6-typing:649`), its four
rules `/func` (`6-typing:660`), `/global` (`6-typing:664`), `/table`
(`6-typing:668`) and `/mem` (`6-typing:672`). Each looks the index up in the
corresponding index space of the context, which already has imports first. -/
inductive ExternIdxOk (C : Context) : ExternIdx → ExternType → Prop where
  /-- `Externidx_ok/func` (`6-typing:660`). -/
  | func {x : FuncIdx} {ft : FuncType} (hx : C.funcs[x.toNat]? = some ft) :
      ExternIdxOk C (.func x) (.func ft)
  /-- `Externidx_ok/global` (`6-typing:664`). -/
  | global {x : GlobalIdx} {gt : GlobalType} (hx : C.globals[x.toNat]? = some gt) :
      ExternIdxOk C (.global x) (.global gt)
  /-- `Externidx_ok/table` (`6-typing:668`). -/
  | table {x : TableIdx} {tt : TableType} (hx : C.tables[x.toNat]? = some tt) :
      ExternIdxOk C (.table x) (.table tt)
  /-- `Externidx_ok/mem` (`6-typing:672`). -/
  | memory {x : MemIdx} {mt : MemoryType} (hx : C.mems[x.toNat]? = some mt) :
      ExternIdxOk C (.memory x) (.memory mt)

/-- `Export_ok: C |- EXPORT name externidx : xt` (`6-typing:655`), whose only
premise is `Externidx_ok`. The name itself is unconstrained by this rule; the
pairwise-distinctness condition lives in `ModuleOk`. -/
def ExportOk (C : Context) (e : Export) (xt : ExternType) : Prop := ExternIdxOk C e.index xt

/-! ## Modules proper

`Module_ok` (`6-typing:679-708`). -/

/-- `Module_ok: |- module : externtype* -> externtype*` (`6-typing:682`).

`ModuleOk m ixt xt` is SpecTec's `|- m : ixt* -> xt*`. The single constructor's
fields are named after the SpecTec premises, in SpecTec's order; the two context
equations `hC` (`6-typing:701`) and `hC'` (`6-typing:703`) come last, as they do
in the source.

Three premises are *not* a literal transcription — see the module documentation
for the evidence behind each:

* `hrefs` is implicit in `hC`/`hC'`, which set `REFS` to `funcIdxNonFuncs m`
  (decided deviation 6, `;; TODO: refs` at `6-typing:681`);
* `hmems_le` bounds `C.MEMS`, i.e. imported *and* defined memories, where
  `6-typing:698` literally bounds only the defined ones;
* `hnames` is the export-name disjointness that `6-typing:699` leaves as
  `;; -- TODO: disjoint export names`.

There is deliberately **no** bound on the number of tables. -/
inductive ModuleOk : Module → List ExternType → List ExternType → Prop where
  /-- `Module_ok` (`6-typing:682`). -/
  | mk {m : Module} {ixt xt : List ExternType} {ft' ft : List FuncType}
      {gt : List GlobalType} {tt : List TableType} {mt : List MemoryType}
      {rt : List RefType} {C C' : Context}
      -- `(Type_ok: |- type : ft')*` (`6-typing:684`).
      (htypes : List.Forall₂ TypeOk m.types ft')
      -- `(Import_ok: {TYPES ft'*} |- import : ixt)*` (`6-typing:685`).
      (himports : List.Forall₂ (ImportOk { types := ft' }) m.imports ixt)
      -- `(Global_ok: C' |- global : gt)*` (`6-typing:687`).
      (hglobals : List.Forall₂ (GlobalOk C') m.globals gt)
      -- `(Table_ok: C' |- table : tt)*` (`6-typing:688`).
      (htables : List.Forall₂ TableOk m.tables tt)
      -- `(Mem_ok: C' |- mem : mt)*` (`6-typing:689`).
      (hmems : List.Forall₂ MemOk m.memories mt)
      -- `(Elem_ok: C' |- elem : rt)*` (`6-typing:691`).
      (helems : List.Forall₂ (ElemOk C') m.elems rt)
      -- `(Data_ok: C' |- data : OK)^n` (`6-typing:692`); the count `n` is
      -- `m.data.length`, tied to `DATAS OK^n` by `hC`.
      (hdatas : ∀ d ∈ m.data, DataOk C' d)
      -- `(Func_ok: C |- func : ft)*` (`6-typing:694`).
      (hfuncs : List.Forall₂ (FuncOk C) m.funcs ft)
      -- `(Start_ok: C |- start : OK)?` (`6-typing:695`).
      (hstart : ∀ x, m.start = some x → StartOk C x)
      -- `(Export_ok: C |- export : xt)*` (`6-typing:696`).
      (hexports : List.Forall₂ (ExportOk C) m.exports xt)
      -- `if |mt*| <= 1` (`6-typing:698`), read on `C.MEMS`; see the docstring.
      (hmems_le : C.mems.length ≤ 1)
      -- `;; -- TODO: disjoint export names` (`6-typing:699`); see the docstring.
      (hnames : (m.exports.map Export.name).Nodup)
      -- `if C = {TYPES ft'*, FUNCS ift* ft*, GLOBALS igt* gt*, TABLES itt* tt*,
      -- MEMS imt* mt*, ELEMS rt*, DATAS OK^n}` (`6-typing:701`), plus `REFS`.
      (hC : C = { types := ft',
                  funcs := ExternType.funcs ixt ++ ft,
                  globals := ExternType.globals ixt ++ gt,
                  tables := ExternType.tables ixt ++ tt,
                  mems := ExternType.mems ixt ++ mt,
                  elems := rt,
                  datas := m.data.map fun _ => (),
                  refs := funcIdxNonFuncs m })
      -- `if C' = {TYPES ft'*, FUNCS ift* ft*, GLOBALS igt*, TABLES itt* tt*,
      -- MEMS imt* mt*}` (`6-typing:703`), plus `REFS`. Note `GLOBALS igt*`:
      -- only the *imported* globals.
      (hC' : C' = { types := ft',
                    funcs := ExternType.funcs ixt ++ ft,
                    globals := ExternType.globals ixt,
                    tables := ExternType.tables ixt ++ tt,
                    mems := ExternType.mems ixt ++ mt,
                    refs := funcIdxNonFuncs m }) :
      ModuleOk m ixt xt

/-- A module is valid when it has some import and export type. -/
def ModuleValid (m : Module) : Prop := ∃ xti xte, ModuleOk m xti xte

/-! ## Properties -/

/-- Determinism transfer along `List.Forall₂`, the shape every uniqueness
argument below needs. -/
theorem forall₂_det {α β : Type _} {R₁ R₂ : α → β → Prop}
    (hR : ∀ a b₁ b₂, R₁ a b₁ → R₂ a b₂ → b₁ = b₂) :
    ∀ {l : List α} {l₁ l₂ : List β}, List.Forall₂ R₁ l l₁ → List.Forall₂ R₂ l l₂ → l₁ = l₂
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons h₁ hs₁, .cons h₂ hs₂ => by
    rw [hR _ _ _ h₁ h₂, forall₂_det hR hs₁ hs₂]

/-- Every element of a `List.Forall₂` domain is related to some element of its
codomain. -/
theorem forall₂_exists_of_mem {α β : Type _} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') {a : α} (ha : a ∈ l) : ∃ b ∈ l', R a b := by
  induction h with
  | nil => exact absurd ha (by simp)
  | cons hr _ ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self .., hr⟩
    · obtain ⟨b, hb, hr'⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hr'⟩

/-- `Externidx_ok` assigns at most one external type. -/
theorem ExternIdxOk.det {C : Context} {x : ExternIdx} {xt₁ xt₂ : ExternType}
    (h₁ : ExternIdxOk C x xt₁) (h₂ : ExternIdxOk C x xt₂) : xt₁ = xt₂ := by
  cases h₁ <;> cases h₂ <;> simp_all

/-- `Func_ok` assigns at most one function type, and it depends on the context
only through `C.TYPES`. -/
theorem FuncOk.det {C₁ C₂ : Context} (hT : C₁.types = C₂.types) {f : Func}
    {ft₁ ft₂ : FuncType} (h₁ : FuncOk C₁ f ft₁) (h₂ : FuncOk C₂ f ft₂) : ft₁ = ft₂ := by
  cases h₁ with
  | mk hp _ =>
    cases h₂ with
    | mk hq _ =>
      rw [hT] at hp
      exact Option.some.inj (hp.symm.trans hq)

/-- `Func_ok` lifted to a whole function section. The contexts may differ
outside `TYPES`, which is what `Module_ok` needs: the two derivations' contexts
agree except in `FUNCS`, the very field being determined. -/
theorem funcsOk_det {C₁ C₂ : Context} {fs : List Func} {ft₁ ft₂ : List FuncType}
    (h₁ : List.Forall₂ (FuncOk C₁) fs ft₁) (h₂ : List.Forall₂ (FuncOk C₂) fs ft₂)
    (hT : C₁.types = C₂.types) : ft₁ = ft₂ :=
  forall₂_det (R₁ := FuncOk C₁) (R₂ := FuncOk C₂) (fun _ _ _ p q => FuncOk.det hT p q) h₁ h₂

/-- `Module_ok` determines the import and export types uniquely: a module has at
most one module type. -/
theorem ModuleOk.unique {m : Module} {ixt₁ xt₁ ixt₂ xt₂ : List ExternType}
    (h₁ : ModuleOk m ixt₁ xt₁) (h₂ : ModuleOk m ixt₂ xt₂) : ixt₁ = ixt₂ ∧ xt₁ = xt₂ := by
  obtain ⟨ht₁, hi₁, hg₁, htb₁, hmm₁, he₁, -, hf₁, -, hx₁, -, -, rfl, rfl⟩ := h₁
  obtain ⟨ht₂, hi₂, hg₂, htb₂, hmm₂, he₂, -, hf₂, -, hx₂, -, -, rfl, rfl⟩ := h₂
  -- the declared types, hence the import types
  have etypes := forall₂_det (R₁ := TypeOk) (R₂ := TypeOk)
    (fun _ _ _ p q => p.1.trans q.1.symm) ht₁ ht₂
  subst etypes
  have eimports := forall₂_det (R₁ := ImportOk _) (R₂ := ImportOk _)
    (fun _ _ _ p q => Option.some.inj (p.1.symm.trans q.1)) hi₁ hi₂
  subst eimports
  -- the defined globals, tables, memories and element segments
  have eglobals := forall₂_det (R₁ := GlobalOk _) (R₂ := GlobalOk _)
    (fun _ _ _ p q => p.1.trans q.1.symm) hg₁ hg₂
  subst eglobals
  have etables := forall₂_det (R₁ := TableOk) (R₂ := TableOk)
    (fun _ _ _ p q => p.1.trans q.1.symm) htb₁ htb₂
  subst etables
  have emems := forall₂_det (R₁ := MemOk) (R₂ := MemOk)
    (fun _ _ _ p q => p.1.trans q.1.symm) hmm₁ hmm₂
  subst emems
  have eelems := forall₂_det (R₁ := ElemOk _) (R₂ := ElemOk _)
    (fun _ _ _ p q => p.1.trans q.1.symm) he₁ he₂
  subst eelems
  -- the defined functions: both contexts now have the same `TYPES`
  have efuncs := funcsOk_det hf₁ hf₂ rfl
  subst efuncs
  -- both module contexts are now identical, so `Externidx_ok` pins the exports
  exact ⟨rfl, forall₂_det (R₁ := ExportOk _) (R₂ := ExportOk _)
    (fun _ _ _ p q => ExternIdxOk.det p q) hx₁ hx₂⟩

/-- The import types of a valid module are determined by the module. -/
theorem ModuleOk.imports_unique {m : Module} {ixt₁ xt₁ ixt₂ xt₂ : List ExternType}
    (h₁ : ModuleOk m ixt₁ xt₁) (h₂ : ModuleOk m ixt₂ xt₂) : ixt₁ = ixt₂ :=
  (ModuleOk.unique h₁ h₂).1

/-- The export types of a valid module are determined by the module. -/
theorem ModuleOk.exports_unique {m : Module} {ixt₁ xt₁ ixt₂ xt₂ : List ExternType}
    (h₁ : ModuleOk m ixt₁ xt₁) (h₂ : ModuleOk m ixt₂ xt₂) : xt₁ = xt₂ :=
  (ModuleOk.unique h₁ h₂).2

/-- A valid module has at most one memory, counting imported and defined
memories together. This is the strengthened reading of `6-typing:698`; see the
module documentation. -/
theorem ModuleOk.memories_le_one {m : Module} {ixt xt : List ExternType}
    (h : ModuleOk m ixt xt) :
    (ExternType.mems ixt).length + m.memories.length ≤ 1 := by
  obtain ⟨-, -, -, -, hmems, -, -, -, -, -, hle, -, rfl, -⟩ := h
  simpa [List.Forall₂.length_eq hmems] using hle

/-- A valid module defines at most one memory. -/
theorem ModuleOk.defined_memories_le_one {m : Module} {ixt xt : List ExternType}
    (h : ModuleOk m ixt xt) : m.memories.length ≤ 1 :=
  Nat.le_trans (Nat.le_add_left _ _) h.memories_le_one

/-- The start function of a valid module is in range: its index is below the
total number of functions, imported plus defined. -/
theorem ModuleOk.start_lt {m : Module} {ixt xt : List ExternType} {x : FuncIdx}
    (h : ModuleOk m ixt xt) (hs : m.start = some x) :
    x.toNat < (ExternType.funcs ixt).length + m.funcs.length := by
  obtain ⟨-, -, -, -, -, -, -, hfuncs, hstart, -, -, -, rfl, -⟩ := h
  have hx := hstart x hs
  simp only [StartOk] at hx
  have := (List.getElem?_eq_some_iff.1 hx).1
  simpa [List.Forall₂.length_eq hfuncs] using this

/-- Every function index exported by a valid module is in range. -/
theorem ModuleOk.export_func_lt {m : Module} {ixt xt : List ExternType} {e : Export}
    {x : FuncIdx} (h : ModuleOk m ixt xt) (he : e ∈ m.exports) (hx : e.index = .func x) :
    x.toNat < (ExternType.funcs ixt).length + m.funcs.length := by
  obtain ⟨-, -, -, -, -, -, -, hfuncs, -, hexports, -, -, rfl, -⟩ := h
  obtain ⟨xt', -, hok⟩ := forall₂_exists_of_mem hexports he
  simp only [ExportOk, hx] at hok
  cases hok with
  | func hf =>
    have := (List.getElem?_eq_some_iff.1 hf).1
    simpa [List.Forall₂.length_eq hfuncs] using this

/-- Export names are pairwise distinct, so an export is determined by its
name. -/
theorem ModuleOk.export_name_injective {m : Module} {ixt xt : List ExternType}
    (h : ModuleOk m ixt xt) {a b : Export} (ha : a ∈ m.exports) (hb : b ∈ m.exports)
    (hn : a.name = b.name) : a = b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hnames, -, -⟩ := h
  exact List.inj_on_of_nodup_map hnames ha hb hn

end Silmaril.Wasm.V2.Validation
