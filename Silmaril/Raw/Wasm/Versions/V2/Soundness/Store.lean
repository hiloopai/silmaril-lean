module

public import Silmaril.Wasm.V2.Execution.Instantiation

/-!
# WebAssembly 2.0: typing of the runtime (store typing and store extension)

Value typing (`Ref_ok`, `Val_ok`), instance typing (`Globalinst_ok`,
`Meminst_ok`, `Tableinst_ok`, `Funcinst_ok`, `Datainst_ok`, `Eleminst_ok`,
`Exportinst_ok`, `Moduleinst_ok`), `Store_ok`, and store extension
(`Extend_globalinst`, …, `Extend_store`).

## Where this comes from

**Deviation (no SpecTec source).** The pinned SpecTec wasm-2.0 sources at
WebAssembly/spec revision `608711107b7f1edb13efd57b7d79b49477462d36` (see
`specs/wasm/core-2.0.json`) are
`{0-aux, 1-syntax, 2-syntax-aux, 3-numerics, 4-runtime, 5-runtime-aux, 6-typing,
8-reduction, 9-module, A-binary}.spectec`: there is **no `7-soundness` file**,
so SpecTec 2.0 defines no store typing, no store extension and no soundness
statement at all. Every judgment in this module is therefore reconstructed,
rule for rule, from two sources that *do* agree with each other:

* the W3C WebAssembly 2.0 text, appendix *Soundness*, sections "Store Validity"
  and "Store Extension" (`document/core/appendix/properties.rst`); and
* the Core 3.0 SpecTec file `7.1-soundness.configurations.spectec`, which this
  development already transcribes in
  `Silmaril/Wasm/Execution/Core/Typing/Store.lean`. Line references of the form
  `7.1-soundness:NN` below point into that 3.0 file, which is the *only*
  machine-checked statement of these rules the upstream repository contains.

Everything 3.0-specific is dropped, because 2.0 has none of it: no recursive or
defined types and hence no `Expand` and no `Deftype_ok`, no tags, no GC
(`Structinst_ok`, `Arrayinst_ok`, `ImmutReachable` and the acyclicity side
conditions of `Store_ok` all disappear), no exceptions (`Exninst_ok`), no
address types, and — crucially — no subtyping between concrete types. The only
subtyping left is `Externtype_sub` (`6-typing:120-134`), which 2.0 uses for
*import matching* and for recovering the declared type of a table or memory
that has grown; it is already transcribed as
`Silmaril.Wasm.V2.ExternType.Sub`, and `ExternAddrOk`
(`Execution/Instantiation.lean`) already closes `Externaddr_ok` under it.

Since 2.0 has no `Reftype_sub` and no `Valtype_sub` other than reflexivity and
`BOT <: t` (`6-typing:74-78`), `Ref_ok` and `Val_ok` have **no subsumption
rule**: every runtime value has a unique type. That is `RefOk.eq_type?` and
`ValOk.eq_type?` below, which turn the usual "principal type" lemma into a
plain equivalence with the total functions `Ref.type?` and `Val.type?`.

## Deviations

**Deviation (host functions).** `Funcinst_ok` (`7.1-soundness:115`) covers only
Wasm code; `Silmaril.Wasm.V2.Execution.FuncInst` has a `code : FuncCode H` with
a `host` alternative (deviation 7 of `Execution/Basic.lean`), so
`FuncInstOk.host` accepts a host function whose type is a valid function type.
The host's *behaviour* is constrained separately by `HostOk`
(`Soundness/Defs.lean`). This is exactly what Core 3.0 does.

**Deviation (`C.REFS` as an explicit list).** `Moduleinst_ok`
(`7.1-soundness:157`) builds the context's `REFS` component as `(i)^(i<k)` with
`k <= |funcaddr*|`, i.e. an initial segment of the function index space. Our
`Validation.Context.refs` is a `List FuncIdx`, not a `List Nat`, so an initial
segment would need a `Fin (2^32)` coercion at every index.
`ModuleInstOk` instead takes the realized `refs` as a parameter constrained by
`∀ x ∈ refs, x.toNat < mi.funcs.length`. That is strictly more general than
`(i)^(i<k)` (every initial segment satisfies it) and is what `ref.func`
preservation actually needs, namely that a declared reference index names a
function the instance has.

**Statement change (`Extend.refl`).** Core 3.0's `Extend.refl` needs `StoreOk s`
because `Extend_structinst`/`Extend_arrayinst` carry an `Expand` premise. Wasm
2.0 has neither rule, and all six remaining `Extend_*` relations are reflexive
outright, so `Extend.refl` is stated **without** any hypothesis. It is the
stronger statement.

**Statement change (`TableInstOk`/`MemInstOk`: equality, not inequality).**
`Tableinst_ok` (`7.1-soundness:109`) and `Meminst_ok` (`7.1-soundness:104`)
require `|ref*| = n` and `|b*| = n * 64Ki` — the instance's *current* length is
the *minimum* of its (current) type, exactly, not merely "within the limits".
That is sound in 2.0 because `$growtable` and `$growmemory`
(`5-runtime-aux:119,126`) rewrite the type's minimum to the new size, and
`$alloctable`/`$allocmem` (`9-module:57,67`) create exactly `n` entries. The
equality is also what `ExternAddrOk.extend` needs: an import typed at a table's
old type must still be typed after the table grows, and it is recovered only
through `Limits_sub`, which compares *minima*.

**Deviation (`ExtendTable`/`ExtendMem`: the type's minimum may grow).**
`ExtendTable` below requires the element type and the limits' **maximum** to be
unchanged, the limits' **minimum** not to shrink, and `|refs|` not to shrink;
`ExtendMem` likewise, without an element type. The W3C 2.0 appendix says
something strictly stronger: its `extend-tableinst` and `extend-meminst` rules
(`document/core/appendix/properties.rst`, section *Store Extension*) are

```
   n_1 <= n_2                                   n_1 <= n_2
--------------------------------------  ------------------------------------
|- {TITYPE tt, TIELEM ref^n_1}           |- {MITYPE mt, MIDATA b^n_1}
     <= {TITYPE tt, TIELEM ref'^n_2}          <= {MITYPE mt, MIDATA b'^n_2}
```

with the *whole* type `tt`, resp. `mt`, syntactically identical on both sides —
only the element vector may grow.

**The appendix contradicts itself there.** Three of its own clauses cannot all
hold:

1. *Store validity* (`valid-tableinst`, `valid-meminst`) pins the length to the
   type: `|ref^*| = limits.LMIN` and `|b^*| = limits.LMIN * 64Ki`, exactly (this
   is the `TableInstOk`/`MemInstOk` equality recorded in the paragraph above).
2. *Execution* grows the type together with the vector: `growtable` and
   `growmem` (`document/core/exec/modules.rst`, sections *Growing tables* and
   *Growing memories*) are defined as
   `tableinst with TITYPE = limits' t with TIELEM = … ref^n` where
   `limits' = limits with LMIN = len`, and symmetrically for memories. SpecTec
   2.0 agrees: `$growtable`/`$growmemory` (`5-runtime-aux:119-131`) rebuild the
   instance with `TYPE` set to the limits `i' .. j?` whose minimum is the new
   size `i' = |r'*| + n`, resp. `i' = |b*| / 64Ki + n`.
3. *The Preservation theorem* (same appendix, section *Theorems*) asserts that
   whenever `S;T -> S';T'` with `S;T` valid, `S'` is valid **and**
   `|- S <= S'`.

A successful `table.grow`/`memory.grow` satisfies (2), so `S'` differs from `S`
in the instance's `LMIN`; by the literal `extend-tableinst`/`extend-meminst` it
is then *not* an extension of `S`, contradicting (3). The only way to keep the
type literally fixed would be to drop (1) and let `|ref^*|` exceed `LMIN`, which
the appendix does not do — and which would in turn break import matching, since
`Limits_sub` compares minima and the embedder's view of a grown table would stay
at the old minimum forever. So no consistent reading of the 2.0 appendix leaves
the type unchanged; one of its three clauses has to give.

**Our choice, and why it is the one `Step.preservation` needs.** We keep (1) and
(2) — they are SpecTec 2.0's literal `Tableinst_ok`/`Meminst_ok` analogues and
its literal `$growtable`/`$growmemory` — and relax the extension relation to
"minimum and length may grow, maximum and element type fixed". Concretely,
`V2.Soundness.Preservation.pres_memoryGrowSucceed` and the `table.grow` case
produce `mi'`/`ti'` whose `type.limits.min` is the new size (forced by (1)
together with `StoreOk`), so `ExtendMem mi mi'` with a fixed type would be
*false* and preservation could not be stated at all. With the relaxed relation
it holds, and nothing is lost downstream: `Limits.sub_of_grow` turns "max fixed,
min grew" into `Limits.Sub` of the *old* type, which is precisely what
`ExternAddrOk.extend` uses to keep an import typed at the type it was declared
with. Fixing the maximum is what makes that subtyping step possible, and no 2.0
rule ever changes a maximum.

This is also what the upstream repository's only machine-checked statement of
these rules says: Core 3.0's `Extend_tableinst` and `Extend_meminst`
(`7.1-soundness:282-290`) are

```
rule Extend_meminst:
  {TYPE at `[n..m?] PAGE, BYTES b*} `<= {TYPE at `[n'..m?] PAGE, BYTES b'*}
  -- if n <= n'   -- if |b*| <= |b'*|
rule Extend_tableinst:
  {TYPE at `[n..m?] rt, REFS ref*} `<= {TYPE at `[n'..m?] rt, REFS ref'*}
  -- if n <= n'   -- if |ref*| <= |ref'*|
```

i.e. our definitions exactly, minus the address type `at` that 2.0 does not
have; `Silmaril/Wasm/Execution/Core/Typing/Store.lean` transcribes them. The
definitions below are therefore left as they are: it is the W3C 2.0 appendix
that is at fault, and this deviation is not among the sixteen already filed
under the tracking issue.
-/

@[expose] public section

namespace Silmaril.Wasm.V2.Execution

open Silmaril.Wasm.V2.Validation
open Silmaril.Wasm.Execution.Memory (pageSize)

variable {H : Type}

/-! ## Value typing (`Ref_ok`, `Val_ok`,
`wasm-3.0/4.1-execution.values.spectec:23-83`)

Wasm 2.0 has three reference values and two reference types. A null reference
carries its own type, a function address is `FUNCREF`, and a host address is
`EXTERNREF`; there is no subsumption rule. -/

/-- `Ref_ok: s |- ref : reftype`, the 2.0 instance of
`wasm-3.0/4.1-execution.values.spectec:25`, whose rules run `:35-69`. -/
inductive RefOk (s : Store H) : Ref → RefType → Prop where
  /-- `Ref_ok/null`: `s |- (REF.NULL rt) : rt`. -/
  | null (t : RefType) : RefOk s (.null t) t
  /-- `Ref_ok/func`: a function address is a `FUNCREF`, provided it is allocated. -/
  | funcAddr {a : FuncAddr} {fi : FuncInst H} (h : s.funcInst? a = some fi) :
      RefOk s (.funcAddr a) .funcref
  /-- `Ref_ok/host`: a host address is an `EXTERNREF`. The store says nothing
  about host addresses, so there is no premise. -/
  | hostAddr (a : HostAddr) : RefOk s (.hostAddr a) .externref

/-- `Val_ok: s |- val : valtype` (with `Num_ok` and `Vec_ok`),
`wasm-3.0/4.1-execution.values.spectec:72-83` (`Num_ok` `:28`, `Vec_ok` `:31`). -/
inductive ValOk (s : Store H) : Val → ValType → Prop where
  /-- `Num_ok`. -/
  | num (v : NumVal) : ValOk s (.num v) (.num v.type)
  /-- `Vec_ok`: the only `vectype` is `V128`. -/
  | vec (b : VecVal) : ValOk s (.vec b) (.vec .v128)
  /-- `Val_ok/ref`. -/
  | ref {r : Ref} {rt : RefType} (h : RefOk s r rt) : ValOk s (.ref r) (.ref rt)

/-! ### Liftings to the validation value type

Instruction typing works with `Validation.CValType = valtype | BOT`
(`1-syntax:135` plus `6-typing`'s `BOT`). No runtime value has type `BOT`, so
the liftings are the obvious partial ones. -/

/-- `RefOk` at a validation value type. -/
def CRefOk (s : Store H) (r : Ref) (t : CValType) : Prop :=
  ∃ rt : RefType, t = .val (.ref rt) ∧ RefOk s r rt

/-- `ValOk` at a validation value type. -/
def CValOk (s : Store H) (v : Val) (t : CValType) : Prop :=
  ∃ t' : ValType, t = .val t' ∧ ValOk s v t'

/-- A value stack typed by a `CResultType`; the pointwise lifting of `CValOk`. -/
abbrev ValsOk (s : Store H) (vs : List Val) (ts : CResultType) : Prop :=
  List.Forall₂ (CValOk s) vs ts

@[simp] theorem cRefOk_val {s : Store H} {r : Ref} {rt : RefType} :
    CRefOk s r (.val (.ref rt)) ↔ RefOk s r rt := by
  constructor
  · rintro ⟨rt', h, hr⟩
    cases h; exact hr
  · exact fun h => ⟨rt, rfl, h⟩

@[simp] theorem cValOk_val {s : Store H} {v : Val} {t : ValType} :
    CValOk s v (.val t) ↔ ValOk s v t := by
  constructor
  · rintro ⟨t', h, hv⟩
    cases h; exact hv
  · exact fun h => ⟨t, rfl, h⟩

@[simp] theorem cValOk_bot {s : Store H} {v : Val} : ¬ CValOk s v .bot := by
  rintro ⟨t, h, -⟩; cases h

@[simp] theorem cRefOk_bot {s : Store H} {r : Ref} : ¬ CRefOk s r .bot := by
  rintro ⟨t, h, -⟩; cases h

theorem CRefOk.toCValOk {s : Store H} {r : Ref} {t : CValType} (h : CRefOk s r t) :
    CValOk s (.ref r) t := by
  obtain ⟨rt, rfl, hr⟩ := h
  exact ⟨_, rfl, .ref hr⟩

/-- A stack typed by a lifted syntactic result type is typed by it pointwise. -/
theorem valsOk_liftResult {s : Store H} {vs : List Val} {ts : ResultType} :
    ValsOk s vs (liftResult ts) ↔ List.Forall₂ (ValOk s) vs ts := by
  constructor
  · intro h
    induction ts generalizing vs with
    | nil => cases h; exact List.Forall₂.nil
    | cons t ts ih =>
      cases h with
      | cons hv hvs => exact List.Forall₂.cons (cValOk_val.mp hv) (ih hvs)
  · intro h
    induction h with
    | nil => exact List.Forall₂.nil
    | cons hv _ ih => exact List.Forall₂.cons (cValOk_val.mpr hv) ih

/-! ### Principal types

Without subsumption the typing of a value is a *function* of the store. -/

/-- The type of a reference, when it has one: the only partiality is a dangling
function address. -/
def Ref.type? (s : Store H) : Ref → Option RefType
  | .null t => some t
  | .funcAddr a => (s.funcInst? a).map fun _ => .funcref
  | .hostAddr _ => some .externref

/-- The type of a value, when it has one. On the `num`/`vec` cases this agrees
with the store-independent `Val.type` (`Execution/Basic.lean`). -/
def Val.type? (s : Store H) : Val → Option ValType
  | .num v => some (.num v.type)
  | .vec _ => some (.vec .v128)
  | .ref r => (Ref.type? s r).map ValType.ref

/-- **Principal types, references.** `Ref_ok` holds at exactly one type. -/
theorem RefOk.eq_type? {s : Store H} {r : Ref} {rt : RefType} :
    RefOk s r rt ↔ Ref.type? s r = some rt := by
  constructor
  · intro h
    cases h with
    | null t => rfl
    | funcAddr h => simp [Ref.type?, h]
    | hostAddr a => rfl
  · intro h
    cases r with
    | null t => cases h; exact .null _
    | funcAddr a =>
      simp only [Ref.type?, Option.map_eq_some_iff] at h
      obtain ⟨fi, hfi, hrt⟩ := h
      cases hrt; exact .funcAddr hfi
    | hostAddr a => cases h; exact .hostAddr _

/-- **Principal types, values.** `Val_ok` holds at exactly one type. -/
theorem ValOk.eq_type? {s : Store H} {v : Val} {t : ValType} :
    ValOk s v t ↔ Val.type? s v = some t := by
  constructor
  · intro h
    cases h with
    | num v => rfl
    | vec b => rfl
    | ref h => simp [Val.type?, RefOk.eq_type?.mp h]
  · intro h
    cases v with
    | num v => cases h; exact .num _
    | vec b => cases h; exact .vec _
    | ref r =>
      simp only [Val.type?, Option.map_eq_some_iff] at h
      obtain ⟨rt, hrt, ht⟩ := h
      cases ht; exact .ref (RefOk.eq_type?.mpr hrt)

/-- Typing is deterministic. -/
theorem ValOk.det {s : Store H} {v : Val} {t t' : ValType} (h : ValOk s v t)
    (h' : ValOk s v t') : t = t' := by
  rw [ValOk.eq_type?] at h h'
  exact Option.some.inj (h.symm.trans h')

/-- Typing is deterministic. -/
theorem RefOk.det {s : Store H} {r : Ref} {rt rt' : RefType} (h : RefOk s r rt)
    (h' : RefOk s r rt') : rt = rt' := by
  rw [RefOk.eq_type?] at h h'
  exact Option.some.inj (h.symm.trans h')

/-- The store-independent `Val.type` of `Execution/Basic.lean` is the typing. -/
theorem ValOk.type_eq {s : Store H} {v : Val} {t : ValType} (h : ValOk s v t) : v.type = t := by
  cases h with
  | num v => rfl
  | vec b => rfl
  | ref h => cases h <;> rfl

/-- Every default value is typed, in every store (`$default_`, `5-runtime-aux`). -/
theorem valOk_defaultVal (s : Store H) (t : ValType) : ValOk s (defaultVal t) t := by
  cases t with
  | num t => cases t <;> exact .num _
  | vec t => cases t; exact .vec _
  | ref t => exact .ref (.null t)

/-! ## Instance typing (`7.1-soundness:95-133`) -/

/-- `Globalinst_ok` (`7.1-soundness:99`). -/
def GlobalInstOk (s : Store H) (gi : GlobalInst) : Prop :=
  GlobalType.Ok gi.type ∧ ValOk s gi.value gi.type.value

/-- `Meminst_ok` (`7.1-soundness:104`): the byte size is exactly the declared
minimum, in pages. -/
def MemInstOk (mi : MemInst) : Prop :=
  MemoryType.Ok mi.type ∧ mi.bytes.size = mi.type.limits.min.val * pageSize

/-- `Tableinst_ok` (`7.1-soundness:109`): the length is exactly the declared
minimum, and every entry has the element type. -/
def TableInstOk (s : Store H) (ti : TableInst) : Prop :=
  TableType.Ok ti.type ∧ ti.refs.length = ti.type.limits.min.val ∧
    ∀ r ∈ ti.refs, RefOk s r ti.type.element

/-- `Eleminst_ok` (`7.1-soundness:126`). `Reftype_ok` is vacuous in 2.0. -/
def ElemInstOk (s : Store H) (ei : ElemInst) : Prop :=
  ∀ r ∈ ei.refs, RefOk s r ei.type

/-- `Datainst_ok` (`7.1-soundness:123`): no premises. -/
def DataInstOk (_di : DataInst) : Prop := True

theorem dataInstOk (di : DataInst) : DataInstOk di := trivial

/-- `Exportinst_ok` (`7.1-soundness:131`). -/
def ExportInstOk (s : Store H) (xi : ExportInst) : Prop := ∃ xt, ExternAddrOk s xi.addr xt

/-- `Moduleinst_ok: s |- moduleinst : context` (`7.1-soundness:157`), the 2.0
instance. The realized context's `TYPES` are the instance's own function types,
its `FUNCS`/`GLOBALS`/`TABLES`/`MEMS` are the types of the instances the
addresses name, its `DATAS` records only the number of data segments
(`datatype = OK`, `1-syntax:177`), and `LOCALS`/`LABELS`/`RETURN` are empty:
a module instance realizes a *module-level* context. See the module docstring
for the `REFS` deviation. -/
inductive ModuleInstOk (s : Store H) : ModuleInst → Context → Prop where
  /-- `Moduleinst_ok`. -/
  | mk {mi : ModuleInst} {funcs : List FuncType} {globals : List GlobalType}
      {tables : List TableType} {mems : List MemoryType} {elems : List ElemType}
      {refs : List FuncIdx}
      (htypes : ∀ ft ∈ mi.types, FuncType.Ok ft)
      (hfuncs : List.Forall₂ (fun a ft => ExternAddrOk s (.func a) (.func ft)) mi.funcs funcs)
      (hglobals :
        List.Forall₂ (fun a gt => ExternAddrOk s (.global a) (.global gt)) mi.globals globals)
      (htables : List.Forall₂ (fun a tt => ExternAddrOk s (.table a) (.table tt)) mi.tables tables)
      (hmems : List.Forall₂ (fun a mt => ExternAddrOk s (.mem a) (.memory mt)) mi.mems mems)
      (helems : List.Forall₂ (fun a rt => ∃ ei, s.elemInst? a = some ei ∧ ElemInstOk s ei ∧
        ei.type = rt) mi.elems elems)
      (hdatas : ∀ a ∈ mi.datas, ∃ di, s.dataInst? a = some di)
      (hexports : ∀ xi ∈ mi.exports, ExportInstOk s xi)
      (hnames : (mi.exports.map ExportInst.name).Nodup)
      (hexportAddrs : ∀ xi ∈ mi.exports, xi.addr ∈ mi.funcs.map ExternAddr.func ++
        mi.globals.map ExternAddr.global ++ mi.tables.map ExternAddr.table ++
        mi.mems.map ExternAddr.mem)
      (hrefs : ∀ x ∈ refs, x.toNat < mi.funcs.length) :
      ModuleInstOk s mi
        { types := mi.types, funcs := funcs, globals := globals, tables := tables,
          mems := mems, elems := elems, datas := mi.datas.map fun _ => (), refs := refs }

theorem ModuleInstOk.types_eq {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) : C.types = mi.types := by cases h; rfl

theorem ModuleInstOk.locals_nil {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) : C.locals = [] := by cases h; rfl

theorem ModuleInstOk.labels_nil {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) : C.labels = [] := by cases h; rfl

theorem ModuleInstOk.return_none {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) : C.return_ = none := by cases h; rfl

theorem ModuleInstOk.funcs_length {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) : C.funcs.length = mi.funcs.length := by
  cases h with | mk _ hfuncs => exact hfuncs.length_eq.symm

theorem ModuleInstOk.globals_length {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) : C.globals.length = mi.globals.length := by
  cases h with | mk _ _ hglobals => exact hglobals.length_eq.symm

theorem ModuleInstOk.tables_length {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) : C.tables.length = mi.tables.length := by
  cases h with | mk _ _ _ htables => exact htables.length_eq.symm

theorem ModuleInstOk.mems_length {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) : C.mems.length = mi.mems.length := by
  cases h with | mk _ _ _ _ hmems => exact hmems.length_eq.symm

theorem ModuleInstOk.elems_length {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) : C.elems.length = mi.elems.length := by
  cases h with | mk _ _ _ _ _ helems => exact helems.length_eq.symm

theorem ModuleInstOk.datas_length {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) : C.datas.length = mi.datas.length := by
  cases h; exact List.length_map _

/-- `Funcinst_ok` (`7.1-soundness:115`), plus the host-function rule; see the
module docstring. In 2.0 `Functype_sub` is equality (`6-typing:105`), so the
code is checked at the instance's own type with no subsumption step. -/
inductive FuncInstOk (s : Store H) : FuncInst H → Prop where
  /-- `Funcinst_ok`: the code is a well-typed 2.0 function under a context the
  function's module instance realizes. -/
  | wasm {fi : FuncInst H} {C : Context} {code : Func}
      (hok : FuncType.Ok fi.type) (hm : ModuleInstOk s fi.module C)
      (hcode : fi.code = .wasm code) (hf : FuncOk C code fi.type) : FuncInstOk s fi
  /-- Host functions (deviation): only the declared type is constrained. -/
  | host {fi : FuncInst H} {h : H} (hok : FuncType.Ok fi.type) (hcode : fi.code = .host h) :
      FuncInstOk s fi

/-- `Store_ok` (`7.1-soundness:202`), one premise per instance list. -/
structure StoreOk (s : Store H) : Prop where
  /-- `(Funcinst_ok: s |- funcinst : functype)*`. -/
  funcs : ∀ fi ∈ s.funcs, FuncInstOk s fi
  /-- `(Globalinst_ok: s |- globalinst : globaltype)*`. -/
  globals : ∀ gi ∈ s.globals, GlobalInstOk s gi
  /-- `(Tableinst_ok: s |- tableinst : tabletype)*`. -/
  tables : ∀ ti ∈ s.tables, TableInstOk s ti
  /-- `(Meminst_ok: s |- meminst : memtype)*`. -/
  mems : ∀ mi ∈ s.mems, MemInstOk mi
  /-- `(Eleminst_ok: s |- eleminst : elemtype)*`. -/
  elems : ∀ ei ∈ s.elems, ElemInstOk s ei
  /-- `(Datainst_ok: s |- datainst : OK)*`. -/
  datas : ∀ di ∈ s.datas, DataInstOk di

/-! ## Store extension (`Extend_*`, `7.1-soundness:264-333`) -/

/-- Pointwise extension of a list of instances: new instances may be appended at
the end, and the ones already there evolve along `R`. This is SpecTec's
`(Extend_xinst: s.XS[a] `<= s'.XS[a])^(a<|s.XS|)` (`7.1-soundness:317`). -/
def ExtendsList {α : Type} (R : α → α → Prop) (l l' : List α) : Prop :=
  l.length ≤ l'.length ∧ ∀ (i : Nat) x, l[i]? = some x → ∃ y, l'[i]? = some y ∧ R x y

/-- `Extend_funcinst` (`7.1-soundness:292`): a function instance never changes.
2.0 has no instruction that writes `s.FUNCS`. -/
def ExtendFunc (a b : FuncInst H) : Prop := a = b

/-- `Extend_globalinst` (`7.1-soundness:278`): the type is fixed; the value may
change only if the global is mutable. -/
def ExtendGlobal (a b : GlobalInst) : Prop :=
  a.type = b.type ∧ (a.type.mutability = .var ∨ a.value = b.value)

/-- `Extend_tableinst` (`7.1-soundness:287`): the element type and the maximum
are fixed, while the minimum and the length may only grow. The W3C 2.0 appendix
fixes the *whole* type here; see the **Deviation (`ExtendTable`/`ExtendMem`)**
paragraph in the module docstring for why that reading is inconsistent with the
appendix's own store-validity and `growtable` rules. -/
def ExtendTable (a b : TableInst) : Prop :=
  a.type.element = b.type.element ∧ a.type.limits.max = b.type.limits.max ∧
    a.type.limits.min.val ≤ b.type.limits.min.val ∧ a.refs.length ≤ b.refs.length

/-- `Extend_meminst` (`7.1-soundness:282`): the maximum is fixed, the minimum
and the byte size may only grow; same deviation from the W3C 2.0 appendix as
`ExtendTable`. -/
def ExtendMem (a b : MemInst) : Prop :=
  a.type.limits.max = b.type.limits.max ∧
    a.type.limits.min.val ≤ b.type.limits.min.val ∧ a.bytes.size ≤ b.bytes.size

/-- `Extend_eleminst` (`7.1-soundness:299`): the type is fixed and the segment
may only be dropped wholesale (`elem.drop`, `8-reduction:483`). -/
def ExtendElem (a b : ElemInst) : Prop := a.type = b.type ∧ (a.refs = b.refs ∨ b.refs = [])

/-- `Extend_datainst` (`7.1-soundness:295`): the segment may only be dropped
wholesale (`data.drop`, `8-reduction:663`). -/
def ExtendData (a b : DataInst) : Prop := a = b ∨ b.bytes = ByteArray.empty

/-- `Extend_store: s `<= s'` (`7.1-soundness:317`), the 2.0 instance: six
components, no tags, no structs, no arrays, no exceptions. -/
structure Extend (s s' : Store H) : Prop where
  /-- `(Extend_funcinst: s.FUNCS[a] `<= s'.FUNCS[a])^(a<|s.FUNCS|)`. -/
  funcs : ExtendsList ExtendFunc s.funcs s'.funcs
  /-- `(Extend_globalinst: …)`. -/
  globals : ExtendsList ExtendGlobal s.globals s'.globals
  /-- `(Extend_tableinst: …)`. -/
  tables : ExtendsList ExtendTable s.tables s'.tables
  /-- `(Extend_meminst: …)`. -/
  mems : ExtendsList ExtendMem s.mems s'.mems
  /-- `(Extend_eleminst: …)`. -/
  elems : ExtendsList ExtendElem s.elems s'.elems
  /-- `(Extend_datainst: …)`. -/
  datas : ExtendsList ExtendData s.datas s'.datas

/-! ### Reflexivity, transitivity and the lookup accessors -/

theorem ExtendsList.refl_of {α : Type} {R : α → α → Prop} {l : List α} (h : ∀ x ∈ l, R x x) :
    ExtendsList R l l :=
  ⟨Nat.le_refl _, fun _ x hx => ⟨x, hx, h x (List.mem_of_getElem? hx)⟩⟩

theorem ExtendsList.trans_of {α : Type} {R : α → α → Prop} {l₁ l₂ l₃ : List α}
    (hR : ∀ x y z, R x y → R y z → R x z)
    (h₁ : ExtendsList R l₁ l₂) (h₂ : ExtendsList R l₂ l₃) : ExtendsList R l₁ l₃ := by
  refine ⟨Nat.le_trans h₁.1 h₂.1, fun i x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := h₁.2 i x hx
  obtain ⟨z, hz, hyz⟩ := h₂.2 i y hy
  exact ⟨z, hz, hR _ _ _ hxy hyz⟩

theorem ExtendsList.get {α : Type} {R : α → α → Prop} {l l' : List α} (h : ExtendsList R l l')
    {i : Nat} {x : α} (hx : l[i]? = some x) : ∃ y, l'[i]? = some y ∧ R x y := h.2 i x hx

theorem ExtendsList.length_le {α : Type} {R : α → α → Prop} {l l' : List α}
    (h : ExtendsList R l l') : l.length ≤ l'.length := h.1

/-- Reflexivity of store extension. **Unconditional**, unlike Core 3.0's: see
the module docstring. -/
theorem Extend.refl (s : Store H) : Extend s s where
  funcs := ExtendsList.refl_of fun _ _ => rfl
  globals := ExtendsList.refl_of fun _ _ => ⟨rfl, .inr rfl⟩
  tables := ExtendsList.refl_of fun _ _ => ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
  mems := ExtendsList.refl_of fun _ _ => ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩
  elems := ExtendsList.refl_of fun _ _ => ⟨rfl, .inl rfl⟩
  datas := ExtendsList.refl_of fun _ _ => .inl rfl

theorem Extend.trans {s₁ s₂ s₃ : Store H} (h₁ : Extend s₁ s₂) (h₂ : Extend s₂ s₃) :
    Extend s₁ s₃ where
  funcs := ExtendsList.trans_of (fun _ _ _ h h' => h.trans h') h₁.funcs h₂.funcs
  globals := ExtendsList.trans_of (fun _ _ _ h h' => ⟨h.1.trans h'.1, by
      rcases h.2 with hv | hv
      · exact .inl hv
      · rcases h'.2 with hv' | hv'
        · exact .inl (by rw [h.1]; exact hv')
        · exact .inr (hv.trans hv')⟩) h₁.globals h₂.globals
  tables := ExtendsList.trans_of (fun _ _ _ h h' => ⟨h.1.trans h'.1, h.2.1.trans h'.2.1,
      Nat.le_trans h.2.2.1 h'.2.2.1, Nat.le_trans h.2.2.2 h'.2.2.2⟩) h₁.tables h₂.tables
  mems := ExtendsList.trans_of (fun _ _ _ h h' => ⟨h.1.trans h'.1,
      Nat.le_trans h.2.1 h'.2.1, Nat.le_trans h.2.2 h'.2.2⟩) h₁.mems h₂.mems
  elems := ExtendsList.trans_of (fun _ _ _ h h' => ⟨h.1.trans h'.1, by
      rcases h'.2 with hr | hr
      · rw [← hr]; exact h.2
      · exact .inr hr⟩) h₁.elems h₂.elems
  datas := ExtendsList.trans_of (fun _ _ _ h h' => by
      rcases h' with rfl | hc
      · exact h
      · exact .inr hc) h₁.datas h₂.datas

/-- Function instances survive extension unchanged. -/
theorem Extend.funcInst? {s s' : Store H} (he : Extend s s') {a : FuncAddr} {fi : FuncInst H}
    (h : s.funcInst? a = some fi) : s'.funcInst? a = some fi := by
  obtain ⟨fi', h', hx⟩ := he.funcs.get (show s.funcs[a]? = some fi from h)
  exact hx ▸ h'

theorem Extend.globalInst? {s s' : Store H} (he : Extend s s') {a : GlobalAddr} {gi : GlobalInst}
    (h : s.globalInst? a = some gi) :
    ∃ gi', s'.globalInst? a = some gi' ∧ ExtendGlobal gi gi' :=
  he.globals.get (show s.globals[a]? = some gi from h)

theorem Extend.tableInst? {s s' : Store H} (he : Extend s s') {a : TableAddr} {ti : TableInst}
    (h : s.tableInst? a = some ti) :
    ∃ ti', s'.tableInst? a = some ti' ∧ ExtendTable ti ti' :=
  he.tables.get (show s.tables[a]? = some ti from h)

theorem Extend.memInst? {s s' : Store H} (he : Extend s s') {a : MemAddr} {mi : MemInst}
    (h : s.memInst? a = some mi) :
    ∃ mi', s'.memInst? a = some mi' ∧ ExtendMem mi mi' :=
  he.mems.get (show s.mems[a]? = some mi from h)

theorem Extend.elemInst? {s s' : Store H} (he : Extend s s') {a : ElemAddr} {ei : ElemInst}
    (h : s.elemInst? a = some ei) :
    ∃ ei', s'.elemInst? a = some ei' ∧ ExtendElem ei ei' :=
  he.elems.get (show s.elems[a]? = some ei from h)

theorem Extend.dataInst? {s s' : Store H} (he : Extend s s') {a : DataAddr} {di : DataInst}
    (h : s.dataInst? a = some di) :
    ∃ di', s'.dataInst? a = some di' ∧ ExtendData di di' :=
  he.datas.get (show s.datas[a]? = some di from h)

/-! ### Monotonicity -/

/-- Reference typing is stable under store extension. -/
theorem RefOk.extend {s s' : Store H} {r : Ref} {rt : RefType} (he : Extend s s')
    (h : RefOk s r rt) : RefOk s' r rt := by
  cases h with
  | null => exact .null _
  | funcAddr h => exact .funcAddr (he.funcInst? h)
  | hostAddr a => exact .hostAddr a

/-- Value typing is stable under store extension. -/
theorem ValOk.extend {s s' : Store H} {v : Val} {t : ValType} (he : Extend s s')
    (h : ValOk s v t) : ValOk s' v t := by
  cases h with
  | num v => exact .num v
  | vec b => exact .vec b
  | ref h => exact .ref (h.extend he)

theorem CRefOk.extend {s s' : Store H} {r : Ref} {t : CValType} (he : Extend s s')
    (h : CRefOk s r t) : CRefOk s' r t := by
  obtain ⟨rt, rfl, hr⟩ := h
  exact ⟨rt, rfl, hr.extend he⟩

theorem CValOk.extend {s s' : Store H} {v : Val} {t : CValType} (he : Extend s s')
    (h : CValOk s v t) : CValOk s' v t := by
  obtain ⟨t', rfl, hv⟩ := h
  exact ⟨t', rfl, hv.extend he⟩

theorem ValsOk.extend {s s' : Store H} {vs : List Val} {ts : CResultType} (he : Extend s s')
    (h : ValsOk s vs ts) : ValsOk s' vs ts :=
  h.imp fun _ _ h => h.extend he

theorem ValOk.forall₂_extend {s s' : Store H} {vs : List Val} {ts : List ValType}
    (he : Extend s s') (h : List.Forall₂ (ValOk s) vs ts) : List.Forall₂ (ValOk s') vs ts :=
  h.imp fun _ _ h => h.extend he

/-- Growing a table or a memory produces a subtype of its old type
(`Limits_sub/max` and `/eps`, `6-typing:95-102`). -/
theorem Limits.sub_of_grow {l l' : Limits} (hmax : l.max = l'.max)
    (hmin : l.min.val ≤ l'.min.val) : Limits.Sub l' l := by
  rw [Limits.sub_iff]
  refine ⟨hmin, fun m₂ hm₂ => ⟨m₂, ?_, Nat.le_refl _⟩⟩
  rw [← hmax]; exact hm₂

/-- An external address stays typed after store extension. Tables and memories
may grow, so the old type is recovered by subsumption, which needs its validity
— hence `StoreOk s`. -/
theorem ExternAddrOk.extend {s s' : Store H} {xa : ExternAddr} {xt : ExternType}
    (hs : StoreOk s) (he : Extend s s') (h : ExternAddrOk s xa xt) : ExternAddrOk s' xa xt := by
  induction h with
  | func h => exact .func (he.funcInst? h)
  | global h =>
    obtain ⟨gi', h', hx, -⟩ := he.globalInst? h
    exact hx ▸ ExternAddrOk.global h'
  | @table a ti h =>
    obtain ⟨ti', h', hel, hmax, hmin, -⟩ := he.tableInst? h
    refine .sub (.table h') (hs.tables ti (List.mem_of_getElem? h)).1 (.table ⟨?_, hel.symm⟩)
    exact Limits.sub_of_grow hmax hmin
  | @mem a mi h =>
    obtain ⟨mi', h', hmax, hmin, -⟩ := he.memInst? h
    refine .sub (.mem h') (hs.mems mi (List.mem_of_getElem? h)).1 (.memory ?_)
    exact Limits.sub_of_grow hmax hmin
  | sub _ hok hsub ih => exact .sub ih hok hsub

/-- The address of a typed external address still names an instance after
extension (with a possibly different, but always existing, type). -/
theorem ExternAddrOk.exists_type {s s' : Store H} {xa : ExternAddr} {xt : ExternType}
    (he : Extend s s') (h : ExternAddrOk s xa xt) : ∃ xt', ExternAddrOk s' xa xt' := by
  induction h with
  | func h => exact ⟨_, .func (he.funcInst? h)⟩
  | global h => obtain ⟨_, h', -⟩ := he.globalInst? h; exact ⟨_, .global h'⟩
  | table h => obtain ⟨_, h', -⟩ := he.tableInst? h; exact ⟨_, .table h'⟩
  | mem h => obtain ⟨_, h', -⟩ := he.memInst? h; exact ⟨_, .mem h'⟩
  | sub _ _ _ ih => exact ih

/-- Element-segment typing is stable under store extension *and* under the
segment's own evolution: a dropped segment is empty, hence trivially typed. -/
theorem ElemInstOk.extend {s s' : Store H} {ei ei' : ElemInst} (he : Extend s s')
    (hx : ExtendElem ei ei') (h : ElemInstOk s ei) : ElemInstOk s' ei' := by
  obtain ⟨ht, hr⟩ := hx
  intro r hr'
  rw [← ht]
  rcases hr with hrs | hrs
  · rw [← hrs] at hr'; exact (h r hr').extend he
  · rw [hrs] at hr'; cases hr'

/-- Module instances stay typed after store extension, at the **same** context. -/
theorem ModuleInstOk.extend {s s' : Store H} {mi : ModuleInst} {C : Context} (hs : StoreOk s)
    (he : Extend s s') (h : ModuleInstOk s mi C) : ModuleInstOk s' mi C := by
  cases h with
  | mk htypes hfuncs hglobals htables hmems helems hdatas hexports hnames hexportAddrs hrefs =>
    refine .mk htypes (hfuncs.imp fun _ _ h => h.extend hs he)
      (hglobals.imp fun _ _ h => h.extend hs he) (htables.imp fun _ _ h => h.extend hs he)
      (hmems.imp fun _ _ h => h.extend hs he) (helems.imp fun _ _ h => ?_) (fun a ha => ?_)
      (fun xi hxi => ?_) hnames hexportAddrs hrefs
    · obtain ⟨ei, hei, hok, rfl⟩ := h
      obtain ⟨ei', h', hxe⟩ := he.elemInst? hei
      exact ⟨ei', h', hok.extend he hxe, hxe.1.symm⟩
    · obtain ⟨di, hdi⟩ := hdatas a ha
      obtain ⟨di', h', -⟩ := he.dataInst? hdi
      exact ⟨di', h'⟩
    · obtain ⟨xt, hxt⟩ := hexports xi hxi
      exact hxt.exists_type he

/-- Export-instance typing is stable under store extension (at a possibly
different external type — a table or memory may have grown). -/
theorem ExportInstOk.extend {s s' : Store H} {xi : ExportInst} (he : Extend s s')
    (h : ExportInstOk s xi) : ExportInstOk s' xi := by
  obtain ⟨xt, hxt⟩ := h
  exact hxt.exists_type he

/-- Global-instance typing is stable under store extension. -/
theorem GlobalInstOk.extend {s s' : Store H} {gi : GlobalInst} (he : Extend s s')
    (h : GlobalInstOk s gi) : GlobalInstOk s' gi :=
  ⟨h.1, h.2.extend he⟩

/-- Table-instance typing is stable under store extension, for the instance's
own (unchanged) contents. -/
theorem TableInstOk.extend {s s' : Store H} {ti : TableInst} (he : Extend s s')
    (h : TableInstOk s ti) : TableInstOk s' ti :=
  ⟨h.1, h.2.1, fun r hr => (h.2.2 r hr).extend he⟩

/-- Function-instance typing is stable under store extension. -/
theorem FuncInstOk.extend {s s' : Store H} {fi : FuncInst H} (hs : StoreOk s) (he : Extend s s')
    (h : FuncInstOk s fi) : FuncInstOk s' fi := by
  cases h with
  | wasm hok hm hcode hf => exact .wasm hok (hm.extend hs he) hcode hf
  | host hok hcode => exact .host hok hcode

end Silmaril.Wasm.V2.Execution
