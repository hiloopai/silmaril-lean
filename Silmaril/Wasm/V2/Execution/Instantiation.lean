module

public import Silmaril.Wasm.V2.Execution.Step
public import Silmaril.Wasm.V2.Validation.Modules

/-!
# WebAssembly 2.0 allocation, instantiation and invocation

Transcribed from the official SpecTec source
`specification/wasm-2.0/9-module.spectec` (the whole file) at WebAssembly/spec
revision `608711107b7f1edb13efd57b7d79b49477462d36` (see
`specs/wasm/core-2.0.json`). Line references of the form `9-module:NN` point
into that file.

The layout follows `Silmaril.Wasm.Execution.Core.Instantiation`, which does the
same job for Core 3.0, adapted down: 2.0 has no recursive or defined types, so
there is no `$alloctypes` and no substitution; `moduleinst.TYPES` is literally
the module's type section.

| SpecTec | Lean |
| --- | --- |
| `$funcs`, `$globals`, `$tables`, `$mems` (`9-module:5-27`) | `ExternAddr.funcs`, … (in `Basic.lean`) |
| `$allocfunc`, `$allocglobal`, `$alloctable`, `$allocmem`, `$allocelem`, `$allocdata` | `allocFunc`, … |
| `$allocfuncs`, … (`9-module:41-95`) | `allocFuncs`, …, all via `allocMany` |
| `$instexport` (`9-module:100-104`) | `instExport?` |
| `$allocmodule` (`9-module:107-147`) | `allocModule?` |
| `$runelem`, `$rundata` (`9-module:154-165`) | `runElem`, `runData` |
| `$instantiate` (`9-module:167-189`) | `Instantiate` |
| `$invoke` (`9-module:196-199`) | `invoke`, `InvokeOk` |

## The projections are already in `Basic.lean`

`$funcs`/`$globals`/`$tables`/`$mems` on `externaddr*` (`9-module:5-27`) are
*character for character* `$funcsxa`/`$globalsxa`/`$tablesxa`/`$memsxa`
(`5-runtime-aux:25-37`), which `Silmaril.Wasm.V2.Execution.Basic` already
transcribes as `ExternAddr.funcs`, `ExternAddr.globals`, `ExternAddr.tables`
and `ExternAddr.mems`. They are not duplicated here; only the four `append`
lemmas the allocation proofs need are added below.

## Partiality

`$allocfunc` reads `moduleinst.TYPES[x]`, and `$instexport` reads `fa*[x]`,
`ga*[x]`, `ta*[x]`, `ma*[x]`; all four indexings are partial. As everywhere else
in this layer the partiality is made explicit: `allocModule?` is `Option`-valued
and is `none` exactly where SpecTec's equation has no instance. A valid module
never gets there.

## The allocation knot (`9-module:107-147`)

`$allocmodule` is mutually referential: each `funcinst` records the
`moduleinst`, and the `moduleinst` records the `funcaddr`s of those `funcinst`s.
SpecTec unties the knot by *predicting* the addresses —

```
  -- if fa* = $(|s.FUNCS|+i_func)^(i_func<n_func)
  …
  -- if moduleinst = { TYPES ft*, FUNCS fa_ex* fa*, … }
  -- if (s_1, fa*) = $allocfuncs(s, moduleinst, func^n_func)
```

— and then *asserting*, in the last six premises, that the allocators really do
return those addresses. `allocModule?` reproduces exactly this: it builds the
module instance from the predicted address ranges and then runs the allocators.
`allocModule?_spec` below is the assertion, discharged as a theorem: the
predicted lists are the lists `allocFuncs`, `allocGlobals`, `allocTables`,
`allocMems`, `allocElems` and `allocDatas` produce.

## `$rundata` and the memory index

**Deviation.** `$rundata` (`9-module:161-165`) is defined only on
`DATA byte* (PASSIVE)` and `DATA byte* (ACTIVE 0 instr*)`: the memory index is
the *literal* `0`, so `$rundata` is undefined on an active segment naming any
other memory. `runData` below accepts any `MemIdx` and ignores it, emitting
`MEMORY.INIT i` (2.0's `memory.init` has no memory immediate at all,
`1-syntax:518`). This changes nothing on modules SpecTec defines `$rundata`
for: `Datamode_ok/active` (`6-typing:632`) carries the premise `x = 0`
(transcribed as `Silmaril.Wasm.V2.Validation.DataModeOk.active`'s `hx`), so a
valid module's active data segments all name memory `0` — `DataOk.active_zero`
below is that statement, proved. The reference interpreter agrees: `decode.ml`
reads the reserved `0x00` byte for data kind `2` and `valid.ml` checks
`memory c x` against the single memory.

## What `$instantiate` does *not* check

**Note (not a deviation).** `$instantiate` (`9-module:167-189`) has **no**
premise relating `externaddr*` to the module's imports — neither a validity
premise `|- module : xt_I* -> xt_E*` nor an import-matching premise. In the W3C
2.0 text that check belongs to the embedder (`exec/modules.rst`, step 2 of
"Instantiation": "assert: module is valid" and "If the number/types of externvals
do not match, fail"). Core 3.0's `Instantiate` carries the check as a field
anyway, because type soundness needs it, and so does `Instantiate` here, via
`ExternAddrOk`, which is the 2.0 analogue of 3.0's `Externaddr_ok` built on
`ExternType.Sub` (`6-typing:120-134`). SpecTec 2.0 has no `Externaddr_ok`
relation at all: it has no store typing.

## `$invoke` and the 2019-era defect

`$invoke` (`9-module:196-199`) is

```
def $invoke(s, fa, val^n) = s; f; val^n (CALL_ADDR fa)
  -- if $funcinst((s; f))[fa].TYPE = t_1^n -> t_2*
```

The premise ties the *number* of arguments to the number of parameters but says
nothing about their *types*. The W3C 2.0 text
(`exec/modules.rst`, "Invocation", step 5) says "For each value type `t_i` …
assert: the value `val_i` is of type `t_i`". `InvokeOk` below states **both**
premises, the arity and the argument types, and additionally the one
store-dependent well-formedness condition on arguments (a `REF.FUNC_ADDR` must
be allocated) that a value-typing judgment would carry; 2.0 has no store typing
to hang it on, so it is inlined here rather than pre-empting the naming of a
later soundness unit.
-/

@[expose] public section

namespace Silmaril.Wasm.V2.Execution

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Memory (Bytes pageSize)
open Silmaril.Wasm.V2.Validation (Context ModuleOk DataOk DataModeOk)

variable {H : Type}

/-! ## Projections on `externaddr*` (`9-module:5-27`)

The four definitions are `ExternAddr.funcs`, `ExternAddr.globals`,
`ExternAddr.tables` and `ExternAddr.mems` of `Basic.lean`; see the module
docstring. Only the `append` lemmas are new. -/

@[simp] theorem ExternAddr.funcs_append (xs ys : List ExternAddr) :
    ExternAddr.funcs (xs ++ ys) = ExternAddr.funcs xs ++ ExternAddr.funcs ys :=
  List.filterMap_append

@[simp] theorem ExternAddr.globals_append (xs ys : List ExternAddr) :
    ExternAddr.globals (xs ++ ys) = ExternAddr.globals xs ++ ExternAddr.globals ys :=
  List.filterMap_append

@[simp] theorem ExternAddr.tables_append (xs ys : List ExternAddr) :
    ExternAddr.tables (xs ++ ys) = ExternAddr.tables xs ++ ExternAddr.tables ys :=
  List.filterMap_append

@[simp] theorem ExternAddr.mems_append (xs ys : List ExternAddr) :
    ExternAddr.mems (xs ++ ys) = ExternAddr.mems xs ++ ExternAddr.mems ys :=
  List.filterMap_append

/-! ## Allocation of single instances (`9-module:36-95`)

Each `$alloc*` appends one instance to its store component and returns the old
length as the fresh address. -/

/-- `$allocfunc(s, moduleinst, func)` (`9-module:36`). SpecTec reads the
function's type out of `moduleinst.TYPES[x]`, which is partial; the resolved
`functype` is taken as an argument here and the lookup is done once, in
`allocModule?`. The `code` argument is `FuncCode H` rather than `func` because
of the host-function deviation recorded in `Basic.lean`. -/
def allocFunc (s : Store H) (ft : FuncType) (mi : ModuleInst) (code : FuncCode H) :
    Store H × FuncAddr :=
  ({ s with funcs := s.funcs ++ [⟨ft, mi, code⟩] }, s.funcs.length)

/-- `$allocglobal(s, globaltype, val)` (`9-module:47`). -/
def allocGlobal (s : Store H) (gt : GlobalType) (v : Val) : Store H × GlobalAddr :=
  ({ s with globals := s.globals ++ [⟨gt, v⟩] }, s.globals.length)

/-- `$alloctable(s, `[i .. j?] rt)` (`9-module:57`): the table starts out with
`i` null references of its own element type. -/
def allocTable (s : Store H) (tt : TableType) : Store H × TableAddr :=
  ({ s with tables := s.tables ++ [⟨tt, List.replicate tt.limits.min.val (.null tt.element)⟩] },
    s.tables.length)

/-- `$allocmem(s, `[i .. j?] PAGE)` (`9-module:67`): `i` zeroed pages of
`64 * $Ki` bytes. -/
def allocMem (s : Store H) (mt : MemoryType) : Store H × MemAddr :=
  ({ s with mems := s.mems ++ [⟨mt, ⟨Array.replicate (mt.limits.min.val * pageSize) 0⟩⟩] },
    s.mems.length)

/-- `$allocelem(s, rt, ref*)` (`9-module:77`). -/
def allocElem (s : Store H) (rt : ElemType) (refs : List Ref) : Store H × ElemAddr :=
  ({ s with elems := s.elems ++ [⟨rt, refs⟩] }, s.elems.length)

/-- `$allocdata(s, byte*)` (`9-module:87`). -/
def allocData (s : Store H) (bs : Bytes) : Store H × DataAddr :=
  ({ s with datas := s.datas ++ [⟨bs⟩] }, s.datas.length)

/-! ## Allocation of sequences (`9-module:41-95`)

Every `$alloc*s` is the same fold: allocate the head, thread the store, allocate
the tail. -/

/-- The common shape of `$allocfuncs`, `$allocglobals`, `$alloctables`,
`$allocmems`, `$allocelems` and `$allocdatas`. -/
def allocMany {α : Type} (alloc : Store H → α → Store H × Addr) :
    Store H → List α → Store H × List Addr
  | s, [] => (s, [])
  | s, x :: xs =>
    ((allocMany alloc (alloc s x).1 xs).1, (alloc s x).2 :: (allocMany alloc (alloc s x).1 xs).2)

/-- `$allocfuncs(s, moduleinst, func*)` (`9-module:41`). -/
def allocFuncs (s : Store H) (mi : ModuleInst) (fs : List (FuncType × Func)) :
    Store H × List FuncAddr :=
  allocMany (fun s p => allocFunc s p.1 mi (.wasm p.2)) s fs

/-- `$allocglobals(s, globaltype*, val*)` (`9-module:51`). -/
def allocGlobals (s : Store H) (gs : List (GlobalType × Val)) : Store H × List GlobalAddr :=
  allocMany (fun s p => allocGlobal s p.1 p.2) s gs

/-- `$alloctables(s, tabletype*)` (`9-module:61`). -/
def allocTables (s : Store H) (ts : List TableType) : Store H × List TableAddr :=
  allocMany allocTable s ts

/-- `$allocmems(s, memtype*)` (`9-module:71`). -/
def allocMems (s : Store H) (ts : List MemoryType) : Store H × List MemAddr :=
  allocMany allocMem s ts

/-- `$allocelems(s, reftype*, (ref*)*)` (`9-module:81`). -/
def allocElems (s : Store H) (es : List (ElemType × List Ref)) : Store H × List ElemAddr :=
  allocMany (fun s p => allocElem s p.1 p.2) s es

/-- `$allocdatas(s, (byte*)*)` (`9-module:91`). -/
def allocDatas (s : Store H) (bs : List Bytes) : Store H × List DataAddr :=
  allocMany allocData s bs

/-! ### Which addresses the allocators produce -/

/-- An allocation that leaves a store component `F` alone leaves it alone for a
whole sequence. -/
theorem allocMany_fst {α β : Type} {alloc : Store H → α → Store H × Addr} (F : Store H → β)
    (hF : ∀ (s : Store H) (x : α), F (alloc s x).1 = F s) :
    ∀ (s : Store H) (xs : List α), F (allocMany alloc s xs).1 = F s := by
  intro s xs
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact (ih (alloc s x).1).trans (hF s x)

/-- The addresses an allocation sequence returns are consecutive, starting at the
size of the store component it allocates into. This is what makes the prediction
in `$allocmodule` (`9-module:125-130`) correct. -/
theorem allocMany_snd {α : Type} {alloc : Store H → α → Store H × Addr} (size : Store H → Nat)
    (haddr : ∀ (s : Store H) (x : α), (alloc s x).2 = size s)
    (hsize : ∀ (s : Store H) (x : α), size (alloc s x).1 = size s + 1) :
    ∀ (s : Store H) (xs : List α),
      (allocMany alloc s xs).2 = (List.range xs.length).map (size s + ·) := by
  intro s xs
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    show (alloc s x).2 :: (allocMany alloc (alloc s x).1 xs).2 = _
    rw [haddr, ih, hsize, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp [Function.comp_def, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem allocFuncs_snd (s : Store H) (mi : ModuleInst) (fs : List (FuncType × Func)) :
    (allocFuncs s mi fs).2 = (List.range fs.length).map (s.funcs.length + ·) :=
  allocMany_snd (fun s => s.funcs.length) (fun _ _ => rfl) (fun _ _ => by simp [allocFunc]) s fs

@[simp] theorem allocGlobals_snd (s : Store H) (gs : List (GlobalType × Val)) :
    (allocGlobals s gs).2 = (List.range gs.length).map (s.globals.length + ·) :=
  allocMany_snd (fun s => s.globals.length) (fun _ _ => rfl) (fun _ _ => by simp [allocGlobal]) s gs

@[simp] theorem allocTables_snd (s : Store H) (ts : List TableType) :
    (allocTables s ts).2 = (List.range ts.length).map (s.tables.length + ·) :=
  allocMany_snd (fun s => s.tables.length) (fun _ _ => rfl) (fun _ _ => by simp [allocTable]) s ts

@[simp] theorem allocMems_snd (s : Store H) (ts : List MemoryType) :
    (allocMems s ts).2 = (List.range ts.length).map (s.mems.length + ·) :=
  allocMany_snd (fun s => s.mems.length) (fun _ _ => rfl) (fun _ _ => by simp [allocMem]) s ts

@[simp] theorem allocElems_snd (s : Store H) (es : List (ElemType × List Ref)) :
    (allocElems s es).2 = (List.range es.length).map (s.elems.length + ·) :=
  allocMany_snd (fun s => s.elems.length) (fun _ _ => rfl) (fun _ _ => by simp [allocElem]) s es

@[simp] theorem allocDatas_snd (s : Store H) (bs : List Bytes) :
    (allocDatas s bs).2 = (List.range bs.length).map (s.datas.length + ·) :=
  allocMany_snd (fun s => s.datas.length) (fun _ _ => rfl) (fun _ _ => by simp [allocData]) s bs

/-! Each allocator touches only its own store component. -/

@[simp] theorem allocFuncs_fst_globals (s : Store H) (mi : ModuleInst)
    (fs : List (FuncType × Func)) : (allocFuncs s mi fs).1.globals = s.globals :=
  allocMany_fst (fun s => s.globals) (fun _ _ => rfl) s fs

@[simp] theorem allocFuncs_fst_tables (s : Store H) (mi : ModuleInst)
    (fs : List (FuncType × Func)) : (allocFuncs s mi fs).1.tables = s.tables :=
  allocMany_fst (fun s => s.tables) (fun _ _ => rfl) s fs

@[simp] theorem allocFuncs_fst_mems (s : Store H) (mi : ModuleInst)
    (fs : List (FuncType × Func)) : (allocFuncs s mi fs).1.mems = s.mems :=
  allocMany_fst (fun s => s.mems) (fun _ _ => rfl) s fs

@[simp] theorem allocFuncs_fst_elems (s : Store H) (mi : ModuleInst)
    (fs : List (FuncType × Func)) : (allocFuncs s mi fs).1.elems = s.elems :=
  allocMany_fst (fun s => s.elems) (fun _ _ => rfl) s fs

@[simp] theorem allocFuncs_fst_datas (s : Store H) (mi : ModuleInst)
    (fs : List (FuncType × Func)) : (allocFuncs s mi fs).1.datas = s.datas :=
  allocMany_fst (fun s => s.datas) (fun _ _ => rfl) s fs

@[simp] theorem allocGlobals_fst_tables (s : Store H) (gs : List (GlobalType × Val)) :
    (allocGlobals s gs).1.tables = s.tables :=
  allocMany_fst (fun s => s.tables) (fun _ _ => rfl) s gs

@[simp] theorem allocGlobals_fst_mems (s : Store H) (gs : List (GlobalType × Val)) :
    (allocGlobals s gs).1.mems = s.mems :=
  allocMany_fst (fun s => s.mems) (fun _ _ => rfl) s gs

@[simp] theorem allocGlobals_fst_elems (s : Store H) (gs : List (GlobalType × Val)) :
    (allocGlobals s gs).1.elems = s.elems :=
  allocMany_fst (fun s => s.elems) (fun _ _ => rfl) s gs

@[simp] theorem allocGlobals_fst_datas (s : Store H) (gs : List (GlobalType × Val)) :
    (allocGlobals s gs).1.datas = s.datas :=
  allocMany_fst (fun s => s.datas) (fun _ _ => rfl) s gs

@[simp] theorem allocTables_fst_mems (s : Store H) (ts : List TableType) :
    (allocTables s ts).1.mems = s.mems :=
  allocMany_fst (fun s => s.mems) (fun _ _ => rfl) s ts

@[simp] theorem allocTables_fst_elems (s : Store H) (ts : List TableType) :
    (allocTables s ts).1.elems = s.elems :=
  allocMany_fst (fun s => s.elems) (fun _ _ => rfl) s ts

@[simp] theorem allocTables_fst_datas (s : Store H) (ts : List TableType) :
    (allocTables s ts).1.datas = s.datas :=
  allocMany_fst (fun s => s.datas) (fun _ _ => rfl) s ts

@[simp] theorem allocMems_fst_elems (s : Store H) (ts : List MemoryType) :
    (allocMems s ts).1.elems = s.elems :=
  allocMany_fst (fun s => s.elems) (fun _ _ => rfl) s ts

@[simp] theorem allocMems_fst_datas (s : Store H) (ts : List MemoryType) :
    (allocMems s ts).1.datas = s.datas :=
  allocMany_fst (fun s => s.datas) (fun _ _ => rfl) s ts

@[simp] theorem allocElems_fst_datas (s : Store H) (es : List (ElemType × List Ref)) :
    (allocElems s es).1.datas = s.datas :=
  allocMany_fst (fun s => s.datas) (fun _ _ => rfl) s es

/-! ## Export instances and module allocation (`9-module:100-147`) -/

/-- `$instexport(fa*, ga*, ta*, ma*, export)` (`9-module:100-104`). The four
address lists are complete index spaces — imports followed by definitions — so
the index is used unchanged. The lookup is partial; `Export_ok`
(`6-typing:655`) is what rules the failure out. -/
def instExport? (fas : List FuncAddr) (gas : List GlobalAddr) (tas : List TableAddr)
    (mas : List MemAddr) (e : Export) : Option ExportInst :=
  (match e.index with
    | .func x => (fas[x.toNat]?).map ExternAddr.func
    | .global x => (gas[x.toNat]?).map ExternAddr.global
    | .table x => (tas[x.toNat]?).map ExternAddr.table
    | .memory x => (mas[x.toNat]?).map ExternAddr.mem).map (⟨e.name, ·⟩)

/-- `$allocmodule(s, module, externaddr*, val*, (ref*)*)` (`9-module:107-147`).

The module instance is built from the *predicted* address ranges
(`9-module:125-130`) and only then passed to the allocators, exactly as SpecTec
writes it; `allocModule?_spec` discharges SpecTec's six assertions that the
prediction is right. `none` arises only where SpecTec's equation has no
instance: an out-of-range `moduleinst.TYPES[x]` in `$allocfunc`, an out-of-range
index in `$instexport`, or a length mismatch in `$allocglobals`/`$allocelems`
(whose SpecTec equations pair `globaltype*` with `val*` and `reftype*` with
`(ref*)*` and so have no instance when the lengths differ). -/
def allocModule? (s : Store H) (m : Module) (xas : List ExternAddr) (vs : List Val)
    (rss : List (List Ref)) : Option (Store H × ModuleInst) := do
  let fts ← m.funcs.mapM fun fn => m.types[fn.type.toNat]?
  -- `$allocglobals` and `$allocelems` (`9-module:51-55`, `9-module:81-85`) are
  -- defined only on equal-length arguments; `Instantiate` forces both.
  guard (vs.length = m.globals.length)
  guard (rss.length = m.elems.length)
  let mi₀ : ModuleInst :=
    { types := m.types
      funcs := ExternAddr.funcs xas ++ (List.range m.funcs.length).map (s.funcs.length + ·)
      globals := ExternAddr.globals xas ++ (List.range m.globals.length).map (s.globals.length + ·)
      tables := ExternAddr.tables xas ++ (List.range m.tables.length).map (s.tables.length + ·)
      mems := ExternAddr.mems xas ++ (List.range m.memories.length).map (s.mems.length + ·)
      elems := (List.range m.elems.length).map (s.elems.length + ·)
      datas := (List.range m.data.length).map (s.datas.length + ·) }
  let xi ← m.exports.mapM (instExport? mi₀.funcs mi₀.globals mi₀.tables mi₀.mems)
  let mi : ModuleInst := { mi₀ with exports := xi }
  let s₁ := (allocFuncs s mi (fts.zip m.funcs)).1
  let s₂ := (allocGlobals s₁ ((m.globals.map Global.type).zip vs)).1
  let s₃ := (allocTables s₂ m.tables).1
  let s₄ := (allocMems s₃ m.memories).1
  let s₅ := (allocElems s₄ ((m.elems.map Elem.type).zip rss)).1
  let s₆ := (allocDatas s₅ (m.data.map Data.bytes)).1
  return (s₆, mi)

/-- The module instance `allocModule?` returns has exactly the predicted address
ranges (`9-module:125-130`, `9-module:132-141`). -/
theorem allocModule?_moduleInst {s s' : Store H} {m : Module} {xas : List ExternAddr}
    {vs : List Val} {rss : List (List Ref)} {mi : ModuleInst}
    (h : allocModule? s m xas vs rss = some (s', mi)) :
    mi.types = m.types ∧
    mi.funcs = ExternAddr.funcs xas ++ (List.range m.funcs.length).map (s.funcs.length + ·) ∧
    mi.globals =
      ExternAddr.globals xas ++ (List.range m.globals.length).map (s.globals.length + ·) ∧
    mi.tables = ExternAddr.tables xas ++ (List.range m.tables.length).map (s.tables.length + ·) ∧
    mi.mems = ExternAddr.mems xas ++ (List.range m.memories.length).map (s.mems.length + ·) ∧
    mi.elems = (List.range m.elems.length).map (s.elems.length + ·) ∧
    mi.datas = (List.range m.data.length).map (s.datas.length + ·) := by
  simp only [allocModule?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.guard_eq_some', Option.some.injEq, Prod.mk.injEq, exists_const] at h
  obtain ⟨fts, _, -, -, xi, _, -, hmi⟩ := h
  subst hmi
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `List.mapM` over `Option` preserves the length. -/
theorem mapM_length_eq {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l'.length = l.length
  | [], l', h => by simp at h; subst h; rfl
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨b, -, bs, hbs, rfl⟩ := h
    simp [mapM_length_eq hbs]

/-- **SpecTec's six assertions, discharged.** The address lists `allocModule?`
predicts for the module instance are exactly the lists the `$alloc*s` functions
return, each run on the store its predecessors have left behind. This is
`9-module:142-147` read as a theorem rather than as a premise, and it is what
makes the knot of `$allocmodule` well founded. -/
theorem allocModule?_spec {s s' : Store H} {m : Module} {xas : List ExternAddr}
    {vs : List Val} {rss : List (List Ref)} {mi : ModuleInst}
    (h : allocModule? s m xas vs rss = some (s', mi)) :
    ∃ (fts : List FuncType) (s₁ s₂ s₃ s₄ s₅ : Store H),
      (m.funcs.mapM fun fn => m.types[fn.type.toNat]?) = some fts ∧
      s₁ = (allocFuncs s mi (fts.zip m.funcs)).1 ∧
      s₂ = (allocGlobals s₁ ((m.globals.map Global.type).zip vs)).1 ∧
      s₃ = (allocTables s₂ m.tables).1 ∧
      s₄ = (allocMems s₃ m.memories).1 ∧
      s₅ = (allocElems s₄ ((m.elems.map Elem.type).zip rss)).1 ∧
      s' = (allocDatas s₅ (m.data.map Data.bytes)).1 ∧
      mi.funcs = ExternAddr.funcs xas ++ (allocFuncs s mi (fts.zip m.funcs)).2 ∧
      mi.globals =
        ExternAddr.globals xas ++ (allocGlobals s₁ ((m.globals.map Global.type).zip vs)).2 ∧
      mi.tables = ExternAddr.tables xas ++ (allocTables s₂ m.tables).2 ∧
      mi.mems = ExternAddr.mems xas ++ (allocMems s₃ m.memories).2 ∧
      mi.elems = (allocElems s₄ ((m.elems.map Elem.type).zip rss)).2 ∧
      mi.datas = (allocDatas s₅ (m.data.map Data.bytes)).2 := by
  simp only [allocModule?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.guard_eq_some', Option.some.injEq, Prod.mk.injEq, exists_const] at h
  obtain ⟨fts, hfts, hv, hr, xi, -, hstore, hmi⟩ := h
  have hftslen : fts.length = m.funcs.length := mapM_length_eq hfts
  subst hmi
  refine ⟨fts, _, _, _, _, _, hfts, rfl, rfl, rfl, rfl, rfl, hstore.symm,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hftslen]
  · simp [hv]
  · simp
  · simp
  · simp [hr]
  · simp

/-! ## Segment programs (`9-module:154-165`) -/

/-- `$runelem(elem, i)` (`9-module:154-159`): `PASSIVE` emits nothing, `DECLARE`
emits only `ELEM.DROP i`, and `ACTIVE x instr*` emits the offset expression
followed by `(CONST I32 0) (CONST I32 n) (TABLE.INIT x i) (ELEM.DROP i)` with
`n = |expr*|`. -/
def runElem (i : Nat) (e : Elem) : List Instr :=
  let xe : ElemIdx := ⟨Fin.ofNat _ i⟩
  match e.mode with
  | .passive => []
  | .declare => [.elemDrop xe]
  | .active x off =>
    off ++ [.intConst .i32 0, .intConst .i32 (BitVec.ofNat 32 e.init.length),
      .tableInit x xe, .elemDrop xe]

/-- `$rundata(data, i)` (`9-module:161-165`): `PASSIVE` emits nothing and
`ACTIVE 0 instr*` emits the offset expression followed by
`(CONST I32 0) (CONST I32 n) (MEMORY.INIT i) (DATA.DROP i)` with `n = |byte*|`.
The memory index is ignored; see the deviation in the module docstring. -/
def runData (i : Nat) (d : Data) : List Instr :=
  let xd : DataIdx := ⟨Fin.ofNat _ i⟩
  match d.mode with
  | .passive => []
  | .active _ off =>
    off ++ [.intConst .i32 0, .intConst .i32 (BitVec.ofNat 32 d.bytes.size),
      .memoryInit xd, .dataDrop xd]

/-- The justification of the `$rundata` deviation: a valid module's active data
segments all name memory `0`, which is the only case `$rundata` covers. -/
theorem DataOk.active_zero {C : Context} {d : Data} {x : MemIdx} {off : Expr}
    (h : DataOk C d) (hd : d.mode = .active x off) : x = memIdx0 := by
  rw [DataOk, hd] at h
  cases h with
  | active hx _ _ =>
    refine congrArg Idx.mk (Fin.ext ?_)
    exact hx

/-- `$concat_(instr, $runelem(elem*[i], i)^(i<n_E))` (`9-module:188`). -/
def runElems (m : Module) : List Instr :=
  ((List.range m.elems.length).zip m.elems).flatMap fun p => runElem p.1 p.2

/-- `$concat_(instr, $rundata(data*[j], j)^(j<n_D))` (`9-module:189`). -/
def runDatas (m : Module) : List Instr :=
  ((List.range m.data.length).zip m.data).flatMap fun p => runData p.1 p.2

/-! ## Import matching

`ExternAddrOk s xa xt` is "the instance `xa` names in `s` has a type at or below
`xt`". SpecTec 2.0 has no such relation (it has no store typing at all); this is
`Externaddr_ok` of Core 3.0 with `ExternType.Sub` (`6-typing:120-134`) in place
of 3.0's `Externtype_sub`, and it is the 2.0 analogue of
`Silmaril.Wasm.V1.Execution.ExternMatches`.

Limit matching is *covariant in the current size* because `$growtable` and
`$growmemory` (`5-runtime-aux:119`, `:126`) rewrite the instance type's
**minimum** to the new size: `ti.TYPE` and `mi.TYPE` are the *current* types,
which is exactly what the W3C text's `externtype` of an instance means. -/

/-- The 2.0 analogue of `Externaddr_ok`; see the section documentation. -/
inductive ExternAddrOk (s : Store H) : ExternAddr → ExternType → Prop where
  /-- A function address is at the type of its instance. -/
  | func {a : FuncAddr} {fi : FuncInst H} (h : s.funcInst? a = some fi) :
      ExternAddrOk s (.func a) (.func fi.type)
  /-- A global address is at the type of its instance. -/
  | global {a : GlobalAddr} {gi : GlobalInst} (h : s.globalInst? a = some gi) :
      ExternAddrOk s (.global a) (.global gi.type)
  /-- A table address is at the *current* type of its instance. -/
  | table {a : TableAddr} {ti : TableInst} (h : s.tableInst? a = some ti) :
      ExternAddrOk s (.table a) (.table ti.type)
  /-- A memory address is at the *current* type of its instance. -/
  | mem {a : MemAddr} {mi : MemInst} (h : s.memInst? a = some mi) :
      ExternAddrOk s (.mem a) (.memory mi.type)
  /-- Subsumption along `Externtype_sub` (`6-typing:120-134`): this is the
  import-matching step. -/
  | sub {xa : ExternAddr} {xt xt' : ExternType} (h : ExternAddrOk s xa xt')
      (hok : ExternType.Ok xt) (hsub : ExternType.Sub xt' xt) : ExternAddrOk s xa xt

/-- An external address and the type it is matched against always have the same
kind: `Externtype_sub` never relates different shapes. -/
theorem ExternAddrOk.kind_eq {s : Store H} {xa : ExternAddr} {xt : ExternType}
    (h : ExternAddrOk s xa xt) :
    (∃ a ft, xa = .func a ∧ xt = .func ft) ∨ (∃ a gt, xa = .global a ∧ xt = .global gt) ∨
      (∃ a tt, xa = .table a ∧ xt = .table tt) ∨ (∃ a mt, xa = .mem a ∧ xt = .memory mt) := by
  induction h with
  | func h => exact .inl ⟨_, _, rfl, rfl⟩
  | global h => exact .inr (.inl ⟨_, _, rfl, rfl⟩)
  | table h => exact .inr (.inr (.inl ⟨_, _, rfl, rfl⟩))
  | mem h => exact .inr (.inr (.inr ⟨_, _, rfl, rfl⟩))
  | sub _ _ hsub ih =>
    cases hsub <;>
      [ (rcases ih with ⟨a, _, rfl, -⟩ | ⟨_, _, -, h⟩ | ⟨_, _, -, h⟩ | ⟨_, _, -, h⟩);
        (rcases ih with ⟨_, _, -, h⟩ | ⟨a, _, rfl, -⟩ | ⟨_, _, -, h⟩ | ⟨_, _, -, h⟩);
        (rcases ih with ⟨_, _, -, h⟩ | ⟨_, _, -, h⟩ | ⟨a, _, rfl, -⟩ | ⟨_, _, -, h⟩);
        (rcases ih with ⟨_, _, -, h⟩ | ⟨_, _, -, h⟩ | ⟨_, _, -, h⟩ | ⟨a, _, rfl, -⟩) ]
    · exact .inl ⟨a, _, rfl, rfl⟩
    all_goals first
      | exact absurd h (by simp)
      | exact .inr (.inl ⟨a, _, rfl, rfl⟩)
      | exact .inr (.inr (.inl ⟨a, _, rfl, rfl⟩))
      | exact .inr (.inr (.inr ⟨a, _, rfl, rfl⟩))

/-! ## Instantiation (`9-module:167-189`) -/

/-- `moduleinst_init` (`9-module:177-181`): the types, the imported **plus
predicted** function addresses, and the imported globals — nothing else. The
predicted function addresses are what lets a global initializer or an element
expression mention `ref.func` of a function this very module defines. -/
def ModuleInst.initial (s : Store H) (m : Module) (xas : List ExternAddr) : ModuleInst :=
  { types := m.types,
    funcs := ExternAddr.funcs xas ++ (List.range m.funcs.length).map (s.funcs.length + ·),
    globals := ExternAddr.globals xas }

/-- `f_init = { MODULE moduleinst_init }` (`9-module:182`). -/
def Frame.initial (s : Store H) (m : Module) (xas : List ExternAddr) : Frame :=
  { module := ModuleInst.initial s m xas }

/-- `$instantiate(s, module, externaddr*) = c` (`9-module:167-189`).

Note that both `Eval_expr` premises run *and end* in the **same** state `z`
(`9-module:184-185`): a 2.0 constant expression reads the store but never writes
it, so unlike Core 3.0 there is nothing to thread. `Properties.lean` proves this
for every expression `Expr_ok_const` accepts.

`valid` is not a premise of `$instantiate`; see the module docstring. `bounded`
is the well-formedness `$runelem`/`$rundata` silently assume. -/
structure Instantiate (P : Profile) (host : HostSemantics H) (s : Store H) (m : Module)
    (xas : List ExternAddr) (c : Config H) : Prop where
  /-- Module validity and import matching. Not in `$instantiate`; the embedder's
  job in the W3C text, and a premise type soundness needs. -/
  valid : ∃ ixt xt, ModuleOk m ixt xt ∧ List.Forall₂ (ExternAddrOk s) xas ixt
  /-- `$runelem`/`$rundata` pass the segment index `i` as an `elemidx`/`dataidx`
  — a `u32` — and emit the segment length as `CONST I32 n`, which is well formed
  only for `n < 2^32`. Both are undefined beyond these bounds. -/
  bounded : m.elems.length ≤ 2 ^ 32 ∧ m.data.length ≤ 2 ^ 32 ∧
    (∀ d ∈ m.data, d.bytes.size < 2 ^ 32) ∧ (∀ e ∈ m.elems, e.init.length < 2 ^ 32)
  /-- `(Eval_expr : z; expr_G ~>* z; val)*`, `(Eval_expr : z; expr_E ~>* z; ref)**`,
  `(s', moduleinst) = $allocmodule(…)` and the resulting configuration
  (`9-module:183-189`). -/
  run : ∃ (valsG : List Val) (refsE : List (List Ref)) (s' : Store H) (mi : ModuleInst),
    List.Forall₂ (fun (g : Global) (v : Val) =>
        EvalExpr P host s (Frame.initial s m xas) (Global.init g)
          s (Frame.initial s m xas) [v]) m.globals valsG ∧
    List.Forall₂ (fun (e : Elem) (rs : List Ref) =>
        List.Forall₂ (fun (ex : Expr) (r : Ref) =>
          EvalExpr P host s (Frame.initial s m xas) ex
            s (Frame.initial s m xas) [Val.ref r]) e.init rs) m.elems refsE ∧
    allocModule? s m xas valsG refsE = some (s', mi) ∧
    c = ⟨s', { module := mi },
      expression (runElems m ++ runDatas m ++
        (match m.start with | some x => [Instr.call x] | none => []))⟩

/-- Instantiation whose start function diverges, in the style of
`Silmaril.Wasm.V1.Execution.InstantiationDiverges`. -/
def InstantiateDiverges (P : Profile) (host : HostSemantics H) (s : Store H) (m : Module)
    (xas : List ExternAddr) : Prop :=
  ∃ c : Config H, Instantiate P host s m xas c ∧ Diverges P host c

/-- `$instantiate` is deterministic up to the values the initializers produce:
the configuration is a function of the allocated store and module instance. -/
theorem Instantiate.code {P : Profile} {host : HostSemantics H} {s : Store H} {m : Module}
    {xas : List ExternAddr} {c : Config H} (h : Instantiate P host s m xas c) :
    c.code = expression (runElems m ++ runDatas m ++
      (match m.start with | some x => [Instr.call x] | none => [])) := by
  obtain ⟨_, _, _, _, _, _, _, hc⟩ := h.run
  rw [hc]

/-! ## Invocation (`9-module:196-199`) -/

/-- `$invoke(s, fa, val^n) = s; f; val^n (CALL_ADDR fa)` with `f = { MODULE {} }`
(`9-module:196-199`). -/
def invoke (s : Store H) (a : FuncAddr) (vs : List Val) : Config H :=
  ⟨s, {}, vals vs ++ [.callAddr a]⟩

/-- The premises of `$invoke`, with the argument-type premise the 2019-era text
lost; see the module docstring.

`arity` is `val^n` against `t_1^n`, `types` is the W3C text's "assert: the value
`val_i` is of type `t_i`", and `allocated` is the one store-dependent condition a
value-typing judgment would carry: a `REF.FUNC_ADDR` argument must name a
function of `s`. (A `REF.HOST_ADDR` carries no condition: 2.0 has no host-instance
component in the store.) -/
def InvokeOk (s : Store H) (a : FuncAddr) (vs : List Val) : Prop :=
  ∃ fi : FuncInst H, s.funcInst? a = some fi ∧
    -- `val^n` against `t_1^n` (`9-module:199`).
    vs.length = fi.type.params.length ∧
    -- The argument types; missing from `9-module:199`.
    List.Forall₂ (fun (v : Val) (t : ValType) => v.type = t) vs fi.type.params ∧
    -- Function-address arguments are allocated.
    (∀ v ∈ vs, ∀ b : FuncAddr, v = .ref (.funcAddr b) → (s.funcInst? b).isSome)

/-- The arity premise is implied by the type premise; `9-module:199` states only
the former, and the W3C 2.0 text states both. The proof discards the stored
arity conjunct and goes through `List.Forall₂.length_eq`, so it really witnesses
the implication. -/
theorem InvokeOk.arity {s : Store H} {a : FuncAddr} {vs : List Val} (h : InvokeOk s a vs) :
    ∃ fi : FuncInst H, s.funcInst? a = some fi ∧ vs.length = fi.type.params.length := by
  obtain ⟨fi, hf, -, ht, -⟩ := h
  exact ⟨fi, hf, ht.length_eq⟩

/-- Consequently the arity conjunct of `InvokeOk` is redundant: deleting it
leaves an equivalent predicate. It is kept as a field only because
`9-module:199` writes it out (`val^n` against `t_1^n`) and the W3C 2.0 text
states it as a separate assertion. -/
theorem invokeOk_iff_types {s : Store H} {a : FuncAddr} {vs : List Val} :
    InvokeOk s a vs ↔
      ∃ fi : FuncInst H, s.funcInst? a = some fi ∧
        List.Forall₂ (fun (v : Val) (t : ValType) => v.type = t) vs fi.type.params ∧
        (∀ v ∈ vs, ∀ b : FuncAddr, v = .ref (.funcAddr b) → (s.funcInst? b).isSome) := by
  constructor
  · rintro ⟨fi, hf, -, ht, ha⟩
    exact ⟨fi, hf, ht, ha⟩
  · rintro ⟨fi, hf, ht, ha⟩
    exact ⟨fi, hf, ht.length_eq, ht, ha⟩

end Silmaril.Wasm.V2.Execution
