module

public import Silmaril.Raw.Wasm.Versions.Lime1.ToV2.Modules
public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Execution
public import Silmaril.Wasm.V2.Execution.Step
public import Silmaril.Raw.Wasm.Versions.V2.Execution.Properties
public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Instantiation

/-!
# Lime1 execution is simulated by WebAssembly 2.0 execution

The runtime half of the subset theorem `Lime1 ⊆ 2.0`: real, total maps from the
shared V1/Lime1 runtime (`Silmaril.Wasm.Execution.Runtime`) to the 2.0 runtime
(`Silmaril.Wasm.V2.Execution`), a simulation relation `ToV2.Sim`, and forward
simulation of steps, finite runs, divergence and instantiation.

## The maps

Every sort maps by a plain total function, named `X.toV2` uniformly with
`Lime1/ToV2/{Types,Instructions,Modules}.lean`:

* values: `Value.toV2 v = NUM (CONST v.TYPE v.BITS)`, so a Lime1 value
  instruction `.source (.intConst t b)` is the 2.0 value instruction
  `.plain (.intConst t b)` (`value_toV2`, by cases);
* instances: a Lime1 table is a `FUNCREF` table whose limit *minimum* is its
  current size (2.0's `$growtable` rewrites the minimum, `5-runtime-aux:119`, so
  an instance type is always the current type), a Lime1 memory is an `i32`
  memory, a Lime1 global keeps its value and mutability and takes its declared
  type from the type of its value;
* code: **`.invoke a` becomes `CALL_ADDR a`**. This is the one place where the
  2.0 target is easier than the Core 3.0 one: `Lime1/ToCore/Runtime.lean` has to
  expand `.invoke a` into `REF.FUNC_ADDR a; CALL_REF dt` and to read `dt` out of
  the store, whereas `4-runtime:132` has `CALL_ADDR funcaddr` verbatim. So
  `Admin.toV2 : Admin → V2.Admin` is a store-independent, length-preserving
  function, and so is `Config.toV2`.

## The simulation relation

A plain function will **not** do, for two reasons, both of which are erasures
rather than mismatches:

1. 2.0 stores and module instances have `ELEMS`/`DATAS` components that Lime1
   has none of. They are empty in the image of `Store.toV2`, but 2.0
   *instantiation* allocates them (`$allocelems`, `$allocdatas`,
   `9-module:107-147`), so after `Instantiate` the two sides differ there.
2. A 2.0 `globalinst` carries a *declared* type that `Step/global.set`
   (`8-reduction:392`) leaves alone, while a Lime1 `globalinst` has no declared
   type at all and `Step/globalSet` simply overwrites the value. Reading the
   declared type off the current value is the only choice available to
   `GlobalInst.toV2`, and the two drift apart on an ill-typed `global.set`.

`ToV2.Config.norm` performs exactly those two erasures (and recursively erases
the module instances of the frames inside the code), and

    ToV2.Sim a c := ToV2.Config.norm c = a.toV2 ∧ ToV2.ConfigWF a .

Unlike `Lime1/ToCore/Runtime.lean` there is **no** `Admin.norm` on annotations:
2.0's `CALL_ADDR` needs no resolution, so normalisation only rebuilds frames.

## Why the simulation is not lock-step

Lime1's `memory.copy` and `memory.fill` are atomic (`Memory.copy`,
`Memory.fill`); 2.0's reduce **one byte at a time**, emitting a `store8` (and
for `copy` a `load8u`) plus the recursive instruction at count `n - 1`
(`Step_read/memory.fill-succ`, `memory.copy-le`, `memory.copy-gt`,
`8-reduction:617`, `:633`, `:640`). The target side therefore needs
`Relation.TransGen`, exactly as `Lime1 → Core 3.0` does, and the loop lemmas are
the ones `Lime1/ToCore/Sim/Memory{Bulk,Copy,Fill}.lean` already develop
(`bulk_fill_get`, `bulk_copy_get`, `bulk_store8`, `bulk_load8`, `bulk_ext`,
`bulk_fill_none`, `bulk_copy_none`): they are statements about `ByteArray`
alone, so they are reused here verbatim rather than rediscovered.

## Well-formedness (`ToV2.StoreWF`)

Three 2.0-side bounds have no Lime1 counterpart and must be assumed:

* memories are page-aligned and at most `2^32` bytes — `$growmemory`
  (`5-runtime-aux:126`) divides by the page size, and the `i + 1` / `n - 1`
  counters of the fill and copy loops are 32-bit and would wrap;
* table sizes and the `Option Nat` maxima of Lime1 tables and memories are below
  `2^32`, because 2.0 limits are `Fin (2^32)` and `Fin.ofNat` would wrap.

They are the 2.0 analogues of `Lime1.Execution.StoreWF` and of the `tables`
field of `Lime1.Execution.InstantiationBounds`. Note what is *not* needed here
and is needed for Core 3.0: no `ModWF`, because 2.0's `Step_read/call`
(`8-reduction:119`) resolves the function *index* and emits `CALL_ADDR` without
consulting the store, exactly like Lime1's `Step/call`; and no `noGlobals`,
because 2.0's `$instantiate` evaluates global initialisers in the *unallocated*
store (`9-module:184`) instead of Core 3.0's `$evalglobals`, so global addresses
do not shift.

## What is assumed rather than proved: 2.0 validity

`V2.Execution.Instantiate` carries a `valid` field (module validity plus import
matching) that `$instantiate` itself does not have. Deriving it from
`Lime1.Validation.ModuleValid` is the business of
`Silmaril/Wasm/Lime1/ToV2/Validation.lean`, under the `NoExtendedConst` side
condition of `NOTES.md` (Lime1 has extended constant expressions, Wasm
2.0 does not — `Instr_const`, `6-typing:543-557`). This file therefore *takes it
as a hypothesis*, in the `valid` field of `ToV2.InstantiationBounds`, rather
than importing a module of a concurrently developed unit; see that field's
documentation.

## The commuting triangle

The composite `Lime1 → 2.0 → 3.0` has to agree with the direct
`Lime1.Execution.Step.toCore`. Its third edge, a `2.0 → 3.0` *runtime* map, now
exists: `Silmaril/Wasm/V2/ToCore/Runtime.lean` defines the simulation relation
and `Silmaril/Wasm/V2/ToCore/Execution.lean` proves the step theorem. What is
still missing is the comparison of that map with the two Lime1 injections, so
the triangle is stated against `ToV2.CoreBridge`, a record of the four
properties it needs: `rel` and `step`, both instantiable from those two files,
and `image`/`faithful`, which say that the 2.0 image and the Core 3.0 image of
one and the same Lime1 configuration are related and *only* so related. Neither
of the latter two is proved yet, so the triangle is conditional on the record.

`Step.toV2_toCore` then runs the Core side *through* 2.0 — the Core
configuration it exhibits comes from `B.step`, not from `Step.toCore` — and
concludes that it simulates the same Lime1 configuration the direct route
reaches. `Step.toV2_toCore_of_sim` specialises it to the direct route's own
starting point. The syntactic edge of the same triangle is already available and
needs no hypothesis: `Lime1.Instr.toV2_toCore`, `Lime1.Expr.toV2_toCore` and
`Lime1.Module.toV2_toCore`.

## Instantiation

`ToV2.prepare_v2` is the allocation-and-segment half, the 2.0 analogue of
`Silmaril/Wasm/Lime1/ToCore/Instantiation.lean`: `ToV2.allocModule_v2` relates
Lime1's `allocate?` to 2.0's `$allocmodule`, `ToV2.constExpr_v2` turns a Lime1
constant expression into a 2.0 `Eval_expr`, and `ToV2.elemLoop_v2` /
`ToV2.dataLoop_v2` run the `$runelem`/`$rundata` programs — which, exactly as in
Core 3.0 and unlike Lime1's atomic `prepare?`, write one element (byte) at a
time. `ToV2.start_sim_v2` then turns the emitted `CALL x` into the `CALL_ADDR a`
that Lime1's `prepare?` produces directly, after which `Steps.toV2` applies.

## State of the proofs

Everything in this file is proved: there is no `sorry`, and the only axioms are
`propext`, `Classical.choice` and `Quot.sound`. Lime1's `ToCore/Instantiation`
is `public import`ed for the Lime1-side inversion lemmas it already proves
(`prepare?_inv`, `resolveElem?_inv`, `applyElem_len`, the `foldl_apply*` shape
lemmas, …), which are target-independent.

**Note.** `Silmaril/Wasm/Lime1/ToV2.lean` is the *syntax* root of the
directory and deliberately does not `public import` this file: the binary and
`V1` units reach it for `Module.toV2` alone, and pulling the runtime layer in
would make them depend on all of `V2/Execution`.
-/

@[expose] public section

namespace Silmaril.Wasm.Lime1.Execution

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

/-! ## Abbreviations for the 2.0 runtime -/

namespace ToV2

abbrev VVal := Silmaril.Wasm.V2.Execution.Val
abbrev VRef := Silmaril.Wasm.V2.Execution.Ref
abbrev VAdmin := Silmaril.Wasm.V2.Execution.Admin
abbrev VExternAddr := Silmaril.Wasm.V2.Execution.ExternAddr
abbrev VModuleInst := Silmaril.Wasm.V2.Execution.ModuleInst
abbrev VFrame := Silmaril.Wasm.V2.Execution.Frame
abbrev VFuncInst (H : Type) := Silmaril.Wasm.V2.Execution.FuncInst H
abbrev VTableInst := Silmaril.Wasm.V2.Execution.TableInst
abbrev VMemInst := Silmaril.Wasm.V2.Execution.MemInst
abbrev VGlobalInst := Silmaril.Wasm.V2.Execution.GlobalInst
abbrev VStore (H : Type) := Silmaril.Wasm.V2.Execution.Store H
abbrev VConfig (H : Type) := Silmaril.Wasm.V2.Execution.Config H
abbrev VResult := Silmaril.Wasm.V2.Execution.Result
abbrev VHostOutcome (H : Type) := Silmaril.Wasm.V2.Execution.HostOutcome H
abbrev VHostSemantics (H : Type) := Silmaril.Wasm.V2.Execution.HostSemantics H

end ToV2

open ToV2

/-- The 2.0 profile used for the subset theorems: the same `Profile.spec` the
Core 3.0 subset theorems use, whose NaN sets and nondeterministic growth failure
are exactly Lime1's nondeterminism. -/
abbrev v2Profile : Profile := Profile.spec

/-! ## The runtime maps -/

/-- `num ::= CONST numtype num_(numtype)` (`4-runtime:37`): a Lime1 value is
already a number type together with its bits. -/
def _root_.Silmaril.Wasm.Execution.Runtime.Value.toV2 (v : Value) : VVal :=
  .num ⟨v.type, v.bits⟩

/-- `externaddr` (`4-runtime:25`). -/
def _root_.Silmaril.Wasm.Execution.Runtime.ExternVal.toV2 : ExternVal → VExternAddr
  | .func a => .func a.value
  | .table a => .table a.value
  | .memory a => .mem a.value
  | .global a => .global a.value

/-- `moduleinst` (`4-runtime:82`). A Lime1 module instance has no element or
data segment addresses, so those two components are empty. -/
def _root_.Silmaril.Wasm.Execution.Runtime.ModuleInst.toV2 (m : ModuleInst) : VModuleInst where
  types := m.types.map FuncType.toV2
  funcs := m.funcs.map Addr.value
  globals := m.globals.map Addr.value
  tables := m.tables.map Addr.value
  mems := m.memories.map Addr.value
  elems := []
  datas := []
  exports := m.exports.map fun e => ⟨e.name, ExternVal.toV2 e.value⟩

/-- `frame ::= { LOCALS val*, MODULE moduleinst }` (`4-runtime:112`). Every 2.0
local is defaultable, so no `Option` wrapper is needed. -/
def _root_.Silmaril.Wasm.Execution.Runtime.Frame.toV2 (f : Frame) : VFrame :=
  ⟨f.locals.map Value.toV2, f.module.toV2⟩

variable {H : Type}

/-- `funcinst` (`4-runtime:60`), with the host alternative of deviation 7 of
`V2/Execution/Basic.lean`. -/
def _root_.Silmaril.Wasm.Execution.Runtime.FuncInst.toV2 : FuncInst Func H → VFuncInst H
  | .wasm t m c => ⟨FuncType.toV2 t, m.toV2, .wasm (Func.toV2 c)⟩
  | .host t h => ⟨FuncType.toV2 t, {}, .host h⟩

/-- `tableinst` (`4-runtime:67`). A Lime1 table is a `FUNCREF` table, and its
type's *minimum* is its current size: `$growtable` (`5-runtime-aux:119`) rewrites
the minimum, so an instance type is always the current type. -/
def _root_.Silmaril.Wasm.Execution.Runtime.TableInst.toV2 (t : TableInst) : VTableInst :=
  ⟨⟨⟨Fin.ofNat _ t.refs.length, t.max.map (Fin.ofNat _)⟩, .funcref⟩,
    t.refs.map fun | none => .null .funcref | some a => .funcAddr a.value⟩

/-- `meminst` (`4-runtime:70`), likewise with the current page count as the
minimum (`$growmemory`, `5-runtime-aux:126`). -/
def _root_.Silmaril.Wasm.Execution.Runtime.MemInst.toV2 (m : MemInst) : VMemInst :=
  ⟨⟨⟨Fin.ofNat _ (m.data.size / Memory.pageSize), m.max.map (Fin.ofNat _)⟩⟩, m.data⟩

/-- `globalinst` (`4-runtime:64`). A Lime1 global has no declared type; the only
type available is the type of its current value. -/
def _root_.Silmaril.Wasm.Execution.Runtime.GlobalInst.toV2 (g : GlobalInst) : VGlobalInst :=
  ⟨⟨g.mutability, .num g.value.type⟩, g.value.toV2⟩

/-- `store` (`4-runtime:104`); Lime1 has no element or data instances. -/
def _root_.Silmaril.Wasm.Execution.Runtime.Store.toV2 (s : Store H) : VStore H where
  funcs := s.funcs.map FuncInst.toV2
  globals := s.globals.map GlobalInst.toV2
  tables := s.tables.map TableInst.toV2
  mems := s.memories.map MemInst.toV2
  elems := []
  datas := []

mutual
/-- `admininstr` (`4-runtime:128`). Store-independent and length-preserving:
`.invoke a` is `CALL_ADDR a` (`4-runtime:132`). -/
def Admin.toV2 : Admin → VAdmin
  | .source i => .plain (Instr.toV2 i)
  | .invoke a => .callAddr a.value
  | .label n cont body => .label n (cont.map Instr.toV2) (Admin.listToV2 body)
  | .frame n f body => .frame n f.toV2 (Admin.listToV2 body)
  | .trap => .trap

/-- `Admin.toV2` on a sequence. -/
def Admin.listToV2 : List Admin → List VAdmin
  | [] => []
  | a :: as => Admin.toV2 a :: Admin.listToV2 as
end

/-- `config ::= state; admininstr*` (`4-runtime:117`). -/
def _root_.Silmaril.Wasm.Execution.Runtime.Config.toV2 (c : Config H) : VConfig H :=
  ⟨c.store.toV2, c.frame.toV2, Admin.listToV2 c.code⟩

/-- `result ::= _VALS val* | TRAP` (`4-runtime:46`). -/
def _root_.Silmaril.Wasm.Execution.Runtime.Result.toV2 : Result → VResult
  | .values vs => .values (vs.map Value.toV2)
  | .trap => .trap

/-! ## Commuting lemmas (the `simp` battery for the simulation proofs) -/

@[simp] theorem listToV2_nil : Admin.listToV2 ([] : List Admin) = [] := by
  simp [Admin.listToV2]

@[simp] theorem listToV2_cons (a : Admin) (as : List Admin) :
    Admin.listToV2 (a :: as) = Admin.toV2 a :: Admin.listToV2 as := by
  simp [Admin.listToV2]

theorem listToV2_eq_map (l : List Admin) : Admin.listToV2 l = l.map Admin.toV2 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

@[simp] theorem listToV2_append (xs ys : List Admin) :
    Admin.listToV2 (xs ++ ys) = Admin.listToV2 xs ++ Admin.listToV2 ys := by
  simp [listToV2_eq_map]

@[simp] theorem value_toV2 (v : Value) : Admin.toV2 (value v) = (Value.toV2 v).toAdmin := by
  rcases v with ⟨_ | _, _⟩ <;> rfl

@[simp] theorem values_toV2 (vs : List Value) :
    Admin.listToV2 (values vs) = Silmaril.Wasm.V2.Execution.vals (vs.map Value.toV2) := by
  simp [listToV2_eq_map, values, Silmaril.Wasm.V2.Execution.vals, List.map_map,
    Function.comp_def]

@[simp] theorem source_toV2 (i : Instr) : Admin.toV2 (.source i) = .plain (Instr.toV2 i) := by
  simp [Admin.toV2]

@[simp] theorem invoke_toV2 (a : FuncAddr) : Admin.toV2 (.invoke a) = .callAddr a.value := by
  simp [Admin.toV2]

@[simp] theorem label_toV2 (n : Nat) (cont : Expr) (body : List Admin) :
    Admin.toV2 (.label n cont body) =
      .label n (cont.map Instr.toV2) (Admin.listToV2 body) := by simp [Admin.toV2]

@[simp] theorem frame_toV2 (n : Nat) (f : Frame) (body : List Admin) :
    Admin.toV2 (.frame n f body) = .frame n f.toV2 (Admin.listToV2 body) := by simp [Admin.toV2]

@[simp] theorem trap_toV2 : Admin.toV2 .trap = .trap := by simp [Admin.toV2]

@[simp] theorem expression_toV2 (es : Expr) :
    Admin.listToV2 (expression es) =
      Silmaril.Wasm.V2.Execution.expression (Expr.toV2 es) := by
  simp [listToV2_eq_map, expression, Silmaril.Wasm.V2.Execution.expression, Expr.toV2_eq_map,
    List.map_map, Function.comp_def, Admin.toV2]

@[simp] theorem result_toV2 (r : Result) :
    Admin.listToV2 (result r) = r.toV2.toAdmin := by
  cases r <;>
    simp [result, Runtime.Result.toV2, Silmaril.Wasm.V2.Execution.Result.toAdmin, Admin.toV2]

/-! ## Retractions

The `X.ofV2?` half of the naming convention of `Lime1/ToV2/**`, and the
injectivity it gives. The runtime maps are injective for the same reason the
syntactic ones are: every Lime1 runtime object is recoverable from its 2.0
image. -/

/-- The retraction of `Value.toV2`: a vector or a reference is not a Lime1
runtime value. -/
def Value.ofV2? : VVal → Option Value
  | .num v => some ⟨v.type, v.bits⟩
  | _ => none

@[simp] theorem Value.ofV2?_toV2 (v : Value) : Value.ofV2? v.toV2 = some v := rfl

theorem Value.toV2_injective : Function.Injective Runtime.Value.toV2 :=
  injective_of_ofV2? Value.ofV2?_toV2

/-- The retraction of `ExternVal.toV2`; total, since 2.0 has exactly Lime1's
four external address kinds. -/
def ExternVal.ofV2 : VExternAddr → ExternVal
  | .func a => .func ⟨a⟩
  | .global a => .global ⟨a⟩
  | .table a => .table ⟨a⟩
  | .mem a => .memory ⟨a⟩

@[simp] theorem ExternVal.ofV2_toV2 (v : ExternVal) : ExternVal.ofV2 v.toV2 = v := by
  cases v <;> rfl

theorem ExternVal.toV2_injective : Function.Injective Runtime.ExternVal.toV2 :=
  Function.LeftInverse.injective ExternVal.ofV2_toV2

/-- The retraction of `ModuleInst.toV2`; the element and data segment addresses
are dropped. -/
def ModuleInst.ofV2? (m : VModuleInst) : Option ModuleInst := do
  return { types := ← m.types.mapM FuncType.ofV2?
           funcs := m.funcs.map (fun a => (⟨a⟩ : FuncAddr))
           tables := m.tables.map (fun a => (⟨a⟩ : TableAddr))
           memories := m.mems.map (fun a => (⟨a⟩ : MemAddr))
           globals := m.globals.map (fun a => (⟨a⟩ : GlobalAddr))
           exports := m.exports.map fun e => ⟨e.name, ExternVal.ofV2 e.addr⟩ }

@[simp] theorem ModuleInst.ofV2?_toV2 (m : ModuleInst) :
    ModuleInst.ofV2? m.toV2 = some m := by
  cases m
  simp [Silmaril.Wasm.Execution.Runtime.ModuleInst.toV2, ModuleInst.ofV2?, List.mapM_map,
    List.map_map, Function.comp_def]

theorem ModuleInst.toV2_injective : Function.Injective Runtime.ModuleInst.toV2 :=
  injective_of_ofV2? ModuleInst.ofV2?_toV2

/-- The retraction of `Frame.toV2`. -/
def Frame.ofV2? (f : VFrame) : Option Frame := do
  return ⟨← f.locals.mapM Value.ofV2?, ← ModuleInst.ofV2? f.module⟩

@[simp] theorem Frame.ofV2?_toV2 (f : Frame) : Frame.ofV2? f.toV2 = some f := by
  cases f
  simp [Silmaril.Wasm.Execution.Runtime.Frame.toV2, Frame.ofV2?, List.mapM_map,
    Function.comp_def]

theorem Frame.toV2_injective : Function.Injective Runtime.Frame.toV2 :=
  injective_of_ofV2? Frame.ofV2?_toV2

mutual
/-- The retraction of `Admin.toV2`: `REF.FUNC_ADDR`, `REF.HOST_ADDR` and the 2.0
instructions outside the Lime1 image are rejected. -/
def Admin.ofV2? : VAdmin → Option Admin
  | .plain i => (Instr.ofV2? i).map .source
  | .callAddr a => some (.invoke ⟨a⟩)
  | .label n cont body => do
      return .label n (← Expr.ofV2? cont) (← Admin.listOfV2? body)
  | .frame n f body => do
      return .frame n (← Frame.ofV2? f) (← Admin.listOfV2? body)
  | .trap => some .trap
  | _ => none

/-- `Admin.ofV2?` on a sequence. -/
def Admin.listOfV2? : List VAdmin → Option (List Admin)
  | [] => some []
  | a :: as => do return (← Admin.ofV2? a) :: (← Admin.listOfV2? as)
end

mutual
@[simp] theorem Admin.ofV2?_toV2 : (a : Admin) → Admin.ofV2? (Admin.toV2 a) = some a
  | .source i => by simp [Admin.ofV2?]
  | .invoke a => by cases a; simp [Admin.ofV2?]
  | .trap => by simp [Admin.ofV2?]
  | .label n cont body => by
      simp [Admin.ofV2?, Admin.listOfV2?_listToV2 body, ← Expr.toV2_eq_map]
  | .frame n f body => by
      simp [Admin.ofV2?, Admin.listOfV2?_listToV2 body]

/-- `Admin.ofV2?_toV2` on a sequence. -/
@[simp] theorem Admin.listOfV2?_listToV2 :
    (l : List Admin) → Admin.listOfV2? (Admin.listToV2 l) = some l
  | [] => by simp [Admin.listOfV2?]
  | a :: as => by
      simp [Admin.listOfV2?, Admin.ofV2?_toV2 a, Admin.listOfV2?_listToV2 as]
end

theorem Admin.toV2_injective : Function.Injective Admin.toV2 :=
  injective_of_ofV2? Admin.ofV2?_toV2

theorem Admin.listToV2_injective : Function.Injective Admin.listToV2 :=
  injective_of_ofV2? Admin.listOfV2?_listToV2

/-! ## Normalisation and the simulation relation -/

namespace ToV2

/-- Forget the element and data segment addresses, which 2.0 module instances
have and Lime1 ones do not. -/
def ModuleInst.erase (m : VModuleInst) : VModuleInst := { m with elems := [], datas := [] }

/-- `ModuleInst.erase` under a frame. -/
def Frame.erase (f : VFrame) : VFrame := { f with module := ModuleInst.erase f.module }

/-- A global's declared type is replaced by the type of its current value: Lime1
globals carry no declared type, and a Lime1 `global.set` (unlike 2.0's, which
keeps the declared type) retypes the global with the stored value. -/
def GlobalInst.erase (g : VGlobalInst) : VGlobalInst :=
  { g with type := ⟨g.type.mutability, g.value.type⟩ }

/-- Forget the element and data instances, which 2.0 stores have and Lime1 ones
do not, and the declared types of globals. -/
def Store.erase (s : VStore H) : VStore H :=
  { s with elems := [], datas := [],
           funcs := s.funcs.map fun fi => { fi with module := ModuleInst.erase fi.module },
           globals := s.globals.map GlobalInst.erase }

mutual
/-- Erase the module instances of the frames inside the code. Unlike
`Lime1/ToCore/Runtime.lean`'s `Admin.norm`, nothing is *resolved*: 2.0's
`CALL_ADDR` needs no annotation. -/
def Admin.norm : VAdmin → VAdmin
  | .label n cont body => .label n cont (Admin.normList body)
  | .frame n f body => .frame n (Frame.erase f) (Admin.normList body)
  | a => a

/-- `Admin.norm` on a sequence. -/
def Admin.normList : List VAdmin → List VAdmin
  | [] => []
  | a :: as => Admin.norm a :: Admin.normList as
end

/-- Normalisation of a whole configuration. -/
def Config.norm (c : VConfig H) : VConfig H :=
  ⟨Store.erase c.store, Frame.erase c.frame, Admin.normList c.code⟩

/-- Module-instance similarity: the 2.0 instance additionally records element
and data segment addresses, which Lime1 never has. -/
def ModuleInstSim (mL : ModuleInst) (mV : VModuleInst) : Prop :=
  ModuleInst.erase mV = mL.toV2

/-! ### Well-formedness of Lime1 configurations

2.0 limits are `Fin (2^32)` where Lime1's are `Option Nat`, 2.0's `$growmemory`
counts whole pages, and 2.0's bulk-memory loops use wrapping 32-bit counters.
The simulation is therefore stated for configurations whose memories are
page-aligned and fit the 32-bit address space and whose table and limit sizes
are representable. -/

/-- Store well-formedness for the 2.0 simulation. -/
structure StoreWF (s : Store H) : Prop where
  /-- `$growmemory` (`5-runtime-aux:126`) divides the byte size by the page size. -/
  memAligned : ∀ mi ∈ s.memories, mi.data.size % Memory.pageSize = 0
  /-- The 32-bit `i + 1` counters of the `memory.fill`/`memory.copy` loops
  (`8-reduction:617`, `:633`, `:640`) must not wrap. -/
  memSize : ∀ mi ∈ s.memories, mi.data.size ≤ 2 ^ 32
  /-- A 2.0 limit maximum is a `Fin (2^32)`. -/
  memMax : ∀ mi ∈ s.memories, ∀ j ∈ mi.max, j < 2 ^ 32
  /-- A 2.0 limit minimum is a `Fin (2^32)`, and the table instance's minimum is
  its current size. -/
  tableSize : ∀ ti ∈ s.tables, ti.refs.length < 2 ^ 32
  /-- A 2.0 limit maximum is a `Fin (2^32)`. -/
  tableMax : ∀ ti ∈ s.tables, ∀ j ∈ ti.max, j < 2 ^ 32

/-- Configuration well-formedness: nothing beyond the store is needed, because
2.0's `Step_read/call` (`8-reduction:119`) resolves a function *index* without
consulting the store, exactly as Lime1's `Step/call` does. -/
def ConfigWF (a : Config H) : Prop := StoreWF a.store

/-- The simulation relation: the normalised 2.0 configuration is the image of a
well-formed Lime1 configuration. -/
def Sim (a : Config H) (c : VConfig H) : Prop := Config.norm c = a.toV2 ∧ ConfigWF a

/-- Host outcomes correspond. The shared `Silmaril.Wasm.Execution.Host.Outcome.Sim`. -/
def HostOutcomeSim : HostOutcome Func H → VHostOutcome H → Prop :=
  Silmaril.Wasm.Execution.Host.Outcome.Sim (fun s sV => Store.erase sV = s.toV2)
    Silmaril.Wasm.Execution.Runtime.Result.toV2

/-- Host calls preserve store well-formedness. The shared
`Silmaril.Wasm.Execution.Host.Preserves`; unlike the two translations into Core 3.0
this one has no store-extension obligation. -/
def HostPreserves (src : HostSemantics H) : Prop :=
  Silmaril.Wasm.Execution.Host.Preserves StoreWF (fun _ s' => StoreWF s') src

/-- Host compatibility: every Lime1 host behaviour is matched by the 2.0 host on
a related store. The shared `Silmaril.Wasm.Execution.Host.Compatible`. -/
def HostCompatible (src : HostSemantics H) (tgt : VHostSemantics H) : Prop :=
  Silmaril.Wasm.Execution.Host.Compatible StoreWF (fun _ s' => StoreWF s')
    (fun s sV => Store.erase sV = s.toV2) Value.toV2 HostOutcomeSim src tgt

/-! ### Normalisation lemmas -/

@[simp] theorem Admin.normList_nil : Admin.normList [] = [] := by simp [Admin.normList]

@[simp] theorem Admin.normList_cons (a : VAdmin) (as : List VAdmin) :
    Admin.normList (a :: as) = Admin.norm a :: Admin.normList as := by simp [Admin.normList]

theorem Admin.normList_eq_map (l : List VAdmin) : Admin.normList l = l.map Admin.norm := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

@[simp] theorem Admin.norm_plain (i : Silmaril.Wasm.V2.Instr) :
    Admin.norm (.plain i) = .plain i := by simp [Admin.norm]

@[simp] theorem Admin.norm_refFuncAddr (a : Nat) :
    Admin.norm (.refFuncAddr a) = .refFuncAddr a := by simp [Admin.norm]

@[simp] theorem Admin.norm_refHostAddr (a : Nat) :
    Admin.norm (.refHostAddr a) = .refHostAddr a := by simp [Admin.norm]

@[simp] theorem Admin.norm_callAddr (a : Nat) :
    Admin.norm (.callAddr a) = .callAddr a := by simp [Admin.norm]

@[simp] theorem Admin.norm_trap : Admin.norm .trap = .trap := by simp [Admin.norm]

@[simp] theorem Admin.norm_label (n : Nat) (cont : List Silmaril.Wasm.V2.Instr)
    (b : List VAdmin) : Admin.norm (.label n cont b) = .label n cont (b.map Admin.norm) := by
  simp [Admin.norm, Admin.normList_eq_map]

@[simp] theorem Admin.norm_frame (n : Nat) (f : VFrame) (b : List VAdmin) :
    Admin.norm (.frame n f b) = .frame n (Frame.erase f) (b.map Admin.norm) := by
  simp [Admin.norm, Admin.normList_eq_map]

@[simp] theorem Admin.norm_val (v : VVal) : Admin.norm v.toAdmin = v.toAdmin := by
  rcases v with ⟨_ | _, _⟩ | _ | (_ | _ | _) <;>
    simp [Silmaril.Wasm.V2.Execution.Val.toAdmin]

@[simp] theorem Admin.map_norm_vals (vs : List VVal) :
    (Silmaril.Wasm.V2.Execution.vals vs).map Admin.norm = Silmaril.Wasm.V2.Execution.vals vs := by
  simp [Silmaril.Wasm.V2.Execution.vals]

/-- Everything that is not a label or a frame is left alone by normalisation,
and is not in the image of anything else. -/
def Rigid : VAdmin → Prop
  | .label _ _ _ => False
  | .frame _ _ _ => False
  | _ => True

theorem Rigid.eq_of_norm {x y : VAdmin} (hy : Rigid y) (h : Admin.norm x = y) : x = y := by
  cases x <;> cases y <;> simp_all [Rigid, Admin.norm]

theorem Rigid.val (v : VVal) : Rigid v.toAdmin := by
  rcases v with ⟨_ | _, _⟩ | _ | (_ | _ | _) <;> simp [Silmaril.Wasm.V2.Execution.Val.toAdmin, Rigid]

theorem Rigid.trap : Rigid (.trap : VAdmin) := trivial

theorem map_norm_eq_of_rigid {l L : List VAdmin} (hL : ∀ y ∈ L, Rigid y)
    (h : l.map Admin.norm = L) : l = L := by
  induction L generalizing l with
  | nil => simpa using h
  | cons y L ih =>
    rcases l with _ | ⟨x, l⟩
    · simp at h
    · simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.mem_cons, forall_eq_or_imp] at hL
      rw [hL.1.eq_of_norm h.1, ih hL.2 h.2]

theorem ModuleInst.erase_toV2 (m : ModuleInst) : ModuleInst.erase m.toV2 = m.toV2 := rfl

theorem Frame.erase_toV2 (f : Frame) : Frame.erase f.toV2 = f.toV2 := rfl

theorem Store.erase_toV2 (s : Store H) : Store.erase s.toV2 = s.toV2 := by
  simp only [Store.erase, Silmaril.Wasm.Execution.Runtime.Store.toV2, List.map_map,
    Silmaril.Wasm.V2.Execution.Store.mk.injEq, and_true]
  constructor
  · exact List.map_congr_left fun x _ => by cases x <;> rfl
  · exact List.map_congr_left fun x _ => rfl

theorem Config.norm_eq_toV2_iff {cs : VStore H} {cf : VFrame} {cl : List VAdmin}
    {a : Config H} :
    Config.norm ⟨cs, cf, cl⟩ = a.toV2 ↔
      Store.erase cs = a.store.toV2 ∧ Frame.erase cf = a.frame.toV2 ∧
        cl.map Admin.norm = Admin.listToV2 a.code := by
  simp [Config.norm, Silmaril.Wasm.Execution.Runtime.Config.toV2, Admin.normList_eq_map]

end ToV2

open ToV2 in
mutual
/-- Lime1 images are normal. -/
theorem norm_toV2 : (a : Admin) → ToV2.Admin.norm (Admin.toV2 a) = Admin.toV2 a
  | .source _ => by simp
  | .invoke _ => by simp
  | .trap => by simp
  | .label _ _ body => by simp [map_norm_listToV2 body]
  | .frame _ f body => by
    simp only [frame_toV2, ToV2.Admin.norm_frame]
    rw [map_norm_listToV2 body, ToV2.Frame.erase_toV2]

/-- `norm_toV2` on a sequence. -/
theorem map_norm_listToV2 :
    (l : List Admin) → (Admin.listToV2 l).map ToV2.Admin.norm = Admin.listToV2 l
  | [] => by simp
  | a :: as => by
    simp only [listToV2_cons, List.map_cons]
    rw [norm_toV2 a, map_norm_listToV2 as]
end

/-- Lime1 images are normal configurations. -/
theorem ToV2.Sim.refl_toV2 (a : Config H) (hwf : ToV2.ConfigWF a) : ToV2.Sim a a.toV2 := by
  refine ⟨?_, hwf⟩
  simp only [ToV2.Config.norm, Silmaril.Wasm.Execution.Runtime.Config.toV2,
    ToV2.Store.erase_toV2, ToV2.Frame.erase_toV2, ToV2.Admin.normList_eq_map,
    map_norm_listToV2]

/-! ## Forward simulation

One Lime1 step is simulated by *at least one* 2.0 step. The simulation is not
lock-step: `memory.copy` and `memory.fill` need the byte loop. -/

/-- An allocated frame memory is a member of the store's memory list. -/
theorem frameMemory_getElem? {s : Store H} {f : Frame} {am : MemAddr} {mi : MemInst}
    (h : frameMemory s f = some (am, mi)) : s.memories[am.value]? = some mi := by
  simp only [frameMemory, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, -, _, hm, rfl, rfl⟩ := h
  exact hm

/-- An allocated frame memory is a member of the store's memory list. -/
theorem frameMemory_mem {s : Store H} {f : Frame} {am : MemAddr} {mi : MemInst}
    (h : frameMemory s f = some (am, mi)) : mi ∈ s.memories := by
  obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.mp (frameMemory_getElem? h)
  exact he ▸ List.getElem_mem hlt

/-- Replacing a memory by one that is still page-aligned, still fits the 32-bit
address space and still has a representable maximum preserves `ToV2.StoreWF`. -/
theorem ToV2.StoreWF.setMemory {s : Store H} (hwf : ToV2.StoreWF s) {am : MemAddr} {mi : MemInst}
    (h1 : mi.data.size % Memory.pageSize = 0) (h2 : mi.data.size ≤ 2 ^ 32)
    (h3 : ∀ j ∈ mi.max, j < 2 ^ 32) :
    ToV2.StoreWF (Silmaril.Wasm.Lime1.Execution.setMemory s am mi) where
  memAligned m hm := by
    rcases List.mem_or_eq_of_mem_set hm with hm | rfl
    · exact hwf.memAligned m hm
    · exact h1
  memSize m hm := by
    rcases List.mem_or_eq_of_mem_set hm with hm | rfl
    · exact hwf.memSize m hm
    · exact h2
  memMax m hm := by
    rcases List.mem_or_eq_of_mem_set hm with hm | rfl
    · exact hwf.memMax m hm
    · exact h3
  tableSize := hwf.tableSize
  tableMax := hwf.tableMax

/-- Changing a global preserves `ToV2.StoreWF`, which constrains only memories
and tables. -/
theorem ToV2.StoreWF.setGlobal {s : Store H} (hwf : ToV2.StoreWF s) (ga : GlobalAddr)
    (gi : GlobalInst) :
    ToV2.StoreWF (Silmaril.Wasm.Lime1.Execution.setGlobal s ga gi) :=
  ⟨hwf.memAligned, hwf.memSize, hwf.memMax, hwf.tableSize, hwf.tableMax⟩

/-- Store well-formedness is preserved: a Lime1 step only writes bytes within a
memory (which changes neither its size nor its alignment), grows a memory by
whole pages (`Memory.Grow`, which keeps both), or changes a global. -/
theorem Step.configWF {src : HostSemantics H} (hp : ToV2.HostPreserves src) {a b : Config H}
    (h : Step src a b) (hwf : ToV2.ConfigWF a) : ToV2.ConfigWF b := by
  induction h with
  | context _ _ _ ih => exact ih hwf
  | label _ _ _ ih => exact ih hwf
  | frame _ _ _ ih => exact ih hwf
  | invokeHost _ _ _ _ _ _ _ _ _ _ behavior => exact hp _ _ _ _ _ behavior hwf
  | globalSet => exact hwf.setGlobal _ _
  | intStore _ _ _ _ _ _ _ _ m _ memory stored =>
    have hmem := frameMemory_mem memory
    have hsz := Silmaril.Wasm.Execution.Memory.writeBytes_size _ _ _ _ stored
    exact hwf.setMemory (by rw [show _ = _ from hsz]; exact hwf.memAligned m hmem)
      (by rw [show _ = _ from hsz]; exact hwf.memSize m hmem) (hwf.memMax m hmem)
  | floatStore _ _ _ _ _ _ _ m _ memory stored =>
    have hmem := frameMemory_mem memory
    have hsz := Silmaril.Wasm.Execution.Memory.writeBytes_size _ _ _ _ stored
    exact hwf.setMemory (by rw [show _ = _ from hsz]; exact hwf.memAligned m hmem)
      (by rw [show _ = _ from hsz]; exact hwf.memSize m hmem) (hwf.memMax m hmem)
  | memoryCopy _ _ _ _ _ _ m _ memory copied =>
    have hmem := frameMemory_mem memory
    have hsz := Silmaril.Wasm.Execution.Memory.copy_size _ _ _ _ _ copied
    exact hwf.setMemory (by rw [show _ = _ from hsz]; exact hwf.memAligned m hmem)
      (by rw [show _ = _ from hsz]; exact hwf.memSize m hmem) (hwf.memMax m hmem)
  | memoryFill _ _ _ _ _ _ m _ memory filled =>
    have hmem := frameMemory_mem memory
    have hsz := Silmaril.Wasm.Execution.Memory.fill_size _ _ _ _ _ filled
    exact hwf.setMemory (by rw [show _ = _ from hsz]; exact hwf.memAligned m hmem)
      (by rw [show _ = _ from hsz]; exact hwf.memSize m hmem) (hwf.memMax m hmem)
  | memoryGrow _ _ _ m c _ _ memory grown =>
    have hmem := frameMemory_mem memory
    have hal := hwf.memAligned m hmem
    cases grown with
    | failure => exact hwf.setMemory hal (hwf.memSize m hmem) (hwf.memMax m hmem)
    | success _ hgrow =>
      have hsz := Silmaril.Wasm.Execution.Memory.grow_size _ _ _ _ hgrow
      have hbound : Silmaril.Wasm.Execution.Memory.size m.data + c.toNat ≤
          Silmaril.Wasm.Execution.Memory.maxPages := by
        unfold Silmaril.Wasm.Execution.Memory.grow? at hgrow
        split at hgrow
        · next hc => exact hc.2.1
        · simp at hgrow
      have hdiv : m.data.size =
          Silmaril.Wasm.Execution.Memory.size m.data *
            Silmaril.Wasm.Execution.Memory.pageSize :=
        (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hal)).symm
      have hle : m.data.size + c.toNat * Silmaril.Wasm.Execution.Memory.pageSize ≤ 2 ^ 32 := by
        rw [hdiv, ← Nat.add_mul]
        calc (Silmaril.Wasm.Execution.Memory.size m.data + c.toNat) *
              Silmaril.Wasm.Execution.Memory.pageSize
            ≤ Silmaril.Wasm.Execution.Memory.maxPages *
              Silmaril.Wasm.Execution.Memory.pageSize := Nat.mul_le_mul_right _ hbound
          _ = 2 ^ 32 := by
              simp [Silmaril.Wasm.Execution.Memory.maxPages,
                Silmaril.Wasm.Execution.Memory.pageSize]
      refine hwf.setMemory ?_ ?_ (hwf.memMax m hmem)
      · rw [show _ = _ from hsz, Nat.add_mul_mod_self_right]; exact hal
      · rw [show _ = _ from hsz]; exact hle
  | _ => exact hwf

/-! ### Helpers for the pure simulation -/

namespace ToV2

/-- An integer Lime1 value is a `CONST` of the same type and bits. -/
@[simp] theorem toAdmin_toV2_int (t : IntType) (b : BitVec t.width) :
    (Runtime.Value.toV2 (.int t b)).toAdmin = .plain (.intConst t b) := rfl

/-- A floating-point Lime1 value is a `CONST` of the same type and bits. -/
@[simp] theorem toAdmin_toV2_float (t : FloatType) (b : BitVec t.width) :
    (Runtime.Value.toV2 (.float t b)).toAdmin = .plain (.floatConst t b) := rfl

@[simp] theorem funcType_toV2_params_length (t : FuncType) :
    (FuncType.toV2 t).params.length = t.params.length := List.length_map _

@[simp] theorem funcType_toV2_results_length (t : FuncType) :
    (FuncType.toV2 t).results.length = t.results.length := List.length_map _

/-- `$blockType(z, bt)` (`8-reduction:63-66`) commutes with the injection: a
Lime1 block signature resolved against `types` is the 2.0 signature resolved
against the image of `types`. -/
theorem blockType_toV2 {types : List FuncType} {m : VModuleInst}
    (hm : m.types = types.map FuncType.toV2) {bt : BlockType} {ft : FuncType}
    (h : blockType? types bt = some ft) :
    m.blockType? (BlockType.toV2 bt) = some (FuncType.toV2 ft) := by
  cases bt with
  | empty => cases h; rfl
  | value t => cases h; rfl
  | typeIdx i =>
    simp only [blockType?] at h
    simp only [BlockType.toV2, Silmaril.Wasm.V2.Execution.ModuleInst.blockType?,
      Silmaril.Wasm.V2.Execution.ModuleInst.type?, hm, List.getElem?_map, h, Option.map_some]

end ToV2

/-- Normalise `Admin.listToV2` of a `PureStep` redex into 2.0 administrative
form. The inner values are deliberately left as `(Value.toV2 v).toAdmin`: for a
*concrete* value that term is definitionally a `CONST`, so the final `exact`
closes the goal, whereas `simp` would have to match up the two spellings of a
bit-vector width. -/
local macro "pure_norm" : tactic =>
  `(tactic| simp only [listToV2_cons, listToV2_nil, listToV2_append, values_toV2,
      expression_toV2, source_toV2, value_toV2, trap_toV2, label_toV2, frame_toV2,
      invoke_toV2, Instr.toV2, Expr.toV2_eq_map, List.map_nil, List.map_cons])

/-- **Milestone.** A store-independent Lime1 step is one 2.0 step. `block` and
`loop`, which are `Step_pure` in Lime1 but `Step_read` in 2.0 (their block type
is resolved against the frame's module, `8-reduction:63-66`), are the reason the
statement mentions a frame at all; `hm` is the only thing it needs of it.

The profile is `v2Profile = Profile.spec` and **not** an arbitrary `P`: Lime1's
float rules carry `Numerics.floatUnOpRel`/`floatBinOpRel`/`convertRel`, the full
NaN sets, whereas `V2.Execution.FloatUnOpResult P` is `Numerics.floatUnOpP P`,
which at `P.nan = .canonical` demands the single canonical NaN. The statement is
false for such a `P`, and `Profile.spec` is exactly the profile whose
nondeterminism is Lime1's. -/
theorem PureStep.toV2 {host : VHostSemantics H} {sV : VStore H} {fV : VFrame}
    {types : List FuncType} (hm : fV.module.types = types.map FuncType.toV2)
    {before after : List Admin} (h : PureStep types before after) :
    Silmaril.Wasm.V2.Execution.Step v2Profile host
      ⟨sV, fV, Admin.listToV2 before⟩ ⟨sV, fV, Admin.listToV2 after⟩ := by
  cases h with
  | nop => refine .pure ?_; pure_norm; exact .nop
  | unreachable => refine .pure ?_; pure_norm; exact .unreachable
  | drop v => refine .pure ?_; pure_norm; exact .drop v.toV2
  | selectZero a b _ => refine .pure ?_; pure_norm; exact .selectFalse a.toV2 b.toV2 none
  | selectNonzero a b _ c hc =>
    refine .pure ?_; pure_norm
    exact .selectTrue (v₁ := a.toV2) (v₂ := b.toV2) (ts := none) hc
  | block bt body ft resolved vs arity =>
    refine .read ?_; pure_norm
    rw [← ToV2.funcType_toV2_results_length ft]
    exact .block (ToV2.blockType_toV2 hm resolved) (by simpa using arity)
  | loop bt body ft resolved vs arity =>
    refine .read ?_; pure_norm
    rw [← ToV2.funcType_toV2_params_length ft]
    exact .loop (ToV2.blockType_toV2 hm resolved) (by simpa using arity)
  | ifZero bt left right => refine .pure ?_; pure_norm; exact .ifFalse
  | ifNonzero bt left right c hc => refine .pure ?_; pure_norm; exact .ifTrue hc
  | brIfZero l => refine .pure ?_; pure_norm; exact .brIfFalse
  | brIfNonzero l c hc => refine .pure ?_; pure_norm; exact .brIfTrue hc
  | brTable ls default c =>
    refine .pure ?_; pure_norm
    by_cases hlt : c.toNat < ls.length
    · have hls : ls[c.toNat]? = some ls[c.toNat] := List.getElem?_eq_getElem hlt
      rw [hls]; exact .brTableLt hls
    · have hge : ls.length ≤ c.toNat := Nat.le_of_not_lt hlt
      have hls : ls[c.toNat]? = none := List.getElem?_eq_none hge
      rw [hls]; exact .brTableGe hge
  | labelDone n cont vs => refine .pure ?_; pure_norm; exact .labelVals
  | labelBranch n cont extra vs tail arity =>
    refine .pure ?_; pure_norm
    refine .brZero ?_ ?_
    · rfl
    · simpa using arity
  | labelBranchOuter n cont vs tail l outer =>
    refine .pure ?_; pure_norm
    exact .brSucc (Nat.pos_of_ne_zero outer)
  | labelReturn n cont vs tail => refine .pure ?_; pure_norm; exact .returnLabel
  | frameDone n f vs arity => refine .pure ?_; pure_norm; exact .frameVals (by simpa using arity)
  | frameReturn n f extra vs tail arity =>
    refine .pure ?_; pure_norm; exact .returnFrame (by simpa using arity)
  | trapValues v vs tail =>
    refine .pure ?_; pure_norm
    refine .trapVals (Or.inl ?_); simp
  | trapTail i tail =>
    refine .pure ?_; pure_norm
    refine .trapVals (vs := []) (Or.inr ?_); simp
  | labelTrap n cont => refine .pure ?_; pure_norm; exact .trapLabel
  | frameTrap n f => refine .pure ?_; pure_norm; exact .trapFrame
  | localTee i v => refine .pure ?_; pure_norm; exact .localTee
  | intUnary t op x _ =>
    refine .pure ?_; pure_norm
    exact .intUnOp (by
      simp [Silmaril.Wasm.V2.Execution.IntUnOpResult, IntUnOp.toV2_eq_toCore,
        Silmaril.Wasm.Execution.Runtime.Value.int])
  | intBinary t op x y z hz => refine .pure ?_; pure_norm; exact .intBinOp hz
  | intBinaryTrap t op x y err he => refine .pure ?_; pure_norm; exact .intBinOpTrap ⟨err, he⟩
  | intTest t op x => refine .pure ?_; pure_norm; exact .testOp
  | intRel t op x y => refine .pure ?_; pure_norm; exact .intRelOp
  | floatUnary t op x y hr => refine .pure ?_; pure_norm; exact .floatUnOp hr
  | floatBinary t op x y z hr => refine .pure ?_; pure_norm; exact .floatBinOp hr
  | floatRel t op x y => refine .pure ?_; pure_norm; exact .floatRelOp
  | convert op x y hr =>
    refine .pure ?_; pure_norm
    cases op with
    | reinterpretInt f => cases f <;> exact .cvtOp hr
    | reinterpretFloat i => cases i <;> exact .cvtOp hr
    | trunc f i sg => cases f <;> cases i <;> exact .cvtOp hr
    | truncSat f i sg => cases f <;> cases i <;> exact .cvtOp hr
    | convert i f sg => cases i <;> cases f <;> exact .cvtOp hr
    | _ => exact .cvtOp hr
  | convertTrap op x err hr =>
    refine .pure ?_; pure_norm
    obtain ⟨s, t, sg, rfl⟩ := Silmaril.Wasm.V2.Execution.convert_error_trunc
      (Silmaril.Wasm.V2.Execution.convertP_error (P := v2Profile) hr)
    cases s <;> cases t <;> exact .cvtOpTrap ⟨err, hr⟩

/-! ### Inverting and rebuilding the simulation relation

`Sim a c` says only that `c` *normalises* to `a.toV2`, so a head rule must first
recover `c`'s code from its normal form. For a redex whose image is `Rigid` —
no `LABEL_` and no `FRAME_` — normalisation is the identity and the code is
determined; `sim_mk'` is the general converse, needed for `invokeWasm`, whose
reduct contains a frame that `Sim` only pins down up to `Frame.erase`. -/

namespace ToV2

theorem sim_inv {s : Store H} {f : Frame} {code : List Admin} {cs : VStore H} {cf : VFrame}
    {cl : List VAdmin} (hs : Sim ⟨s, f, code⟩ ⟨cs, cf, cl⟩)
    (hr : ∀ y ∈ Admin.listToV2 code, Rigid y) :
    cl = Admin.listToV2 code ∧ Store.erase cs = s.toV2 ∧
      Frame.erase cf = f.toV2 ∧ StoreWF s := by
  obtain ⟨hn, hwf⟩ := hs
  rw [Config.norm_eq_toV2_iff] at hn
  obtain ⟨h1, h2, h3⟩ := hn
  exact ⟨map_norm_eq_of_rigid hr h3, h1, h2, hwf⟩

theorem sim_mk' {s : Store H} {f : Frame} {code : List Admin} {cs : VStore H} {cf : VFrame}
    {cl : List VAdmin} (hE : Store.erase cs = s.toV2) (hF : Frame.erase cf = f.toV2)
    (hcl : cl.map Admin.norm = Admin.listToV2 code) (hwf : StoreWF s) :
    Sim ⟨s, f, code⟩ ⟨cs, cf, cl⟩ :=
  ⟨Config.norm_eq_toV2_iff.mpr ⟨hE, hF, hcl⟩, hwf⟩

theorem sim_mk {s : Store H} {f : Frame} {code : List Admin} {cs : VStore H} {cf : VFrame}
    (hE : Store.erase cs = s.toV2) (hF : Frame.erase cf = f.toV2) (hwf : StoreWF s) :
    Sim ⟨s, f, code⟩ ⟨cs, cf, Admin.listToV2 code⟩ :=
  sim_mk' hE hF (map_norm_listToV2 code) hwf

/-! ### Rigidity of the Lime1 image -/

theorem rigid_nil : ∀ y ∈ Admin.listToV2 ([] : List Admin), Rigid y := by simp

theorem rigid_value (v : Value) : Rigid (Admin.toV2 (value v)) := by
  rw [value_toV2]; exact Rigid.val _

theorem rigid_source (i : Instr) : Rigid (Admin.toV2 (.source i)) := by
  rw [source_toV2]; trivial

theorem rigid_invoke (a : FuncAddr) : Rigid (Admin.toV2 (.invoke a)) := by
  rw [invoke_toV2]; trivial

theorem rigid_trap : Rigid (Admin.toV2 (.trap : Admin)) := by rw [trap_toV2]; trivial

theorem rigid_cons {a : Admin} {l : List Admin} (ha : Rigid (Admin.toV2 a))
    (hl : ∀ y ∈ Admin.listToV2 l, Rigid y) : ∀ y ∈ Admin.listToV2 (a :: l), Rigid y := by
  intro y hy
  rw [listToV2_cons, List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact ha
  · exact hl y hy

theorem rigid_values {vs : List Value} {l : List Admin}
    (hl : ∀ y ∈ Admin.listToV2 l, Rigid y) :
    ∀ y ∈ Admin.listToV2 (values vs ++ l), Rigid y := by
  intro y hy
  rw [listToV2_append, values_toV2, List.mem_append] at hy
  rcases hy with h | h
  · obtain ⟨v, -, rfl⟩ := List.mem_map.mp h
    exact Rigid.val v
  · exact hl y h

/-! ### Reading the store and the frame off `Store.erase`/`Frame.erase` -/

theorem erase_mems {cs : VStore H} {s : Store H} (hE : Store.erase cs = s.toV2) :
    cs.mems = s.memories.map MemInst.toV2 := by
  have := congrArg Silmaril.Wasm.V2.Execution.Store.mems hE
  simpa [Store.erase, Silmaril.Wasm.Execution.Runtime.Store.toV2] using this

theorem erase_tables {cs : VStore H} {s : Store H} (hE : Store.erase cs = s.toV2) :
    cs.tables = s.tables.map TableInst.toV2 := by
  have := congrArg Silmaril.Wasm.V2.Execution.Store.tables hE
  simpa [Store.erase, Silmaril.Wasm.Execution.Runtime.Store.toV2] using this

theorem erase_globals {cs : VStore H} {s : Store H} (hE : Store.erase cs = s.toV2) :
    cs.globals.map GlobalInst.erase = s.globals.map GlobalInst.toV2 := by
  have := congrArg Silmaril.Wasm.V2.Execution.Store.globals hE
  simpa [Store.erase, Silmaril.Wasm.Execution.Runtime.Store.toV2] using this

theorem erase_funcs {cs : VStore H} {s : Store H} (hE : Store.erase cs = s.toV2) :
    (cs.funcs.map fun fi => { fi with module := ModuleInst.erase fi.module }) =
      s.funcs.map FuncInst.toV2 := by
  have := congrArg Silmaril.Wasm.V2.Execution.Store.funcs hE
  simpa [Store.erase, Silmaril.Wasm.Execution.Runtime.Store.toV2] using this

theorem erase_locals {cf : VFrame} {f : Frame} (hF : Frame.erase cf = f.toV2) :
    cf.locals = f.locals.map Value.toV2 := by
  have := congrArg Silmaril.Wasm.V2.Execution.Frame.locals hF
  simpa [Frame.erase, Silmaril.Wasm.Execution.Runtime.Frame.toV2] using this

theorem erase_types {cf : VFrame} {f : Frame} (hF : Frame.erase cf = f.toV2) :
    cf.module.types = f.module.types.map FuncType.toV2 := by
  have := congrArg (fun fr : VFrame => fr.module.types) hF
  simpa [Frame.erase, ModuleInst.erase, Silmaril.Wasm.Execution.Runtime.Frame.toV2,
    Silmaril.Wasm.Execution.Runtime.ModuleInst.toV2] using this

theorem erase_mfuncs {cf : VFrame} {f : Frame} (hF : Frame.erase cf = f.toV2) :
    cf.module.funcs = f.module.funcs.map Addr.value := by
  have := congrArg (fun fr : VFrame => fr.module.funcs) hF
  simpa [Frame.erase, ModuleInst.erase, Silmaril.Wasm.Execution.Runtime.Frame.toV2,
    Silmaril.Wasm.Execution.Runtime.ModuleInst.toV2] using this

theorem erase_mglobals {cf : VFrame} {f : Frame} (hF : Frame.erase cf = f.toV2) :
    cf.module.globals = f.module.globals.map Addr.value := by
  have := congrArg (fun fr : VFrame => fr.module.globals) hF
  simpa [Frame.erase, ModuleInst.erase, Silmaril.Wasm.Execution.Runtime.Frame.toV2,
    Silmaril.Wasm.Execution.Runtime.ModuleInst.toV2] using this

theorem erase_mtables {cf : VFrame} {f : Frame} (hF : Frame.erase cf = f.toV2) :
    cf.module.tables = f.module.tables.map Addr.value := by
  have := congrArg (fun fr : VFrame => fr.module.tables) hF
  simpa [Frame.erase, ModuleInst.erase, Silmaril.Wasm.Execution.Runtime.Frame.toV2,
    Silmaril.Wasm.Execution.Runtime.ModuleInst.toV2] using this

theorem erase_mmems {cf : VFrame} {f : Frame} (hF : Frame.erase cf = f.toV2) :
    cf.module.mems = f.module.memories.map Addr.value := by
  have := congrArg (fun fr : VFrame => fr.module.mems) hF
  simpa [Frame.erase, ModuleInst.erase, Silmaril.Wasm.Execution.Runtime.Frame.toV2,
    Silmaril.Wasm.Execution.Runtime.ModuleInst.toV2] using this

/-! ### Looking indices up through an erasure -/

/-- Two lists with a common image agree pointwise: this is how a Lime1 store
lookup is transported to the 2.0 store, whose instances are only determined up
to `GlobalInst.erase`/`ModuleInst.erase`. -/
theorem getElem?_of_map_eq {α β γ : Type*} {l : List α} {l' : List β} {g : α → γ} {g' : β → γ}
    (h : l.map g = l'.map g') {i : Nat} {b : β} (hb : l'[i]? = some b) :
    ∃ a, l[i]? = some a ∧ g a = g' b := by
  have h' : (l[i]?).map g = (l'[i]?).map g' := by
    rw [← List.getElem?_map, ← List.getElem?_map, h]
  rw [hb, Option.map_some] at h'
  rcases hl : l[i]? with _ | a
  · rw [hl, Option.map_none] at h'; exact absurd h'.symm (by simp)
  · rw [hl, Option.map_some, Option.some.injEq] at h'
    exact ⟨a, rfl, h'⟩

theorem lookup_memAddr {cf : VFrame} {f : Frame} {s : Store H} {a : MemAddr} {m : MemInst}
    (hF : Frame.erase cf = f.toV2) (hm : frameMemory s f = some (a, m)) :
    cf.module.memAddr? Silmaril.Wasm.V2.Execution.memIdx0 = some a.value := by
  simp only [frameMemory, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨a', ha, m', -, rfl, -⟩ := hm
  simp [Silmaril.Wasm.V2.Execution.ModuleInst.memAddr?, erase_mmems hF,
    Silmaril.Wasm.V2.Execution.memIdx0, Silmaril.Wasm.Idx.toNat, ha]

theorem lookup_memInst {cs : VStore H} {s : Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    (hE : Store.erase cs = s.toV2) (hm : frameMemory s f = some (a, m)) :
    cs.memInst? a.value = some m.toV2 := by
  simp only [frameMemory, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨a', -, m', hm', rfl, rfl⟩ := hm
  simp [Silmaril.Wasm.V2.Execution.Store.memInst?, erase_mems hE, hm']

theorem lookup_mem {cs : VStore H} {cf : VFrame} {s : Store H} {f : Frame} {a : MemAddr}
    {m : MemInst} (hE : Store.erase cs = s.toV2) (hF : Frame.erase cf = f.toV2)
    (hm : frameMemory s f = some (a, m)) :
    (⟨cs, cf⟩ : Silmaril.Wasm.V2.Execution.State H).mem?
      Silmaril.Wasm.V2.Execution.memIdx0 = some m.toV2 := by
  simp [Silmaril.Wasm.V2.Execution.State.mem?, lookup_memAddr hF hm, lookup_memInst hE hm]

theorem lookup_table {cs : VStore H} {cf : VFrame} {s : Store H} {f : Frame} {ti : TableInst}
    {x : TableIdx} (hx : x.toNat = 0) (hE : Store.erase cs = s.toV2)
    (hF : Frame.erase cf = f.toV2) (ht : frameTable s f = some ti) :
    (⟨cs, cf⟩ : Silmaril.Wasm.V2.Execution.State H).table? x = some ti.toV2 := by
  simp only [frameTable, Option.bind_eq_bind, Option.bind_eq_some_iff] at ht
  obtain ⟨a, ha, ht⟩ := ht
  simp [Silmaril.Wasm.V2.Execution.State.table?,
    Silmaril.Wasm.V2.Execution.ModuleInst.tableAddr?,
    Silmaril.Wasm.V2.Execution.Store.tableInst?, erase_mtables hF, erase_tables hE, hx, ha, ht]

theorem lookup_global {cs : VStore H} {cf : VFrame} {s : Store H} {f : Frame} {i : GlobalIdx}
    {a : GlobalAddr} {g : GlobalInst} (hE : Store.erase cs = s.toV2)
    (hF : Frame.erase cf = f.toV2) (index : f.module.globals[i.toNat]? = some a)
    (found : s.globals[a.value]? = some g) :
    ∃ gi, cf.module.globalAddr? i = some a.value ∧ cs.globalInst? a.value = some gi ∧
      GlobalInst.erase gi = g.toV2 := by
  obtain ⟨gi, hgi, hg⟩ := getElem?_of_map_eq (erase_globals hE) found
  exact ⟨gi, by simp [Silmaril.Wasm.V2.Execution.ModuleInst.globalAddr?, erase_mglobals hF, index],
    hgi, hg⟩

theorem lookup_func {cs : VStore H} {s : Store H} {a : FuncAddr} {fn : FuncInst Func H}
    (hE : Store.erase cs = s.toV2) (found : s.funcs[a.value]? = some fn) :
    ∃ fi, cs.funcInst? a.value = some fi ∧
      ({ fi with module := ModuleInst.erase fi.module } : VFuncInst H) = FuncInst.toV2 fn :=
  getElem?_of_map_eq (erase_funcs hE) found

/-! ### Writing through an erasure -/

theorem erase_setMemInst {cs : VStore H} {s : Store H} (hE : Store.erase cs = s.toV2)
    (a : MemAddr) (m' : MemInst) :
    Store.erase (cs.setMemInst a.value m'.toV2) = (setMemory s a m').toV2 := by
  have h : Store.erase (cs.setMemInst a.value m'.toV2)
      = (Store.erase cs).setMemInst a.value m'.toV2 := rfl
  rw [h, hE]
  simp [Silmaril.Wasm.V2.Execution.Store.setMemInst,
    Silmaril.Wasm.Execution.Runtime.Store.toV2, setMemory, List.map_set]

theorem erase_setGlobalInst {cs : VStore H} {s : Store H} (hE : Store.erase cs = s.toV2)
    {a : GlobalAddr} {gi : VGlobalInst} {g : GlobalInst} (h : GlobalInst.erase gi = g.toV2) :
    Store.erase (cs.setGlobalInst a.value gi) = (setGlobal s a g).toV2 := by
  have hh : Store.erase (cs.setGlobalInst a.value gi)
      = (Store.erase cs).setGlobalInst a.value (GlobalInst.erase gi) := by
    simp [Store.erase, Silmaril.Wasm.V2.Execution.Store.setGlobalInst, List.map_set]
  rw [hh, hE, h]
  simp [Silmaril.Wasm.V2.Execution.Store.setGlobalInst,
    Silmaril.Wasm.Execution.Runtime.Store.toV2, setGlobal, List.map_set]

theorem erase_setLocal {cf : VFrame} {f : Frame} (hF : Frame.erase cf = f.toV2) (i : LocalIdx)
    (v : Value) :
    Frame.erase (cf.setLocal i v.toV2) =
      ({ f with locals := f.locals.set i.toNat v } : Frame).toV2 := by
  have hh : Frame.erase (cf.setLocal i v.toV2)
      = (Frame.erase cf).setLocal i v.toV2 := rfl
  rw [hh, hF]
  simp [Silmaril.Wasm.V2.Execution.Frame.setLocal,
    Silmaril.Wasm.Execution.Runtime.Frame.toV2, List.map_set]

/-! ### Lifting 2.0 runs through the evaluation contexts -/

variable {tgt : VHostSemantics H}

theorem transGen_ctxtInstrs {cs cs' : VStore H} {cf cf' : VFrame} {vs : List VVal}
    {is is' rest : List VAdmin}
    (h : Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) ⟨cs, cf, is⟩
      ⟨cs', cf', is'⟩) :
    Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt)
      ⟨cs, cf, Silmaril.Wasm.V2.Execution.vals vs ++ is ++ rest⟩
      ⟨cs', cf', Silmaril.Wasm.V2.Execution.vals vs ++ is' ++ rest⟩ :=
  Relation.TransGen.lift
    (fun c : VConfig H =>
      (⟨c.store, c.frame, Silmaril.Wasm.V2.Execution.vals vs ++ c.code ++ rest⟩ : VConfig H))
    (fun a b hst => by
      rcases a with ⟨sa, fa, ia⟩
      rcases b with ⟨sb, fb, ib⟩
      by_cases hne : vs ≠ [] ∨ rest ≠ []
      · exact Silmaril.Wasm.V2.Execution.Step.ctxtInstrs hst hne
      · simp only [ne_eq, not_or, not_not] at hne
        obtain ⟨rfl, rfl⟩ := hne
        simpa [Silmaril.Wasm.V2.Execution.vals] using hst) _ _ h

theorem transGen_label {cs cs' : VStore H} {cf cf' : VFrame} {n : Nat}
    {cont : List Silmaril.Wasm.V2.Instr} {is is' : List VAdmin}
    (h : Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) ⟨cs, cf, is⟩
      ⟨cs', cf', is'⟩) :
    Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt)
      ⟨cs, cf, [.label n cont is]⟩ ⟨cs', cf', [.label n cont is']⟩ :=
  Relation.TransGen.lift
    (fun c : VConfig H => (⟨c.store, c.frame, [.label n cont c.code]⟩ : VConfig H))
    (fun a b hst => by
      rcases a with ⟨sa, fa, ia⟩; rcases b with ⟨sb, fb, ib⟩
      exact Silmaril.Wasm.V2.Execution.Step.ctxtLabel hst) _ _ h

theorem transGen_frame {cs cs' : VStore H} {cf fi fi' : VFrame} {n : Nat}
    {is is' : List VAdmin}
    (h : Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) ⟨cs, fi, is⟩
      ⟨cs', fi', is'⟩) :
    Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt)
      ⟨cs, cf, [.frame n fi is]⟩ ⟨cs', cf, [.frame n fi' is']⟩ :=
  Relation.TransGen.lift
    (fun c : VConfig H => (⟨c.store, cf, [.frame n c.frame c.code]⟩ : VConfig H))
    (fun a b hst => by
      rcases a with ⟨sa, fa, ia⟩; rcases b with ⟨sb, fb, ib⟩
      exact Silmaril.Wasm.V2.Execution.Step.ctxtFrame hst) _ _ h

/-! ### Inverting normalisation at a label or a frame -/

theorem norm_eq_label {x : VAdmin} {n : Nat} {cont : List Silmaril.Wasm.V2.Instr}
    {b : List VAdmin} (h : Admin.norm x = .label n cont b) :
    ∃ b', x = .label n cont b' ∧ b'.map Admin.norm = b := by
  cases x with
  | label n' cont' b' =>
    rw [Admin.norm_label] at h
    obtain ⟨rfl, rfl, rfl⟩ := Silmaril.Wasm.V2.Execution.Admin.label.inj h
    exact ⟨b', rfl, rfl⟩
  | _ => simp [Admin.norm] at h

theorem norm_eq_frame {x : VAdmin} {n : Nat} {fr : VFrame} {b : List VAdmin}
    (h : Admin.norm x = .frame n fr b) :
    ∃ fr' b', x = .frame n fr' b' ∧ Frame.erase fr' = fr ∧ b'.map Admin.norm = b := by
  cases x with
  | frame n' fr' b' =>
    rw [Admin.norm_frame] at h
    obtain ⟨rfl, rfl, rfl⟩ := Silmaril.Wasm.V2.Execution.Admin.frame.inj h
    exact ⟨fr', b', rfl, rfl, rfl⟩
  | _ => simp [Admin.norm] at h

end ToV2

/-! ### The `Step/pure` case

`Sim` pins the 2.0 code down only up to `Admin.norm`, which rebuilds the frames
inside `FRAME_`. For a redex whose image is `Rigid` that is no loss and
`PureStep.toV2` applies verbatim; the eleven Lime1 `PureStep` rules whose redex
is a `LABEL_`, a `FRAME_` or has an arbitrary tail are done by hand, and each is
again a single 2.0 `Step_pure` — the 2.0 rules quantify over the frame and over
the tail exactly as Lime1's do. -/

namespace ToV2

theorem rigid_vals (vs : List VVal) :
    ∀ y ∈ Silmaril.Wasm.V2.Execution.vals vs, Rigid y := by
  intro y hy
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hy
  exact Rigid.val v

theorem map_norm_vals_inv {l : List VAdmin} {vs : List VVal}
    (h : l.map Admin.norm = Silmaril.Wasm.V2.Execution.vals vs) :
    l = Silmaril.Wasm.V2.Execution.vals vs :=
  map_norm_eq_of_rigid (rigid_vals vs) h

theorem rigid_append {A B : List VAdmin} (hA : ∀ y ∈ A, Rigid y) (hB : ∀ y ∈ B, Rigid y) :
    ∀ y ∈ A ++ B, Rigid y := by
  intro y hy
  rcases List.mem_append.mp hy with h | h
  · exact hA y h
  · exact hB y h

theorem rigid_plain (i : Silmaril.Wasm.V2.Instr) : ∀ y ∈ [(.plain i : VAdmin)], Rigid y := by
  intro y hy; rw [List.mem_singleton] at hy; subst hy; trivial

theorem rigid_trap_singleton : ∀ y ∈ [(.trap : VAdmin)], Rigid y := by
  intro y hy; rw [List.mem_singleton] at hy; subst hy; exact Rigid.trap

theorem map_norm_trap {l : List VAdmin} (h : l.map Admin.norm = [(.trap : VAdmin)]) :
    l = [.trap] :=
  map_norm_eq_of_rigid rigid_trap_singleton h

/-- Peel a rigid prefix off a normalised code sequence: the prefix is determined
exactly, the suffix only up to normalisation. -/
theorem map_norm_split {l : List VAdmin} {A B : List VAdmin} (h : l.map Admin.norm = A ++ B)
    (hA : ∀ y ∈ A, Rigid y) : ∃ t, l = A ++ t ∧ t.map Admin.norm = B := by
  obtain ⟨l1, t, rfl, h1, h2⟩ := List.map_eq_append_iff.mp h
  rw [map_norm_eq_of_rigid hA h1]
  exact ⟨t, rfl, h2⟩

theorem map_norm_label {l : List VAdmin} {n : Nat} {cont : List Silmaril.Wasm.V2.Instr}
    {body : List VAdmin} (h : l.map Admin.norm = [.label n cont body]) :
    ∃ b', l = [.label n cont b'] ∧ b'.map Admin.norm = body := by
  obtain ⟨x, rfl, hx⟩ := List.map_eq_singleton_iff.mp h
  obtain ⟨b', rfl, hb⟩ := norm_eq_label hx
  exact ⟨b', rfl, hb⟩

theorem map_norm_frame {l : List VAdmin} {n : Nat} {fr : VFrame} {body : List VAdmin}
    (h : l.map Admin.norm = [.frame n fr body]) :
    ∃ fr' b', l = [.frame n fr' b'] ∧ Frame.erase fr' = fr ∧ b'.map Admin.norm = body := by
  obtain ⟨x, rfl, hx⟩ := List.map_eq_singleton_iff.mp h
  obtain ⟨fr', b', rfl, hfr, hb⟩ := norm_eq_frame hx
  exact ⟨fr', b', rfl, hfr, hb⟩

theorem pure_of_rigid {host : VHostSemantics H} {cs : VStore H} {cf : VFrame}
    {types : List FuncType} (hm : cf.module.types = types.map FuncType.toV2)
    {before after : List Admin} (h : PureStep types before after) {cl : List VAdmin}
    (hcl : cl.map Admin.norm = Admin.listToV2 before)
    (hr : ∀ y ∈ Admin.listToV2 before, Rigid y) :
    Silmaril.Wasm.V2.Execution.Step v2Profile host ⟨cs, cf, cl⟩
      ⟨cs, cf, Admin.listToV2 after⟩ := by
  rw [map_norm_eq_of_rigid hr hcl]
  exact PureStep.toV2 hm h

end ToV2

open ToV2 in
/-- `PureStep.toV2` up to normalisation of the 2.0 code: this is what the
`Step/pure` case of `Step.toV2` needs, since `Sim` determines the code only up to
`Admin.norm`. -/
theorem PureStep.toV2_norm {host : VHostSemantics H} {cs : VStore H} {cf : VFrame}
    {types : List FuncType} (hm : cf.module.types = types.map FuncType.toV2)
    {before after : List Admin} (h : PureStep types before after) {cl : List VAdmin}
    (hcl : cl.map Admin.norm = Admin.listToV2 before) :
    Silmaril.Wasm.V2.Execution.Step v2Profile host ⟨cs, cf, cl⟩
      ⟨cs, cf, Admin.listToV2 after⟩ := by
  have h' := h
  cases h' with
  | labelDone n cont vs =>
    simp only [listToV2_cons, listToV2_nil, label_toV2, values_toV2] at hcl
    obtain ⟨b', rfl, hb⟩ := map_norm_label hcl
    rw [map_norm_vals_inv hb]
    refine .pure ?_
    simpa using Silmaril.Wasm.V2.Execution.PureStep.labelVals (P := v2Profile)
      (n := n) (cont := cont.map Instr.toV2) (vs := vs.map Value.toV2)
  | labelBranch n cont extra vs tail arity =>
    simp only [listToV2_cons, listToV2_nil, label_toV2, listToV2_append, values_toV2,
      source_toV2, Instr.toV2] at hcl
    obtain ⟨b', rfl, hb⟩ := map_norm_label hcl
    obtain ⟨t, rfl, -⟩ := map_norm_split hb
      (rigid_append (rigid_append (rigid_vals _) (rigid_vals _)) (rigid_plain _))
    refine .pure ?_
    simp only [listToV2_append, values_toV2, expression_toV2, Expr.toV2_eq_map]
    refine .brZero ?_ ?_
    · rfl
    · simpa using arity
  | labelBranchOuter n cont vs tail l outer =>
    simp only [listToV2_cons, listToV2_nil, label_toV2, listToV2_append, values_toV2,
      source_toV2, Instr.toV2] at hcl
    obtain ⟨b', rfl, hb⟩ := map_norm_label hcl
    obtain ⟨t, rfl, -⟩ := map_norm_split hb (rigid_append (rigid_vals _) (rigid_plain _))
    refine .pure ?_
    simp only [listToV2_append, values_toV2, listToV2_cons, listToV2_nil, source_toV2,
      Instr.toV2]
    exact Silmaril.Wasm.V2.Execution.PureStep.brSucc (P := v2Profile) (n := n)
      (cont := cont.map Instr.toV2) (vs := vs.map Value.toV2) (l := l) (rest := t)
      (Nat.pos_of_ne_zero outer)
  | labelReturn n cont vs tail =>
    simp only [listToV2_cons, listToV2_nil, label_toV2, listToV2_append, values_toV2,
      source_toV2, Instr.toV2] at hcl
    obtain ⟨b', rfl, hb⟩ := map_norm_label hcl
    obtain ⟨t, rfl, -⟩ := map_norm_split hb (rigid_append (rigid_vals _) (rigid_plain _))
    refine .pure ?_
    simp only [listToV2_append, values_toV2, listToV2_cons, listToV2_nil, source_toV2,
      Instr.toV2]
    exact Silmaril.Wasm.V2.Execution.PureStep.returnLabel (P := v2Profile) (n := n)
      (cont := cont.map Instr.toV2) (vs := vs.map Value.toV2) (rest := t)
  | labelTrap n cont =>
    simp only [listToV2_cons, listToV2_nil, label_toV2, trap_toV2] at hcl
    obtain ⟨b', rfl, hb⟩ := map_norm_label hcl
    rw [map_norm_trap hb]
    refine .pure ?_
    simpa using Silmaril.Wasm.V2.Execution.PureStep.trapLabel (P := v2Profile)
      (n := n) (cont := cont.map Instr.toV2)
  | frameDone n fr vs arity =>
    simp only [listToV2_cons, listToV2_nil, frame_toV2, values_toV2] at hcl
    obtain ⟨fr', b', rfl, -, hb⟩ := map_norm_frame hcl
    rw [map_norm_vals_inv hb]
    refine .pure ?_
    simpa using Silmaril.Wasm.V2.Execution.PureStep.frameVals (P := v2Profile)
      (n := n) (fr := fr') (vs := vs.map Value.toV2) (by simpa using arity)
  | frameReturn n fr extra vs tail arity =>
    simp only [listToV2_cons, listToV2_nil, frame_toV2, listToV2_append, values_toV2,
      source_toV2, Instr.toV2] at hcl
    obtain ⟨fr', b', rfl, -, hb⟩ := map_norm_frame hcl
    obtain ⟨t, rfl, -⟩ := map_norm_split hb
      (rigid_append (rigid_append (rigid_vals _) (rigid_vals _)) (rigid_plain _))
    refine .pure ?_
    simp only [values_toV2]
    exact Silmaril.Wasm.V2.Execution.PureStep.returnFrame (P := v2Profile) (n := n)
      (fr := fr') (vs' := extra.map Value.toV2) (vs := vs.map Value.toV2) (rest := t)
      (by simpa using arity)
  | frameTrap n fr =>
    simp only [listToV2_cons, listToV2_nil, frame_toV2, trap_toV2] at hcl
    obtain ⟨fr', b', rfl, -, hb⟩ := map_norm_frame hcl
    rw [map_norm_trap hb]
    refine .pure ?_
    simpa using Silmaril.Wasm.V2.Execution.PureStep.trapFrame (P := v2Profile) (n := n) (fr := fr')
  | trapValues v vs tail =>
    simp only [listToV2_append, values_toV2, listToV2_cons, listToV2_nil, trap_toV2] at hcl
    obtain ⟨t, rfl, -⟩ := map_norm_split hcl
      (rigid_append (rigid_vals _) rigid_trap_singleton)
    refine .pure ?_
    simpa using Silmaril.Wasm.V2.Execution.PureStep.trapVals (P := v2Profile)
      (vs := (v :: vs).map Value.toV2) (rest := t) (Or.inl (by simp))
  | trapTail i tail =>
    simp only [listToV2_cons, trap_toV2] at hcl
    obtain ⟨x, t, rfl, h1, h2⟩ := List.map_eq_cons_iff.mp hcl
    rw [Rigid.eq_of_norm Rigid.trap h1]
    refine .pure ?_
    have hne : t ≠ [] := by
      intro hc; rw [hc] at h2; simp at h2
    simpa [Silmaril.Wasm.V2.Execution.vals] using
      Silmaril.Wasm.V2.Execution.PureStep.trapVals (P := v2Profile) (vs := []) (rest := t)
        (Or.inr hne)
  | nop => exact pure_of_rigid hm h hcl (rigid_cons (rigid_source _) rigid_nil)
  | unreachable => exact pure_of_rigid hm h hcl (rigid_cons (rigid_source _) rigid_nil)
  | drop v =>
    exact pure_of_rigid hm h hcl (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))
  | selectZero a b st =>
    exact pure_of_rigid hm h hcl (rigid_cons (rigid_value _) (rigid_cons (rigid_value _)
      (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))))
  | selectNonzero a b st c hc =>
    exact pure_of_rigid hm h hcl (rigid_cons (rigid_value _) (rigid_cons (rigid_value _)
      (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))))
  | block => exact pure_of_rigid hm h hcl (rigid_values (rigid_cons (rigid_source _) rigid_nil))
  | loop => exact pure_of_rigid hm h hcl (rigid_values (rigid_cons (rigid_source _) rigid_nil))
  | ifZero =>
    exact pure_of_rigid hm h hcl (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))
  | ifNonzero =>
    exact pure_of_rigid hm h hcl (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))
  | brIfZero =>
    exact pure_of_rigid hm h hcl (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))
  | brIfNonzero =>
    exact pure_of_rigid hm h hcl (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))
  | brTable =>
    exact pure_of_rigid hm h hcl (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))
  | localTee =>
    exact pure_of_rigid hm h hcl (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))
  | intUnary =>
    exact pure_of_rigid hm h hcl (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))
  | intBinary =>
    exact pure_of_rigid hm h hcl (rigid_cons (rigid_value _) (rigid_cons (rigid_value _)
      (rigid_cons (rigid_source _) rigid_nil)))
  | intBinaryTrap =>
    exact pure_of_rigid hm h hcl (rigid_cons (rigid_value _) (rigid_cons (rigid_value _)
      (rigid_cons (rigid_source _) rigid_nil)))
  | intTest =>
    exact pure_of_rigid hm h hcl (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))
  | intRel =>
    exact pure_of_rigid hm h hcl (rigid_cons (rigid_value _) (rigid_cons (rigid_value _)
      (rigid_cons (rigid_source _) rigid_nil)))
  | floatUnary =>
    exact pure_of_rigid hm h hcl (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))
  | floatBinary =>
    exact pure_of_rigid hm h hcl (rigid_cons (rigid_value _) (rigid_cons (rigid_value _)
      (rigid_cons (rigid_source _) rigid_nil)))
  | floatRel =>
    exact pure_of_rigid hm h hcl (rigid_cons (rigid_value _) (rigid_cons (rigid_value _)
      (rigid_cons (rigid_source _) rigid_nil)))
  | convert =>
    exact pure_of_rigid hm h hcl (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))
  | convertTrap =>
    exact pure_of_rigid hm h hcl (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))

/-! ### The three context cases -/

namespace ToV2

variable {tgt : VHostSemantics H}

/-- `Step/ctxt-instrs`: a value prefix and an arbitrary tail. -/
theorem step_context {s s' : Store H} {f f' : Frame} {before after : List Admin}
    (ih : ∀ c : VConfig H, Sim ⟨s, f, before⟩ c →
      ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
        Sim ⟨s', f', after⟩ c')
    (vs : List Value) (tail : List Admin) {c : VConfig H}
    (hs : Sim ⟨s, f, values vs ++ before ++ tail⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s', f', values vs ++ after ++ tail⟩ c' := by
  obtain ⟨hn, hwf⟩ := hs
  obtain ⟨cs, cf, cl⟩ := c
  rw [Config.norm_eq_toV2_iff] at hn
  obtain ⟨hst, hfr, hl⟩ := hn
  simp only [listToV2_append, values_toV2] at hl
  obtain ⟨l12, l3, rfl, h12, h3⟩ := List.map_eq_append_iff.mp hl
  obtain ⟨l1, l2, rfl, h1, h2⟩ := List.map_eq_append_iff.mp h12
  rw [map_norm_vals_inv h1]
  obtain ⟨⟨cs', cf', l2'⟩, hT, hn', hwf'⟩ := ih ⟨cs, cf, l2⟩ (sim_mk' hst hfr h2 hwf)
  rw [Config.norm_eq_toV2_iff] at hn'
  obtain ⟨hst', hfr', hl2'⟩ := hn'
  refine ⟨⟨cs', cf', Silmaril.Wasm.V2.Execution.vals (vs.map Value.toV2) ++ l2' ++ l3⟩,
    transGen_ctxtInstrs hT, sim_mk' hst' hfr' ?_ hwf'⟩
  simp only [List.map_append, Admin.map_norm_vals, hl2', h3, listToV2_append, values_toV2]

/-- `Step/ctxt-label`. -/
theorem step_label {s s' : Store H} {f f' : Frame} {before after : List Admin}
    (ih : ∀ c : VConfig H, Sim ⟨s, f, before⟩ c →
      ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
        Sim ⟨s', f', after⟩ c')
    (n : Nat) (cont : Expr) {c : VConfig H}
    (hs : Sim ⟨s, f, [.label n cont before]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s', f', [.label n cont after]⟩ c' := by
  obtain ⟨hn, hwf⟩ := hs
  obtain ⟨cs, cf, cl⟩ := c
  rw [Config.norm_eq_toV2_iff] at hn
  obtain ⟨hst, hfr, hl⟩ := hn
  simp only [listToV2_cons, listToV2_nil, label_toV2] at hl
  obtain ⟨b', rfl, hb⟩ := map_norm_label hl
  obtain ⟨⟨cs', cf', b''⟩, hT, hn', hwf'⟩ := ih ⟨cs, cf, b'⟩ (sim_mk' hst hfr hb hwf)
  rw [Config.norm_eq_toV2_iff] at hn'
  obtain ⟨hst', hfr', hb''⟩ := hn'
  refine ⟨⟨cs', cf', [.label n (cont.map Instr.toV2) b'']⟩, transGen_label hT,
    sim_mk' hst' hfr' ?_ hwf'⟩
  simp only [listToV2_cons, listToV2_nil, label_toV2, List.map_cons, List.map_nil,
    Admin.norm_label, hb'']

/-- `Step/ctxt-frame`. -/
theorem step_frame {s s' : Store H} {inner inner' : Frame} {before after : List Admin}
    (ih : ∀ c : VConfig H, Sim ⟨s, inner, before⟩ c →
      ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
        Sim ⟨s', inner', after⟩ c')
    (n : Nat) (outer : Frame) {c : VConfig H}
    (hs : Sim ⟨s, outer, [.frame n inner before]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s', outer, [.frame n inner' after]⟩ c' := by
  obtain ⟨hn, hwf⟩ := hs
  obtain ⟨cs, cf, cl⟩ := c
  rw [Config.norm_eq_toV2_iff] at hn
  obtain ⟨hst, hfr, hl⟩ := hn
  simp only [listToV2_cons, listToV2_nil, frame_toV2] at hl
  obtain ⟨fi, b', rfl, hfi, hb⟩ := map_norm_frame hl
  obtain ⟨⟨cs', fi', b''⟩, hT, hn', hwf'⟩ := ih ⟨cs, fi, b'⟩ (sim_mk' hst hfi hb hwf)
  rw [Config.norm_eq_toV2_iff] at hn'
  obtain ⟨hst', hfi', hb''⟩ := hn'
  refine ⟨⟨cs', cf, [.frame n fi' b'']⟩, transGen_frame hT, sim_mk' hst' hfr ?_ hwf'⟩
  simp only [listToV2_cons, listToV2_nil, frame_toV2, List.map_cons, List.map_nil,
    Admin.norm_frame, hb'', hfi']

end ToV2

/-! ### The head rules: variables and calls -/

namespace ToV2

variable {tgt : VHostSemantics H}

theorem step_localGet {s : Store H} {f : Frame} {i : LocalIdx} {v : Value}
    (found : f.locals[i.toNat]? = some v) {c : VConfig H}
    (hs : Sim ⟨s, f, [.source (.localGet i)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s, f, [value v]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs (rigid_cons (rigid_source _) rigid_nil)
  subst hc
  refine ⟨⟨cs, cf, Admin.listToV2 [value v]⟩, ?_, sim_mk hE hF hwf⟩
  refine .single (.read ?_)
  simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2]
  exact .localGet (by
    simp [Silmaril.Wasm.V2.Execution.State.local?, Silmaril.Wasm.V2.Execution.Frame.local?,
      erase_locals hF, found])

theorem step_localSet {s : Store H} {f : Frame} {i : LocalIdx} {v old : Value}
    (found : f.locals[i.toNat]? = some old) {c : VConfig H}
    (hs : Sim ⟨s, f, [value v, .source (.localSet i)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s, { f with locals := f.locals.set i.toNat v }, []⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs
    (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))
  subst hc
  have hlt : i.toNat < cf.locals.length := by
    rw [erase_locals hF, List.length_map]
    exact (List.getElem?_eq_some_iff.mp found).1
  refine ⟨⟨cs, cf.setLocal i v.toV2, Admin.listToV2 []⟩, ?_,
    sim_mk hE (erase_setLocal hF i v) hwf⟩
  refine .single ?_
  simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2]
  exact .localSet hlt

theorem step_globalGet {s : Store H} {f : Frame} {i : GlobalIdx} {a : GlobalAddr}
    {g : GlobalInst} (index : f.module.globals[i.toNat]? = some a)
    (found : s.globals[a.value]? = some g) {c : VConfig H}
    (hs : Sim ⟨s, f, [.source (.globalGet i)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s, f, [value g.value]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs (rigid_cons (rigid_source _) rigid_nil)
  subst hc
  obtain ⟨gi, ha, hg, hgi⟩ := lookup_global hE hF index found
  have hval : gi.value = g.value.toV2 := by
    have := congrArg Silmaril.Wasm.V2.Execution.GlobalInst.value hgi
    simpa [GlobalInst.erase, Silmaril.Wasm.Execution.Runtime.GlobalInst.toV2] using this
  refine ⟨⟨cs, cf, Admin.listToV2 [value g.value]⟩, ?_, sim_mk hE hF hwf⟩
  refine .single (.read ?_)
  simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2, ← hval]
  exact .globalGet (by simp [Silmaril.Wasm.V2.Execution.State.global?, ha, hg])

theorem step_globalSet {s : Store H} {f : Frame} {i : GlobalIdx} {a : GlobalAddr}
    {g : GlobalInst} {v : Value} (index : f.module.globals[i.toNat]? = some a)
    (found : s.globals[a.value]? = some g) {c : VConfig H}
    (hs : Sim ⟨s, f, [value v, .source (.globalSet i)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨setGlobal s a { g with value := v }, f, []⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs
    (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))
  subst hc
  obtain ⟨gi, ha, hg, hgi⟩ := lookup_global hE hF index found
  have hmut : gi.type.mutability = g.mutability := by
    have := congrArg (fun x : VGlobalInst => x.type.mutability) hgi
    simpa [GlobalInst.erase, Silmaril.Wasm.Execution.Runtime.GlobalInst.toV2] using this
  have hera : GlobalInst.erase { gi with value := v.toV2 }
      = ({ g with value := v } : GlobalInst).toV2 := by
    simp [GlobalInst.erase, Silmaril.Wasm.Execution.Runtime.GlobalInst.toV2, hmut,
      Silmaril.Wasm.Execution.Runtime.Value.toV2, Silmaril.Wasm.V2.Execution.Val.type]
  refine ⟨⟨cs.setGlobalInst a.value { gi with value := v.toV2 }, cf, Admin.listToV2 []⟩, ?_,
    sim_mk (erase_setGlobalInst hE hera) hF (hwf.setGlobal _ _)⟩
  refine .single ?_
  simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2]
  exact .globalSet ha hg

theorem step_call {s : Store H} {f : Frame} {i : FuncIdx} {a : FuncAddr}
    (found : f.module.funcs[i.toNat]? = some a) {c : VConfig H}
    (hs : Sim ⟨s, f, [.source (.call i)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s, f, [.invoke a]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs (rigid_cons (rigid_source _) rigid_nil)
  subst hc
  refine ⟨⟨cs, cf, Admin.listToV2 [.invoke a]⟩, ?_, sim_mk hE hF hwf⟩
  refine .single (.read ?_)
  simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, invoke_toV2]
  exact .call (by
    simp [Silmaril.Wasm.V2.Execution.ModuleInst.funcAddr?, erase_mfuncs hF, found])

end ToV2

/-! ### The head rules: indirect calls and invocation -/

namespace ToV2

variable {tgt : VHostSemantics H}

theorem funcInst_toV2_type (fn : FuncInst Func H) :
    (FuncInst.toV2 fn).type = FuncType.toV2 fn.type := by cases fn <;> rfl

theorem tableInst_toV2_refs (t : TableInst) :
    (TableInst.toV2 t).refs =
      t.refs.map (fun r => match r with
        | none => .null .funcref
        | some a => .funcAddr a.value) := rfl

theorem map_norm_expression (e : Silmaril.Wasm.V2.Expr) :
    (Silmaril.Wasm.V2.Execution.expression e).map Admin.norm =
      Silmaril.Wasm.V2.Execution.expression e := by
  simp [Silmaril.Wasm.V2.Execution.expression, List.map_map, Function.comp_def]

theorem defaultVal_toV2 (t : NumType) :
    Silmaril.Wasm.V2.Execution.defaultVal (ValType.toV2 t) = (Value.zero t).toV2 := by
  cases t <;> rfl

theorem step_callIndirect {s : Store H} {f : Frame} {i : TypeIdx} {cc : BitVec 32}
    {table : TableInst} {a : FuncAddr} {fn : FuncInst Func H} {ft : FuncType}
    (tableFound : frameTable s f = some table) (typeFound : f.module.types[i.toNat]? = some ft)
    (element : table.refs[cc.toNat]? = some (some a)) (found : s.funcs[a.value]? = some fn)
    (typeMatch : fn.type = ft) {c : VConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 cc), .source (.callIndirect i)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s, f, [.invoke a]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs
    (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))
  subst hc
  obtain ⟨fi, hfi, hfe⟩ := lookup_func hE found
  have hty : fi.type = FuncType.toV2 ft := by
    have := congrArg Silmaril.Wasm.V2.Execution.FuncInst.type hfe
    rw [funcInst_toV2_type, typeMatch] at this
    exact this
  refine ⟨⟨cs, cf, Admin.listToV2 [.invoke a]⟩, ?_, sim_mk hE hF hwf⟩
  refine .single (.read ?_)
  simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2, invoke_toV2]
  refine .callIndirectCall (ti := table.toV2) (i := cc) (lookup_table rfl hE hF tableFound) ?_
    hfi ?_
  · rw [tableInst_toV2_refs, List.getElem?_map, element]; rfl
  · rw [hty]
    simp [Silmaril.Wasm.V2.Execution.State.type?, Silmaril.Wasm.V2.Execution.ModuleInst.type?,
      erase_types hF, typeFound]

theorem step_callIndirectBounds {s : Store H} {f : Frame} {i : TypeIdx} {cc : BitVec 32}
    {table : TableInst} (tableFound : frameTable s f = some table)
    (outOfBounds : table.refs[cc.toNat]? = none) {c : VConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 cc), .source (.callIndirect i)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s, f, [.trap]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs
    (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))
  subst hc
  have hrefs : (TableInst.toV2 table).refs[cc.toNat]? = none := by
    rw [tableInst_toV2_refs, List.getElem?_map, outOfBounds]; rfl
  refine ⟨⟨cs, cf, Admin.listToV2 [.trap]⟩, ?_, sim_mk hE hF hwf⟩
  refine .single (.read ?_)
  simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2, trap_toV2]
  refine .callIndirectTrap (ti := table.toV2) (i := cc) (lookup_table rfl hE hF tableFound) ?_
  rintro ⟨a', fi, hr, -, -⟩
  rw [hrefs] at hr
  exact absurd hr (by simp)

theorem step_callIndirectNull {s : Store H} {f : Frame} {i : TypeIdx} {cc : BitVec 32}
    {table : TableInst} (tableFound : frameTable s f = some table)
    (null : table.refs[cc.toNat]? = some none) {c : VConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 cc), .source (.callIndirect i)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s, f, [.trap]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs
    (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))
  subst hc
  have hrefs : (TableInst.toV2 table).refs[cc.toNat]? =
      some (.null .funcref) := by
    rw [tableInst_toV2_refs, List.getElem?_map, null]; rfl
  refine ⟨⟨cs, cf, Admin.listToV2 [.trap]⟩, ?_, sim_mk hE hF hwf⟩
  refine .single (.read ?_)
  simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2, trap_toV2]
  refine .callIndirectTrap (ti := table.toV2) (i := cc) (lookup_table rfl hE hF tableFound) ?_
  rintro ⟨a', fi, hr, -, -⟩
  rw [hrefs, Option.some.injEq] at hr
  exact Silmaril.Wasm.V2.Execution.Ref.noConfusion hr

theorem step_callIndirectType {s : Store H} {f : Frame} {i : TypeIdx} {cc : BitVec 32}
    {table : TableInst} {a : FuncAddr} {fn : FuncInst Func H} {ft : FuncType}
    (tableFound : frameTable s f = some table) (typeFound : f.module.types[i.toNat]? = some ft)
    (element : table.refs[cc.toNat]? = some (some a)) (found : s.funcs[a.value]? = some fn)
    (typeMismatch : fn.type ≠ ft) {c : VConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 cc), .source (.callIndirect i)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s, f, [.trap]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs
    (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))
  subst hc
  obtain ⟨fi, hfi, hfe⟩ := lookup_func hE found
  have hty : fi.type = FuncType.toV2 fn.type := by
    have := congrArg Silmaril.Wasm.V2.Execution.FuncInst.type hfe
    rw [funcInst_toV2_type] at this
    exact this
  have hrefs : (TableInst.toV2 table).refs[cc.toNat]? = some (.funcAddr a.value) := by
    rw [tableInst_toV2_refs, List.getElem?_map, element]; rfl
  have htype : (⟨cs, cf⟩ : Silmaril.Wasm.V2.Execution.State H).type? i
      = some (FuncType.toV2 ft) := by
    simp [Silmaril.Wasm.V2.Execution.State.type?, Silmaril.Wasm.V2.Execution.ModuleInst.type?,
      erase_types hF, typeFound]
  refine ⟨⟨cs, cf, Admin.listToV2 [.trap]⟩, ?_, sim_mk hE hF hwf⟩
  refine .single (.read ?_)
  simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2, trap_toV2]
  refine .callIndirectTrap (ti := table.toV2) (i := cc) (lookup_table rfl hE hF tableFound) ?_
  rintro ⟨a', fi', hr, hf', hy'⟩
  rw [hrefs, Option.some.injEq] at hr
  cases hr
  rw [hfi, Option.some.injEq] at hf'
  cases hf'
  rw [htype, Option.some.injEq, hty] at hy'
  exact typeMismatch (FuncType.toV2_injective hy'.symm)

theorem step_invokeWasm {s : Store H} {f : Frame} {a : FuncAddr} {ft : FuncType}
    {module : ModuleInst} {fn : Func} {args : List Value}
    (found : s.funcs[a.value]? = some (.wasm ft module fn))
    (arity : args.length = ft.params.length) {c : VConfig H}
    (hs : Sim ⟨s, f, values args ++ [.invoke a]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s, f, [.frame ft.results.length ⟨args ++ fn.locals.map Value.zero, module⟩
        [.label ft.results.length [] (expression fn.body)]]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs (rigid_values (rigid_cons (rigid_invoke _) rigid_nil))
  subst hc
  obtain ⟨fi, hfi, hfe⟩ := lookup_func hE found
  have hty : fi.type = FuncType.toV2 ft := congrArg Silmaril.Wasm.V2.Execution.FuncInst.type hfe
  have hmod : ModuleInst.erase fi.module = module.toV2 :=
    congrArg Silmaril.Wasm.V2.Execution.FuncInst.module hfe
  have hcode : fi.code = .wasm (Func.toV2 fn) :=
    congrArg Silmaril.Wasm.V2.Execution.FuncInst.code hfe
  refine ⟨⟨cs, cf, [.frame fi.type.results.length
      (Silmaril.Wasm.V2.Execution.Frame.forCall fi.module (args.map Value.toV2)
        (Func.toV2 fn).locals)
      [.label fi.type.results.length [] (Silmaril.Wasm.V2.Execution.expression
        (Func.toV2 fn).body)]]⟩, ?_, sim_mk' hE hF ?_ hwf⟩
  · refine .single (.read ?_)
    simp only [listToV2_append, values_toV2, listToV2_cons, listToV2_nil, invoke_toV2]
    exact .callAddr hfi hcode (by simpa [hty] using arity)
  · have hloc : (Func.toV2 fn).locals = fn.locals.map ValType.toV2 := rfl
    have hbody : (Func.toV2 fn).body = Expr.toV2 fn.body := rfl
    have hfr : Frame.erase (Silmaril.Wasm.V2.Execution.Frame.forCall fi.module
        (args.map Value.toV2) (Func.toV2 fn).locals)
        = (⟨args ++ fn.locals.map Value.zero, module⟩ : Frame).toV2 := by
      rw [hloc]
      simp only [Frame.erase, Silmaril.Wasm.V2.Execution.Frame.forCall, hmod,
        Silmaril.Wasm.Execution.Runtime.Frame.toV2, List.map_append, List.map_map,
        Function.comp_def, Silmaril.Wasm.V2.Execution.Frame.mk.injEq, and_true]
      congr 1
      exact List.map_congr_left fun t _ => defaultVal_toV2 t
    simp only [List.map_cons, List.map_nil, Admin.norm_frame, Admin.norm_label,
      map_norm_expression, listToV2_cons, listToV2_nil, frame_toV2, label_toV2,
      expression_toV2, hty, funcType_toV2_results_length, hfr, hbody]

theorem hostOutcome_returned {out : VHostOutcome H} {s' : Store H} {r : Result}
    (h : HostOutcomeSim (.returned s' r) out) :
    ∃ sV', out = .returned sV' r.toV2 ∧ Store.erase sV' = s'.toV2 := by
  cases out with
  | returned sV rV => exact ⟨sV, by rw [h.2], h.1⟩
  | diverged => exact h.elim

theorem hostOutcome_diverged {out : VHostOutcome H} (h : HostOutcomeSim .diverged out) :
    out = .diverged := by
  cases out with
  | returned sV rV => exact h.elim
  | diverged => rfl

theorem step_invokeHost {src : HostSemantics H} (hosts : HostCompatible src tgt)
    {s s' : Store H} {f : Frame} {a : FuncAddr} {ft : FuncType} {fn : H} {args : List Value}
    {r : Result} (found : s.funcs[a.value]? = some (.host ft fn))
    (arity : args.length = ft.params.length) (behavior : src fn s args (.returned s' r))
    {c : VConfig H} (hs : Sim ⟨s, f, values args ++ [.invoke a]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s', f, result r⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs (rigid_values (rigid_cons (rigid_invoke _) rigid_nil))
  subst hc
  obtain ⟨fi, hfi, hfe⟩ := lookup_func hE found
  have hty : fi.type = FuncType.toV2 ft := congrArg Silmaril.Wasm.V2.Execution.FuncInst.type hfe
  have hcode : fi.code = .host fn := congrArg Silmaril.Wasm.V2.Execution.FuncInst.code hfe
  obtain ⟨outV, htgt, hsim⟩ := hosts.2 fn s args _ cs behavior hE
  obtain ⟨sV', rfl, hsV⟩ := hostOutcome_returned hsim
  refine ⟨⟨sV', cf, Admin.listToV2 (result r)⟩, ?_,
    sim_mk hsV hF (hosts.1 _ _ _ _ _ behavior hwf)⟩
  refine .single ?_
  simp only [listToV2_append, values_toV2, listToV2_cons, listToV2_nil, invoke_toV2,
    result_toV2]
  exact .callAddrHost hfi hcode (by simpa [hty] using arity) htgt

theorem step_invokeHostDiverges {src : HostSemantics H} (hosts : HostCompatible src tgt)
    {s : Store H} {f : Frame} {a : FuncAddr} {ft : FuncType} {fn : H} {args : List Value}
    (found : s.funcs[a.value]? = some (.host ft fn))
    (arity : args.length = ft.params.length) (behavior : src fn s args .diverged)
    {c : VConfig H} (hs : Sim ⟨s, f, values args ++ [.invoke a]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s, f, values args ++ [.invoke a]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs (rigid_values (rigid_cons (rigid_invoke _) rigid_nil))
  subst hc
  obtain ⟨fi, hfi, hfe⟩ := lookup_func hE found
  have hty : fi.type = FuncType.toV2 ft := congrArg Silmaril.Wasm.V2.Execution.FuncInst.type hfe
  have hcode : fi.code = .host fn := congrArg Silmaril.Wasm.V2.Execution.FuncInst.code hfe
  obtain ⟨outV, htgt, hsim⟩ := hosts.2 fn s args _ cs behavior hE
  rw [hostOutcome_diverged hsim] at htgt
  refine ⟨⟨cs, cf, Admin.listToV2 (values args ++ [.invoke a])⟩, ?_, sim_mk hE hF hwf⟩
  refine .single ?_
  simp only [listToV2_append, values_toV2, listToV2_cons, listToV2_nil, invoke_toV2]
  exact .callAddrHostDiv hfi hcode (by simpa [hty] using arity) htgt

end ToV2

/-! ### The head rules: memory

The Lime1 machine reads and writes bytes with the shared
`Silmaril.Wasm.Execution.Memory.load`/`store`, while `8-reduction:489-593` is
written with `$ibytes_`/`$nbytes_` and `readBytes`/`writeBytes`; the two agree,
which is `readBytes_of_load` and `writeBytes_of_store`. -/

namespace ToV2

variable {tgt : VHostSemantics H}

/-- `$ibytes_` recovers the bytes a `Memory.load` decoded. -/
theorem readBytes_of_load {mem : Memory.Bytes} {start count : Nat} {x : BitVec (8 * count)}
    (h : Memory.load mem start count = some x) :
    Memory.readBytes mem start count
      = some (Silmaril.Wasm.V2.Execution.ibytes (8 * count) x) := by
  simp only [Memory.load, Option.map_eq_some_iff] at h
  obtain ⟨bs, hbs, rfl⟩ := h
  have hsz : bs.size = count := Memory.readBytes_size _ _ _ _ hbs
  have hlt : Memory.decodeLE bs < 2 ^ (8 * count) := by
    have hd := Silmaril.Wasm.V2.Execution.decodeLE_lt bs
    rw [hsz] at hd
    have he : (256 : Nat) ^ count = 2 ^ (8 * count) := by
      rw [Nat.pow_mul]
    rwa [he] at hd
  rw [hbs, Silmaril.Wasm.V2.Execution.ibytes,
    Nat.mul_div_cancel_left _ (by decide : 0 < 8), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hlt, ← hsz, Silmaril.Wasm.V2.Execution.encodeLE_decodeLE]

/-- `Memory.store` writes exactly `$ibytes_` of its argument. -/
theorem writeBytes_of_store {mem after : Memory.Bytes} {start count : Nat}
    {x : BitVec (8 * count)} (h : Memory.store mem start x = some after) :
    Memory.writeBytes mem start (Silmaril.Wasm.V2.Execution.ibytes (8 * count) x)
      = some after := by
  rw [Silmaril.Wasm.V2.Execution.ibytes, Nat.mul_div_cancel_left _ (by decide : 0 < 8)]
  exact h

theorem memInst_toV2_bytes (m : MemInst) (b : Memory.Bytes) (h : b.size = m.data.size) :
    ({ (MemInst.toV2 m) with bytes := b } : VMemInst)
      = ({ m with data := b } : MemInst).toV2 := by
  simp [Silmaril.Wasm.Execution.Runtime.MemInst.toV2, h]

theorem writeBytes?_of_store {m : MemInst} {after : Memory.Bytes} {start count : Nat}
    {x : BitVec (8 * count)} (h : Memory.store m.data start x = some after) :
    (MemInst.toV2 m).writeBytes? start count
        (Silmaril.Wasm.V2.Execution.ibytes (8 * count) x)
      = some ({ m with data := after } : MemInst).toV2 := by
  have hsz : after.size = m.data.size := Memory.writeBytes_size _ _ _ _ h
  simp only [Silmaril.Wasm.V2.Execution.MemInst.writeBytes?,
    Silmaril.Wasm.V2.Execution.ibytes_size, Nat.mul_div_cancel_left _ (by decide : 0 < 8),
    ↓reduceIte]
  show (Memory.writeBytes (MemInst.toV2 m).bytes start _).map _ = _
  rw [show (MemInst.toV2 m).bytes = m.data from rfl, writeBytes_of_store h, Option.map_some,
    memInst_toV2_bytes m after hsz]

theorem frameMemory_wf {s : Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    (hwf : StoreWF s) (hm : frameMemory s f = some (a, m)) :
    m.data.size % Memory.pageSize = 0 ∧ m.data.size ≤ 2 ^ 32 ∧ ∀ j ∈ m.max, j < 2 ^ 32 :=
  ⟨hwf.memAligned m (frameMemory_mem hm), hwf.memSize m (frameMemory_mem hm),
    hwf.memMax m (frameMemory_mem hm)⟩

theorem setMemory_self {s : Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    (hm : frameMemory s f = some (a, m)) : setMemory s a m = s := by
  have h := frameMemory_getElem? hm
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp h
  simp only [setMemory]
  rw [← heq, List.set_getElem_self hlt]

end ToV2

/-! ### The head rules: loads, stores, size and growth -/

namespace ToV2

variable {tgt : VHostSemantics H}

theorem step_intLoad {s : Store H} {f : Frame} {t : IntType}
    {packed : Option (PackSize × Signedness)} {arg : MemArg} {cc : BitVec 32}
    {a : MemAddr} {m : MemInst} {v : Value}
    (memory : frameMemory s f = some (a, m))
    (loaded : loadInt t packed m.data (effectiveAddress cc arg) = some v) {c : VConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 cc), .source (.intLoad t packed arg)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s, f, [value v]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs
    (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))
  subst hc
  have hm := lookup_mem hE hF memory
  refine ⟨⟨cs, cf, Admin.listToV2 [value v]⟩, ?_, sim_mk hE hF hwf⟩
  refine .single (.read ?_)
  simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2, loadPackToV2]
  rcases packed with _ | ⟨pk, sx⟩
  · simp only [loadInt, Option.map_eq_some_iff] at loaded
    obtain ⟨x, hx, rfl⟩ := loaded
    cases t <;>
      exact .loadIntVal (i := cc) hm (readBytes_of_load hx)
  · simp only [loadInt, Option.map_eq_some_iff] at loaded
    obtain ⟨x, hx, rfl⟩ := loaded
    simp only [Option.map_some, PackSize.toV2]
    cases pk <;> cases sx <;> cases t <;> exact .loadPackVal (i := cc) hm (readBytes_of_load hx)

theorem step_intLoadTrap {s : Store H} {f : Frame} {t : IntType}
    {packed : Option (PackSize × Signedness)} {arg : MemArg} {cc : BitVec 32}
    {a : MemAddr} {m : MemInst}
    (memory : frameMemory s f = some (a, m))
    (loaded : loadInt t packed m.data (effectiveAddress cc arg) = none) {c : VConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 cc), .source (.intLoad t packed arg)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s, f, [.trap]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs
    (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))
  subst hc
  have hm := lookup_mem hE hF memory
  refine ⟨⟨cs, cf, Admin.listToV2 [.trap]⟩, ?_, sim_mk hE hF hwf⟩
  refine .single (.read ?_)
  simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2, trap_toV2,
    loadPackToV2]
  rcases packed with _ | ⟨pk, sx⟩
  · simp only [loadInt, Option.map_eq_none_iff] at loaded
    cases t <;> exact .loadIntTrap (i := cc) hm (ToCoreSim.mem_load_none loaded)
  · simp only [loadInt, Option.map_eq_none_iff] at loaded
    simp only [Option.map_some, PackSize.toV2]
    cases pk <;> cases sx <;> cases t <;>
      exact .loadPackTrap (i := cc) hm (ToCoreSim.mem_load_none loaded)

theorem step_floatLoad {s : Store H} {f : Frame} {t : FloatType} {arg : MemArg}
    {cc : BitVec 32} {a : MemAddr} {m : MemInst} {v : Value}
    (memory : frameMemory s f = some (a, m))
    (loaded : loadFloat t m.data (effectiveAddress cc arg) = some v) {c : VConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 cc), .source (.floatLoad t arg)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s, f, [value v]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs
    (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))
  subst hc
  have hm := lookup_mem hE hF memory
  refine ⟨⟨cs, cf, Admin.listToV2 [value v]⟩, ?_, sim_mk hE hF hwf⟩
  refine .single (.read ?_)
  simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2]
  simp only [loadFloat, Option.map_eq_some_iff] at loaded
  obtain ⟨x, hx, rfl⟩ := loaded
  cases t <;>
    exact .loadFloatVal (i := cc) hm (readBytes_of_load hx)

theorem step_floatLoadTrap {s : Store H} {f : Frame} {t : FloatType} {arg : MemArg}
    {cc : BitVec 32} {a : MemAddr} {m : MemInst}
    (memory : frameMemory s f = some (a, m))
    (loaded : loadFloat t m.data (effectiveAddress cc arg) = none) {c : VConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 cc), .source (.floatLoad t arg)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s, f, [.trap]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs
    (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))
  subst hc
  have hm := lookup_mem hE hF memory
  refine ⟨⟨cs, cf, Admin.listToV2 [.trap]⟩, ?_, sim_mk hE hF hwf⟩
  refine .single (.read ?_)
  simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2, trap_toV2]
  simp only [loadFloat, Option.map_eq_none_iff] at loaded
  cases t <;> exact .loadFloatTrap (i := cc) hm (ToCoreSim.mem_load_none loaded)

theorem storeWF_set {s : Store H} {f : Frame} {a : MemAddr} {m m' : MemInst}
    (hwf : StoreWF s) (hm : frameMemory s f = some (a, m))
    (hal : m'.data.size % Memory.pageSize = 0) (hsz : m'.data.size ≤ 2 ^ 32)
    (hmax : m'.max = m.max) : StoreWF (setMemory s a m') :=
  hwf.setMemory hal hsz (by rw [hmax]; exact hwf.memMax m (frameMemory_mem hm))

theorem step_intStore {s : Store H} {f : Frame} {t : IntType} {packed : Option PackSize}
    {arg : MemArg} {cc : BitVec 32} {x : BitVec t.width} {a : MemAddr} {m : MemInst}
    {bytes : Memory.Bytes} (memory : frameMemory s f = some (a, m))
    (stored : storeInt t packed m.data (effectiveAddress cc arg) x = some bytes)
    {c : VConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 cc), value (.int t x),
      .source (.intStore t packed arg)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨setMemory s a { m with data := bytes }, f, []⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs
    (rigid_cons (rigid_value _) (rigid_cons (rigid_value _)
      (rigid_cons (rigid_source _) rigid_nil)))
  subst hc
  have hsz : bytes.size = m.data.size := ToCoreSim.mem_store_size stored
  obtain ⟨hal, hle, -⟩ := frameMemory_wf hwf memory
  refine ⟨⟨cs.setMemInst a.value ({ m with data := bytes } : MemInst).toV2, cf,
    Admin.listToV2 []⟩, ?_,
    sim_mk (erase_setMemInst hE a _) hF
      (storeWF_set hwf memory (by rw [show _ = _ from hsz]; exact hal)
        (by rw [show _ = _ from hsz]; exact hle) rfl)⟩
  refine .single ?_
  simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2]
  rcases packed with _ | pk
  · simp only [storeInt, Option.map_none] at stored
    cases t <;>
      exact .storeIntVal (i := cc) (lookup_memAddr hF memory) (lookup_memInst hE memory)
        (writeBytes?_of_store stored)
  · simp only [storeInt, Option.map_some] at stored
    simp only [Option.map_some, PackSize.toV2]
    cases pk <;> cases t <;>
      exact .storePackVal (i := cc) (lookup_memAddr hF memory) (lookup_memInst hE memory)
        (writeBytes?_of_store stored)

theorem step_intStoreTrap {s : Store H} {f : Frame} {t : IntType} {packed : Option PackSize}
    {arg : MemArg} {cc : BitVec 32} {x : BitVec t.width} {a : MemAddr} {m : MemInst}
    (memory : frameMemory s f = some (a, m))
    (stored : storeInt t packed m.data (effectiveAddress cc arg) x = none) {c : VConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 cc), value (.int t x),
      .source (.intStore t packed arg)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s, f, [.trap]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs
    (rigid_cons (rigid_value _) (rigid_cons (rigid_value _)
      (rigid_cons (rigid_source _) rigid_nil)))
  subst hc
  refine ⟨⟨cs, cf, Admin.listToV2 [.trap]⟩, ?_, sim_mk hE hF hwf⟩
  refine .single ?_
  simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2, trap_toV2]
  rcases packed with _ | pk
  · simp only [storeInt, Option.map_none] at stored
    cases t <;>
      exact .storeIntTrap (i := cc) (lookup_memAddr hF memory) (lookup_memInst hE memory)
        (ToCoreSim.mem_store_none stored)
  · simp only [storeInt, Option.map_some] at stored
    simp only [Option.map_some, PackSize.toV2]
    cases pk <;> cases t <;>
      exact .storePackTrap (i := cc) (lookup_memAddr hF memory) (lookup_memInst hE memory)
        (ToCoreSim.mem_store_none stored)

theorem step_floatStore {s : Store H} {f : Frame} {t : FloatType} {arg : MemArg}
    {cc : BitVec 32} {x : BitVec t.width} {a : MemAddr} {m : MemInst}
    {bytes : Memory.Bytes} (memory : frameMemory s f = some (a, m))
    (stored : storeFloat t m.data (effectiveAddress cc arg) x = some bytes) {c : VConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 cc), value (.float t x),
      .source (.floatStore t arg)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨setMemory s a { m with data := bytes }, f, []⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs
    (rigid_cons (rigid_value _) (rigid_cons (rigid_value _)
      (rigid_cons (rigid_source _) rigid_nil)))
  subst hc
  have hsz : bytes.size = m.data.size := ToCoreSim.mem_store_size stored
  obtain ⟨hal, hle, -⟩ := frameMemory_wf hwf memory
  refine ⟨⟨cs.setMemInst a.value ({ m with data := bytes } : MemInst).toV2, cf,
    Admin.listToV2 []⟩, ?_,
    sim_mk (erase_setMemInst hE a _) hF
      (storeWF_set hwf memory (by rw [show _ = _ from hsz]; exact hal)
        (by rw [show _ = _ from hsz]; exact hle) rfl)⟩
  refine .single ?_
  simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2]
  simp only [storeFloat] at stored
  cases t <;>
    exact .storeFloatVal (i := cc) (lookup_memAddr hF memory) (lookup_memInst hE memory)
      (writeBytes?_of_store stored)

theorem step_floatStoreTrap {s : Store H} {f : Frame} {t : FloatType} {arg : MemArg}
    {cc : BitVec 32} {x : BitVec t.width} {a : MemAddr} {m : MemInst}
    (memory : frameMemory s f = some (a, m))
    (stored : storeFloat t m.data (effectiveAddress cc arg) x = none) {c : VConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 cc), value (.float t x),
      .source (.floatStore t arg)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s, f, [.trap]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs
    (rigid_cons (rigid_value _) (rigid_cons (rigid_value _)
      (rigid_cons (rigid_source _) rigid_nil)))
  subst hc
  refine ⟨⟨cs, cf, Admin.listToV2 [.trap]⟩, ?_, sim_mk hE hF hwf⟩
  refine .single ?_
  simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2, trap_toV2]
  simp only [storeFloat] at stored
  cases t <;>
    exact .storeFloatTrap (i := cc) (lookup_memAddr hF memory) (lookup_memInst hE memory)
      (ToCoreSim.mem_store_none stored)

theorem step_memorySize {s : Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    (memory : frameMemory s f = some (a, m)) {c : VConfig H}
    (hs : Sim ⟨s, f, [.source .memorySize]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s, f, [value (.int .i32 (BitVec.ofNat 32 (Memory.size m.data)))]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs (rigid_cons (rigid_source _) rigid_nil)
  subst hc
  obtain ⟨hal, hle, -⟩ := frameMemory_wf hwf memory
  have hk : Memory.size m.data < 2 ^ 32 := by
    have h1 : m.data.size / Memory.pageSize ≤ 2 ^ 32 / Memory.pageSize :=
      Nat.div_le_div_right hle
    have h2 : (2 : Nat) ^ 32 / Memory.pageSize = 65536 := rfl
    rw [h2] at h1
    exact Nat.lt_of_le_of_lt h1 (by norm_num)
  refine ⟨⟨cs, cf, Admin.listToV2
    [value (.int .i32 (BitVec.ofNat 32 (Memory.size m.data)))]⟩, ?_, sim_mk hE hF hwf⟩
  refine .single (.read ?_)
  simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2]
  refine .memorySize (lookup_mem hE hF memory) ?_
  show (BitVec.ofNat 32 (Memory.size m.data)).toNat * Memory.pageSize = m.data.size
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hal)

theorem mem_grow_toV2 {m : MemInst} {delta : Nat} {bytes : Memory.Bytes}
    (h : Memory.grow? m.data m.max delta = some bytes) (hmax : ∀ j ∈ m.max, j < 2 ^ 32) :
    (MemInst.toV2 m).grow? delta = some ({ m with data := bytes } : MemInst).toV2 ∧
      bytes.size % Memory.pageSize = 0 ∧ bytes.size ≤ 2 ^ 32 := by
  unfold Memory.grow? at h
  split_ifs at h with hc
  obtain ⟨hmod, hle, hmx⟩ := hc
  cases h
  have hsz : (m.data ++ (⟨Array.replicate (delta * Memory.pageSize) 0⟩ : ByteArray)).size
      = m.data.size + delta * Memory.pageSize := by
    rw [ByteArray.size_append]
    show m.data.size + (Array.replicate (delta * Memory.pageSize) (0 : UInt8)).size = _
    rw [Array.size_replicate]
  have hdiv : (m.data.size + delta * Memory.pageSize) / Memory.pageSize
      = m.data.size / Memory.pageSize + delta :=
    Nat.add_mul_div_right _ _ (by decide : 0 < Memory.pageSize)
  unfold Memory.size at hle hmx
  have hcond : m.data.size / Memory.pageSize + delta ≤ 2 ^ 16 := by
    simpa [Memory.maxPages] using hle
  have hcond2 : ((MemInst.toV2 m).type.limits.max).all
      (fun j => m.data.size / Memory.pageSize + delta ≤ j.val) = true := by
    rcases hmm : m.max with _ | j₀
    · simp [Silmaril.Wasm.Execution.Runtime.MemInst.toV2, hmm]
    · have hj : j₀ < 2 ^ 32 := hmax j₀ (by rw [hmm]; exact rfl)
      simp only [hmm, Option.isNone_some, Bool.false_eq_true, Option.getD_some,
        false_or] at hmx
      simp only [Silmaril.Wasm.Execution.Runtime.MemInst.toV2, hmm, Option.map_some,
        Option.all_some, decide_eq_true_eq, Fin.ofNat]
      omega
  have hk : m.data.size / Memory.pageSize + delta < 2 ^ 32 :=
    Nat.lt_of_le_of_lt hcond (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · unfold Silmaril.Wasm.V2.Execution.MemInst.grow?
    split_ifs with hcond3
    · have hfin : (⟨m.data.size / Memory.pageSize + delta, hk⟩ : Fin (2 ^ 32))
          = Fin.ofNat (2 ^ 32)
            ((m.data ++ (⟨Array.replicate (delta * Memory.pageSize) 0⟩ : ByteArray)).size
              / Memory.pageSize) := by
        apply Fin.val_injective
        simp only [Fin.ofNat, hsz, hdiv]
        exact (Nat.mod_eq_of_lt hk).symm
      exact congrArg (fun z => some (⟨⟨⟨z, m.max.map (Fin.ofNat (2 ^ 32))⟩⟩,
        m.data ++ ⟨Array.replicate (delta * Memory.pageSize) 0⟩⟩ : VMemInst)) hfin
    · exact absurd ⟨hcond, hcond2⟩ hcond3
  · rw [hsz, Nat.add_mul_mod_self_right]; exact hmod
  · rw [hsz]
    have hkk : m.data.size = m.data.size / Memory.pageSize * Memory.pageSize :=
      (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)).symm
    calc m.data.size + delta * Memory.pageSize
        = (m.data.size / Memory.pageSize + delta) * Memory.pageSize := by
          rw [Nat.add_mul, ← hkk]
      _ ≤ 2 ^ 16 * Memory.pageSize := Nat.mul_le_mul_right _ hcond
      _ = 2 ^ 32 := by decide

theorem step_memoryGrow {s : Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    {cc r : BitVec 32} {bytes : Memory.Bytes} (memory : frameMemory s f = some (a, m))
    (grown : Memory.Grow m.data m.max cc.toNat bytes r) {c : VConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 cc), .source .memoryGrow]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨setMemory s a { m with data := bytes }, f, [value (.int .i32 r)]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs
    (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))
  subst hc
  obtain ⟨hal, hle, hmx⟩ := frameMemory_wf hwf memory
  cases grown with
  | success _ hg =>
    obtain ⟨hgV, hal', hle'⟩ := mem_grow_toV2 hg hmx
    refine ⟨⟨cs.setMemInst a.value ({ m with data := bytes } : MemInst).toV2, cf,
      Admin.listToV2 [value (.int .i32 (BitVec.ofNat 32 (Memory.size m.data)))]⟩, ?_,
      sim_mk (erase_setMemInst hE a _) hF (storeWF_set hwf memory hal' hle' rfl)⟩
    refine .single ?_
    simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2]
    exact .memoryGrowSucceed (n := cc) (lookup_memAddr hF memory) (lookup_memInst hE memory)
      hgV trivial
  | failure =>
    rw [show ({ m with data := m.data } : MemInst) = m from rfl, setMemory_self memory]
    have h1 : (-1 : BitVec 32) = BitVec.allOnes 32 := by decide
    rw [h1]
    refine ⟨⟨cs, cf, Admin.listToV2 [value (.int .i32 (BitVec.allOnes 32))]⟩, ?_,
      sim_mk hE hF hwf⟩
    refine .single ?_
    simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2]
    exact .memoryGrowFail (n := cc) (lookup_memAddr hF memory) (lookup_memInst hE memory)
      (.inl trivial)

end ToV2

/-! ### The head rules: bulk memory

Lime1's `memory.fill`/`memory.copy` are atomic; 2.0's emit a `store8` (and, for
`copy`, a `load8u`) together with the recursive instruction at count `n - 1`
(`8-reduction:617`, `:633`, `:640`). The loops are run by induction on the
count, with the pointwise byte invariants of
`Lime1/ToCore/Sim/MemoryBulk.lean` — statements about `ByteArray` alone, so they
are reused verbatim. -/

namespace ToV2

variable {tgt : VHostSemantics H}

open Silmaril.Wasm.Lime1.Execution.ToCoreSim (bulk_fill_get bulk_fill_none bulk_copy_get
  bulk_copy_none bulk_store8 bulk_load8 bulk_ext fill_uint8_setWidth)

theorem writeBytes?_of_store' {mi : VMemInst} {after : Memory.Bytes} {start count : Nat}
    {x : BitVec (8 * count)} (h : Memory.store mi.bytes start x = some after) :
    mi.writeBytes? start count (Silmaril.Wasm.V2.Execution.ibytes (8 * count) x)
      = some { mi with bytes := after } := by
  simp only [Silmaril.Wasm.V2.Execution.MemInst.writeBytes?,
    Silmaril.Wasm.V2.Execution.ibytes_size, Nat.mul_div_cancel_left _ (by decide : 0 < 8),
    ↓reduceIte]
  rw [writeBytes_of_store h, Option.map_some]

theorem state_mem? {cs : VStore H} {cf : VFrame} {ma : Nat} {mi : VMemInst}
    (ha : cf.module.memAddr? Silmaril.Wasm.V2.Execution.memIdx0 = some ma)
    (hm : cs.memInst? ma = some mi) :
    (⟨cs, cf⟩ : Silmaril.Wasm.V2.Execution.State H).mem?
      Silmaril.Wasm.V2.Execution.memIdx0 = some mi := by
  simp [Silmaril.Wasm.V2.Execution.State.mem?, ha, hm]

theorem memInst?_setMemInst {cs : VStore H} {ma : Nat} {mi : VMemInst}
    (hm : cs.memInst? ma = some mi) (mi' : VMemInst) :
    (cs.setMemInst ma mi').memInst? ma = some mi' := by
  simp only [Silmaril.Wasm.V2.Execution.Store.memInst?,
    Silmaril.Wasm.V2.Execution.Store.setMemInst] at hm ⊢
  rw [List.getElem?_set_self]
  exact (List.getElem?_eq_some_iff.mp hm).1

theorem setMemInst_self {cs : VStore H} {ma : Nat} {mi : VMemInst}
    (hm : cs.memInst? ma = some mi) : cs.setMemInst ma mi = cs := by
  simp only [Silmaril.Wasm.V2.Execution.Store.memInst?] at hm
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hm
  simp only [Silmaril.Wasm.V2.Execution.Store.setMemInst]
  rw [← heq, List.set_getElem_self hlt]

theorem setMemInst_setMemInst (cs : VStore H) (ma : Nat) (m₁ m₂ : VMemInst) :
    (cs.setMemInst ma m₁).setMemInst ma m₂ = cs.setMemInst ma m₂ := by
  simp [Silmaril.Wasm.V2.Execution.Store.setMemInst]

/-- `(STORE I32 8 $memarg0)` on an in-range address. -/
theorem bulk_store_step {cs : VStore H} {cf : VFrame} {ma : Nat} {mi : VMemInst}
    (ha : cf.module.memAddr? Silmaril.Wasm.V2.Execution.memIdx0 = some ma)
    (hm : cs.memInst? ma = some mi) {d w : BitVec 32} {A : Memory.Bytes}
    (hA : Memory.store mi.bytes d.toNat (count := 1) (w.setWidth 8) = some A) :
    Silmaril.Wasm.V2.Execution.Step v2Profile tgt
      ⟨cs, cf, [Silmaril.Wasm.V2.Execution.constI32 d, Silmaril.Wasm.V2.Execution.constI32 w,
        Silmaril.Wasm.V2.Execution.store8]⟩
      ⟨cs.setMemInst ma { mi with bytes := A }, cf, []⟩ :=
  .storePackVal (t := .i32) (sz := .i8) (ao := Silmaril.Wasm.V2.Execution.memarg0) (i := d)
    (c := w) ha hm (writeBytes?_of_store' hA)

/-- The 2.0 `memory.fill` loop, by induction on the count. -/
theorem fill_loop {cf : VFrame} {ma : Nat}
    (ha : cf.module.memAddr? Silmaril.Wasm.V2.Execution.memIdx0 = some ma) (b : BitVec 32) :
    ∀ (k : Nat) (cs : VStore H) (mi : VMemInst) (i n : BitVec 32),
      cs.memInst? ma = some mi → n.toNat = k → i.toNat + k ≤ mi.bytes.size →
      mi.bytes.size ≤ 2 ^ 32 →
      ∃ B : Memory.Bytes, B.size = mi.bytes.size ∧
        (∀ j, B.data[j]? = if i.toNat ≤ j ∧ j < i.toNat + k then some (UInt8.ofNat b.toNat)
          else mi.bytes.data[j]?) ∧
        Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt)
          ⟨cs, cf, [Silmaril.Wasm.V2.Execution.constI32 i,
            Silmaril.Wasm.V2.Execution.constI32 b,
            Silmaril.Wasm.V2.Execution.constI32 n, .plain .memoryFill]⟩
          ⟨cs.setMemInst ma { mi with bytes := B }, cf, []⟩ := by
  intro k
  induction k with
  | zero =>
    intro cs mi i n hm hn hle _
    have hn0 : n = 0 := BitVec.eq_of_toNat_eq (by simpa using hn)
    subst hn0
    refine ⟨mi.bytes, rfl, fun j => by simp, ?_⟩
    rw [show ({ mi with bytes := mi.bytes } : VMemInst) = mi from rfl, setMemInst_self hm]
    exact .single (.read (.memoryFillZero (i := i) (v := .num ⟨.int .i32, b⟩)
      (state_mem? ha hm) (by omega)))
  | succ k ih =>
    intro cs mi i n hm hn hle hsz
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    have hi1 : i.toNat + 1 ≤ mi.bytes.size := by omega
    obtain ⟨A, hA, hAsz, hAget⟩ := bulk_store8 (M := mi.bytes) (i := i.toNat) (b.setWidth 8) hi1
    have hm' := memInst?_setMemInst hm { mi with bytes := A }
    have hn' : (n - 1).toNat = k := by bv_omega
    have hi' : (i + 1).toNat ≤ i.toNat + 1 := by bv_omega
    have hcase : k = 0 ∨ (i + 1).toNat = i.toNat + 1 := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · exact .inl hk
      · exact .inr (by bv_omega)
    have hle' : (i + 1).toNat + k ≤ (⟨mi.type, A⟩ : VMemInst).bytes.size := by
      show (i + 1).toNat + k ≤ A.size
      rw [hAsz]; omega
    obtain ⟨B, hBsz, hBget, hsteps⟩ := ih (cs.setMemInst ma { mi with bytes := A })
      { mi with bytes := A } (i + 1) (n - 1) hm' hn' hle' (by show A.size ≤ 2 ^ 32; omega)
    refine ⟨B, by rw [hBsz]; exact hAsz, fun j => ?_, ?_⟩
    · rw [hBget j]
      simp only [hAget j]
      split_ifs <;> first | omega | rfl | (congr 1; exact fill_uint8_setWidth b)
    · refine .head (.read (.memoryFillSucc (i := i) (n := n) (v := .num ⟨.int .i32, b⟩)
        (state_mem? ha hm) (by omega) hn0)) ?_
      have hctx := Silmaril.Wasm.V2.Execution.Step.ctxtInstrs (P := v2Profile) (host := tgt)
        (vs := [])
        (rest := [Silmaril.Wasm.V2.Execution.constI32 (i + 1),
          Silmaril.Wasm.V2.Execution.constI32 b,
          Silmaril.Wasm.V2.Execution.constI32 (n - 1), .plain .memoryFill])
        (bulk_store_step (tgt := tgt) ha hm hA) (.inr (by simp))
      simp only [Silmaril.Wasm.V2.Execution.vals, List.map_nil, List.nil_append,
        List.cons_append] at hctx
      refine .head hctx ?_
      rw [setMemInst_setMemInst] at hsteps
      exact hsteps

theorem step_memoryFill {s : Store H} {f : Frame} {d byte n : BitVec 32} {a : MemAddr}
    {m : MemInst} {bytes : Memory.Bytes} (memory : frameMemory s f = some (a, m))
    (filled : Memory.fill m.data d.toNat (UInt8.ofNat byte.toNat) n.toNat = some bytes)
    {c : VConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 d), value (.int .i32 byte), value (.int .i32 n),
      .source .memoryFill]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨setMemory s a { m with data := bytes }, f, []⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs
    (rigid_cons (rigid_value _) (rigid_cons (rigid_value _)
      (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))))
  subst hc
  obtain ⟨hal, hle, -⟩ := frameMemory_wf hwf memory
  have hsize : bytes.size = m.data.size := Memory.writeBytes_size _ _ _ _ filled
  have hbound : d.toNat + n.toNat ≤ m.data.size := by
    have h := (bulk_fill_none (M := m.data) (d := d.toNat) (n := n.toNat)
      (b := UInt8.ofNat byte.toNat)).not.mp (by rw [filled]; simp)
    omega
  obtain ⟨B, hBsz, hBget, hsteps⟩ := fill_loop (tgt := tgt) (lookup_memAddr hF memory) byte
    n.toNat cs (MemInst.toV2 m) d n (lookup_memInst hE memory) rfl
    (by show d.toNat + n.toNat ≤ m.data.size; omega) (by show m.data.size ≤ 2 ^ 32; exact hle)
  have hB : B = bytes := bulk_ext fun j => by
    rw [hBget j, bulk_fill_get filled j]; rfl
  subst hB
  refine ⟨⟨cs.setMemInst a.value ({ m with data := B } : MemInst).toV2, cf,
    Admin.listToV2 []⟩, ?_,
    sim_mk (erase_setMemInst hE a _) hF
      (storeWF_set hwf memory (by rw [show _ = _ from hsize]; exact hal)
        (by rw [show _ = _ from hsize]; exact hle) rfl)⟩
  simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2]
  rw [← memInst_toV2_bytes m B hsize]
  exact hsteps

theorem step_memoryFillTrap {s : Store H} {f : Frame} {d byte n : BitVec 32} {a : MemAddr}
    {m : MemInst} (memory : frameMemory s f = some (a, m))
    (filled : Memory.fill m.data d.toNat (UInt8.ofNat byte.toNat) n.toNat = none)
    {c : VConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 d), value (.int .i32 byte), value (.int .i32 n),
      .source .memoryFill]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s, f, [.trap]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs
    (rigid_cons (rigid_value _) (rigid_cons (rigid_value _)
      (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))))
  subst hc
  have hlt := bulk_fill_none.mp filled
  refine ⟨⟨cs, cf, Admin.listToV2 [.trap]⟩, ?_, sim_mk hE hF hwf⟩
  refine .single (.read ?_)
  simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2, trap_toV2]
  exact .memoryFillTrap (i := d) (n := n) (v := .num ⟨.int .i32, byte⟩)
    (lookup_mem hE hF memory) hlt

end ToV2

/-! ### The head rules: `memory.copy` -/

namespace ToV2

variable {tgt : VHostSemantics H}

open Silmaril.Wasm.Lime1.Execution.ToCoreSim (bulk_copy_get bulk_copy_none bulk_store8
  bulk_load8 bulk_ext cp_setWidth)

/-- The 2.0 `memory.copy` redex on memory `0`. -/
def cpCode (d sa n : BitVec 32) : List VAdmin :=
  [Silmaril.Wasm.V2.Execution.constI32 d, Silmaril.Wasm.V2.Execution.constI32 sa,
    Silmaril.Wasm.V2.Execution.constI32 n, .plain .memoryCopy]

/-- One byte move: `d s load8u store8` followed by `rest` reduces in two steps to
`rest`, with byte `d` set to byte `s`. -/
theorem cp_move {cs : VStore H} {cf : VFrame} {ma : Nat} {mi : VMemInst}
    (ha : cf.module.memAddr? Silmaril.Wasm.V2.Execution.memIdx0 = some ma)
    (hm : cs.memInst? ma = some mi) (d sa : BitVec 32)
    (hd : d.toNat + 1 ≤ mi.bytes.size) (hsrc : sa.toNat + 1 ≤ mi.bytes.size)
    (rest : List VAdmin) (hr : rest ≠ []) :
    ∃ A : Memory.Bytes, A.size = mi.bytes.size ∧
      (∀ j, A.data[j]? = if j = d.toNat then mi.bytes.data[sa.toNat]? else mi.bytes.data[j]?) ∧
      Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt)
        ⟨cs, cf, [Silmaril.Wasm.V2.Execution.constI32 d,
          Silmaril.Wasm.V2.Execution.constI32 sa, Silmaril.Wasm.V2.Execution.load8u,
          Silmaril.Wasm.V2.Execution.store8] ++ rest⟩
        ⟨cs.setMemInst ma { mi with bytes := A }, cf, rest⟩ := by
  obtain ⟨w, hl, hw⟩ := bulk_load8 (M := mi.bytes) (i := sa.toNat) hsrc
  obtain ⟨A, hA, hsz, hget⟩ := bulk_store8 (M := mi.bytes) (i := d.toNat)
    ((w.setWidth 32).setWidth 8) hd
  refine ⟨A, hsz, fun j => ?_, ?_⟩
  · rw [hget j, hw, cp_setWidth]
  · have h1 : Silmaril.Wasm.V2.Execution.Step v2Profile tgt
        ⟨cs, cf, [Silmaril.Wasm.V2.Execution.constI32 d,
          Silmaril.Wasm.V2.Execution.constI32 sa, Silmaril.Wasm.V2.Execution.load8u,
          Silmaril.Wasm.V2.Execution.store8] ++ rest⟩
        ⟨cs, cf, [Silmaril.Wasm.V2.Execution.constI32 d,
          .plain (.intConst .i32 (w.setWidth 32)),
          Silmaril.Wasm.V2.Execution.store8] ++ rest⟩ :=
      Silmaril.Wasm.V2.Execution.Step.ctxtInstrs (vs := [.num ⟨.int .i32, d⟩])
        (is := [Silmaril.Wasm.V2.Execution.constI32 sa, Silmaril.Wasm.V2.Execution.load8u])
        (rest := Silmaril.Wasm.V2.Execution.store8 :: rest)
        (.read (.loadPackVal (t := .i32) (sz := .i8) (sx := .unsigned) (i := sa) (c := w)
          (state_mem? ha hm) (readBytes_of_load hl))) (Or.inl (by simp))
    have h2 : Silmaril.Wasm.V2.Execution.Step v2Profile tgt
        ⟨cs, cf, [Silmaril.Wasm.V2.Execution.constI32 d,
          .plain (.intConst .i32 (w.setWidth 32)),
          Silmaril.Wasm.V2.Execution.store8] ++ rest⟩
        ⟨cs.setMemInst ma { mi with bytes := A }, cf, rest⟩ := by
      have hstep := Silmaril.Wasm.V2.Execution.Step.ctxtInstrs (P := v2Profile) (host := tgt)
        (vs := []) (rest := rest) (bulk_store_step (tgt := tgt) ha hm hA) (Or.inr hr)
      simpa [Silmaril.Wasm.V2.Execution.vals] using hstep
    exact .head h1 (.single h2)

/-- Forward copy (`memory.copy-le`, `8-reduction:633`). -/
theorem copy_fwd {cf : VFrame} {ma : Nat}
    (ha : cf.module.memAddr? Silmaril.Wasm.V2.Execution.memIdx0 = some ma) :
    ∀ (k : Nat) (cs : VStore H) (mi : VMemInst) (d sa n : BitVec 32), n.toNat = k →
      cs.memInst? ma = some mi → mi.bytes.size ≤ 2 ^ 32 →
      d.toNat + k ≤ mi.bytes.size → sa.toNat + k ≤ mi.bytes.size →
      (0 < k → d.toNat ≤ sa.toNat) →
      ∃ B : Memory.Bytes, B.size = mi.bytes.size ∧
        (∀ j, B.data[j]? = if d.toNat ≤ j ∧ j < d.toNat + k then
          mi.bytes.data[sa.toNat + (j - d.toNat)]? else mi.bytes.data[j]?) ∧
        Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt)
          ⟨cs, cf, cpCode d sa n⟩ ⟨cs.setMemInst ma { mi with bytes := B }, cf, []⟩ := by
  intro k
  induction k with
  | zero =>
    intro cs mi d sa n hn hm _ hd hsrc _
    have hn0 : n = 0 := BitVec.eq_of_toNat_eq (by simpa using hn)
    subst hn0
    refine ⟨mi.bytes, rfl, fun j => by simp, ?_⟩
    rw [show ({ mi with bytes := mi.bytes } : VMemInst) = mi from rfl, setMemInst_self hm]
    exact .single (.read (.memoryCopyZero (j := d) (i := sa) (state_mem? ha hm)
      ⟨by omega, by omega⟩))
  | succ k ih =>
    intro cs mi d sa n hn hm hsz hd hsrc hle
    have hle := hle (by omega)
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    obtain ⟨A, hAsz, hA, hst⟩ := cp_move (tgt := tgt) ha hm d sa (by omega) (by omega)
      (cpCode (d + 1) (sa + 1) (n - 1)) (by simp [cpCode])
    have hm' := memInst?_setMemInst hm { mi with bytes := A }
    have hn' : (n - 1).toNat = k := by bv_omega
    have hd1 : (d + 1).toNat ≤ d.toNat + 1 := by bv_omega
    have hs1 : (sa + 1).toNat ≤ sa.toNat + 1 := by bv_omega
    have hd2 : 0 < k → (d + 1).toNat = d.toNat + 1 := by intro; bv_omega
    have hs2 : 0 < k → (sa + 1).toNat = sa.toNat + 1 := by intro; bv_omega
    obtain ⟨B, hBsz, hB, hsteps⟩ := ih (cs.setMemInst ma { mi with bytes := A })
      { mi with bytes := A } (d + 1) (sa + 1) (n - 1) hn' hm'
      (by show A.size ≤ 2 ^ 32; omega) (by show _ ≤ A.size; omega) (by show _ ≤ A.size; omega)
      (by intro hk; rw [hd2 hk, hs2 hk]; omega)
    refine ⟨B, by rw [hBsz]; exact hAsz, fun j => ?_, ?_⟩
    · rw [hB j]
      simp only [hA]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)
      · have e1 := hd2 hk
        have e2 := hs2 hk
        split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)
    · have hc : Silmaril.Wasm.V2.Execution.Step v2Profile tgt ⟨cs, cf, cpCode d sa n⟩
          ⟨cs, cf, [Silmaril.Wasm.V2.Execution.constI32 d,
            Silmaril.Wasm.V2.Execution.constI32 sa, Silmaril.Wasm.V2.Execution.load8u,
            Silmaril.Wasm.V2.Execution.store8] ++ cpCode (d + 1) (sa + 1) (n - 1)⟩ :=
        .read (.memoryCopyLe (j := d) (i := sa) (n := n) (state_mem? ha hm)
          ⟨by omega, by omega⟩ hn0 hle)
      have hfin := hsteps
      rw [setMemInst_setMemInst] at hfin
      exact .head hc (.trans hst hfin)

/-- Backward copy (`memory.copy-gt`, `8-reduction:640`). -/
theorem copy_bwd {cf : VFrame} {ma : Nat}
    (ha : cf.module.memAddr? Silmaril.Wasm.V2.Execution.memIdx0 = some ma) :
    ∀ (k : Nat) (cs : VStore H) (mi : VMemInst) (d sa n : BitVec 32), n.toNat = k →
      cs.memInst? ma = some mi → mi.bytes.size ≤ 2 ^ 32 →
      d.toNat + k ≤ mi.bytes.size → sa.toNat + k ≤ mi.bytes.size →
      (0 < k → sa.toNat < d.toNat) →
      ∃ B : Memory.Bytes, B.size = mi.bytes.size ∧
        (∀ j, B.data[j]? = if d.toNat ≤ j ∧ j < d.toNat + k then
          mi.bytes.data[sa.toNat + (j - d.toNat)]? else mi.bytes.data[j]?) ∧
        Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt)
          ⟨cs, cf, cpCode d sa n⟩ ⟨cs.setMemInst ma { mi with bytes := B }, cf, []⟩ := by
  intro k
  induction k with
  | zero =>
    intro cs mi d sa n hn hm _ hd hsrc _
    have hn0 : n = 0 := BitVec.eq_of_toNat_eq (by simpa using hn)
    subst hn0
    refine ⟨mi.bytes, rfl, fun j => by simp, ?_⟩
    rw [show ({ mi with bytes := mi.bytes } : VMemInst) = mi from rfl, setMemInst_self hm]
    exact .single (.read (.memoryCopyZero (j := d) (i := sa) (state_mem? ha hm)
      ⟨by omega, by omega⟩))
  | succ k ih =>
    intro cs mi d sa n hn hm hsz hd hsrc hlt
    have hlt := hlt (by omega)
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    have hdk : (d + n - 1).toNat = d.toNat + k := by bv_omega
    have hsk : (sa + n - 1).toNat = sa.toNat + k := by bv_omega
    obtain ⟨A, hAsz, hA, hst⟩ := cp_move (tgt := tgt) ha hm (d + n - 1) (sa + n - 1)
      (by omega) (by omega) (cpCode d sa (n - 1)) (by simp [cpCode])
    have hm' := memInst?_setMemInst hm { mi with bytes := A }
    have hn' : (n - 1).toNat = k := by bv_omega
    obtain ⟨B, hBsz, hB, hsteps⟩ := ih (cs.setMemInst ma { mi with bytes := A })
      { mi with bytes := A } d sa (n - 1) hn' hm'
      (by show A.size ≤ 2 ^ 32; omega) (by show _ ≤ A.size; omega) (by show _ ≤ A.size; omega)
      (fun _ => hlt)
    refine ⟨B, by rw [hBsz]; exact hAsz, fun j => ?_, ?_⟩
    · rw [hB j]
      simp only [hA, hdk, hsk]
      split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)
    · have hc : Silmaril.Wasm.V2.Execution.Step v2Profile tgt ⟨cs, cf, cpCode d sa n⟩
          ⟨cs, cf, [Silmaril.Wasm.V2.Execution.constI32 (d + n - 1),
            Silmaril.Wasm.V2.Execution.constI32 (sa + n - 1),
            Silmaril.Wasm.V2.Execution.load8u, Silmaril.Wasm.V2.Execution.store8]
            ++ cpCode d sa (n - 1)⟩ :=
        .read (.memoryCopyGt (j := d) (i := sa) (n := n) (state_mem? ha hm)
          ⟨by omega, by omega⟩ hn0 hlt)
      have hfin := hsteps
      rw [setMemInst_setMemInst] at hfin
      exact .head hc (.trans hst hfin)

theorem step_memoryCopy {s : Store H} {f : Frame} {d src n : BitVec 32} {a : MemAddr}
    {m : MemInst} {bytes : Memory.Bytes} (memory : frameMemory s f = some (a, m))
    (copied : Memory.copy m.data d.toNat src.toNat n.toNat = some bytes) {c : VConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 d), value (.int .i32 src), value (.int .i32 n),
      .source .memoryCopy]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨setMemory s a { m with data := bytes }, f, []⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs
    (rigid_cons (rigid_value _) (rigid_cons (rigid_value _)
      (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))))
  subst hc
  obtain ⟨hal, hle, -⟩ := frameMemory_wf hwf memory
  have hb : ¬ (m.data.size < src.toNat + n.toNat ∨ m.data.size < d.toNat + n.toNat) := by
    intro h; rw [← bulk_copy_none] at h; rw [h] at copied; cases copied
  have hsize : bytes.size = m.data.size := by
    simp only [Memory.copy, Option.bind_eq_bind, Option.bind_eq_some_iff] at copied
    obtain ⟨bs, -, hw⟩ := copied
    exact Memory.writeBytes_size _ bs _ _ hw
  have hmain : ∃ B : Memory.Bytes, B.size = (MemInst.toV2 m).bytes.size ∧
      (∀ j, B.data[j]? = if d.toNat ≤ j ∧ j < d.toNat + n.toNat then
        (MemInst.toV2 m).bytes.data[src.toNat + (j - d.toNat)]?
        else (MemInst.toV2 m).bytes.data[j]?) ∧
      Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt)
        ⟨cs, cf, cpCode d src n⟩
        ⟨cs.setMemInst a.value { (MemInst.toV2 m) with bytes := B }, cf, []⟩ := by
    have h1 : (MemInst.toV2 m).bytes = m.data := rfl
    by_cases hd : d.toNat ≤ src.toNat
    · exact copy_fwd (lookup_memAddr hF memory) n.toNat cs (MemInst.toV2 m) d src n rfl
        (lookup_memInst hE memory) (by rw [h1]; exact hle) (by rw [h1]; omega)
        (by rw [h1]; omega) (fun _ => hd)
    · exact copy_bwd (lookup_memAddr hF memory) n.toNat cs (MemInst.toV2 m) d src n rfl
        (lookup_memInst hE memory) (by rw [h1]; exact hle) (by rw [h1]; omega)
        (by rw [h1]; omega) (fun _ => by omega)
  obtain ⟨B, -, hB, hsteps⟩ := hmain
  have hBeq : B = bytes := bulk_ext fun j => by
    rw [hB j, bulk_copy_get copied j]; rfl
  subst hBeq
  refine ⟨⟨cs.setMemInst a.value ({ m with data := B } : MemInst).toV2, cf,
    Admin.listToV2 []⟩, ?_,
    sim_mk (erase_setMemInst hE a _) hF
      (storeWF_set hwf memory (by rw [show _ = _ from hsize]; exact hal)
        (by rw [show _ = _ from hsize]; exact hle) rfl)⟩
  simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2]
  rw [← memInst_toV2_bytes m B hsize]
  exact hsteps

theorem step_memoryCopyTrap {s : Store H} {f : Frame} {d src n : BitVec 32} {a : MemAddr}
    {m : MemInst} (memory : frameMemory s f = some (a, m))
    (copied : Memory.copy m.data d.toNat src.toNat n.toNat = none) {c : VConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 d), value (.int .i32 src), value (.int .i32 n),
      .source .memoryCopy]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim ⟨s, f, [.trap]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hc, hE, hF, hwf⟩ := sim_inv hs
    (rigid_cons (rigid_value _) (rigid_cons (rigid_value _)
      (rigid_cons (rigid_value _) (rigid_cons (rigid_source _) rigid_nil))))
  subst hc
  have hb := bulk_copy_none.mp copied
  refine ⟨⟨cs, cf, Admin.listToV2 [.trap]⟩, ?_, sim_mk hE hF hwf⟩
  refine .single (.read ?_)
  simp only [listToV2_cons, listToV2_nil, source_toV2, Instr.toV2, value_toV2, trap_toV2]
  exact .memoryCopyTrap (j := d) (i := src) (n := n) (lookup_mem hE hF memory) hb

end ToV2

/-- **Milestone.** One Lime1 step is simulated by at least one 2.0 step.

`Relation.TransGen` rather than a single step because Lime1's `memory.copy` and
`memory.fill` are atomic while 2.0's iterate one byte at a time
(`8-reduction:617`, `:633`, `:640`); every other rule is in fact lock-step, and
`CALL_ADDR` makes `call`, `call_indirect` and the invocations lock-step too —
unlike the Core 3.0 target, where `call` expands to `ref.func; call_ref`. -/
theorem Step.toV2 {src : HostSemantics H} {tgt : VHostSemantics H}
    (hosts : ToV2.HostCompatible src tgt) {a b : Config H} {c : VConfig H}
    (h : Step src a b) (hs : ToV2.Sim a c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      ToV2.Sim b c' := by
  induction h generalizing c with
  | context _ vs tail ih => exact ToV2.step_context (fun _ hh => ih hh) vs tail hs
  | label _ n cont ih => exact ToV2.step_label (fun _ hh => ih hh) n cont hs
  | frame _ n outer ih => exact ToV2.step_frame (fun _ hh => ih hh) n outer hs
  | pure s f hp =>
    obtain ⟨cs, cf, cl⟩ := c
    obtain ⟨hn, hwf⟩ := hs
    rw [ToV2.Config.norm_eq_toV2_iff] at hn
    obtain ⟨hE, hF, hl⟩ := hn
    exact ⟨⟨cs, cf, Admin.listToV2 _⟩,
      .single (PureStep.toV2_norm (ToV2.erase_types hF) hp hl), ToV2.sim_mk hE hF hwf⟩
  | localGet s f i v found => exact ToV2.step_localGet found hs
  | localSet s f i v old found => exact ToV2.step_localSet found hs
  | globalGet s f i a g index found => exact ToV2.step_globalGet index found hs
  | globalSet s f i a g v index found _ => exact ToV2.step_globalSet index found hs
  | call s f i a found => exact ToV2.step_call found hs
  | callIndirect s f i cc table a fn ft tf tyf el found tm =>
    exact ToV2.step_callIndirect tf tyf el found tm hs
  | callIndirectBounds s f i cc table tf oob => exact ToV2.step_callIndirectBounds tf oob hs
  | callIndirectNull s f i cc table tf nl => exact ToV2.step_callIndirectNull tf nl hs
  | callIndirectType s f i cc table a fn ft tf tyf el found tm =>
    exact ToV2.step_callIndirectType tf tyf el found tm hs
  | invokeWasm s f a ft module fn args found arity => exact ToV2.step_invokeWasm found arity hs
  | invokeHost s s' f a ft fn args r found arity behavior =>
    exact ToV2.step_invokeHost hosts found arity behavior hs
  | invokeHostDiverges s f a ft fn args found arity behavior =>
    exact ToV2.step_invokeHostDiverges hosts found arity behavior hs
  | intLoad s f t packed arg cc a m v memory loaded => exact ToV2.step_intLoad memory loaded hs
  | intLoadTrap s f t packed arg cc a m memory loaded =>
    exact ToV2.step_intLoadTrap memory loaded hs
  | floatLoad s f t arg cc a m v memory loaded => exact ToV2.step_floatLoad memory loaded hs
  | floatLoadTrap s f t arg cc a m memory loaded =>
    exact ToV2.step_floatLoadTrap memory loaded hs
  | intStore s f t packed arg cc x a m bytes memory stored =>
    exact ToV2.step_intStore memory stored hs
  | intStoreTrap s f t packed arg cc x a m memory stored =>
    exact ToV2.step_intStoreTrap memory stored hs
  | floatStore s f t arg cc x a m bytes memory stored =>
    exact ToV2.step_floatStore memory stored hs
  | floatStoreTrap s f t arg cc x a m memory stored =>
    exact ToV2.step_floatStoreTrap memory stored hs
  | memorySize s f a m memory => exact ToV2.step_memorySize memory hs
  | memoryGrow s f a m cc r bytes memory grown => exact ToV2.step_memoryGrow memory grown hs
  | memoryCopy s f d srcAddr n a m bytes memory copied =>
    exact ToV2.step_memoryCopy memory copied hs
  | memoryCopyTrap s f d srcAddr n a m memory copied =>
    exact ToV2.step_memoryCopyTrap memory copied hs
  | memoryFill s f d byte n a m bytes memory filled => exact ToV2.step_memoryFill memory filled hs
  | memoryFillTrap s f d byte n a m memory filled =>
    exact ToV2.step_memoryFillTrap memory filled hs

/-- **Milestone.** Finite runs are simulated. -/
theorem Steps.toV2 {src : HostSemantics H} {tgt : VHostSemantics H}
    (hosts : ToV2.HostCompatible src tgt) {a b : Config H} {c : VConfig H}
    (h : Steps src a b) (hs : ToV2.Sim a c) :
    ∃ c', Silmaril.Wasm.V2.Execution.Steps v2Profile tgt c c' ∧ ToV2.Sim b c' :=
  LockstepSim.steps (R := ToV2.Sim) ⟨Step.toV2 hosts⟩ h hs

/-- **Milestone.** Divergence is preserved. This is what `TransGen` rather than
`ReflTransGen` in `Step.toV2` is for. -/
theorem Diverges.toV2 {src : HostSemantics H} {tgt : VHostSemantics H}
    (hosts : ToV2.HostCompatible src tgt) {a : Config H} {c : VConfig H}
    (h : Diverges src a) (hs : ToV2.Sim a c) :
    Silmaril.Wasm.V2.Execution.Diverges v2Profile tgt c :=
  LockstepSim.diverges (R := ToV2.Sim) ⟨Step.toV2 hosts⟩ h hs

/-- A terminal Lime1 result is a terminal 2.0 result. -/
theorem ToV2.Sim.result {a : Config H} {c : VConfig H} {r : Result}
    (hs : ToV2.Sim a c) (hr : a.code = result r) : c.code = r.toV2.toAdmin := by
  obtain ⟨hn, -⟩ := hs
  obtain ⟨cs, cf, cl⟩ := c
  rw [ToV2.Config.norm_eq_toV2_iff] at hn
  obtain ⟨-, -, hl⟩ := hn
  rw [hr, result_toV2] at hl
  refine ToV2.map_norm_eq_of_rigid ?_ hl
  cases r with
  | values vs =>
    simp only [Silmaril.Wasm.Execution.Runtime.Result.toV2,
      Silmaril.Wasm.V2.Execution.Result.toAdmin, Silmaril.Wasm.V2.Execution.vals, List.mem_map]
    rintro _ ⟨v, -, rfl⟩
    exact ToV2.Rigid.val v
  | trap =>
    simp only [Silmaril.Wasm.Execution.Runtime.Result.toV2,
      Silmaril.Wasm.V2.Execution.Result.toAdmin, List.mem_singleton]
    rintro _ rfl
    exact ToV2.Rigid.trap

/-! ## Instantiation

Lime1 *writes* its element and data segments inside `prepare?`, before the start
function runs; Wasm 2.0 instead emits `$runelem`/`$rundata` instruction sequences
into the initial configuration (`9-module:154-165`, `:186-189`) and executes
them. The statement therefore produces two 2.0 configurations: the one
`$instantiate` returns, and the one reached after running the segment programs
and the start function. -/

namespace ToV2

/-- Side conditions for `Instantiation.toV2`.

Compare `Lime1.Execution.InstantiationBounds` (the Core 3.0 analogue): the
`noGlobals` field is **not** needed here, because 2.0's `$instantiate` evaluates
global initialisers in the unallocated store (`9-module:184`) rather than
through Core 3.0's `$evalglobals`, so global addresses do not shift. -/
structure InstantiationBounds (before : Store H) (m : Module) (imports : List ExternVal) :
    Prop where
  /-- The memory/table representability bounds of `ToV2.StoreWF`. -/
  storeWF : StoreWF before
  /-- The `valid` field of `V2.Execution.Instantiate`: 2.0 module validity and
  import matching. It is *not* a premise of SpecTec's `$instantiate`; deriving
  it from `Lime1.Validation.ModuleValid` is the job of
  `Silmaril/Wasm/Lime1/ToV2/Validation.lean` and needs that file's
  `Module.NoExtendedConst` side condition, since Lime1 admits extended constant
  expressions and Wasm 2.0 does not (`Instr_const`, `6-typing:543-557`). It is
  taken as a hypothesis here so that this unit does not depend on a module
  outside it. -/
  valid : ∃ ixt xt, Silmaril.Wasm.V2.Validation.ModuleOk m.toV2 ixt xt ∧
    List.Forall₂ (Silmaril.Wasm.V2.Execution.ExternAddrOk before.toV2)
      (imports.map ExternVal.toV2) ixt
  /-- `$rundata` emits `CONST I32 |b*|` (`9-module:161-165`). -/
  data : ∀ d ∈ m.data, d.bytes.size < 2 ^ 32
  /-- `$runelem` emits `CONST I32 |expr*|` (`9-module:154-159`). -/
  elemSize : ∀ e ∈ m.elems, e.init.length < 2 ^ 32
  /-- `$runelem` passes the segment index as an `elemidx`, a `u32`. -/
  elemCount : m.elems.length ≤ 2 ^ 32
  /-- `$rundata` passes the segment index as a `dataidx`, a `u32`. -/
  dataCount : m.data.length ≤ 2 ^ 32

/-! ### The four `externaddr*` projections -/

theorem externAddr_funcs_toV2 : (imports : List ExternVal) →
    Silmaril.Wasm.V2.Execution.ExternAddr.funcs (imports.map ExternVal.toV2) =
      (importedInstance imports).funcs.map Addr.value
  | [] => rfl
  | .func _ :: rest | .table _ :: rest | .memory _ :: rest | .global _ :: rest => by
      simpa [Silmaril.Wasm.V2.Execution.ExternAddr.funcs, importedInstance,
        ExternVal.toV2] using externAddr_funcs_toV2 rest

theorem externAddr_globals_toV2 : (imports : List ExternVal) →
    Silmaril.Wasm.V2.Execution.ExternAddr.globals (imports.map ExternVal.toV2) =
      (importedInstance imports).globals.map Addr.value
  | [] => rfl
  | .func _ :: rest | .table _ :: rest | .memory _ :: rest | .global _ :: rest => by
      simpa [Silmaril.Wasm.V2.Execution.ExternAddr.globals, importedInstance,
        ExternVal.toV2] using externAddr_globals_toV2 rest

theorem externAddr_tables_toV2 : (imports : List ExternVal) →
    Silmaril.Wasm.V2.Execution.ExternAddr.tables (imports.map ExternVal.toV2) =
      (importedInstance imports).tables.map Addr.value
  | [] => rfl
  | .func _ :: rest | .table _ :: rest | .memory _ :: rest | .global _ :: rest => by
      simpa [Silmaril.Wasm.V2.Execution.ExternAddr.tables, importedInstance,
        ExternVal.toV2] using externAddr_tables_toV2 rest

theorem externAddr_mems_toV2 : (imports : List ExternVal) →
    Silmaril.Wasm.V2.Execution.ExternAddr.mems (imports.map ExternVal.toV2) =
      (importedInstance imports).memories.map Addr.value
  | [] => rfl
  | .func _ :: rest | .table _ :: rest | .memory _ :: rest | .global _ :: rest => by
      simpa [Silmaril.Wasm.V2.Execution.ExternAddr.mems, importedInstance,
        ExternVal.toV2] using externAddr_mems_toV2 rest

/-! ### Inverting Lime1 allocation -/

/-- The allocated Lime1 module instance, before exports are recorded. -/
def baseInstV (s : Store H) (m : Module) (imports : List ExternVal) : ModuleInst where
  types := m.types
  funcs := (importedInstance imports).funcs ++ addresses .func s.funcs.length m.funcs.length
  tables := (importedInstance imports).tables ++ addresses .table s.tables.length m.tables.length
  memories := (importedInstance imports).memories ++
    addresses .memory s.memories.length m.memories.length
  globals := (importedInstance imports).globals ++
    addresses .global s.globals.length m.globals.length

theorem allocate?_invV {s : Store H} {m : Module} {imports : List ExternVal}
    {st : Store H} {mod : ModuleInst} (h : allocate? s m imports = some (st, mod)) :
    ∃ (inits : List Value) (exports : List ExportInst) (funcs : List (FuncInst Func H)),
      m.globals.mapM (fun g =>
        constExpr? s { globals := (importedInstance imports).globals } g.init) = some inits ∧
      m.exports.mapM (fun e => (exportValue? (baseInstV s m imports) e.index).bind
        fun v => some (⟨e.name, v⟩ : ExportInst)) = some exports ∧
      m.funcs.mapM (fun f => (m.types[f.type.toNat]?).bind
        fun ft => some (FuncInst.wasm ft
          { baseInstV s m imports with exports := exports } f)) = some funcs ∧
      mod = { baseInstV s m imports with exports := exports } ∧
      st = ⟨s.funcs ++ funcs,
        s.tables ++ m.tables.map (fun t =>
          TableInst.mk (List.replicate t.limits.min.val none) (t.limits.max.map Fin.val)),
        s.memories ++ m.memories.map (fun t => MemInst.mk
          ⟨Array.replicate (t.limits.min.val * Memory.pageSize) 0⟩ (t.limits.max.map Fin.val)),
        s.globals ++ List.zipWith (fun g v => GlobalInst.mk v g.type.mutability)
          m.globals inits⟩ := by
  simp only [allocate?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨inits, hin, exports, hex, funcs, hfn, h⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨inits, exports, funcs, hin, hex, hfn, rfl, rfl⟩

/-! ### Lime1 constant expressions evaluate in 2.0 -/

/-- A Lime1 constant stack (top at the head) as 2.0 value instructions. -/
def stkV (st : List Value) : List VAdmin :=
  Silmaril.Wasm.V2.Execution.vals ((st.map Value.toV2).reverse)

@[simp] theorem stkV_cons (v : Value) (st : List Value) :
    stkV (v :: st) = stkV st ++ [(Value.toV2 v).toAdmin] := by
  simp [stkV, Silmaril.Wasm.V2.Execution.vals]

section ConstEval

variable {tgt : VHostSemantics H} {cs : VStore H} {cf : VFrame} {s : Store H}
  {module : ModuleInst}

theorem binop_v2 {t : IntType} {op : IntBinOp} {st st' : List Value}
    (h : constBinary? t op st = some st') (rest : List VAdmin) :
    Silmaril.Wasm.V2.Execution.Steps v2Profile tgt
      ⟨cs, cf, stkV st ++ [.plain (Instr.toV2 (.intBinOp t op))] ++ rest⟩
      ⟨cs, cf, stkV st' ++ rest⟩ := by
  obtain ⟨x, y, z, r, rfl, hz, rfl⟩ := constBinary_inv h
  have := Silmaril.Wasm.V2.Execution.Steps.ctxtInstrs (P := v2Profile) (host := tgt)
    (s := cs) (f := cf) ((r.map Value.toV2).reverse) rest
    (Silmaril.Wasm.V2.Execution.Step.steps
      (Silmaril.Wasm.V2.Execution.Step.pure
        (Silmaril.Wasm.V2.Execution.PureStep.intBinOp hz)))
  simpa [stkV, Silmaril.Wasm.V2.Execution.vals, Value.toV2,
    Silmaril.Wasm.V2.Execution.Val.toAdmin, Instr.toV2] using this

theorem constStep_v2 (hG : cs.globals.map GlobalInst.erase = s.globals.map GlobalInst.toV2)
    (hF : cf.module.globals = module.globals.map Addr.value)
    {i : Instr} {st st' : List Value} (h : constStep? s module i st = some st')
    (rest : List VAdmin) :
    Silmaril.Wasm.V2.Execution.Steps v2Profile tgt
      ⟨cs, cf, stkV st ++ [.plain (Instr.toV2 i)] ++ rest⟩ ⟨cs, cf, stkV st' ++ rest⟩ := by
  cases i with
  | intConst t x =>
    simp only [constStep?, constInstr?, Option.map_some, Option.some.injEq] at h
    subst h
    simp only [stkV_cons, List.append_assoc]
    exact Relation.ReflTransGen.refl
  | floatConst t x =>
    simp only [constStep?, constInstr?, Option.map_some, Option.some.injEq] at h
    subst h
    simp only [stkV_cons, List.append_assoc]
    exact Relation.ReflTransGen.refl
  | globalGet x =>
    simp only [constStep?, constInstr?, Option.bind_eq_bind, Option.map_eq_some_iff,
      Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨v, ⟨a, ha, g, hg, rfl⟩, rfl⟩ := h
    obtain ⟨gi, hgi, hgv⟩ := getElem?_of_map_eq hG hg
    have hgl : (⟨cs, cf⟩ : Silmaril.Wasm.V2.Execution.State H).global? x = some gi := by
      simp [Silmaril.Wasm.V2.Execution.State.global?,
        Silmaril.Wasm.V2.Execution.ModuleInst.globalAddr?,
        Silmaril.Wasm.V2.Execution.Store.globalInst?, hF, ha, hgi]
    have hval : gi.value = Value.toV2 g.value := by
      have := congrArg Silmaril.Wasm.V2.Execution.GlobalInst.value hgv
      simpa [GlobalInst.erase, Silmaril.Wasm.Execution.Runtime.GlobalInst.toV2] using this
    have := Silmaril.Wasm.V2.Execution.Steps.ctxtInstrs (P := v2Profile) (host := tgt)
      (s := cs) (f := cf) ((st.map Value.toV2).reverse) rest
      (Silmaril.Wasm.V2.Execution.Step.steps
        (Silmaril.Wasm.V2.Execution.Step.read
          (Silmaril.Wasm.V2.Execution.ReadStep.globalGet hgl)))
    rw [hval] at this
    simpa [stkV, Silmaril.Wasm.V2.Execution.vals, Instr.toV2] using this
  | intBinOp t op =>
    cases op <;> first
      | (simp [constStep?, constInstr?] at h; done)
      | exact binop_v2 (by simpa [constStep?] using h) rest
  | _ => simp [constStep?, constInstr?] at h

theorem constFold_v2 (hG : cs.globals.map GlobalInst.erase = s.globals.map GlobalInst.toV2)
    (hF : cf.module.globals = module.globals.map Addr.value) :
    (es : Expr) → (st st' : List Value) →
    es.foldlM (fun stack i => constStep? s module i stack) st = some st' →
    (rest : List VAdmin) →
    Silmaril.Wasm.V2.Execution.Steps v2Profile tgt
      ⟨cs, cf, stkV st ++ Silmaril.Wasm.V2.Execution.expression (Expr.toV2 es) ++ rest⟩
      ⟨cs, cf, stkV st' ++ rest⟩
  | [], st, st', h, rest => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simpa [Expr.toV2, Silmaril.Wasm.V2.Execution.expression] using
      (Relation.ReflTransGen.refl :
        Silmaril.Wasm.V2.Execution.Steps v2Profile tgt ⟨cs, cf, stkV st ++ rest⟩ _)
  | i :: es, st, st', h, rest => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨st₁, h₁, h₂⟩ := h
    have e1 := constStep_v2 (tgt := tgt) hG hF h₁
      (Silmaril.Wasm.V2.Execution.expression (Expr.toV2 es) ++ rest)
    have e2 := constFold_v2 hG hF es st₁ st' h₂ rest
    simp only [Expr.toV2, Silmaril.Wasm.V2.Execution.expression, List.map_cons,
      List.append_assoc, List.cons_append] at e1 e2 ⊢
    exact e1.trans e2

/-- A Lime1 constant expression is a 2.0 `Eval_expr` to the same value, with the
store and the frame unchanged. -/
theorem constExpr_v2 (hG : cs.globals.map GlobalInst.erase = s.globals.map GlobalInst.toV2)
    (hF : cf.module.globals = module.globals.map Addr.value)
    {es : Expr} {v : Value} (h : constExpr? s module es = some v) :
    Silmaril.Wasm.V2.Execution.EvalExpr v2Profile tgt cs cf (Expr.toV2 es) cs cf
      [Value.toV2 v] := by
  simp only [constExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨vs, hvs, hv⟩ := h
  match vs, hv with
  | [v'], hv =>
    simp only [Option.some.injEq] at hv
    subst hv
    have := constFold_v2 (tgt := tgt) hG hF es [] _ hvs []
    simpa [stkV, Silmaril.Wasm.V2.Execution.vals, Silmaril.Wasm.V2.Execution.EvalExpr] using this

/-- A Lime1 offset expression reduces in 2.0 to its `i32` value. -/
theorem offset_v2 (hG : cs.globals.map GlobalInst.erase = s.globals.map GlobalInst.toV2)
    (hF : cf.module.globals = module.globals.map Addr.value)
    {es : Expr} {off : Nat} (h : offset? s module es = some off) (rest : List VAdmin) :
    ∃ x : BitVec 32, x.toNat = off ∧ Silmaril.Wasm.V2.Execution.Steps v2Profile tgt
      ⟨cs, cf, Silmaril.Wasm.V2.Execution.expression (Expr.toV2 es) ++ rest⟩
      ⟨cs, cf, Silmaril.Wasm.V2.Execution.constI32 x :: rest⟩ := by
  simp only [offset?, constExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨v, ⟨vs, hvs, hv⟩, hoff⟩ := h
  match vs, hv with
  | [v'], hv =>
    simp only [Option.some.injEq] at hv
    subst hv
    rcases v' with ⟨ty, bits⟩
    cases ty with
    | int t =>
      cases t with
      | i32 =>
        simp only [Option.some.injEq] at hoff
        refine ⟨bits, hoff, ?_⟩
        have := constFold_v2 (tgt := tgt) hG hF es [] _ hvs rest
        simpa [stkV, Silmaril.Wasm.V2.Execution.vals, Value.toV2,
          Silmaril.Wasm.V2.Execution.Val.toAdmin,
          Silmaril.Wasm.V2.Execution.constI32] using this
      | i64 => simp at hoff
    | float t => simp at hoff

end ConstEval

/-! ### Allocation of sequences -/

section Alloc

open Silmaril.Wasm.V2.Execution (allocMany allocFuncs allocGlobals allocTables allocMems
  allocElems allocDatas)

theorem allocMany_eqV {α β : Type} (get : VStore H → List β)
    (set : VStore H → List β → VStore H) (g : α → β)
    (alloc : VStore H → α → VStore H × Nat)
    (halloc : ∀ s x, alloc s x = (set s (get s ++ [g x]), (get s).length))
    (hgs : ∀ s l, get (set s l) = l) (hss : ∀ s l l', set (set s l) l' = set s l')
    (hsg : ∀ s, set s (get s) = s) :
    ∀ (xs : List α) (s : VStore H), allocMany alloc s xs =
      (set s (get s ++ xs.map g), (List.range xs.length).map ((get s).length + ·))
  | [], s => by simp [allocMany, hsg]
  | x :: xs, s => by
    have ih := allocMany_eqV get set g alloc halloc hgs hss hsg xs (set s (get s ++ [g x]))
    simp only [allocMany, halloc, ih, hgs, hss, List.length_append,
      List.map_cons, List.length_cons, range_map_succ,
      List.append_assoc, List.singleton_append, List.length_nil, Nat.zero_add]

theorem allocFuncs_eqV (s : VStore H) (mi : VModuleInst)
    (ps : List (Silmaril.Wasm.V2.FuncType × Silmaril.Wasm.V2.Func)) :
    allocFuncs s mi ps = ({ s with funcs := s.funcs ++ ps.map fun p =>
      (⟨p.1, mi, .wasm p.2⟩ : VFuncInst H) },
      (List.range ps.length).map (s.funcs.length + ·)) :=
  allocMany_eqV (·.funcs) (fun s l => { s with funcs := l }) _ _ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ => rfl) ps s

theorem allocGlobals_eqV (s : VStore H) (ps : List (Silmaril.Wasm.V2.GlobalType × VVal)) :
    allocGlobals s ps = ({ s with globals := s.globals ++ ps.map fun p =>
      (⟨p.1, p.2⟩ : VGlobalInst) }, (List.range ps.length).map (s.globals.length + ·)) :=
  allocMany_eqV (·.globals) (fun s l => { s with globals := l }) _ _ (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) ps s

theorem allocTables_eqV (s : VStore H) (ts : List Silmaril.Wasm.V2.TableType) :
    allocTables s ts = ({ s with tables := s.tables ++ ts.map fun tt =>
      (⟨tt, List.replicate tt.limits.min.val (.null tt.element)⟩ : VTableInst) },
      (List.range ts.length).map (s.tables.length + ·)) :=
  allocMany_eqV (·.tables) (fun s l => { s with tables := l }) _ _ (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) ts s

theorem allocMems_eqV (s : VStore H) (ts : List Silmaril.Wasm.V2.MemoryType) :
    allocMems s ts = ({ s with mems := s.mems ++ ts.map fun mt =>
      (⟨mt, ⟨Array.replicate (mt.limits.min.val * Memory.pageSize) 0⟩⟩ : VMemInst) },
      (List.range ts.length).map (s.mems.length + ·)) :=
  allocMany_eqV (·.mems) (fun s l => { s with mems := l }) _ _ (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) ts s

theorem allocElems_eqV (s : VStore H)
    (ps : List (Silmaril.Wasm.V2.ElemType × List Silmaril.Wasm.V2.Execution.Ref)) :
    allocElems s ps = ({ s with elems := s.elems ++ ps.map fun p =>
      (⟨p.1, p.2⟩ : Silmaril.Wasm.V2.Execution.ElemInst) },
      (List.range ps.length).map (s.elems.length + ·)) :=
  allocMany_eqV (·.elems) (fun s l => { s with elems := l }) _ _ (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) ps s

theorem allocDatas_eqV (s : VStore H) (bs : List Memory.Bytes) :
    allocDatas s bs = ({ s with datas := s.datas ++ bs.map fun b =>
      (⟨b⟩ : Silmaril.Wasm.V2.Execution.DataInst) },
      (List.range bs.length).map (s.datas.length + ·)) :=
  allocMany_eqV (·.datas) (fun s l => { s with datas := l }) _ _ (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) bs s

/-- `$allocmodule` computes, given the two partial lookups and the two length
guards. -/
theorem allocModule?_eqV {s : VStore H} {m : Silmaril.Wasm.V2.Module}
    {xas : List Silmaril.Wasm.V2.Execution.ExternAddr} {vs : List VVal}
    {rss : List (List Silmaril.Wasm.V2.Execution.Ref)}
    {fts : List Silmaril.Wasm.V2.FuncType}
    {xi : List Silmaril.Wasm.V2.Execution.ExportInst}
    (hfts : (m.funcs.mapM fun fn => m.types[fn.type.toNat]?) = some fts)
    (hv : vs.length = m.globals.length) (hr : rss.length = m.elems.length)
    (mi₀ : VModuleInst)
    (hmi₀ : mi₀ =
      { types := m.types
        funcs := Silmaril.Wasm.V2.Execution.ExternAddr.funcs xas ++
          (List.range m.funcs.length).map (s.funcs.length + ·)
        globals := Silmaril.Wasm.V2.Execution.ExternAddr.globals xas ++
          (List.range m.globals.length).map (s.globals.length + ·)
        tables := Silmaril.Wasm.V2.Execution.ExternAddr.tables xas ++
          (List.range m.tables.length).map (s.tables.length + ·)
        mems := Silmaril.Wasm.V2.Execution.ExternAddr.mems xas ++
          (List.range m.memories.length).map (s.mems.length + ·)
        elems := (List.range m.elems.length).map (s.elems.length + ·)
        datas := (List.range m.data.length).map (s.datas.length + ·) })
    (hxi : m.exports.mapM (Silmaril.Wasm.V2.Execution.instExport?
      mi₀.funcs mi₀.globals mi₀.tables mi₀.mems) = some xi) :
    Silmaril.Wasm.V2.Execution.allocModule? s m xas vs rss =
      some ((allocDatas (allocElems (allocMems (allocTables
        (allocGlobals (allocFuncs s { mi₀ with exports := xi } (fts.zip m.funcs)).1
          ((m.globals.map Silmaril.Wasm.V2.Global.type).zip vs)).1 m.tables).1 m.memories).1
            ((m.elems.map Silmaril.Wasm.V2.Elem.type).zip rss)).1
              (m.data.map Silmaril.Wasm.V2.Data.bytes)).1,
        { mi₀ with exports := xi }) := by
  subst hmi₀
  simp only [Silmaril.Wasm.V2.Execution.allocModule?, hfts, hxi, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, hv, hr]
  rfl

end Alloc

/-! ### The image of each allocated component -/

theorem erase_globalInst_toV2 (g : GlobalInst) :
    GlobalInst.erase (GlobalInst.toV2 g) = GlobalInst.toV2 g := rfl

theorem erase_funcInst_toV2 (fi : FuncInst Func H) :
    ({ FuncInst.toV2 fi with module := ModuleInst.erase (FuncInst.toV2 fi).module }
      : VFuncInst H) = FuncInst.toV2 fi := by
  cases fi <;> rfl

theorem instExports_eqV {base : ModuleInst}
    {fas : List Silmaril.Wasm.V2.Execution.FuncAddr}
    {gas : List Silmaril.Wasm.V2.Execution.GlobalAddr}
    {tas : List Silmaril.Wasm.V2.Execution.TableAddr}
    {mas : List Silmaril.Wasm.V2.Execution.MemAddr}
    (hf : fas = base.funcs.map Addr.value) (hg : gas = base.globals.map Addr.value)
    (ht : tas = base.tables.map Addr.value) (hm : mas = base.memories.map Addr.value) :
    {es : List Export} → {xs : List ExportInst} →
    es.mapM (fun e => (exportValue? base e.index).bind
      fun v => some (⟨e.name, v⟩ : ExportInst)) = some xs →
    (es.map Export.toV2).mapM
      (Silmaril.Wasm.V2.Execution.instExport? fas gas tas mas) =
      some (xs.map fun e =>
        (⟨e.name, ExternVal.toV2 e.value⟩ : Silmaril.Wasm.V2.Execution.ExportInst))
  | [], _, h => by cases h; rfl
  | e :: es, xs, h => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨x, hx, xs', hxs, rfl⟩ := h
    have ih := instExports_eqV hf hg ht hm hxs
    obtain ⟨v, hv, rfl⟩ := hx
    have hx' : Silmaril.Wasm.V2.Execution.instExport? fas gas tas mas (Export.toV2 e) =
        some ⟨e.name, ExternVal.toV2 v⟩ := by
      cases hi : e.index with
      | func i =>
        rw [hi] at hv
        simp only [exportValue?, Option.map_eq_some_iff] at hv
        obtain ⟨a, ha, rfl⟩ := hv
        simp [Silmaril.Wasm.V2.Execution.instExport?, Export.toV2, ExternIdx.toV2, hi, hf,
          List.getElem?_map, ha, ExternVal.toV2]
      | global i =>
        rw [hi] at hv
        simp only [exportValue?, Option.map_eq_some_iff] at hv
        obtain ⟨a, ha, rfl⟩ := hv
        simp [Silmaril.Wasm.V2.Execution.instExport?, Export.toV2, ExternIdx.toV2, hi, hg,
          List.getElem?_map, ha, ExternVal.toV2]
      | table i =>
        rw [hi] at hv
        simp only [exportValue?, Option.map_eq_some_iff] at hv
        obtain ⟨a, ha, rfl⟩ := hv
        simp [Silmaril.Wasm.V2.Execution.instExport?, Export.toV2, ExternIdx.toV2, hi, ht,
          List.getElem?_map, ha, ExternVal.toV2]
      | memory i =>
        rw [hi] at hv
        simp only [exportValue?, Option.map_eq_some_iff] at hv
        obtain ⟨a, ha, rfl⟩ := hv
        simp [Silmaril.Wasm.V2.Execution.instExport?, Export.toV2, ExternIdx.toV2, hi, hm,
          List.getElem?_map, ha, ExternVal.toV2]
    simp only [List.map_cons, List.mapM_cons, hx', ih, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some]

theorem allocFuncs_imageV {types : List FuncType} {mod : ModuleInst} {mi : VModuleInst}
    (hmi : ModuleInst.erase mi = mod.toV2) :
    {fs : List Func} → {fis : List (FuncInst Func H)} →
    List.Forall₂ (fun f fi => (types[f.type.toNat]?).bind
      (fun ft => some (FuncInst.wasm ft mod f)) = some fi) fs fis →
    ∃ fts : List Silmaril.Wasm.V2.FuncType,
      (fs.map Func.toV2).mapM (fun fn => (types.map FuncType.toV2)[fn.type.toNat]?) = some fts ∧
      ((fts.zip (fs.map Func.toV2)).map
        (fun p => (⟨p.1, mi, .wasm p.2⟩ : VFuncInst H))).map
          (fun fi => ({ fi with module := ModuleInst.erase fi.module } : VFuncInst H)) =
        fis.map FuncInst.toV2
  | [], [], .nil => ⟨[], rfl, rfl⟩
  | f :: fs, fi :: fis, .cons h hs => by
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ft, hft, rfl⟩ := h
    obtain ⟨fts, hfts, him⟩ := allocFuncs_imageV hmi hs
    refine ⟨FuncType.toV2 ft :: fts, ?_, ?_⟩
    · have hhead : (types.map FuncType.toV2)[(Func.toV2 f).type.toNat]? =
          some (FuncType.toV2 ft) := by
        simp [Func.toV2, List.getElem?_map, hft]
      simp only [List.map_cons, List.mapM_cons, hhead, hfts, Option.pure_def,
        Option.bind_eq_bind, Option.bind_some]
    · simp only [List.map_cons, List.zip_cons_cons, him]
      refine congrArg₂ _ ?_ rfl
      simp only [hmi]
      rfl

theorem allocGlobals_imageV : (gs : List Global) → (vs : List Value) → gs.length = vs.length →
    ((((gs.map Global.toV2).map Silmaril.Wasm.V2.Global.type).zip
        (vs.map Value.toV2)).map
      (fun p => (⟨p.1, p.2⟩ : VGlobalInst))).map GlobalInst.erase =
      (List.zipWith (fun g v => (GlobalInst.mk v g.type.mutability)) gs vs).map
        GlobalInst.toV2
  | [], [], _ => rfl
  | g :: gs, v :: vs, h => by
    have ih := allocGlobals_imageV gs vs (by simpa using h)
    simp only [List.map_cons, List.zip_cons_cons, List.zipWith_cons_cons, ih]
    rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem allocTables_imageV : (ts : List TableType) →
    (ts.map TableType.toV2).map (fun tt =>
      (⟨tt, List.replicate tt.limits.min.val (.null tt.element)⟩ : VTableInst)) =
    (ts.map (fun t =>
      TableInst.mk (List.replicate t.limits.min.val none) (t.limits.max.map Fin.val))).map
      TableInst.toV2
  | [] => rfl
  | t :: ts => by
    simp only [List.map_cons, allocTables_imageV ts]
    congr 1
    simp only [Silmaril.Wasm.Execution.Runtime.TableInst.toV2, TableType.toV2, Limits.toV2]
    refine congrArg₂ _ ?_ ?_
    · refine congrArg₂ _ ?_ rfl
      refine congrArg₂ _ ?_ ?_
      · simp [List.length_replicate, Fin.ofNat, Nat.mod_eq_of_lt t.limits.min.isLt]
      · cases hmx : t.limits.max with
        | none => rfl
        | some j => simp [Fin.ofNat, Nat.mod_eq_of_lt j.isLt]
    · simp

theorem allocMems_imageV : (ts : List MemoryType) →
    (ts.map MemoryType.toV2).map (fun mt =>
      (⟨mt, ⟨Array.replicate (mt.limits.min.val * Memory.pageSize) 0⟩⟩ : VMemInst)) =
    (ts.map (fun t => MemInst.mk
      ⟨Array.replicate (t.limits.min.val * Memory.pageSize) 0⟩ (t.limits.max.map Fin.val))).map
      MemInst.toV2
  | [] => rfl
  | t :: ts => by
    simp only [List.map_cons, allocMems_imageV ts]
    congr 1
    simp only [Silmaril.Wasm.Execution.Runtime.MemInst.toV2, MemoryType.toV2, Limits.toV2]
    refine congrArg₂ _ ?_ rfl
    refine congrArg _ ?_
    refine congrArg₂ _ ?_ ?_
    · simp only [ByteArray.size, Array.size_replicate]
      rw [Nat.mul_div_cancel _ (by decide : 0 < Memory.pageSize)]
      simp [Fin.ofNat, Nat.mod_eq_of_lt t.limits.min.isLt]
    · cases hmx : t.limits.max with
      | none => rfl
      | some j => simp [Fin.ofNat, Nat.mod_eq_of_lt j.isLt]

/-- The 2.0 references a Lime1 element write initialises a table with. -/
def elemRefsV (w : ElemWrite) : List Silmaril.Wasm.V2.Execution.Ref :=
  w.values.map fun a => .funcAddr a.value

theorem elemInsts_eqV : (es : List Elem) → (ws : List ElemWrite) → es.length = ws.length →
    (((es.map Elem.toV2).map Silmaril.Wasm.V2.Elem.type).zip (ws.map elemRefsV)).map
      (fun p => (⟨p.1, p.2⟩ : Silmaril.Wasm.V2.Execution.ElemInst)) =
    ws.map (fun w => ⟨Silmaril.Wasm.V2.RefType.funcref, elemRefsV w⟩)
  | [], [], _ => rfl
  | e :: es, w :: ws, h => by
    simp only [List.map_cons, List.zip_cons_cons, elemInsts_eqV es ws (by simpa using h)]
    rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-! ### `$allocmodule` agreement -/

theorem storeExtV {a b : VStore H} (hf : a.funcs = b.funcs) (hg : a.globals = b.globals)
    (ht : a.tables = b.tables) (hm : a.mems = b.mems) (he : a.elems = b.elems)
    (hd : a.datas = b.datas) : a = b := by
  rcases a with ⟨_, _, _, _, _, _⟩
  rcases b with ⟨_, _, _, _, _, _⟩
  simp_all

theorem moduleInstExtV {a b : VModuleInst} (hty : a.types = b.types) (hf : a.funcs = b.funcs)
    (hg : a.globals = b.globals) (ht : a.tables = b.tables) (hm : a.mems = b.mems)
    (he : a.elems = b.elems) (hd : a.datas = b.datas) (hx : a.exports = b.exports) : a = b := by
  rcases a with ⟨_, _, _, _, _, _, _, _⟩
  rcases b with ⟨_, _, _, _, _, _, _, _⟩
  simp_all

/-- The address ranges `$allocmodule` (`9-module:125-130`) predicts for the
image of a Lime1 module: the imports followed by the fresh addresses. -/
def predInstV (before : Store H) (m : Module) (imports : List ExternVal) : VModuleInst :=
  { types := m.toV2.types
    funcs := Silmaril.Wasm.V2.Execution.ExternAddr.funcs (imports.map ExternVal.toV2) ++
      (List.range m.toV2.funcs.length).map (before.toV2.funcs.length + ·)
    globals := Silmaril.Wasm.V2.Execution.ExternAddr.globals (imports.map ExternVal.toV2) ++
      (List.range m.toV2.globals.length).map (before.toV2.globals.length + ·)
    tables := Silmaril.Wasm.V2.Execution.ExternAddr.tables (imports.map ExternVal.toV2) ++
      (List.range m.toV2.tables.length).map (before.toV2.tables.length + ·)
    mems := Silmaril.Wasm.V2.Execution.ExternAddr.mems (imports.map ExternVal.toV2) ++
      (List.range m.toV2.memories.length).map (before.toV2.mems.length + ·)
    elems := (List.range m.toV2.elems.length).map (before.toV2.elems.length + ·)
    datas := (List.range m.toV2.data.length).map (before.toV2.datas.length + ·) }

theorem predInstV_funcs (before : Store H) (m : Module) (imports : List ExternVal) :
    (predInstV before m imports).funcs = (baseInstV before m imports).funcs.map Addr.value := by
  simp [predInstV, baseInstV, externAddr_funcs_toV2, addresses, List.map_map,
    Function.comp_def, Module.toV2, Silmaril.Wasm.Execution.Runtime.Store.toV2]

theorem predInstV_globals (before : Store H) (m : Module) (imports : List ExternVal) :
    (predInstV before m imports).globals =
      (baseInstV before m imports).globals.map Addr.value := by
  simp [predInstV, baseInstV, externAddr_globals_toV2, addresses, List.map_map,
    Function.comp_def, Module.toV2, Silmaril.Wasm.Execution.Runtime.Store.toV2]

theorem predInstV_tables (before : Store H) (m : Module) (imports : List ExternVal) :
    (predInstV before m imports).tables = (baseInstV before m imports).tables.map Addr.value := by
  simp [predInstV, baseInstV, externAddr_tables_toV2, addresses, List.map_map,
    Function.comp_def, Module.toV2, Silmaril.Wasm.Execution.Runtime.Store.toV2]

theorem predInstV_mems (before : Store H) (m : Module) (imports : List ExternVal) :
    (predInstV before m imports).mems =
      (baseInstV before m imports).memories.map Addr.value := by
  simp [predInstV, baseInstV, externAddr_mems_toV2, addresses, List.map_map,
    Function.comp_def, Module.toV2, Silmaril.Wasm.Execution.Runtime.Store.toV2]

theorem predInstV_elems (before : Store H) (m : Module) (imports : List ExternVal) :
    (predInstV before m imports).elems = List.range m.elems.length := by
  simp [predInstV, Module.toV2, Silmaril.Wasm.Execution.Runtime.Store.toV2]

theorem predInstV_datas (before : Store H) (m : Module) (imports : List ExternVal) :
    (predInstV before m imports).datas = List.range m.data.length := by
  simp [predInstV, Module.toV2, Silmaril.Wasm.Execution.Runtime.Store.toV2]

open Silmaril.Wasm.V2.Execution (allocFuncs allocGlobals allocTables allocMems

  allocElems allocDatas) in
/-- **`$allocmodule` agreement.** Lime1's `allocate?` and 2.0's `$allocmodule`
allocate the same instances, up to the element and data instances 2.0 has and
Lime1 does not (`ToV2.Store.erase`) and the declared global types
(`ToV2.GlobalInst.erase`). -/
theorem allocModule_v2 {before : Store H} {m : Module} {imports : List ExternVal}
    {allocated : Store H} {mod : ModuleInst}
    (ha : allocate? before m imports = some (allocated, mod))
    {elems : List ElemWrite} (hlen : m.elems.length = elems.length) :
    ∃ (inits : List Value) (SA : VStore H) (mi : VModuleInst),
      m.globals.mapM (fun g =>
        constExpr? before { globals := (importedInstance imports).globals } g.init) = some inits ∧
      Silmaril.Wasm.V2.Execution.allocModule? before.toV2 m.toV2 (imports.map ExternVal.toV2)
        (inits.map Value.toV2) (elems.map elemRefsV) = some (SA, mi) ∧
      ModuleInst.erase mi = mod.toV2 ∧
      mi.elems = List.range m.elems.length ∧
      mi.datas = List.range m.data.length ∧
      Store.erase SA = allocated.toV2 ∧
      SA.elems = elems.map (fun w => ⟨Silmaril.Wasm.V2.RefType.funcref, elemRefsV w⟩) ∧
      SA.datas = m.data.map (fun d => ⟨d.bytes⟩) := by
  obtain ⟨inits, exports, funcs, hin, hex, hfn, rfl, rfl⟩ := allocate?_invV ha
  have hinlen : inits.length = m.globals.length := mapM_length_eq hin
  have hMIerase : ModuleInst.erase
      { predInstV before m imports with
        exports := exports.map fun e =>
          (⟨e.name, ExternVal.toV2 e.value⟩ : Silmaril.Wasm.V2.Execution.ExportInst) }
      = ({ baseInstV before m imports with exports := exports } : ModuleInst).toV2 := by
    refine moduleInstExtV rfl ?_ ?_ ?_ ?_ rfl rfl rfl
    · exact predInstV_funcs before m imports
    · exact predInstV_globals before m imports
    · exact predInstV_tables before m imports
    · exact predInstV_mems before m imports
  obtain ⟨fts, hfts, hfimg⟩ := allocFuncs_imageV hMIerase (mapM_forall₂ hfn)
  have hxi := instExports_eqV (base := baseInstV before m imports)
    (predInstV_funcs before m imports) (predInstV_globals before m imports)
    (predInstV_tables before m imports) (predInstV_mems before m imports) hex
  have halloc := allocModule?_eqV (s := before.toV2) (m := m.toV2)
    (xas := imports.map ExternVal.toV2) (vs := inits.map Value.toV2)
    (rss := elems.map elemRefsV) hfts
    (by simp [hinlen, Module.toV2]) (by simp [hlen, Module.toV2])
    (predInstV before m imports) rfl hxi
  refine ⟨inits, _, _, hin, halloc, hMIerase, ?_, ?_, ?_, ?_, ?_⟩
  · exact predInstV_elems before m imports
  · exact predInstV_datas before m imports
  · simp only [allocFuncs_eqV, allocGlobals_eqV, allocTables_eqV, allocMems_eqV,
      allocElems_eqV, allocDatas_eqV]
    refine storeExtV ?_ ?_ ?_ ?_ rfl rfl
    · simp only [Store.erase, Silmaril.Wasm.Execution.Runtime.Store.toV2, List.map_append]
      refine congrArg₂ _ ?_ hfimg
      simp only [List.map_map, Function.comp_def, erase_funcInst_toV2]
    · simp only [Store.erase, Silmaril.Wasm.Execution.Runtime.Store.toV2, List.map_append]
      refine congrArg₂ _ ?_ (allocGlobals_imageV m.globals inits hinlen.symm)
      simp only [List.map_map, Function.comp_def, erase_globalInst_toV2]
    · simp only [Store.erase, Silmaril.Wasm.Execution.Runtime.Store.toV2, List.map_append]
      exact congrArg₂ _ rfl (allocTables_imageV m.tables)
    · simp only [Store.erase, Silmaril.Wasm.Execution.Runtime.Store.toV2, List.map_append]
      exact congrArg₂ _ rfl (allocMems_imageV m.memories)
  · simp only [allocFuncs_eqV, allocGlobals_eqV, allocTables_eqV, allocMems_eqV,
      allocElems_eqV, allocDatas_eqV]
    show ((before.toV2).elems ++ _) = _
    simp only [Silmaril.Wasm.Execution.Runtime.Store.toV2, List.nil_append]
    exact elemInsts_eqV m.elems elems hlen
  · simp only [allocFuncs_eqV, allocGlobals_eqV, allocTables_eqV, allocMems_eqV,
      allocElems_eqV, allocDatas_eqV]
    show ((before.toV2).datas ++ _) = _
    simp [Silmaril.Wasm.Execution.Runtime.Store.toV2, Module.toV2, List.map_map,
      Function.comp_def, Data.toV2]

/-! ### The `table.init` and `memory.init` loops -/

section Loops

variable {tgt : VHostSemantics H}

theorem state_table?V {cs : VStore H} {cf : VFrame} {x : TableIdx}
    {a : Silmaril.Wasm.V2.Execution.TableAddr} {ti : VTableInst}
    (ha : cf.module.tableAddr? x = some a) (ht : cs.tableInst? a = some ti) :
    (⟨cs, cf⟩ : Silmaril.Wasm.V2.Execution.State H).table? x = some ti := by
  simp [Silmaril.Wasm.V2.Execution.State.table?, ha, ht]

theorem tableInst?_setTableInstV {cs : VStore H} {a : Silmaril.Wasm.V2.Execution.TableAddr}
    {ti : VTableInst} (ht : cs.tableInst? a = some ti) (ti' : VTableInst) :
    (cs.setTableInst a ti').tableInst? a = some ti' := by
  simp only [Silmaril.Wasm.V2.Execution.Store.tableInst?,
    Silmaril.Wasm.V2.Execution.Store.setTableInst] at ht ⊢
  rw [List.getElem?_set_self]
  exact (List.getElem?_eq_some_iff.mp ht).1

theorem setTableInst_selfV {cs : VStore H} {a : Silmaril.Wasm.V2.Execution.TableAddr}
    {ti : VTableInst} (ht : cs.tableInst? a = some ti) : cs.setTableInst a ti = cs := by
  simp only [Silmaril.Wasm.V2.Execution.Store.tableInst?] at ht
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp ht
  simp only [Silmaril.Wasm.V2.Execution.Store.setTableInst]
  rw [← heq, List.set_getElem_self hlt]

theorem setTableInst_setTableInstV (cs : VStore H) (a : Silmaril.Wasm.V2.Execution.TableAddr)
    (t₁ t₂ : VTableInst) : (cs.setTableInst a t₁).setTableInst a t₂ = cs.setTableInst a t₂ := by
  simp [Silmaril.Wasm.V2.Execution.Store.setTableInst]

/-- The 2.0 `table.init` loop, by induction on the count. -/
theorem tableInit_v2 {cf : VFrame} {x : TableIdx} {y : ElemIdx}
    {ta : Silmaril.Wasm.V2.Execution.TableAddr} {ei : Silmaril.Wasm.V2.Execution.ElemInst}
    (hta : cf.module.tableAddr? x = some ta) :
    (n : Nat) → (cs : VStore H) → (ti : VTableInst) → (d sr : BitVec 32) →
    cs.tableInst? ta = some ti →
    (⟨cs, cf⟩ : Silmaril.Wasm.V2.Execution.State H).elem? y = some ei →
    ti.refs.length < 2 ^ 32 → ei.refs.length < 2 ^ 32 →
    d.toNat + n ≤ ti.refs.length → sr.toNat + n ≤ ei.refs.length →
    Silmaril.Wasm.V2.Execution.Steps v2Profile tgt
      ⟨cs, cf, [Silmaril.Wasm.V2.Execution.constI32 d, Silmaril.Wasm.V2.Execution.constI32 sr,
        Silmaril.Wasm.V2.Execution.constI32 (BitVec.ofNat 32 n), .plain (.tableInit x y)]⟩
      ⟨cs.setTableInst ta { ti with refs := (ti.refs.take d.toNat ++
        (ei.refs.drop sr.toNat).take n ++ ti.refs.drop (d.toNat + n)) }, cf, []⟩
  | 0, cs, ti, d, sr, ht, he, _, _, hd, hs => by
    have hstep : Silmaril.Wasm.V2.Execution.Step v2Profile tgt
        ⟨cs, cf, [Silmaril.Wasm.V2.Execution.constI32 d, Silmaril.Wasm.V2.Execution.constI32 sr,
          Silmaril.Wasm.V2.Execution.constI32 (BitVec.ofNat 32 0), .plain (.tableInit x y)]⟩
        ⟨cs, cf, []⟩ :=
      .read (.tableInitZero (j := d) (i := sr) (state_table?V hta ht) he
        ⟨(by omega), (by omega)⟩)
    have hS : cs.setTableInst ta { ti with refs := (ti.refs.take d.toNat ++
        (ei.refs.drop sr.toNat).take 0 ++ ti.refs.drop (d.toNat + 0)) } = cs := by
      simp only [List.take_zero, List.append_nil, Nat.add_zero, List.take_append_drop]
      exact setTableInst_selfV ht
    rw [hS]
    exact Relation.ReflTransGen.single hstep
  | n + 1, cs, ti, d, sr, ht, he, hti, hei, hd, hs => by
    obtain ⟨r, hr⟩ : ∃ r, ei.refs[sr.toNat]? = some r :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have h1 : (1 : BitVec 32).toNat = 1 := rfl
    have hN : (BitVec.ofNat 32 (n + 1)).toNat = n + 1 := by
      simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
    have hn : BitVec.ofNat 32 (n + 1) ≠ 0 := by
      intro h0
      have := congrArg BitVec.toNat h0
      rw [hN] at this
      simp at this
    have s1 : Silmaril.Wasm.V2.Execution.Step v2Profile tgt
        ⟨cs, cf, [Silmaril.Wasm.V2.Execution.constI32 d, Silmaril.Wasm.V2.Execution.constI32 sr,
          Silmaril.Wasm.V2.Execution.constI32 (BitVec.ofNat 32 (n + 1)), .plain (.tableInit x y)]⟩
        ⟨cs, cf, [Silmaril.Wasm.V2.Execution.constI32 d, Silmaril.Wasm.V2.Execution.aref r,
          .plain (.tableSet x), Silmaril.Wasm.V2.Execution.constI32 (d + 1),
          Silmaril.Wasm.V2.Execution.constI32 (sr + 1),
          Silmaril.Wasm.V2.Execution.constI32 (BitVec.ofNat 32 (n + 1) - 1),
          .plain (.tableInit x y)]⟩ :=
      .read (.tableInitSucc (j := d) (i := sr) (state_table?V hta ht) he
        ⟨(by rw [hN]; omega), (by rw [hN]; omega)⟩ hn hr)
    have s2 : Silmaril.Wasm.V2.Execution.Step v2Profile tgt
        ⟨cs, cf, [Silmaril.Wasm.V2.Execution.constI32 d, Silmaril.Wasm.V2.Execution.aref r,
          .plain (.tableSet x)]⟩
        ⟨cs.setTableInst ta (ti.setRef d.toNat r), cf, []⟩ :=
      .tableSetVal hta ht (by omega)
    have s2' := Silmaril.Wasm.V2.Execution.Steps.ctxtInstrs (P := v2Profile) (host := tgt)
      []
      [Silmaril.Wasm.V2.Execution.constI32 (d + 1), Silmaril.Wasm.V2.Execution.constI32 (sr + 1),
        Silmaril.Wasm.V2.Execution.constI32 (BitVec.ofNat 32 (n + 1) - 1),
        .plain (.tableInit x y)]
      (Silmaril.Wasm.V2.Execution.Step.steps s2)
    have hd1 : (d + 1).toNat = d.toNat + 1 := by
      rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
    have hs1 : (sr + 1).toNat = sr.toNat + 1 := by
      rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
    have hsub : BitVec.ofNat 32 (n + 1) - 1 = BitVec.ofNat 32 n := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, hN, h1, BitVec.toNat_ofNat]
      omega
    have hlen : (ti.refs.set d.toNat r).length = ti.refs.length := List.length_set ..
    have s3 := tableInit_v2 hta n (cs.setTableInst ta (ti.setRef d.toNat r))
      (ti.setRef d.toNat r) (d + 1) (sr + 1)
      (tableInst?_setTableInstV ht _) he (by simpa [Silmaril.Wasm.V2.Execution.TableInst.setRef,
        hlen] using hti) hei
      (show (d + 1).toNat + n ≤ (ti.setRef d.toNat r).refs.length by
        simp only [Silmaril.Wasm.V2.Execution.TableInst.setRef, hlen]; omega)
      (show (sr + 1).toNat + n ≤ ei.refs.length by rw [hs1]; omega)
    rw [setTableInst_setTableInstV] at s3
    rw [hsub] at s1 s2'
    simp only [Silmaril.Wasm.V2.Execution.vals, List.map_nil, List.nil_append,
      List.cons_append, List.append_nil] at s2'
    have hlist : (ti.setRef d.toNat r).refs.take (d + 1).toNat ++
        (ei.refs.drop (sr + 1).toNat).take n ++
        (ti.setRef d.toNat r).refs.drop ((d + 1).toNat + n) =
        ti.refs.take d.toNat ++ (ei.refs.drop sr.toNat).take (n + 1) ++
          ti.refs.drop (d.toNat + (n + 1)) := by
      simp only [Silmaril.Wasm.V2.Execution.TableInst.setRef, hd1, hs1]
      have hk : d.toNat < ti.refs.length := by omega
      have hdj : ei.refs.drop sr.toNat = r :: ei.refs.drop (sr.toNat + 1) := by
        rw [List.drop_eq_getElem_cons (by omega)]
        obtain ⟨_, hr'⟩ := List.getElem?_eq_some_iff.mp hr
        rw [hr']
      have ht1 : (ti.refs.set d.toNat r).take (d.toNat + 1) = ti.refs.take d.toNat ++ [r] := by
        rw [List.take_add_one, List.take_set, List.getElem?_set_self hk,
          List.set_eq_of_length_le (by simp)]
        rfl
      have hd2 : (ti.refs.set d.toNat r).drop (d.toNat + 1 + n) =
          ti.refs.drop (d.toNat + (n + 1)) := by
        rw [List.drop_set, ite_eq_left (by omega)]; congr 1; omega
      rw [ht1, hd2, hdj, List.take_succ_cons]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    simp only [Silmaril.Wasm.V2.Execution.TableInst.setRef] at s3 hlist
    rw [hlist] at s3
    exact (Relation.ReflTransGen.single s1).trans (s2'.trans s3)

theorem state_data?V {cs : VStore H} {cf : VFrame} {y : DataIdx}
    {a : Silmaril.Wasm.V2.Execution.DataAddr} {di : Silmaril.Wasm.V2.Execution.DataInst}
    (ha : cf.module.dataAddr? y = some a) (hd : cs.dataInst? a = some di) :
    (⟨cs, cf⟩ : Silmaril.Wasm.V2.Execution.State H).data? y = some di := by
  simp [Silmaril.Wasm.V2.Execution.State.data?, ha, hd]

theorem uint8_ofNat_setWidth (b : UInt8) :
    UInt8.ofNat ((BitVec.ofNat 32 b.toNat).setWidth 8).toNat = b := by
  have hb : b.toNat < 256 := b.toNat_lt_size
  have : ((BitVec.ofNat 32 b.toNat).setWidth 8).toNat = b.toNat := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  rw [this]
  exact UInt8.ofNat_toNat

/-- The 2.0 `memory.init` loop, by induction on the count. The result is
described pointwise, which is what `ByteArray.copySlice` of `applyData` gives. -/
theorem memInit_v2 {cf : VFrame} {ma : Silmaril.Wasm.V2.Execution.MemAddr} {y : DataIdx}
    {di : Silmaril.Wasm.V2.Execution.DataInst}
    (hma : cf.module.memAddr? Silmaril.Wasm.V2.Execution.memIdx0 = some ma) :
    ∀ (k : Nat) (cs : VStore H) (mi : VMemInst) (d sr n : BitVec 32),
      cs.memInst? ma = some mi →
      (⟨cs, cf⟩ : Silmaril.Wasm.V2.Execution.State H).data? y = some di →
      n.toNat = k → d.toNat + k ≤ mi.bytes.size → sr.toNat + k ≤ di.bytes.size →
      mi.bytes.size ≤ 2 ^ 32 → di.bytes.size ≤ 2 ^ 32 →
      ∃ B : Memory.Bytes, B.size = mi.bytes.size ∧
        (∀ j, B.data[j]? = if d.toNat ≤ j ∧ j < d.toNat + k
          then di.bytes.data[sr.toNat + (j - d.toNat)]? else mi.bytes.data[j]?) ∧
        Silmaril.Wasm.V2.Execution.Steps v2Profile tgt
          ⟨cs, cf, [Silmaril.Wasm.V2.Execution.constI32 d,
            Silmaril.Wasm.V2.Execution.constI32 sr,
            Silmaril.Wasm.V2.Execution.constI32 n, .plain (.memoryInit y)]⟩
          ⟨cs.setMemInst ma { mi with bytes := B }, cf, []⟩ := by
  intro k
  induction k with
  | zero =>
    intro cs mi d sr n hm hd hn hdb hsb _ _
    have hn0 : n = 0 := BitVec.eq_of_toNat_eq (by simpa using hn)
    subst hn0
    refine ⟨mi.bytes, rfl, fun j => by simp, ?_⟩
    rw [show ({ mi with bytes := mi.bytes } : VMemInst) = mi from rfl, setMemInst_self hm]
    exact Relation.ReflTransGen.single
      (.read (.memoryInitZero (j := d) (i := sr) (state_mem? hma hm) hd ⟨by omega, by omega⟩))
  | succ k ih =>
    intro cs mi d sr n hm hd hn hdb hsb hmsz hdsz
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    have h1 : (1 : BitVec 32).toNat = 1 := rfl
    have hsrlt : sr.toNat < di.bytes.data.size := by
      have : di.bytes.size = di.bytes.data.size := rfl
      omega
    obtain ⟨b, hb⟩ : ∃ b, di.bytes.data[sr.toNat]? = some b :=
      ⟨_, Array.getElem?_eq_getElem hsrlt⟩
    have hd1 : d.toNat + 1 ≤ mi.bytes.size := by omega
    obtain ⟨A, hA, hAsz, hAget⟩ :=
      Silmaril.Wasm.Lime1.Execution.ToCoreSim.bulk_store8 (M := mi.bytes) (i := d.toNat)
        ((BitVec.ofNat 32 b.toNat).setWidth 8) hd1
    have hm' := memInst?_setMemInst hm { mi with bytes := A }
    have hn' : (n - 1).toNat = k := by bv_omega
    have hcase : k = 0 ∨ ((d + 1).toNat = d.toNat + 1 ∧ (sr + 1).toNat = sr.toNat + 1) := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · exact .inl hk
      · exact .inr ⟨by bv_omega, by bv_omega⟩
    have hdb' : (d + 1).toNat + k ≤ (⟨mi.type, A⟩ : VMemInst).bytes.size := by
      show (d + 1).toNat + k ≤ A.size
      rcases hcase with rfl | ⟨he1, -⟩
      · have : (d + 1).toNat ≤ d.toNat + 1 := by
          rw [BitVec.toNat_add, h1]; exact Nat.mod_le _ _
        omega
      · rw [he1, hAsz]; omega
    have hsb' : (sr + 1).toNat + k ≤ di.bytes.size := by
      rcases hcase with rfl | ⟨-, he2⟩
      · have : (sr + 1).toNat ≤ sr.toNat + 1 := by
          rw [BitVec.toNat_add, h1]; exact Nat.mod_le _ _
        omega
      · rw [he2]; omega
    obtain ⟨B, hBsz, hBget, hsteps⟩ := ih (cs.setMemInst ma { mi with bytes := A })
      { mi with bytes := A } (d + 1) (sr + 1) (n - 1) hm' hd hn' hdb' hsb'
      (by show A.size ≤ 2 ^ 32; omega) hdsz
    refine ⟨B, by rw [hBsz]; exact hAsz, fun j => ?_, ?_⟩
    · rw [hBget j]
      simp only [hAget j]
      rcases hcase with rfl | ⟨he1, he2⟩
      · rw [ite_eq_right (by omega)]
        by_cases hj : j = d.toNat
        · subst hj
          rw [ite_eq_left rfl, ite_eq_left (by omega), Nat.sub_self, Nat.add_zero, hb]
          exact congrArg some (uint8_ofNat_setWidth b)
        · rw [ite_eq_right hj, ite_eq_right (by omega)]
      · rw [he1, he2]
        by_cases hj1 : d.toNat + 1 ≤ j ∧ j < d.toNat + 1 + k
        · obtain ⟨hja, hjb⟩ := hj1
          rw [ite_eq_left ⟨hja, hjb⟩, ite_eq_left (by omega)]
          rw [show sr.toNat + 1 + (j - (d.toNat + 1)) = sr.toNat + (j - d.toNat) by omega]
        · rw [ite_eq_right hj1]
          by_cases hj : j = d.toNat
          · subst hj
            rw [ite_eq_left rfl, ite_eq_left (by omega), Nat.sub_self, Nat.add_zero, hb]
            exact congrArg some (uint8_ofNat_setWidth b)
          · rw [ite_eq_right hj, ite_eq_right (by omega)]
    · refine Relation.ReflTransGen.head
        (.read (.memoryInitSucc (j := d) (i := sr) (n := n) (state_mem? hma hm) hd
          (by omega) hn0 hb)) ?_
      have hctx := Silmaril.Wasm.V2.Execution.Step.ctxtInstrs (P := v2Profile) (host := tgt)
        (vs := [])
        (rest := [Silmaril.Wasm.V2.Execution.constI32 (d + 1),
          Silmaril.Wasm.V2.Execution.constI32 (sr + 1),
          Silmaril.Wasm.V2.Execution.constI32 (n - 1), .plain (.memoryInit y)])
        (bulk_store_step (tgt := tgt) hma hm hA) (.inr (by simp))
      simp only [Silmaril.Wasm.V2.Execution.vals, List.map_nil, List.nil_append,
        List.cons_append] at hctx
      refine Relation.ReflTransGen.head hctx ?_
      rw [setMemInst_setMemInst] at hsteps
      exact hsteps

end Loops

/-! ### One segment program -/

section Segments

variable {tgt : VHostSemantics H}

/-- One element segment program. -/
theorem elemSeg_v2 {L0 L : Store H} {module : ModuleInst} {cf : VFrame} {cs : VStore H}
    {e : Elem} {w : ElemWrite} {k : Nat}
    (hw : resolveElem? L0 module e = some w)
    (hG : cs.globals.map GlobalInst.erase = L0.globals.map GlobalInst.toV2)
    (hFg : cf.module.globals = module.globals.map Addr.value)
    (hFt : cf.module.tables = module.tables.map Addr.value)
    (hFe : cf.module.elems[k]? = some k) (hk : k < 2 ^ 32)
    (hSe : (cs.elems[k]?).map (·.refs) = some (elemRefsV w))
    (hS : Store.erase cs = L.toV2)
    (hlen : ∀ i : Nat, (L.tables[i]?).map (fun t : TableInst => t.refs.length) =
      (L0.tables[i]?).map (fun t : TableInst => t.refs.length))
    (htab : ∀ t ∈ L0.tables, t.refs.length < 2 ^ 32)
    (rest : List VAdmin) :
    ∃ cs', Silmaril.Wasm.V2.Execution.Steps v2Profile tgt
        ⟨cs, cf, Silmaril.Wasm.V2.Execution.expression
          (Silmaril.Wasm.V2.Execution.runElem k (Elem.toV2 e)) ++ rest⟩ ⟨cs', cf, rest⟩ ∧
      Store.erase cs' = (applyElem L w).toV2 ∧ cs'.globals = cs.globals ∧
      cs'.datas = cs.datas ∧ cs'.mems = cs.mems ∧
      (∀ i, i ≠ k → cs'.elems[i]? = cs.elems[i]?) := by
  obtain ⟨a, table, hoff, ha, htable, hrefs, hbnd, hwa⟩ := resolveElem?_inv hw
  have hvlen : w.values.length = e.init.length := mapM_length_eq hrefs
  have hl := hlen a.value
  rw [htable] at hl
  obtain ⟨tL, htL, htLlen⟩ : ∃ tL, L.tables[a.value]? = some tL ∧
      tL.refs.length = table.refs.length := by
    cases h : L.tables[a.value]? with
    | none => rw [h] at hl; cases hl
    | some tL => rw [h] at hl; exact ⟨tL, rfl, Option.some.inj hl⟩
  have htbl0 : table.refs.length < 2 ^ 32 := htab _ (List.mem_of_getElem? htable)
  have hStab : cs.tables = L.tables.map TableInst.toV2 := erase_tables hS
  have hta : cf.module.tableAddr? e.table = some a.value := by
    simp [Silmaril.Wasm.V2.Execution.ModuleInst.tableAddr?, hFt, ha]
  have htc : cs.tableInst? a.value = some (TableInst.toV2 tL) := by
    simp [Silmaril.Wasm.V2.Execution.Store.tableInst?, hStab, htL]
  obtain ⟨ei, hei, heir⟩ : ∃ ei, cs.elems[k]? = some ei ∧ ei.refs = elemRefsV w := by
    cases h : cs.elems[k]? with
    | none => rw [h] at hSe; cases hSe
    | some ei => rw [h] at hSe; exact ⟨ei, rfl, Option.some.inj hSe⟩
  have hxe : (⟨Fin.ofNat _ k⟩ : ElemIdx).toNat = k := by
    show (Fin.ofNat (2 ^ 32) k).val = k
    rw [Fin.val_ofNat]; exact Nat.mod_eq_of_lt hk
  have helA : cf.module.elemAddr? (⟨Fin.ofNat _ k⟩ : ElemIdx) = some k := by
    show cf.module.elems[(⟨Fin.ofNat _ k⟩ : ElemIdx).toNat]? = some k
    rw [hxe]; exact hFe
  have hel : (⟨cs, cf⟩ : Silmaril.Wasm.V2.Execution.State H).elem?
      (⟨Fin.ofNat _ k⟩ : ElemIdx) = some ei := by
    show (cf.module.elemAddr? (⟨Fin.ofNat _ k⟩ : ElemIdx)).bind
      (fun a => cs.elemInst? a) = some ei
    rw [helA]
    exact hei
  obtain ⟨x, hx, hsx⟩ := offset_v2 (tgt := tgt) hG hFg hoff
    ([Silmaril.Wasm.V2.Execution.constI32 0,
      Silmaril.Wasm.V2.Execution.constI32 (BitVec.ofNat 32 e.init.length),
      .plain (.tableInit e.table ⟨Fin.ofNat _ k⟩), .plain (.elemDrop ⟨Fin.ofNat _ k⟩)] ++ rest)
  have htlen : (TableInst.toV2 tL).refs.length = table.refs.length := by
    simp [tableInst_toV2_refs, htLlen]
  have heilen : ei.refs.length = e.init.length := by simp [heir, elemRefsV, hvlen]
  have hti := tableInit_v2 (tgt := tgt) hta e.init.length cs (TableInst.toV2 tL) x 0 htc hel
    (by rw [htlen]; exact htbl0) (by rw [heilen, ← hvlen]; omega)
    (by rw [hx, htlen, ← hvlen]; exact hbnd) (by rw [heilen]; simp)
  have hti' := Silmaril.Wasm.V2.Execution.Steps.ctxtInstrs (P := v2Profile) (host := tgt)
    [] ([.plain (.elemDrop (⟨Fin.ofNat _ k⟩ : ElemIdx))] ++ rest) hti
  simp only [Silmaril.Wasm.V2.Execution.vals, List.map_nil, List.nil_append,
    List.append_nil] at hti'
  set ti' : VTableInst := { TableInst.toV2 tL with refs :=
    ((TableInst.toV2 tL).refs.take x.toNat ++ (ei.refs.drop (0 : BitVec 32).toNat).take
      e.init.length ++ (TableInst.toV2 tL).refs.drop (x.toNat + e.init.length)) } with hti'def
  have hdrop : Silmaril.Wasm.V2.Execution.Step v2Profile tgt
      ⟨cs.setTableInst a.value ti', cf, [.plain (.elemDrop (⟨Fin.ofNat _ k⟩ : ElemIdx))]⟩
      ⟨(cs.setTableInst a.value ti').setElemInst k { ei with refs := [] }, cf, []⟩ :=
    .elemDrop helA (by exact hei)
  have hdrop' := Silmaril.Wasm.V2.Execution.Steps.ctxtInstrs (P := v2Profile) (host := tgt)
    [] rest (Silmaril.Wasm.V2.Execution.Step.steps hdrop)
  simp only [Silmaril.Wasm.V2.Execution.vals, List.map_nil, List.nil_append,
    List.nil_append] at hdrop'
  refine ⟨(cs.setTableInst a.value ti').setElemInst k { ei with refs := [] }, ?_, ?_, rfl, rfl,
    rfl, ?_⟩
  · have e2 : Silmaril.Wasm.V2.Execution.expression
        (Silmaril.Wasm.V2.Execution.runElem k (Elem.toV2 e)) =
        Silmaril.Wasm.V2.Execution.expression (Expr.toV2 e.offset) ++
        [Silmaril.Wasm.V2.Execution.constI32 0,
          Silmaril.Wasm.V2.Execution.constI32 (BitVec.ofNat 32 e.init.length),
          .plain (.tableInit e.table ⟨Fin.ofNat _ k⟩),
          .plain (.elemDrop ⟨Fin.ofNat _ k⟩)] := by
      simp only [Silmaril.Wasm.V2.Execution.runElem, Elem.toV2,
        Silmaril.Wasm.V2.Execution.expression, List.map_append, List.length_map]
      rfl
    rw [e2, List.append_assoc]
    exact hsx.trans (hti'.trans hdrop')
  · have hmod := map_modify_eq_set (f := elemUpd w) (g := TableInst.toV2) htL
    have htiupd : TableInst.toV2 (elemUpd w tL) = ti' := by
      have hl2 : (tL.refs.take w.offset ++ w.values.map some ++
          tL.refs.drop (w.offset + w.values.length)).length = tL.refs.length := by
        simp only [List.length_append, List.length_take, List.length_map, List.length_drop]
        omega
      simp only [hti'def, elemUpd, Silmaril.Wasm.Execution.Runtime.TableInst.toV2, hl2]
      congr 1
      simp only [List.map_append, List.map_take, List.map_drop, List.map_map, hx, heir]
      rw [show (0 : BitVec 32).toNat = 0 from rfl, List.drop_zero,
        List.take_of_length_le
          (show (elemRefsV w).length ≤ e.init.length by simp [elemRefsV, hvlen])]
      simp [elemRefsV, Function.comp_def, hvlen]
    rw [htiupd] at hmod
    have hSe' : Store.erase ((cs.setTableInst a.value ti').setElemInst k { ei with refs := [] }) =
        { Store.erase cs with tables := cs.tables.set a.value ti' } := rfl
    rw [hSe', hS, hStab, ← hmod]
    subst hwa
    rfl
  · intro i hi
    simp only [Silmaril.Wasm.V2.Execution.Store.setElemInst,
      Silmaril.Wasm.V2.Execution.Store.setTableInst]
    rw [List.getElem?_set_ne (Ne.symm hi)]

/-- One data segment program. The memory index is `0`: `$rundata`
(`9-module:161-165`) ignores it, and a valid Lime1 module has only one memory. -/
theorem dataSeg_v2 {Lb L : Store H} {module : ModuleInst} {cf : VFrame} {cs : VStore H}
    {d : Data} {w : DataWrite} {k : Nat}
    (hw : resolveData? Lb module d = some w) (hm0 : d.memory.toNat = 0)
    (hG : cs.globals.map GlobalInst.erase = Lb.globals.map GlobalInst.toV2)
    (hFg : cf.module.globals = module.globals.map Addr.value)
    (hFm : cf.module.mems = module.memories.map Addr.value)
    (hFd : cf.module.datas[k]? = some k) (hk : k < 2 ^ 32)
    (hSd : (cs.datas[k]?).map (·.bytes) = some d.bytes)
    (hS : Store.erase cs = L.toV2)
    (hlen : ∀ i : Nat, (L.memories[i]?).map (fun t : MemInst => t.data.size) =
      (Lb.memories[i]?).map (fun t : MemInst => t.data.size))
    (hmem : ∀ t ∈ Lb.memories, t.data.size ≤ 2 ^ 32)
    (hdb : d.bytes.size < 2 ^ 32)
    (rest : List VAdmin) :
    ∃ cs', Silmaril.Wasm.V2.Execution.Steps v2Profile tgt
        ⟨cs, cf, Silmaril.Wasm.V2.Execution.expression
          (Silmaril.Wasm.V2.Execution.runData k (Data.toV2 d)) ++ rest⟩ ⟨cs', cf, rest⟩ ∧
      Store.erase cs' = (applyData L w).toV2 ∧ cs'.globals = cs.globals ∧
      (∀ i, i ≠ k → cs'.datas[i]? = cs.datas[i]?) := by
  obtain ⟨a, memory, hoff, ha, hmemA, hwb, hbnd, hwa⟩ := resolveData?_inv hw
  have hl := hlen a.value
  rw [hmemA] at hl
  obtain ⟨mL, hmL, hmLlen⟩ : ∃ mL, L.memories[a.value]? = some mL ∧
      mL.data.size = memory.data.size := by
    cases h : L.memories[a.value]? with
    | none => rw [h] at hl; cases hl
    | some mL => rw [h] at hl; exact ⟨mL, rfl, Option.some.inj hl⟩
  have hmsz0 : memory.data.size ≤ 2 ^ 32 := hmem _ (List.mem_of_getElem? hmemA)
  have hSmem : cs.mems = L.memories.map MemInst.toV2 := erase_mems hS
  have hma : cf.module.memAddr? Silmaril.Wasm.V2.Execution.memIdx0 = some a.value := by
    show cf.module.mems[(Silmaril.Wasm.V2.Execution.memIdx0 : MemIdx).toNat]? = some a.value
    rw [hFm, show (Silmaril.Wasm.V2.Execution.memIdx0 : MemIdx).toNat = 0 from rfl,
      List.getElem?_map, ← hm0, ha]
    rfl
  have hmc : cs.memInst? a.value = some (MemInst.toV2 mL) := by
    simp [Silmaril.Wasm.V2.Execution.Store.memInst?, hSmem, hmL]
  obtain ⟨di, hdi, hdib⟩ : ∃ di, cs.datas[k]? = some di ∧ di.bytes = d.bytes := by
    cases h : cs.datas[k]? with
    | none => rw [h] at hSd; cases hSd
    | some di => rw [h] at hSd; exact ⟨di, rfl, Option.some.inj hSd⟩
  have hxd : (⟨Fin.ofNat _ k⟩ : DataIdx).toNat = k := by
    show (Fin.ofNat (2 ^ 32) k).val = k
    rw [Fin.val_ofNat]; exact Nat.mod_eq_of_lt hk
  have hdaA : cf.module.dataAddr? (⟨Fin.ofNat _ k⟩ : DataIdx) = some k := by
    show cf.module.datas[(⟨Fin.ofNat _ k⟩ : DataIdx).toNat]? = some k
    rw [hxd]; exact hFd
  have hda : (⟨cs, cf⟩ : Silmaril.Wasm.V2.Execution.State H).data?
      (⟨Fin.ofNat _ k⟩ : DataIdx) = some di := by
    show (cf.module.dataAddr? (⟨Fin.ofNat _ k⟩ : DataIdx)).bind
      (fun a => cs.dataInst? a) = some di
    rw [hdaA]
    exact hdi
  obtain ⟨x, hx, hsx⟩ := offset_v2 (tgt := tgt) hG hFg hoff
    ([Silmaril.Wasm.V2.Execution.constI32 0,
      Silmaril.Wasm.V2.Execution.constI32 (BitVec.ofNat 32 d.bytes.size),
      .plain (.memoryInit ⟨Fin.ofNat _ k⟩), .plain (.dataDrop ⟨Fin.ofNat _ k⟩)] ++ rest)
  have hnn : (BitVec.ofNat 32 d.bytes.size).toNat = d.bytes.size := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hdb
  obtain ⟨B, hBsz, hBget, hsteps⟩ := memInit_v2 (tgt := tgt) hma d.bytes.size cs
    (MemInst.toV2 mL) x 0 (BitVec.ofNat 32 d.bytes.size) hmc hda hnn
    (by show x.toNat + d.bytes.size ≤ mL.data.size; rw [hx, hmLlen]; exact hbnd)
    (by show (0 : BitVec 32).toNat + d.bytes.size ≤ di.bytes.size; rw [hdib]; simp)
    (by show mL.data.size ≤ 2 ^ 32; rw [hmLlen]; exact hmsz0)
    (by rw [hdib]; omega)
  have hsteps' := Silmaril.Wasm.V2.Execution.Steps.ctxtInstrs (P := v2Profile) (host := tgt)
    [] ([.plain (.dataDrop (⟨Fin.ofNat _ k⟩ : DataIdx))] ++ rest) hsteps
  simp only [Silmaril.Wasm.V2.Execution.vals, List.map_nil, List.nil_append,
    List.append_nil] at hsteps'
  have hdrop : Silmaril.Wasm.V2.Execution.Step v2Profile tgt
      ⟨cs.setMemInst a.value { MemInst.toV2 mL with bytes := B }, cf,
        [.plain (.dataDrop (⟨Fin.ofNat _ k⟩ : DataIdx))]⟩
      ⟨(cs.setMemInst a.value { MemInst.toV2 mL with bytes := B }).setDataInst k
        ⟨ByteArray.empty⟩, cf, []⟩ :=
    .dataDrop hdaA (by exact hdi)
  have hdrop' := Silmaril.Wasm.V2.Execution.Steps.ctxtInstrs (P := v2Profile) (host := tgt)
    [] rest (Silmaril.Wasm.V2.Execution.Step.steps hdrop)
  simp only [Silmaril.Wasm.V2.Execution.vals, List.map_nil, List.nil_append] at hdrop'
  refine ⟨(cs.setMemInst a.value { MemInst.toV2 mL with bytes := B }).setDataInst k
    ⟨ByteArray.empty⟩, ?_, ?_, rfl, ?_⟩
  · have e2 : Silmaril.Wasm.V2.Execution.expression
        (Silmaril.Wasm.V2.Execution.runData k (Data.toV2 d)) =
        Silmaril.Wasm.V2.Execution.expression (Expr.toV2 d.offset) ++
        [Silmaril.Wasm.V2.Execution.constI32 0,
          Silmaril.Wasm.V2.Execution.constI32 (BitVec.ofNat 32 d.bytes.size),
          .plain (.memoryInit ⟨Fin.ofNat _ k⟩),
          .plain (.dataDrop ⟨Fin.ofNat _ k⟩)] := by
      simp only [Silmaril.Wasm.V2.Execution.runData, Data.toV2,
        Silmaril.Wasm.V2.Execution.expression, List.map_append]
      rfl
    rw [e2, List.append_assoc]
    exact hsx.trans (hsteps'.trans hdrop')
  · have hbnd' : w.offset + w.bytes.size ≤ mL.data.size := by rw [hwb, hmLlen]; exact hbnd
    have hA : Memory.writeBytes mL.data w.offset w.bytes =
        some (w.bytes.copySlice 0 mL.data w.offset w.bytes.size) := by
      simp [Memory.writeBytes, hbnd']
    have hBeq : B = w.bytes.copySlice 0 mL.data w.offset w.bytes.size := by
      refine ByteArray.ext (Array.ext_getElem? fun j => ?_)
      rw [hBget j, Silmaril.Wasm.Lime1.Execution.ToCoreSim.bulk_writeBytes_get hA j, hx, hwb,
        hdib]
      simp only [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_add]
      rfl
    have hmod := map_modify_eq_set
      (f := fun mm : MemInst => { mm with data := (w.bytes.copySlice 0 mm.data w.offset
        w.bytes.size) }) (g := MemInst.toV2) hmL
    have hmiupd : MemInst.toV2 { mL with data := (w.bytes.copySlice 0 mL.data w.offset
        w.bytes.size) } = { MemInst.toV2 mL with bytes := B } := by
      have hsz := copySlice_size hbnd'
      simp only [Silmaril.Wasm.Execution.Runtime.MemInst.toV2, hsz, hBeq]
    rw [hmiupd] at hmod
    have hSe' : Store.erase ((cs.setMemInst a.value
        { MemInst.toV2 mL with bytes := B }).setDataInst k ⟨ByteArray.empty⟩) =
        { Store.erase cs with
          mems := (cs.mems.set a.value { MemInst.toV2 mL with bytes := B }) } := rfl
    rw [hSe', hS, hSmem, ← hmod]
    subst hwa
    rfl
  · intro i hi
    simp only [Silmaril.Wasm.V2.Execution.Store.setDataInst,
      Silmaril.Wasm.V2.Execution.Store.setMemInst]
    rw [List.getElem?_set_ne (Ne.symm hi)]

/-! ### The segment loops -/

/-- The element segment programs. -/
theorem elemLoop_v2 {L0 : Store H} {module : ModuleInst} {cf : VFrame}
    (hFg : cf.module.globals = module.globals.map Addr.value)
    (hFt : cf.module.tables = module.tables.map Addr.value)
    (htab : ∀ t ∈ L0.tables, t.refs.length < 2 ^ 32) :
    (es : List Elem) → (ws : List ElemWrite) → (k : Nat) → (cs : VStore H) → (L : Store H) →
    List.Forall₂ (fun e w => resolveElem? L0 module e = some w) es ws →
    k + es.length ≤ 2 ^ 32 →
    (∀ i, i < es.length → cf.module.elems[k + i]? = some (k + i)) →
    (∀ i, i < es.length → (cs.elems[k + i]?).map (·.refs) = (ws[i]?).map elemRefsV) →
    cs.globals.map GlobalInst.erase = L0.globals.map GlobalInst.toV2 →
    Store.erase cs = L.toV2 →
    (∀ i : Nat, (L.tables[i]?).map (fun t : TableInst => t.refs.length) =
      (L0.tables[i]?).map (fun t : TableInst => t.refs.length)) →
    (rest : List VAdmin) →
    ∃ cs', Silmaril.Wasm.V2.Execution.Steps v2Profile tgt
        ⟨cs, cf, Silmaril.Wasm.V2.Execution.expression
          (((List.range' k es.length).zip (es.map Elem.toV2)).flatMap fun p =>
            Silmaril.Wasm.V2.Execution.runElem p.1 p.2) ++ rest⟩ ⟨cs', cf, rest⟩ ∧
      Store.erase cs' = (ws.foldl applyElem L).toV2 ∧ cs'.globals = cs.globals ∧
      cs'.datas = cs.datas ∧ cs'.mems = cs.mems
  | [], [], _, cs, _, .nil, _, _, _, _, hS, _, rest =>
    ⟨cs, by simpa [Silmaril.Wasm.V2.Execution.expression] using Relation.ReflTransGen.refl,
      hS, rfl, rfl, rfl⟩
  | e :: es, w :: ws, k, cs, L, .cons hw hws, hk, hFe, hSe, hG, hS, hlen, rest => by
    simp only [List.length_cons] at hk
    obtain ⟨cs1, h1, hS1, hG1, hD1, hM1, hE1⟩ := elemSeg_v2 (tgt := tgt) (k := k)
      hw hG hFg hFt (by simpa using hFe 0 (by simp)) (by omega)
      (by simpa using hSe 0 (by simp)) hS hlen htab
      (Silmaril.Wasm.V2.Execution.expression
        (((List.range' (k + 1) es.length).zip (es.map Elem.toV2)).flatMap fun p =>
          Silmaril.Wasm.V2.Execution.runElem p.1 p.2) ++ rest)
    obtain ⟨cs2, h2, hS2, hG2, hD2, hM2⟩ := elemLoop_v2 hFg hFt htab es ws (k + 1) cs1
      (applyElem L w) hws (by omega)
      (fun i hi => by
        have := hFe (i + 1) (by simp; omega)
        rwa [show k + (i + 1) = k + 1 + i by omega] at this)
      (fun i hi => by
        rw [hE1 (k + 1 + i) (by omega)]
        have := hSe (i + 1) (by simp; omega)
        rw [show k + (i + 1) = k + 1 + i by omega] at this
        simpa using this)
      (by rw [hG1]; exact hG) hS1 (applyElem_len hw hlen) rest
    refine ⟨cs2, ?_, hS2, hG2.trans hG1, hD2.trans hD1, hM2.trans hM1⟩
    have e1 : Silmaril.Wasm.V2.Execution.expression
        (((List.range' k (e :: es).length).zip ((e :: es).map Elem.toV2)).flatMap fun p =>
          Silmaril.Wasm.V2.Execution.runElem p.1 p.2) ++ rest =
        Silmaril.Wasm.V2.Execution.expression
          (Silmaril.Wasm.V2.Execution.runElem k (Elem.toV2 e)) ++
        (Silmaril.Wasm.V2.Execution.expression
          (((List.range' (k + 1) es.length).zip (es.map Elem.toV2)).flatMap fun p =>
            Silmaril.Wasm.V2.Execution.runElem p.1 p.2) ++ rest) := by
      simp [Silmaril.Wasm.V2.Execution.expression, List.range'_succ]
    rw [e1]
    exact h1.trans h2

/-- The data segment programs. -/
theorem dataLoop_v2 {Lb : Store H} {module : ModuleInst} {cf : VFrame}
    (hFg : cf.module.globals = module.globals.map Addr.value)
    (hFm : cf.module.mems = module.memories.map Addr.value)
    (hmem : ∀ t ∈ Lb.memories, t.data.size ≤ 2 ^ 32) :
    (ds : List Data) → (ws : List DataWrite) → (k : Nat) → (cs : VStore H) → (L : Store H) →
    List.Forall₂ (fun d w => resolveData? Lb module d = some w) ds ws →
    (∀ d ∈ ds, d.memory.toNat = 0) →
    (∀ d ∈ ds, d.bytes.size < 2 ^ 32) →
    k + ds.length ≤ 2 ^ 32 →
    (∀ i, i < ds.length → cf.module.datas[k + i]? = some (k + i)) →
    (∀ i, i < ds.length → (cs.datas[k + i]?).map (·.bytes) = (ds[i]?).map (·.bytes)) →
    cs.globals.map GlobalInst.erase = Lb.globals.map GlobalInst.toV2 →
    Store.erase cs = L.toV2 →
    (∀ i : Nat, (L.memories[i]?).map (fun t : MemInst => t.data.size) =
      (Lb.memories[i]?).map (fun t : MemInst => t.data.size)) →
    (rest : List VAdmin) →
    ∃ cs', Silmaril.Wasm.V2.Execution.Steps v2Profile tgt
        ⟨cs, cf, Silmaril.Wasm.V2.Execution.expression
          (((List.range' k ds.length).zip (ds.map Data.toV2)).flatMap fun p =>
            Silmaril.Wasm.V2.Execution.runData p.1 p.2) ++ rest⟩ ⟨cs', cf, rest⟩ ∧
      Store.erase cs' = (ws.foldl applyData L).toV2
  | [], [], _, cs, _, .nil, _, _, _, _, _, _, hS, _, rest =>
    ⟨cs, by simpa [Silmaril.Wasm.V2.Execution.expression] using Relation.ReflTransGen.refl, hS⟩
  | d :: ds, w :: ws, k, cs, L, .cons hw hws, hm0, hdb, hk, hFd, hSd, hG, hS, hlen, rest => by
    simp only [List.length_cons] at hk
    obtain ⟨cs1, h1, hS1, hG1, hD1⟩ := dataSeg_v2 (tgt := tgt) (k := k)
      hw (hm0 d (by simp)) hG hFg hFm (by simpa using hFd 0 (by simp)) (by omega)
      (by simpa using hSd 0 (by simp)) hS hlen hmem (hdb d (by simp))
      (Silmaril.Wasm.V2.Execution.expression
        (((List.range' (k + 1) ds.length).zip (ds.map Data.toV2)).flatMap fun p =>
          Silmaril.Wasm.V2.Execution.runData p.1 p.2) ++ rest)
    obtain ⟨cs2, h2, hS2⟩ := dataLoop_v2 hFg hFm hmem ds ws (k + 1) cs1
      (applyData L w) hws (fun d' hd' => hm0 d' (by simp [hd']))
      (fun d' hd' => hdb d' (by simp [hd'])) (by omega)
      (fun i hi => by
        have := hFd (i + 1) (by simp; omega)
        rwa [show k + (i + 1) = k + 1 + i by omega] at this)
      (fun i hi => by
        rw [hD1 (k + 1 + i) (by omega)]
        have := hSd (i + 1) (by simp; omega)
        rw [show k + (i + 1) = k + 1 + i by omega] at this
        simpa using this)
      (by rw [hG1]; exact hG) hS1 (applyData_len hw hlen) rest
    refine ⟨cs2, ?_, hS2⟩
    have e1 : Silmaril.Wasm.V2.Execution.expression
        (((List.range' k (d :: ds).length).zip ((d :: ds).map Data.toV2)).flatMap fun p =>
          Silmaril.Wasm.V2.Execution.runData p.1 p.2) ++ rest =
        Silmaril.Wasm.V2.Execution.expression
          (Silmaril.Wasm.V2.Execution.runData k (Data.toV2 d)) ++
        (Silmaril.Wasm.V2.Execution.expression
          (((List.range' (k + 1) ds.length).zip (ds.map Data.toV2)).flatMap fun p =>
            Silmaril.Wasm.V2.Execution.runData p.1 p.2) ++ rest) := by
      simp [Silmaril.Wasm.V2.Execution.expression, List.range'_succ]
    rw [e1]
    exact h1.trans h2

end Segments

/-! ### Well-formedness of the prepared store -/

/-- The size and maximum of a table. -/
def tableShapeV (ti : TableInst) : Nat × Option Nat := (ti.refs.length, ti.max)

/-- Element writes preserve table sizes and maxima, given their bounds against
the original store. -/
theorem foldl_applyElem_tables (st : Store H) :
    (ws : List ElemWrite) → (st' : Store H) →
    (∀ i : Nat, (st'.tables[i]?).map tableShapeV = (st.tables[i]?).map tableShapeV) →
    (∀ w ∈ ws, ∃ ti, st.tables[w.address.value]? = some ti ∧
      w.offset + w.values.length ≤ ti.refs.length) →
    ∀ i : Nat, ((ws.foldl applyElem st').tables[i]?).map tableShapeV =
      (st.tables[i]?).map tableShapeV
  | [], st', h, _ => h
  | w :: ws, st', h, hb => by
    refine foldl_applyElem_tables st ws (applyElem st' w) ?_ (fun w' hw' => hb w' (by simp [hw']))
    intro i
    obtain ⟨ti, hti, hbd⟩ := hb w (by simp)
    rw [← h i]
    simp only [applyElem, List.getElem?_modify]
    split
    · next heq =>
      subst heq
      have h' := h w.address.value
      rw [hti] at h'
      cases hc : st'.tables[w.address.value]? with
      | none => rw [hc] at h'; cases h'
      | some ti' =>
        rw [hc] at h'
        simp only [tableShapeV, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h'
        simp only [tableShapeV, Option.map_some, Option.some.injEq, Prod.mk.injEq, Functor.map]
        refine ⟨?_, trivial⟩
        simp only [List.length_append, List.length_take, List.length_map, List.length_drop]
        omega
    · simp

theorem storeWF_of_shapes {s s' : Store H} (hwf : StoreWF s)
    (hm : ∀ i : Nat, (s'.memories[i]?).map memShape = (s.memories[i]?).map memShape)
    (ht : ∀ i : Nat, (s'.tables[i]?).map tableShapeV = (s.tables[i]?).map tableShapeV) :
    StoreWF s' := by
  have hmem : ∀ mi ∈ s'.memories, ∃ mi0 ∈ s.memories,
      mi0.data.size = mi.data.size ∧ mi0.max = mi.max := by
    intro mi hmi
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmi
    have := hm i
    rw [hi] at this
    cases hc : s.memories[i]? with
    | none => rw [hc] at this; cases this
    | some mi0 =>
      rw [hc] at this
      simp only [memShape, Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
      exact ⟨mi0, List.mem_of_getElem? hc, this.1.symm, this.2.symm⟩
  have htab : ∀ ti ∈ s'.tables, ∃ ti0 ∈ s.tables,
      ti0.refs.length = ti.refs.length ∧ ti0.max = ti.max := by
    intro ti hti
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hti
    have := ht i
    rw [hi] at this
    cases hc : s.tables[i]? with
    | none => rw [hc] at this; cases this
    | some ti0 =>
      rw [hc] at this
      simp only [tableShapeV, Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
      exact ⟨ti0, List.mem_of_getElem? hc, this.1.symm, this.2.symm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro mi hmi
    obtain ⟨mi0, h0, hsz, -⟩ := hmem mi hmi
    rw [← hsz]; exact hwf.memAligned mi0 h0
  · intro mi hmi
    obtain ⟨mi0, h0, hsz, -⟩ := hmem mi hmi
    rw [← hsz]; exact hwf.memSize mi0 h0
  · intro mi hmi j hj
    obtain ⟨mi0, h0, -, hmx⟩ := hmem mi hmi
    exact hwf.memMax mi0 h0 j (by rw [hmx]; exact hj)
  · intro ti hti
    obtain ⟨ti0, h0, hsz, -⟩ := htab ti hti
    rw [← hsz]; exact hwf.tableSize ti0 h0
  · intro ti hti j hj
    obtain ⟨ti0, h0, -, hmx⟩ := htab ti hti
    exact hwf.tableMax ti0 h0 j (by rw [hmx]; exact hj)

/-! ### The `Eval_expr` premises of `$instantiate` -/

section Eval

variable {tgt : VHostSemantics H} {cs : VStore H} {cf : VFrame} {s : Store H}
  {module : ModuleInst}

theorem evalGlobals_v2 (hG : cs.globals.map GlobalInst.erase = s.globals.map GlobalInst.toV2)
    (hF : cf.module.globals = module.globals.map Addr.value) :
    {gs : List Global} → {vs : List Value} →
    List.Forall₂ (fun g v => constExpr? s module g.init = some v) gs vs →
    List.Forall₂ (fun (g : Silmaril.Wasm.V2.Global) (v : VVal) =>
      Silmaril.Wasm.V2.Execution.EvalExpr v2Profile tgt cs cf
        (Silmaril.Wasm.V2.Global.init g) cs cf [v])
      (gs.map Global.toV2) (vs.map Value.toV2)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs =>
    .cons (constExpr_v2 hG hF h) (evalGlobals_v2 hG hF hs)

theorem evalRefs_v2 (hf : cf.module.funcs = module.funcs.map Addr.value) :
    (xs : List FuncIdx) → (as : List FuncAddr) →
    xs.mapM (fun i => module.funcs[i.toNat]?) = some as →
    List.Forall₂ (fun (ex : Silmaril.Wasm.V2.Expr) (r : Silmaril.Wasm.V2.Execution.Ref) =>
      Silmaril.Wasm.V2.Execution.EvalExpr v2Profile tgt cs cf ex cs cf [.ref r])
      (xs.map funcRefV2) (as.map fun a => .funcAddr a.value)
  | [], as, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact .nil
  | x :: xs, as, h => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨a, ha, as', has, rfl⟩ := h
    refine .cons ?_ (evalRefs_v2 hf xs as' has)
    have hx : cf.module.funcAddr? x = some a.value := by
      show cf.module.funcs[x.toNat]? = some a.value
      rw [hf, List.getElem?_map, ha]; rfl
    exact Relation.ReflTransGen.single
      (Silmaril.Wasm.V2.Execution.Step.read (Silmaril.Wasm.V2.Execution.ReadStep.refFunc hx))

theorem evalElems_v2 (hf : cf.module.funcs = module.funcs.map Addr.value) :
    {es : List Elem} → {ws : List ElemWrite} →
    List.Forall₂ (fun e w => resolveElem? s module e = some w) es ws →
    List.Forall₂ (fun (e : Silmaril.Wasm.V2.Elem)
        (rs : List Silmaril.Wasm.V2.Execution.Ref) =>
      List.Forall₂ (fun (ex : Silmaril.Wasm.V2.Expr) (r : Silmaril.Wasm.V2.Execution.Ref) =>
        Silmaril.Wasm.V2.Execution.EvalExpr v2Profile tgt cs cf ex cs cf [.ref r])
        e.init rs)
      (es.map Elem.toV2) (ws.map elemRefsV)
  | [], [], .nil => .nil
  | e :: es, w :: ws, .cons h hs => by
    obtain ⟨-, -, -, -, -, hrefs, -, -⟩ := resolveElem?_inv h
    exact .cons (evalRefs_v2 hf e.init w.values hrefs) (evalElems_v2 hf hs)

end Eval

/-! ### Preparation is 2.0 instantiation followed by the segment programs -/

/-- The 2.0 start code of a module. -/
def startCodeV (m : Silmaril.Wasm.V2.Module) : List VAdmin :=
  match m.start with | some x => [(.plain (.call x) : VAdmin)] | none => []

/-- A valid Lime1 module's active data segments all name memory `0`, which is
the memory `$rundata` (`9-module:161-165`) initialises. -/
theorem data_memory_zero {m : Module} (hv : Validation.ModuleValid m) {d : Data}
    (hd : d ∈ m.data) : d.memory.toNat = 0 := by
  obtain ⟨mt, hmt⟩ := (hv.data d hd).memory
  have := (List.getElem?_eq_some_iff.mp hmt).1
  have hle := hv.singleMemory
  omega

/-- 2.0 instantiation, followed by the element and data segment programs, reaches
the start code on a store whose erasure is the image of the prepared Lime1 store. -/
theorem prepare_v2 {tgt : VHostSemantics H} {before : Store H} {m : Module}
    {imports : List ExternVal} {p : Prepared H}
    (bounds : InstantiationBounds before m imports) (hv : Validation.ModuleValid m)
    (hp : prepare? before m imports = some p) :
    ∃ (c : VConfig H) (S : VStore H),
      Silmaril.Wasm.V2.Execution.Instantiate v2Profile tgt before.toV2 m.toV2
        (imports.map ExternVal.toV2) c ∧
      Silmaril.Wasm.V2.Execution.Steps v2Profile tgt c ⟨S, c.frame, startCodeV m.toV2⟩ ∧
      Store.erase S = p.store.toV2 ∧ ModuleInstSim p.module c.frame.module ∧
      c.frame.locals = [] ∧ StoreWF p.store := by
  obtain ⟨allocated, elems, data, ha, he, hd, hst⟩ := prepare?_inv hp
  have he2 := mapM_forall₂ he
  have hd2 := mapM_forall₂ hd
  obtain ⟨inits, SA, mi, hin, hAM, hmi, hmiE, hmiD, hSA, hSAe, hSAd⟩ :=
    allocModule_v2 ha he2.length_eq
  obtain ⟨inits', exports, funcs, hin', hex, hfn, hmodeq, halloceq⟩ := allocate?_invV ha
  have hinits : inits' = inits := by rw [hin'] at hin; exact Option.some.inj hin
  rw [hinits] at halloceq
  -- the module instance of the running frame
  have hmif : mi.funcs = p.module.funcs.map Addr.value := congrArg (·.funcs) hmi
  have hmig : mi.globals = p.module.globals.map Addr.value := congrArg (·.globals) hmi
  have hmit : mi.tables = p.module.tables.map Addr.value := congrArg (·.tables) hmi
  have hmim : mi.mems = p.module.memories.map Addr.value := congrArg (·.mems) hmi
  -- bounds on the allocated store
  have htab : ∀ t ∈ allocated.tables, t.refs.length < 2 ^ 32 := by
    rw [halloceq]
    intro t ht
    simp only [List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨tt, -, rfl⟩
    · exact bounds.storeWF.tableSize t ht
    · simp only [List.length_replicate]; exact tt.limits.min.isLt
  have hmem : ∀ t ∈ allocated.memories, t.data.size ≤ 2 ^ 32 := by
    rw [halloceq]
    intro t ht
    simp only [List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨mt, hmt, rfl⟩
    · exact bounds.storeWF.memSize t ht
    · have hvt := (hv.memories mt hmt).1
      simp only [ByteArray.size, Array.size_replicate, Silmaril.Wasm.Execution.Memory.pageSize]
      omega
  have hwfAlloc : StoreWF allocated := by
    have hmems : ∀ t ∈ allocated.memories, t.data.size % Memory.pageSize = 0 ∧
        ∀ j ∈ t.max, j < 2 ^ 32 := by
      rw [halloceq]
      intro t ht
      simp only [List.mem_append, List.mem_map] at ht
      rcases ht with ht | ⟨mt, -, rfl⟩
      · exact ⟨bounds.storeWF.memAligned t ht, bounds.storeWF.memMax t ht⟩
      · refine ⟨?_, ?_⟩
        · simp only [ByteArray.size, Array.size_replicate]
          exact Nat.mul_mod_left _ _
        · intro j hj
          simp only [Option.mem_def, Option.map_eq_some_iff] at hj
          obtain ⟨b, -, rfl⟩ := hj
          exact b.isLt
    have htabs : ∀ t ∈ allocated.tables, ∀ j ∈ t.max, j < 2 ^ 32 := by
      rw [halloceq]
      intro t ht
      simp only [List.mem_append, List.mem_map] at ht
      rcases ht with ht | ⟨tt, -, rfl⟩
      · exact bounds.storeWF.tableMax t ht
      · intro j hj
        simp only [Option.mem_def, Option.map_eq_some_iff] at hj
        obtain ⟨b, -, rfl⟩ := hj
        exact b.isLt
    exact ⟨fun t ht => (hmems t ht).1, hmem, fun t ht => (hmems t ht).2, htab, htabs⟩
  -- the prepared Lime1 store is well formed
  have hdbnd : ∀ w ∈ data, ∃ mi, allocated.memories[w.address.value]? = some mi ∧
      w.offset + w.bytes.size ≤ mi.data.size := by
    intro w hw
    obtain ⟨d, -, hrd⟩ := forall₂_mem_right hd2 hw
    simpa using resolveData?_bounds hrd
  have hebnd : ∀ w ∈ elems, ∃ ti, allocated.tables[w.address.value]? = some ti ∧
      w.offset + w.values.length ≤ ti.refs.length := by
    intro w hw
    obtain ⟨e, -, hre⟩ := forall₂_mem_right he2 hw
    simpa using resolveElem?_bounds hre
  have hwfP : StoreWF p.store := by
    refine storeWF_of_shapes hwfAlloc ?_ ?_
    · rw [hst]
      exact foldl_applyData_memories allocated data (elems.foldl applyElem allocated)
        (fun i => by rw [foldl_applyElem_memories]) hdbnd
    · rw [hst]
      intro i
      rw [foldl_applyData_tables]
      exact foldl_applyElem_tables allocated elems allocated (fun _ => rfl) hebnd i
  -- the element segment programs
  obtain ⟨cs1, h1, hS1, hG1, hD1, hM1⟩ := elemLoop_v2 (tgt := tgt) (L0 := allocated)
    (module := p.module) (cf := { module := mi }) hmig hmit htab m.elems elems 0 SA allocated
    he2 (by simpa using bounds.elemCount)
    (fun i hi => by simp [hmiE, List.getElem?_range hi])
    (fun i hi => by
      simp only [Nat.zero_add, hSAe, List.getElem?_map, Option.map_map, Function.comp_def])
    (erase_globals hSA) hSA (fun _ => rfl)
    (Silmaril.Wasm.V2.Execution.expression
      (((List.range' 0 m.data.length).zip (m.data.map Data.toV2)).flatMap fun q =>
        Silmaril.Wasm.V2.Execution.runData q.1 q.2) ++ startCodeV m.toV2)
  -- the data segment programs
  obtain ⟨cs2, h2, hS2⟩ := dataLoop_v2 (tgt := tgt) (Lb := allocated)
    (module := p.module) (cf := { module := mi }) hmig hmim hmem m.data data 0 cs1
    (elems.foldl applyElem allocated) hd2 (fun d hd => data_memory_zero hv hd) bounds.data
    (by simpa using bounds.dataCount)
    (fun i hi => by simp [hmiD, List.getElem?_range hi])
    (fun i hi => by
      simp only [Nat.zero_add, hD1, hSAd, List.getElem?_map, Option.map_map, Function.comp_def])
    (by rw [hG1]; exact erase_globals hSA) hS1 (fun i => by rw [foldl_applyElem_memories])
    (startCodeV m.toV2)
  -- the configuration `$instantiate` returns
  have hinst : Silmaril.Wasm.V2.Execution.Instantiate v2Profile tgt before.toV2 m.toV2
      (imports.map ExternVal.toV2)
      ⟨SA, { module := mi }, Silmaril.Wasm.V2.Execution.expression
        (Silmaril.Wasm.V2.Execution.runElems m.toV2 ++
          Silmaril.Wasm.V2.Execution.runDatas m.toV2 ++
          (match m.toV2.start with | some x => [Silmaril.Wasm.V2.Instr.call x] | none => []))⟩ := by
    refine ⟨bounds.valid, ⟨by simpa [Module.toV2] using bounds.elemCount,
      by simpa [Module.toV2] using bounds.dataCount, ?_, ?_⟩, ?_⟩
    · intro d hd
      simp only [Module.toV2, List.mem_map] at hd
      obtain ⟨d', hd', rfl⟩ := hd
      exact bounds.data d' hd'
    · intro e he'
      simp only [Module.toV2, List.mem_map] at he'
      obtain ⟨e', he'', rfl⟩ := he'
      simpa [Elem.toV2] using bounds.elemSize e' he''
    refine ⟨inits.map Value.toV2, elems.map elemRefsV, SA, mi, ?_, ?_, hAM, rfl⟩
    · exact evalGlobals_v2 (tgt := tgt)
        (cf := Silmaril.Wasm.V2.Execution.Frame.initial before.toV2 m.toV2
          (imports.map ExternVal.toV2))
        (erase_globals (Store.erase_toV2 before))
        (externAddr_globals_toV2 imports) (mapM_forall₂ hin)
    · refine evalElems_v2 (tgt := tgt) (module := p.module)
        (cf := Silmaril.Wasm.V2.Execution.Frame.initial before.toV2 m.toV2
          (imports.map ExternVal.toV2)) ?_ he2
      rw [hmodeq]
      exact predInstV_funcs before m imports
  refine ⟨_, cs2, hinst, ?_, ?_, hmi, rfl, hwfP⟩
  · have e1 : Silmaril.Wasm.V2.Execution.expression
        (Silmaril.Wasm.V2.Execution.runElems m.toV2 ++
          Silmaril.Wasm.V2.Execution.runDatas m.toV2 ++
          (match m.toV2.start with
            | some x => [Silmaril.Wasm.V2.Instr.call x] | none => [])) =
        Silmaril.Wasm.V2.Execution.expression
          (((List.range' 0 m.elems.length).zip (m.elems.map Elem.toV2)).flatMap fun q =>
            Silmaril.Wasm.V2.Execution.runElem q.1 q.2) ++
        (Silmaril.Wasm.V2.Execution.expression
          (((List.range' 0 m.data.length).zip (m.data.map Data.toV2)).flatMap fun q =>
            Silmaril.Wasm.V2.Execution.runData q.1 q.2) ++ startCodeV m.toV2) := by
      simp only [Silmaril.Wasm.V2.Execution.runElems, Silmaril.Wasm.V2.Execution.runDatas,
        Module.toV2, List.length_map, List.range_eq_range',
        Silmaril.Wasm.V2.Execution.expression, List.map_append, List.append_assoc]
      refine congrArg₂ _ rfl (congrArg₂ _ rfl ?_)
      cases m.start <;> rfl
    show Silmaril.Wasm.V2.Execution.Steps v2Profile tgt
      ⟨SA, { module := mi }, _⟩ ⟨cs2, { module := mi }, _⟩
    rw [e1]
    exact h1.trans h2
  · rw [hS2, hst]

/-! ### 2.0 steps never change the frame's module -/

theorem v2Step_frame_module {tgt : VHostSemantics H} {c c' : VConfig H}
    (h : Silmaril.Wasm.V2.Execution.Step v2Profile tgt c c') :
    c'.frame.module = c.frame.module := by
  induction h with
  | ctxtInstrs _ _ ih => exact ih
  | ctxtLabel _ ih => exact ih
  | _ => rfl

theorem v2Steps_frame_module {tgt : VHostSemantics H} {c c' : VConfig H}
    (h : Silmaril.Wasm.V2.Execution.Steps v2Profile tgt c c') :
    c'.frame.module = c.frame.module := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [v2Step_frame_module hs, ih]

/-! ### The start call -/

/-- From the start code, one 2.0 `call` (if any) reaches a configuration
simulating the prepared Lime1 configuration. -/
theorem start_sim_v2 {tgt : VHostSemantics H} {before : Store H} {m : Module}
    {imports : List ExternVal} {p : Prepared H}
    (hp : prepare? before m imports = some p) (hwf : StoreWF p.store)
    {S : VStore H} {cf : VFrame}
    (hS : Store.erase S = p.store.toV2) (hF : ModuleInstSim p.module cf.module)
    (hl : cf.locals = []) :
    ∃ c₁, Silmaril.Wasm.V2.Execution.Steps v2Profile tgt ⟨S, cf, startCodeV m.toV2⟩ c₁ ∧
      c₁.frame = cf ∧ Sim (⟨p.store, ⟨[], p.module⟩, p.start⟩ : Config H) c₁ := by
  have hFe : Frame.erase cf = (⟨[], p.module⟩ : Frame).toV2 := by
    rcases cf with ⟨locals, mod⟩
    simp only at hl hF
    subst hl
    simp only [Frame.erase, Silmaril.Wasm.Execution.Runtime.Frame.toV2, List.map_nil]
    rw [show ModuleInst.erase mod = p.module.toV2 from hF]
  rcases prepare_start hp with ⟨hs, hps⟩ | ⟨i, a, hs, ha, hps⟩
  · refine ⟨⟨S, cf, []⟩, ?_, rfl, ?_, hwf⟩
    · simp only [startCodeV, Module.toV2, hs]
      exact Relation.ReflTransGen.refl
    · rw [Config.norm_eq_toV2_iff]
      exact ⟨hS, hFe, by simp [hps]⟩
  · have hmf : cf.module.funcAddr? i = some a.value := by
      show cf.module.funcs[i.toNat]? = some a.value
      have := congrArg (·.funcs) hF
      simp only [ModuleInst.erase, Silmaril.Wasm.Execution.Runtime.ModuleInst.toV2] at this
      rw [this, List.getElem?_map, ha]
      rfl
    refine ⟨⟨S, cf, [.callAddr a.value]⟩, ?_, rfl, ?_, hwf⟩
    · have hsc : startCodeV m.toV2 = [(.plain (.call i) : VAdmin)] := by
        simp [startCodeV, Module.toV2, hs]
      rw [hsc]
      exact Relation.ReflTransGen.single
        (Silmaril.Wasm.V2.Execution.Step.read
          (Silmaril.Wasm.V2.Execution.ReadStep.call hmf))
    · rw [Config.norm_eq_toV2_iff]
      exact ⟨hS, hFe, by simp [hps]⟩

end ToV2

/-- **Milestone.** Lime1 instantiation (preparation, segment initialisation and
the start function) is simulated by 2.0 instantiation followed by 2.0 execution
of the segment programs and the start call.

`c` is the configuration `$instantiate` returns, whose code is
`$runelem* $rundata* (CALL x)?`; `c'` is reached after running it. Lime1's
element and data instances are the ones 2.0 allocates and immediately drops, so
the store agreement is stated up to `ToV2.Store.erase`, and the module instance
agreement up to `ToV2.ModuleInstSim`. -/
theorem Instantiation.toV2 {src : HostSemantics H} {tgt : VHostSemantics H}
    (hosts : ToV2.HostCompatible src tgt) {before after : Store H} {m : Module}
    {imports : List ExternVal} {module : ModuleInst} {outcome : Result}
    (bounds : ToV2.InstantiationBounds before m imports)
    (h : Instantiation src before m imports after module outcome) :
    ∃ c c' : VConfig H,
      Silmaril.Wasm.V2.Execution.Instantiate v2Profile tgt before.toV2 m.toV2
        (imports.map ExternVal.toV2) c ∧
      Silmaril.Wasm.V2.Execution.Steps v2Profile tgt c c' ∧
      c'.code = outcome.toV2.toAdmin ∧
      ToV2.Store.erase c'.store = after.toV2 ∧
      ToV2.ModuleInstSim module c.frame.module ∧
      c'.frame.module = c.frame.module := by
  obtain ⟨hv, hi, p, hp, rfl, hrun⟩ := h
  obtain ⟨c, S, hinst, hsteps, hS, hF, hl, hwf⟩ := ToV2.prepare_v2 (tgt := tgt) bounds hv hp
  obtain ⟨c₁, hsteps₁, hc₁, hsim₁⟩ := ToV2.start_sim_v2 (tgt := tgt) hp hwf hS hF hl
  obtain ⟨c', hsteps', hsim'⟩ := Steps.toV2 hosts hrun hsim₁
  refine ⟨c, c', hinst, (hsteps.trans hsteps₁).trans hsteps', ToV2.Sim.result hsim' rfl, ?_,
    hF, ?_⟩
  · obtain ⟨hn, -⟩ := hsim'
    rcases c' with ⟨cs, cf, cl⟩
    exact (ToV2.Config.norm_eq_toV2_iff.mp hn).1
  · rw [ToV2.v2Steps_frame_module hsteps', hc₁]

/-- **Milestone.** A divergent Lime1 instantiation diverges in Wasm 2.0. -/
theorem InstantiationDiverges.toV2 {src : HostSemantics H} {tgt : VHostSemantics H}
    (hosts : ToV2.HostCompatible src tgt) {before : Store H} {m : Module}
    {imports : List ExternVal}
    (bounds : ToV2.InstantiationBounds before m imports)
    (h : InstantiationDiverges src before m imports) :
    Silmaril.Wasm.V2.Execution.InstantiateDiverges v2Profile tgt before.toV2 m.toV2
      (imports.map ExternVal.toV2) := by
  obtain ⟨hv, hi, p, hp, hdiv⟩ := h
  obtain ⟨c, S, hinst, hsteps, hS, hF, hl, hwf⟩ := ToV2.prepare_v2 (tgt := tgt) bounds hv hp
  obtain ⟨c₁, hsteps₁, -, hsim₁⟩ := ToV2.start_sim_v2 (tgt := tgt) hp hwf hS hF hl
  exact ⟨c, hinst, InfiniteTrace.of_steps (hsteps.trans hsteps₁)
    (Diverges.toV2 hosts hdiv hsim₁)⟩

/-! ## The commuting triangle `Lime1 → 2.0 → 3.0` -/

namespace ToV2

/-- The `2.0 → 3.0` runtime embedding, as a record of exactly the properties the
triangle needs.

The map itself now exists: `Silmaril/Wasm/V2/ToCore/Runtime.lean` defines the
simulation relation `V2.Execution.Sim` and `Silmaril/Wasm/V2/ToCore/Execution.lean`
proves `V2.Execution.Step.toCore`, so `rel` and `step` are instantiable by them.
The bridge is still a *hypothesis* here because the two remaining fields are
not: `image` and `faithful` compare the 2.0 image and the Core 3.0 image of one
and the same **Lime1** configuration, and neither direction is proved yet. Note
that `image` is **not** the equation
`V2.Config.toCore (Lime1.Config.toV2 a) = a.toCore`: `ToV2.Sim` and
`Lime1.Execution.Sim` both quotient their target by a normalisation (`ToV2.norm`
erases the `ELEMS`/`DATAS` components and a `globalinst`'s declared type), so
what is needed is the implication between the three `Sim`s, not an identity
between the three injections. -/
structure CoreBridge (H : Type) (tgtC : ToCore.CHostSemantics H)
    (tgtV : VHostSemantics H) where
  /-- The simulation relation of the `2.0 → 3.0` execution unit. -/
  rel : VConfig H → ToCore.CConfig H → Prop
  /-- 2.0 steps are simulated in Core 3.0. This is what transports the 2.0 run
  of `relation Step: config ~> config` (`8-reduction:5-8`, rules at
  `8-reduction:10-24`) along the third edge of the triangle. -/
  step : ∀ {d d' : VConfig H} {c : ToCore.CConfig H},
    Silmaril.Wasm.V2.Execution.Step v2Profile tgtV d d' → rel d c →
      ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step coreProfile tgtC) c c' ∧
        rel d' c'
  /-- The 2.0 image and the Core 3.0 image of one and the same Lime1
  configuration are related: the runtime counterpart of the syntactic
  `Lime1.Instr.toV2_toCore`, `Lime1.Expr.toV2_toCore` and
  `Lime1.Module.toV2_toCore`. -/
  image : ∀ {a : Config H} {d : VConfig H} {c : ToCore.CConfig H},
    Sim a d → Silmaril.Wasm.Lime1.Execution.Sim a c → rel d c
  /-- **Faithfulness**, the converse of `image`, and what gives the triangle its
  content. A Core 3.0 configuration that the bridge relates to the 2.0 image of
  a Lime1 configuration is itself a Core 3.0 image of that *same* Lime1
  configuration. Without it, the Core configuration reached by stepping *through*
  2.0 could be unrelated to the one the direct `Lime1.Execution.Step.toCore`
  reaches, and the triangle below would degenerate into the conjunction of
  `Step.toV2` and `Step.toCore`. -/
  faithful : ∀ {a : Config H} {d : VConfig H} {c : ToCore.CConfig H},
    rel d c → Sim a d → Silmaril.Wasm.Lime1.Execution.Sim a c

/-- The bridge's `rel` and `step` fields *are* a lock-step forward simulation
from 2.0 into Core 3.0. Lifting a run along the third edge of the triangle is
therefore `LockstepSim.plus` (nonempty runs, `Relation.TransGen`) or
`LockstepSim.steps` (`Steps/refl` and `Steps/trans`, `8-reduction:18-24`) at
this simulation. -/
theorem CoreBridge.sim {tgtC : ToCore.CHostSemantics H} {tgtV : VHostSemantics H}
    (B : CoreBridge H tgtC tgtV) :
    LockstepSim (Silmaril.Wasm.V2.Execution.Step v2Profile tgtV)
      (Silmaril.Wasm.Execution.Core.Step coreProfile tgtC) B.rel :=
  ⟨B.step⟩

end ToV2

/-- **The commuting triangle.** The Core 3.0 configuration reached *through*
2.0 simulates the same Lime1 configuration that the direct route reaches.

The Core run starts from an arbitrary `c` that the bridge relates to the 2.0
configuration `d` — not from the one the direct `Lime1 → 3.0` simulation
happens to supply — and it is produced by `B.step`, lifted over
`Relation.TransGen` by `LockstepSim.plus` at `ToV2.CoreBridge.sim`. That is what makes this the
*composite* `Lime1 → 2.0 → 3.0` route: `Sim b c'` holds because `B.faithful`
transports `ToV2.Sim b d'` across `B.rel d' c'`, not because `c'` was obtained
from `Step.toCore`.

`Step.toV2_toCore_of_sim` below is the special case `c` = the configuration the
direct route starts from, obtained by discharging `hrel` with `B.image`. -/
theorem Step.toV2_toCore {src : HostSemantics H} {tgtC : ToCore.CHostSemantics H}
    {tgtV : VHostSemantics H} (B : ToV2.CoreBridge H tgtC tgtV)
    (hostsV : ToV2.HostCompatible src tgtV)
    {a b : Config H} {d : VConfig H} {c : ToCore.CConfig H}
    (h : Step src a b) (hd : ToV2.Sim a d) (hrel : B.rel d c) :
    ∃ (d' : VConfig H) (c' : ToCore.CConfig H),
      Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgtV) d d' ∧
      ToV2.Sim b d' ∧
      Relation.TransGen (Silmaril.Wasm.Execution.Core.Step coreProfile tgtC) c c' ∧
      Sim b c' ∧ B.rel d' c' := by
  obtain ⟨d', hdd, hbd⟩ := Step.toV2 hostsV h hd
  obtain ⟨c', hcc, hrel'⟩ := B.sim.plus hdd hrel
  exact ⟨d', c', hdd, hbd, hcc, B.faithful hrel' hbd, hrel'⟩

/-- The triangle in the form in which the *direct* route supplies its Core
starting point: `B.image` turns `Sim a c` into `B.rel d c`. This is the exact
statement the old, bridge-free formulation made, and it is now a corollary. -/
theorem Step.toV2_toCore_of_sim {src : HostSemantics H} {tgtC : ToCore.CHostSemantics H}
    {tgtV : VHostSemantics H} (B : ToV2.CoreBridge H tgtC tgtV)
    (hostsV : ToV2.HostCompatible src tgtV)
    {a b : Config H} {d : VConfig H} {c : ToCore.CConfig H}
    (h : Step src a b) (hd : ToV2.Sim a d) (hc : Sim a c) :
    ∃ (d' : VConfig H) (c' : ToCore.CConfig H),
      Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgtV) d d' ∧
      ToV2.Sim b d' ∧
      Relation.TransGen (Silmaril.Wasm.Execution.Core.Step coreProfile tgtC) c c' ∧
      Sim b c' ∧ B.rel d' c' :=
  Step.toV2_toCore B hostsV h hd (B.image hd hc)

/-- The finite-run form of the triangle, over `Steps` (`8-reduction:8`, rules
`Steps/refl` and `Steps/trans` at `8-reduction:18-24`). The Core run is again
the bridge's, by `LockstepSim.steps` at `ToV2.CoreBridge.sim`. -/
theorem Steps.toV2_toCore {src : HostSemantics H} {tgtC : ToCore.CHostSemantics H}
    {tgtV : VHostSemantics H} (B : ToV2.CoreBridge H tgtC tgtV)
    (hostsV : ToV2.HostCompatible src tgtV)
    {a b : Config H} {d : VConfig H} {c : ToCore.CConfig H}
    (h : Steps src a b) (hd : ToV2.Sim a d) (hrel : B.rel d c) :
    ∃ (d' : VConfig H) (c' : ToCore.CConfig H),
      Silmaril.Wasm.V2.Execution.Steps v2Profile tgtV d d' ∧ ToV2.Sim b d' ∧
      Silmaril.Wasm.Execution.Core.Steps coreProfile tgtC c c' ∧ Sim b c' ∧ B.rel d' c' := by
  obtain ⟨d', hdd, hbd⟩ := Steps.toV2 hostsV h hd
  obtain ⟨c', hcc, hrel'⟩ := B.sim.steps hdd hrel
  exact ⟨d', c', hdd, hbd, hcc, B.faithful hrel' hbd, hrel'⟩

/-- The finite-run triangle from the direct route's Core starting point. -/
theorem Steps.toV2_toCore_of_sim {src : HostSemantics H} {tgtC : ToCore.CHostSemantics H}
    {tgtV : VHostSemantics H} (B : ToV2.CoreBridge H tgtC tgtV)
    (hostsV : ToV2.HostCompatible src tgtV)
    {a b : Config H} {d : VConfig H} {c : ToCore.CConfig H}
    (h : Steps src a b) (hd : ToV2.Sim a d) (hc : Sim a c) :
    ∃ (d' : VConfig H) (c' : ToCore.CConfig H),
      Silmaril.Wasm.V2.Execution.Steps v2Profile tgtV d d' ∧ ToV2.Sim b d' ∧
      Silmaril.Wasm.Execution.Core.Steps coreProfile tgtC c c' ∧ Sim b c' ∧ B.rel d' c' :=
  Steps.toV2_toCore B hostsV h hd (B.image hd hc)

end Silmaril.Wasm.Lime1.Execution

namespace Silmaril.Wasm.V1.Execution

/-! # Wasm 1.0 execution is simulated by WebAssembly 2.0 execution

The 1.0 results are the Lime1 ones composed with the lock-step 1.0 → Lime1
simulation of `Silmaril/Wasm/Lime1/Execution/FromV1.lean`. The host semantics is
transported canonically by `Runtime.HostSemantics.mapCode Func.toLime`, so no
host premise beyond 2.0 compatibility of the transported host is needed. -/

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Lime1.Execution (v2Profile)
open Silmaril.Wasm.Lime1.Execution.ToV2 (VConfig VHostSemantics Sim HostCompatible
  ModuleInstSim InstantiationBounds)

variable {H : Type}

/-- A Wasm 1.0 configuration as a Wasm 2.0 configuration, through Lime1. -/
def Config.toV2 (c : Config H) : VConfig H := c.toLime.toV2

@[simp] theorem Config.toLime_toV2 (c : Config H) :
    Silmaril.Wasm.Execution.Runtime.Config.toV2 c.toLime = c.toV2 := rfl

/-- **Milestone.** One Wasm 1.0 step is simulated by at least one 2.0 step. -/
theorem Step.toV2 {src : HostSemantics H} {tgt : VHostSemantics H}
    (hosts : HostCompatible (src.mapCode Func.toLime) tgt)
    {a b : Config H} {c : VConfig H}
    (h : Step src a b) (hs : Sim a.toLime c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.V2.Execution.Step v2Profile tgt) c c' ∧
      Sim b.toLime c' :=
  Silmaril.Wasm.Lime1.Execution.Step.toV2 hosts h.toLime_mapHost hs

/-- **Milestone.** Finite Wasm 1.0 runs are simulated. -/
theorem Steps.toV2 {src : HostSemantics H} {tgt : VHostSemantics H}
    (hosts : HostCompatible (src.mapCode Func.toLime) tgt)
    {a b : Config H} {c : VConfig H}
    (h : Steps src a b) (hs : Sim a.toLime c) :
    ∃ c', Silmaril.Wasm.V2.Execution.Steps v2Profile tgt c c' ∧ Sim b.toLime c' :=
  Silmaril.Wasm.Lime1.Execution.Steps.toV2 hosts
    (h.toLime (Runtime.HostSemantics.compatible_mapCode _ _)) hs

/-- **Milestone.** Wasm 1.0 divergence is preserved. -/
theorem Diverges.toV2 {src : HostSemantics H} {tgt : VHostSemantics H}
    (hosts : HostCompatible (src.mapCode Func.toLime) tgt)
    {a : Config H} {c : VConfig H}
    (h : Diverges src a) (hs : Sim a.toLime c) :
    Silmaril.Wasm.V2.Execution.Diverges v2Profile tgt c :=
  Silmaril.Wasm.Lime1.Execution.Diverges.toV2 hosts
    (h.toLime (Runtime.HostSemantics.compatible_mapCode _ _)) hs

/-- **Milestone.** Wasm 1.0 instantiation is simulated by 2.0 instantiation
followed by 2.0 execution. The side conditions are the Lime1 ones at the
transported module; `V1 ⊆ Lime1` adds none of its own. -/
theorem Instantiation.toV2 {src : HostSemantics H} {tgt : VHostSemantics H}
    (hosts : HostCompatible (src.mapCode Func.toLime) tgt)
    {before after : Store H} {m : Module} {imports : List ExternVal}
    {module : ModuleInst} {outcome : Result}
    (bounds : InstantiationBounds (before.mapCode Func.toLime) m.toLime imports)
    (h : Instantiation src before m imports after module outcome) :
    ∃ c c' : VConfig H,
      Silmaril.Wasm.V2.Execution.Instantiate v2Profile tgt
        (before.mapCode Func.toLime).toV2 m.toV2 (imports.map ExternVal.toV2) c ∧
      Silmaril.Wasm.V2.Execution.Steps v2Profile tgt c c' ∧
      c'.code = outcome.toV2.toAdmin ∧
      Silmaril.Wasm.Lime1.Execution.ToV2.Store.erase c'.store = (after.mapCode Func.toLime).toV2 ∧
      ModuleInstSim module c.frame.module ∧
      c'.frame.module = c.frame.module :=
  Silmaril.Wasm.Lime1.Execution.Instantiation.toV2 hosts bounds
    (h.toLime (Runtime.HostSemantics.compatible_mapCode _ _))

/-- **Milestone.** A divergent Wasm 1.0 instantiation diverges in Wasm 2.0. -/
theorem InstantiationDiverges.toV2 {src : HostSemantics H} {tgt : VHostSemantics H}
    (hosts : HostCompatible (src.mapCode Func.toLime) tgt)
    {before : Store H} {m : Module} {imports : List ExternVal}
    (bounds : InstantiationBounds (before.mapCode Func.toLime) m.toLime imports)
    (h : InstantiationDiverges src before m imports) :
    Silmaril.Wasm.V2.Execution.InstantiateDiverges v2Profile tgt
      (before.mapCode Func.toLime).toV2 m.toV2 (imports.map ExternVal.toV2) :=
  Silmaril.Wasm.Lime1.Execution.InstantiationDiverges.toV2 hosts bounds
    (instantiationDiverges_toLime (Runtime.HostSemantics.compatible_mapCode _ _) h)

end Silmaril.Wasm.V1.Execution
