module

public import Silmaril.Raw.Wasm.Versions.Foundations.ListExt
public import Silmaril.Wasm.V2.Execution.Step
public import Silmaril.Wasm.V2.ToCore
public import Silmaril.Wasm.Execution.Core.Soundness

@[expose] public section

/-! # Wasm 2.0 runtime objects as Core 3.0 runtime objects

The runtime half of the `2.0 ⊆ 3.0` subset theorem, the exact analogue of
`Silmaril/Wasm/Lime1/ToCore/Runtime.lean`. `Silmaril/Wasm/V2/ToCore/*` injects
the 2.0 *syntax* into the Core 3.0 syntax; this file injects the 2.0 *runtime*
of `Silmaril.Wasm.V2.Execution` (`4-runtime`, `5-runtime-aux`, `8-reduction`)
into the Core 3.0 runtime of `Silmaril.Wasm.Execution.Core`:

```
Val.toCore Ref.toCore ExternAddr.toCore ModuleInst.toCore Frame.toCore
FuncInst.toCore TableInst.toCore MemInst.toCore GlobalInst.toCore
ElemInst.toCore DataInst.toCore Store.toCore Admin.toCore Admin.listToCore
Config.toCore Result.toCore
```

together with the normalisation `ToCore.Config.norm`, the well-formedness
predicate `ConfigWF` and the simulation relation `Sim`.

Line references of the form `4-runtime:NN`, `5-runtime-aux:NN` and
`8-reduction:NN` point into `specification/wasm-2.0/*.spectec` at
WebAssembly/spec revision `608711107b7f1edb13efd57b7d79b49477462d36`
(hash-pinned in `specs/wasm/core-2.0.json`).

## Everything is `Option`-valued, for one reason

`V2.Instr.toCore` is partial — 2.0's `CVTOP numtype_1 numtype_2 cvtop`
(`1-syntax:437`) is *untyped*, and 111 of its 144 immediate triples denote no
Core 3.0 `ConvertOp`; see the module docstring of `ToCore/Instructions.lean`.
Function bodies therefore only sometimes convert, so `FuncInst.toCore`,
`Store.toCore`, `Admin.toCore` and `Config.toCore` are `Option`-valued, exactly
as `Func.toCore` and `Module.toCore` are in `ToCore/Modules.lean`. No real
module is affected: neither `A-binary` nor the reference interpreter's typed
`Ast.cvtop` can express an undefined triple.

## Three places where the two runtimes genuinely differ

**`CALL_ADDR a` (`4-runtime:132`).** Core 3.0 deleted this administrative form:
`Step_read/call` produces `(REF.FUNC_ADDR a) (CALL_REF dt)` where `dt` is the
callee's *defined* type, read from the store
(`Silmaril/Wasm/Execution/Core/Step.lean:220`). `Admin.toCore` therefore maps
`CALL_ADDR a` to `[.ref (.func a), .callRefType (s.funcDefType a)]`, where
`Store.funcDefType` reads `s.FUNCS[a].TYPE` and injects it with
`V2.FuncType.toDefType`. This is the same trick `Lime1.Admin.toCore` plays for
`.invoke`, and it is sound because a function instance's type never changes.

**`REF.NULL reftype` (`4-runtime:41`, `1-syntax:476`).** This is the one 2.0
*value* whose Core 3.0 counterpart is not the image of the corresponding
instruction. In 2.0, `REF.NULL rt` is a value: `Val.toAdmin` sends
`.ref (.null rt)` to the *source* instruction `REF.NULL rt`, and there is no
reduction rule for it. In Core 3.0, null references are untyped
(`Ref.null = REF.NULL_ADDR`) and `REF.NULL ht` is a genuine instruction that
takes one `Step_read/ref.null` to become the value `REF.NULL_ADDR`
(`Silmaril/Wasm/Execution/Core/Step/Reference.lean:26`). We put the discrepancy
in the *image*: `ToCore.plainOrNull` sends the Core instruction `REF.NULL ht` to
the Core value `.ref .null`, so `Val.toCore` and `Val.toAdmin` commute
(`values_toCore`) and a 2.0 configuration maps to the Core configuration *after*
all its `ref.null`s have been reduced. The matching `ToCore.Admin.norm` case
collapses `REF.NULL ht` to `REF.NULL_ADDR`, so a Core configuration that is up
to one `ref.null` step behind is still related. Taking the other option — map
`REF.NULL rt` to the Core instruction — would only move the same one-step gap
from `norm` into every values-inversion lemma, and would make `values_toCore`
false.

**`REF.HOST_ADDR a` (`4-runtime:131`).** A 2.0 host address has type `EXTERNREF`
(`6-typing`, `Ref_ok/host`), and Core 3.0 reaches `externref` only through
`REF.EXTERN`: `Ref_ok/host` gives `(ref any)` and `Ref_ok/extern` lifts it to
`(ref extern)` (`Silmaril/Wasm/Execution/Core/Values.lean:43-47`). So
`Ref.toCore (.hostAddr a) = .extern (.host a)`. No 2.0 instruction creates or
inspects a host address, so the choice is only observable through the embedder.

## What `Store.erase`/`Frame.erase` erase, and what they do not

Unlike Lime1, Wasm 2.0 *has* element and data segments, typed globals and typed
tables and memories, so none of Lime1's erasures is needed here: a 2.0 store maps
onto a Core store field for field. What a Core store can carry and a 2.0 store
cannot is exactly what Core 3.0 added: tags, struct instances, array instances
and exception instances. `ToCore.Store.erase` drops those four (and the `tags`
of every function instance's module), `ToCore.ModuleInst.erase` drops a module
instance's tags and `ToCore.Frame.erase` applies it to a frame's module. On the
image of `Store.toCore` all of these are the identity (`Store.erase_toCore`); they
matter only because a Core *host function* is free to allocate GC or exception
objects that 2.0 code can never observe, and `HostCompatible` must not forbid
that.

## `Rigid`: still needed, and slightly different

`ToCore.Admin.norm` is not injective, so inverting `Admin.norm m x = y` needs to
know that `y` is not in the image of a collapsing case; that is `ToCore.Rigid`,
exactly as in Lime1. 2.0 needs it for the same reason, but the predicate is not
Lime1's:

* 2.0 has **no tail calls**, so `RETURN_CALL_REF` never occurs in a 2.0 image and
  `Admin.norm` leaves `.plain (.returnCallRef _)` and `.returnCallRefType _`
  alone. Lime1's two `returnCall*` cases are dropped.
* 2.0 **does** have typed nulls, so (see above) `.ref .null` is *not* rigid: it
  is the normal form of `.plain (.refNull ht)`. `Rigid.val` consequently holds
  only for values other than the null reference, and the inversion lemma for the
  null case is `ToCore.norm_eq_null`, which returns the two possibilities.

So the machinery is kept, with `Rigid` weakened on `.ref .null` and strengthened
(in the sense of having fewer cases) by the absence of tail calls. Replacing it
by a `Config.norm`-free relation was considered and rejected: Core 3.0's
`call_indirect` provably produces an index-annotated `CALL_REF y`
(`Core/Step.lean:271-273`) where 2.0 produces `CALL_ADDR a`, so *some*
normalisation of the annotation is unavoidable, and once `norm` exists the
inversion lemmas need `Rigid`.

**Note.** `ConfigWF` is not a transcription of anything in SpecTec; it is the
set of side conditions under which the Core machine can follow the 2.0 machine,
in the style of `Lime1.Execution.ConfigWF`. It asks that (i) every function
address named by a module instance, and every `CALL_ADDR`, is allocated —
2.0's `Step_read/call` (`8-reduction:119`) does *not* look up the store, while
Core 3.0's does, and `Store.funcDefType` needs the lookup to be the right one;
(ii) every memory fits the 32-bit address space *and* holds a whole number of
pages, and every table has fewer than `2^32` entries — the size bounds are what
make Core 3.0's wrapping 32-bit `memory.fill`/`memory.copy`/`table.fill`/
`table.copy` iterations agree with 2.0's, and the page-alignment clause is what
turns `$growmemory`'s bound on *pages* into `StoreWF`'s bound on *bytes* (see
`StoreWF` below, and its use in `Step.toCore`). All three are invariants of 2.0
execution: `$allocmem` and `$growmemory` only ever produce whole pages
(`9-module:67-69`, `5-runtime-aux:126-131`), `$growmemory` caps a memory at
`2^16` pages and `$growtable` at `2^32 - 1` entries (`5-runtime-aux:119-131`).

**Note.** No new SpecTec 2.0 errata were found while writing this file; all the
choices above are modelling choices forced by Core 3.0's syntax, each documented
in the paragraph above.
-/

namespace Silmaril.Wasm.V2.Execution

open Silmaril.Wasm.Validation (DefType CGlobalType CTableType)

namespace ToCore

abbrev CVal := Silmaril.Wasm.Execution.Core.Val
abbrev CRef := Silmaril.Wasm.Execution.Core.Ref
abbrev CAdmin := Silmaril.Wasm.Execution.Core.Admin
abbrev CModuleInst := Silmaril.Wasm.Execution.Core.ModuleInst
abbrev CFrame := Silmaril.Wasm.Execution.Core.Frame
abbrev CExternAddr := Silmaril.Wasm.Execution.Core.ExternAddr
abbrev CFuncInst (H : Type) := Silmaril.Wasm.Execution.Core.FuncInst H
abbrev CTableInst := Silmaril.Wasm.Execution.Core.TableInst
abbrev CMemInst := Silmaril.Wasm.Execution.Core.MemInst
abbrev CGlobalInst := Silmaril.Wasm.Execution.Core.GlobalInst
abbrev CElemInst := Silmaril.Wasm.Execution.Core.ElemInst
abbrev CDataInst := Silmaril.Wasm.Execution.Core.DataInst
abbrev CStore (H : Type) := Silmaril.Wasm.Execution.Core.Store H
abbrev CConfig (H : Type) := Silmaril.Wasm.Execution.Core.Config H
abbrev CResult := Silmaril.Wasm.Execution.Core.Result
abbrev CHostOutcome (H : Type) := Silmaril.Wasm.Execution.Core.HostOutcome H
abbrev CHostSemantics (H : Type) := Silmaril.Wasm.Execution.Core.HostSemantics H

/-- The closed Core 3.0 global type of a 2.0 `globaltype` (`1-syntax:167`).
This is `Silmaril.Wasm.V2.Validation.globalToC` of `ToCore/Validation.lean`,
repeated here so that the runtime embedding does not depend on the validation
embedding. -/
def globalToC (t : GlobalType) : CGlobalType := ⟨t.mutability, t.value.toC⟩

/-- The closed Core 3.0 table type of a 2.0 `tabletype` (`1-syntax:171`); the
address type of every 2.0 table is `I32`. This is
`Silmaril.Wasm.V2.Validation.tableToC` of `ToCore/Validation.lean`. -/
def tableToC (t : TableType) : CTableType := ⟨.i32, t.limits.toCore, t.element.toC⟩

/-- A Core 3.0 *source* instruction occurring in the image of 2.0 code, as a
Core administrative instruction. The only interesting case is `REF.NULL ht`,
which is a *value* on the 2.0 side (`4-runtime:41`) and therefore maps to the
Core value `REF.NULL_ADDR` rather than to the instruction; see the module
docstring. -/
def plainOrNull : Wasm.Instr → CAdmin
  | .refNull _ => .ref .null
  | c => .plain c

end ToCore

open ToCore

/-! ## Values, references and addresses (`4-runtime:25-51`) -/

/-- `ref ::= REF.NULL reftype | REF.FUNC_ADDR funcaddr | REF.HOST_ADDR hostaddr`
(`4-runtime:41`). Core 3.0 nulls are untyped and host references reach
`externref` only through `REF.EXTERN`; see the module docstring. -/
def Ref.toCore : Ref → CRef
  | .null _ => .null
  | .funcAddr a => .func a
  | .hostAddr a => .extern (.host a)

/-- `val ::= num | vec | ref` (`4-runtime:43`). -/
def Val.toCore : Val → CVal
  | .num v => .num ⟨v.type, v.bits⟩
  | .vec b => .vec b
  | .ref r => .ref r.toCore

/-- `externaddr ::= FUNC _ | GLOBAL _ | TABLE _ | MEM _` (`4-runtime:25`); Core
3.0 additionally has `TAG`, which 2.0 has not. -/
def ExternAddr.toCore : ExternAddr → CExternAddr
  | .func a => .func a
  | .global a => .global a
  | .table a => .table a
  | .mem a => .mem a

/-- `exportinst ::= { NAME name, ADDR externaddr }` (`4-runtime:78`). -/
def ExportInst.toCore (e : ExportInst) : Silmaril.Wasm.Execution.Core.ExportInst :=
  ⟨e.name, e.addr.toCore⟩

/-! ## Instances (`4-runtime:60-99`) -/

/-- `moduleinst` (`4-runtime:82`). Each 2.0 `functype` becomes one singleton
recursive group, so type indices do not shift (`ToCore/Types.lean`); Core 3.0's
`TAGS` component is empty. -/
def ModuleInst.toCore (m : ModuleInst) : CModuleInst where
  types := m.types.map FuncType.toDefType
  tags := []
  globals := m.globals
  mems := m.mems
  tables := m.tables
  funcs := m.funcs
  datas := m.datas
  elems := m.elems
  exports := m.exports.map ExportInst.toCore

/-- `frame ::= { LOCALS val*, MODULE moduleinst }` (`4-runtime:112`). Every 2.0
local is defaultable, so every Core local slot is set. -/
def Frame.toCore (f : Frame) : CFrame := ⟨f.locals.map (some ∘ Val.toCore), f.module.toCore⟩

variable {H : Type}

/-- `funcinst ::= { TYPE functype, MODULE moduleinst, CODE func }`
(`4-runtime:60`), with the host extension of `Execution/Basic.lean`. Partial,
because the body is (`ToCore/Instructions.lean`). -/
def FuncInst.toCore (fi : FuncInst H) : Option (CFuncInst H) :=
  match fi.code with
  | .wasm fn => (Func.toCore fn).map fun c => ⟨fi.type.toDefType, fi.module.toCore, .wasm c⟩
  | .host h => some ⟨fi.type.toDefType, fi.module.toCore, .host h⟩

/-- `tableinst ::= { TYPE tabletype, REFS ref* }` (`4-runtime:67`). The Core
table type is `ToCore.tableToC`, the same closed type the validation embedding
uses. -/
def TableInst.toCore (ti : TableInst) : CTableInst :=
  ⟨ToCore.tableToC ti.type, ti.refs.map Ref.toCore⟩

/-- `meminst ::= { TYPE memtype, BYTES byte* }` (`4-runtime:70`). -/
def MemInst.toCore (mi : MemInst) : CMemInst := ⟨mi.type.toCore, mi.bytes⟩

/-- `globalinst ::= { TYPE globaltype, VALUE val }` (`4-runtime:64`). -/
def GlobalInst.toCore (gi : GlobalInst) : CGlobalInst :=
  ⟨ToCore.globalToC gi.type, gi.value.toCore⟩

/-- `eleminst ::= { TYPE elemtype, REFS ref* }` (`4-runtime:73`). -/
def ElemInst.toCore (ei : ElemInst) : CElemInst := ⟨ei.type.toC, ei.refs.map Ref.toCore⟩

/-- `datainst ::= { BYTES byte* }` (`4-runtime:76`). -/
def DataInst.toCore (di : DataInst) : CDataInst := ⟨di.bytes⟩

/-- `store` (`4-runtime:104`). Core 3.0's `TAGS`, `STRUCTS`, `ARRAYS` and `EXNS`
are empty: Wasm 2.0 has neither exceptions nor garbage-collected objects. -/
def Store.toCore (s : Store H) : Option (CStore H) :=
  (s.funcs.mapM FuncInst.toCore).map fun fs =>
    { tags := []
      globals := s.globals.map GlobalInst.toCore
      mems := s.mems.map MemInst.toCore
      tables := s.tables.map TableInst.toCore
      funcs := fs
      datas := s.datas.map DataInst.toCore
      elems := s.elems.map ElemInst.toCore
      structs := []
      arrays := []
      exns := [] }

/-- The defined type of the function at address `a` (`default` if unallocated).
This is the annotation Core 3.0's `Step_read/call` puts on its `CALL_REF`. -/
def Store.funcDefType (s : Store H) (a : FuncAddr) : DefType :=
  ((s.funcs[a]?).map fun fi => fi.type.toDefType).getD default

/-! ## Administrative instructions and configurations (`4-runtime:117-135`) -/

mutual

/-- `admininstr` (`4-runtime:128`) as Core 3.0 administrative code. A single 2.0
instruction can need two Core instructions (`CALL_ADDR`), so the result is a
list. -/
def Admin.toCore (s : Store H) : Admin → Option (List CAdmin)
  | .plain i => (Instr.toCore i).map fun c => [ToCore.plainOrNull c]
  | .refFuncAddr a => some [.ref (.func a)]
  | .refHostAddr a => some [.ref (.extern (.host a))]
  | .callAddr a => some [.ref (.func a), .callRefType (s.funcDefType a)]
  | .label n cont body =>
      (Expr.toCore cont).bind fun c =>
        (Admin.listToCore s body).map fun b => [.label n c b]
  | .frame n f body => (Admin.listToCore s body).map fun b => [.frame n f.toCore b]
  | .trap => some [.trap]

/-- `admininstr*` (`4-runtime:128`), concatenated. -/
def Admin.listToCore (s : Store H) : List Admin → Option (List CAdmin)
  | [] => some []
  | a :: as => (Admin.toCore s a).bind fun x => (Admin.listToCore s as).map fun y => x ++ y

end

/-- `config ::= state; admininstr*` (`4-runtime:117`). -/
def Config.toCore (c : Config H) : Option (CConfig H) :=
  (c.store.toCore).bind fun s =>
    (Admin.listToCore c.store c.code).map fun code => ⟨s, c.frame.toCore, code⟩

/-- `result ::= _VALS val* | TRAP` (`4-runtime:46`); Core 3.0's third
alternative, an escaping exception, is outside the 2.0 image. -/
def Result.toCore : Result → CResult
  | .values vs => .values (vs.map Val.toCore)
  | .trap => .trap

/-! ## Normalisation -/

namespace ToCore

/-- Core 3.0 module instances carry a `TAGS` component that Wasm 2.0 has not. -/
def ModuleInst.erase (m : CModuleInst) : CModuleInst := { m with tags := [] }

/-- `ModuleInst.erase` on a frame's module. -/
def Frame.erase (f : CFrame) : CFrame := { f with module := ModuleInst.erase f.module }

/-- Drop everything a Core 3.0 store can hold and a Wasm 2.0 store cannot: tags,
struct, array and exception instances. -/
def Store.erase (s : CStore H) : CStore H :=
  { s with tags := [], structs := [], arrays := [], exns := [],
           funcs := s.funcs.map fun fi => { fi with module := ModuleInst.erase fi.module } }

/-- Normalise a Core 3.0 *source* instruction occurring as administrative code
in a module whose types are `m.types`: an index-annotated `CALL_REF y`, as
produced by Core 3.0's `call_indirect`, is resolved to the defined type that
2.0's `CALL_ADDR` carries, and `REF.NULL ht` is reduced to the value it denotes.
2.0 has no tail calls, so `RETURN_CALL_REF` is left alone. -/
def normPlain (m : CModuleInst) : Wasm.Instr → CAdmin
  | .callRef x => .callRefType ((m.types[x.toNat]?).getD default)
  | .refNull _ => .ref .null
  | c => .plain c

mutual

/-- Resolve `CALL_REF` annotations and `REF.NULL` values against module `m`. -/
def Admin.norm (m : CModuleInst) : CAdmin → CAdmin
  | .plain i => normPlain m i
  | .label n cont body => .label n cont (Admin.normList m body)
  | .handler n cs body => .handler n cs (Admin.normList m body)
  | .frame n f body => .frame n (Frame.erase f) (Admin.normList f.module body)
  | a => a

/-- `Admin.norm`, pointwise. -/
def Admin.normList (m : CModuleInst) : List CAdmin → List CAdmin
  | [] => []
  | a :: as => Admin.norm m a :: Admin.normList m as

end

/-- The normal form of a Core 3.0 configuration. -/
def Config.norm (c : CConfig H) : CConfig H :=
  ⟨Store.erase c.store, Frame.erase c.frame, Admin.normList c.frame.module c.code⟩

/-- Module-instance similarity: the Core instance additionally records (empty)
tag addresses. -/
def ModuleInstSim (mV : Silmaril.Wasm.V2.Execution.ModuleInst) (mC : CModuleInst) : Prop :=
  ModuleInst.erase mC = mV.toCore

end ToCore

/-! ## Well-formedness of 2.0 configurations

See the module docstring: these are the side conditions under which the Core 3.0
machine can follow the 2.0 machine. -/

/-- Function addresses of a module instance are allocated. -/
def ModWF (s : Store H) (m : ModuleInst) : Prop := ∀ a ∈ m.funcs, a < s.funcs.length

mutual

/-- `CALL_ADDR` names an allocated function; frames have well-formed modules. -/
def Admin.WF (s : Store H) : Admin → Prop
  | .plain _ => True
  | .refFuncAddr _ => True
  | .refHostAddr _ => True
  | .callAddr a => a < s.funcs.length
  | .label _ _ body => Admin.listWF s body
  | .frame _ f body => ModWF s f.module ∧ Admin.listWF s body
  | .trap => True

/-- `Admin.WF`, pointwise. -/
def Admin.listWF (s : Store H) : List Admin → Prop
  | [] => True
  | a :: as => Admin.WF s a ∧ Admin.listWF s as

end

/-- Store well-formedness: every function instance's module is well formed,
every memory fits the 32-bit address space and is a whole number of pages, and
every table has fewer than `2^32` entries.

The page-alignment clause is an invariant of the 2.0 semantics, not a
restriction: `$allocmem` allocates `0^(i * 64 * $Ki)` bytes (`9-module:67-69`) and
`$growmemory` appends `0^(n * 64 * $Ki)` (`5-runtime-aux:131`), so every
reachable memory instance satisfies it. It is needed because `$growmemory`'s
bound is on *pages* while `StoreWF`'s is on *bytes*: without it,
`|b*| / (64 * $Ki) + n <= 2^16` does not imply `|b*| + n * 64 * $Ki <= 2^32`,
and the Core 3.0 image of a grown memory could exceed the 32-bit address space. -/
def StoreWF (s : Store H) : Prop :=
  (∀ (i : Nat) (fi : FuncInst H), s.funcs[i]? = some fi → ModWF s fi.module) ∧
  (∀ (i : Nat) (mi : MemInst), s.mems[i]? = some mi → mi.bytes.size ≤ 2 ^ 32) ∧
  (∀ (i : Nat) (mi : MemInst), s.mems[i]? = some mi →
    mi.bytes.size % Silmaril.Wasm.Execution.Memory.pageSize = 0) ∧
  (∀ (i : Nat) (ti : TableInst), s.tables[i]? = some ti → ti.refs.length < 2 ^ 32)

/-- Configuration well-formedness. -/
def ConfigWF (c : Config H) : Prop :=
  StoreWF c.store ∧ ModWF c.store c.frame.module ∧ Admin.listWF c.store c.code

/-- Store extension as far as functions are concerned: allocated functions stay
allocated with the same type, so `Store.funcDefType` is stable. -/
def StoreExt (s s' : Store H) : Prop := ListExt FuncInst.type s.funcs s'.funcs

/-- Host calls preserve store well-formedness and extend the store. The shared
`Silmaril.Wasm.Execution.Host.Preserves` with 2.0's invariants. -/
def HostPreserves (src : HostSemantics H) : Prop :=
  Silmaril.Wasm.Execution.Host.Preserves StoreWF (fun s s' => StoreWF s' ∧ StoreExt s s') src

/-! ## The simulation relation -/

/-- The simulation relation between 2.0 and Core 3.0 configurations: the
normalised Core configuration is the image of a well-formed 2.0 configuration.
`Config.toCore` is `Option`-valued, so this also says that the 2.0 configuration
has an image at all. -/
def Sim (a : Config H) (c : CConfig H) : Prop :=
  a.toCore = some (ToCore.Config.norm c) ∧ ConfigWF a

/-- Host outcomes correspond. A Core host function may allocate tags, structs,
arrays or exceptions, which `ToCore.Store.erase` drops; it may not return a
value that Wasm 2.0 cannot express, which `rC = r.toCore` forbids. The shared
`Silmaril.Wasm.Execution.Host.Outcome.Sim`. -/
def HostOutcomeSim : HostOutcome H → CHostOutcome H → Prop :=
  Silmaril.Wasm.Execution.Host.Outcome.Sim
    (fun s sC => s.toCore = some (ToCore.Store.erase sC)) Result.toCore

/-- Host compatibility: every 2.0 host behaviour is matched by the Core 3.0 host
on a related store. The shared `Silmaril.Wasm.Execution.Host.Compatible`. -/
def HostCompatible (src : HostSemantics H) (tgt : CHostSemantics H) : Prop :=
  Silmaril.Wasm.Execution.Host.Compatible StoreWF (fun s s' => StoreWF s' ∧ StoreExt s s')
    (fun s sC => s.toCore = some (ToCore.Store.erase sC)) Val.toCore HostOutcomeSim src tgt

/-! ## Commuting lemmas (the `simp` battery for the simulation proofs) -/

@[simp] theorem Admin.listToCore_nil (s : Store H) : Admin.listToCore s [] = some [] := by
  simp [Admin.listToCore]

@[simp] theorem Admin.listToCore_cons (s : Store H) (a : Admin) (as : List Admin) :
    Admin.listToCore s (a :: as) =
      (Admin.toCore s a).bind fun x => (Admin.listToCore s as).map fun y => x ++ y := by
  simp [Admin.listToCore]

@[simp] theorem Admin.plain_toCore (s : Store H) (i : Instr) :
    Admin.toCore s (.plain i) = (Instr.toCore i).map fun c => [ToCore.plainOrNull c] := by
  simp [Admin.toCore]

@[simp] theorem Admin.refFuncAddr_toCore (s : Store H) (a : FuncAddr) :
    Admin.toCore s (.refFuncAddr a) = some [.ref (.func a)] := by simp [Admin.toCore]

@[simp] theorem Admin.refHostAddr_toCore (s : Store H) (a : HostAddr) :
    Admin.toCore s (.refHostAddr a) = some [.ref (.extern (.host a))] := by simp [Admin.toCore]

@[simp] theorem Admin.callAddr_toCore (s : Store H) (a : FuncAddr) :
    Admin.toCore s (.callAddr a) =
      some [.ref (.func a), .callRefType (s.funcDefType a)] := by simp [Admin.toCore]

@[simp] theorem Admin.label_toCore (s : Store H) (n : Nat) (cont : Expr) (body : List Admin) :
    Admin.toCore s (.label n cont body) =
      (Expr.toCore cont).bind fun c =>
        (Admin.listToCore s body).map fun b => [.label n c b] := by simp [Admin.toCore]

@[simp] theorem Admin.frame_toCore (s : Store H) (n : Nat) (f : Frame) (body : List Admin) :
    Admin.toCore s (.frame n f body) =
      (Admin.listToCore s body).map fun b => [.frame n f.toCore b] := by simp [Admin.toCore]

@[simp] theorem Admin.trap_toCore (s : Store H) : Admin.toCore s .trap = some [.trap] := by
  simp [Admin.toCore]

theorem Admin.listToCore_append (s : Store H) {xs ys : List Admin} {x y : List CAdmin}
    (hx : Admin.listToCore s xs = some x) (hy : Admin.listToCore s ys = some y) :
    Admin.listToCore s (xs ++ ys) = some (x ++ y) := by
  induction xs generalizing x with
  | nil => simp_all
  | cons a as ih =>
    simp only [List.cons_append, Admin.listToCore_cons, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hx ⊢
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    exact ⟨u, hu, v ++ y, ih hv, by simp⟩

/-- A 2.0 value maps to the Core value it denotes: the `REF.NULL` case is where
`ToCore.plainOrNull` earns its keep. -/
@[simp] theorem Admin.value_toCore (s : Store H) (v : Val) :
    Admin.toCore s v.toAdmin = some [(Val.toCore v).toAdmin] := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | (_ | _ | _) <;>
    simp [Val.toAdmin, Val.toCore, Ref.toCore, Instr.toCore,
      ToCore.plainOrNull, Silmaril.Wasm.Execution.Core.Val.toAdmin]

@[simp] theorem values_toCore (s : Store H) (vs : List Val) :
    Admin.listToCore s (vals vs) =
      some (Silmaril.Wasm.Execution.Core.vals (vs.map Val.toCore)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [vals_cons, Admin.listToCore_cons, Admin.value_toCore, ih, List.map_cons,
      Option.bind_some, Option.map_some, List.cons_append, List.nil_append]
    rfl

/-- `Instr.toCore` never produces `CALL_REF`: 2.0 has no `call_ref`, and its
`CALL_INDIRECT` keeps its own immediates (`1-syntax:427`). -/
theorem Instr.toCore_ne_callRef {i : Instr} {c : Wasm.Instr} (h : Instr.toCore i = some c)
    (x : TypeIdx) : c ≠ .callRef x := by
  rintro rfl
  cases i <;> simp_all [Instr.toCore, Option.bind_eq_some_iff]

/-- `Instr.toCore` never produces `RETURN_CALL_REF`: 2.0 has no tail calls. -/
theorem Instr.toCore_ne_returnCallRef {i : Instr} {c : Wasm.Instr} (h : Instr.toCore i = some c)
    (x : TypeIdx) : c ≠ .returnCallRef x := by
  rintro rfl
  cases i <;> simp_all [Instr.toCore, Option.bind_eq_some_iff]

/-- `Instr.toCore` produces `REF.NULL` exactly on `REF.NULL` (`1-syntax:476`). -/
theorem Instr.toCore_refNull {i : Instr} {ht : Wasm.HeapType} (h : Instr.toCore i = some (.refNull ht)) :
    ∃ t : RefType, i = .refNull t ∧ t.toCoreHeap = ht := by
  cases i <;> simp_all [Instr.toCore, Option.bind_eq_some_iff]


/-- Every instruction in the image of a 2.0 expression is a non-`CALL_REF`. -/
theorem Expr.toCore_ne_callRef {es : Expr} {cs : Wasm.Expr} (h : Expr.toCore es = some cs) :
    ∀ c ∈ cs, ∀ x : TypeIdx, c ≠ .callRef x := by
  induction es generalizing cs with
  | nil => simp_all [Expr.toCore]
  | cons i es ih =>
    simp only [Expr.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, cs', hcs, rfl⟩ := h
    intro d hd x
    cases hd with
    | head => exact Instr.toCore_ne_callRef hc x
    | tail _ hd => exact ih hcs d hd x

@[simp] theorem expression_toCore (s : Store H) (es : Expr) :
    Admin.listToCore s (expression es) =
      (Expr.toCore es).map (fun cs => cs.map ToCore.plainOrNull) := by
  induction es with
  | nil => simp [expression, Expr.toCore]
  | cons i es ih =>
    simp only [expression, List.map_cons, Admin.listToCore_cons, Admin.plain_toCore, ih,
      Expr.toCore] at *
    cases Instr.toCore i <;> cases Expr.toCore es <;> simp

/-! ## Normalisation lemmas -/

namespace ToCore

@[simp] theorem normPlain_callRef (m : CModuleInst) (x : TypeIdx) :
    normPlain m (.callRef x) = .callRefType ((m.types[x.toNat]?).getD default) := rfl

@[simp] theorem normPlain_refNull (m : CModuleInst) (ht : Wasm.HeapType) :
    normPlain m (.refNull ht) = .ref .null := rfl

@[simp] theorem plainOrNull_refNull (ht : Wasm.HeapType) :
    plainOrNull (.refNull ht) = .ref .null := rfl

/-- Off `REF.NULL`, `plainOrNull` is the inclusion of source instructions. -/
theorem plainOrNull_eq_plain {c : Wasm.Instr} (h : ∀ ht, c ≠ .refNull ht) :
    plainOrNull c = .plain c := by
  cases c <;> first | rfl | exact absurd rfl (h _)

/-- Off `CALL_REF` and `REF.NULL`, normalising a plain instruction does nothing. -/
theorem normPlain_eq_plain (m : CModuleInst) {c : Wasm.Instr} (h₁ : ∀ x, c ≠ .callRef x)
    (h₂ : ∀ ht, c ≠ .refNull ht) : normPlain m c = .plain c := by
  cases c <;> first | rfl | exact absurd rfl (h₁ _) | exact absurd rfl (h₂ _)

/-- Off `CALL_REF`, normalising a plain instruction is `plainOrNull`. -/
theorem normPlain_eq_plainOrNull (m : CModuleInst) {c : Wasm.Instr}
    (h : ∀ x, c ≠ .callRef x) : normPlain m c = plainOrNull c := by
  cases c <;> first | rfl | exact absurd rfl (h _)

@[simp] theorem Admin.normList_nil (m : CModuleInst) : Admin.normList m [] = [] := by
  simp [Admin.normList]

@[simp] theorem Admin.normList_cons (m : CModuleInst) (a : CAdmin) (as : List CAdmin) :
    Admin.normList m (a :: as) = Admin.norm m a :: Admin.normList m as := by
  simp [Admin.normList]

theorem Admin.normList_eq_map (m : CModuleInst) (l : List CAdmin) :
    Admin.normList m l = l.map (Admin.norm m) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

@[simp] theorem Admin.norm_plain (m : CModuleInst) (i : Wasm.Instr) :
    Admin.norm m (.plain i) = normPlain m i := by simp [Admin.norm]

@[simp] theorem Admin.norm_ref (m : CModuleInst) (r : CRef) :
    Admin.norm m (.ref r) = .ref r := by simp [Admin.norm]

@[simp] theorem Admin.norm_trap (m : CModuleInst) : Admin.norm m .trap = .trap := by
  simp [Admin.norm]

@[simp] theorem Admin.norm_callRefType (m : CModuleInst) (d : DefType) :
    Admin.norm m (.callRefType d) = .callRefType d := by simp [Admin.norm]

@[simp] theorem Admin.norm_returnCallRefType (m : CModuleInst) (d : DefType) :
    Admin.norm m (.returnCallRefType d) = .returnCallRefType d := by simp [Admin.norm]

@[simp] theorem Admin.norm_label (m : CModuleInst) (n : Nat) (k : List Wasm.Instr)
    (b : List CAdmin) :
    Admin.norm m (.label n k b) = .label n k (b.map (Admin.norm m)) := by
  simp [Admin.norm, Admin.normList_eq_map]

@[simp] theorem Admin.norm_handler (m : CModuleInst) (n : Nat)
    (cs : List Silmaril.Wasm.Catch) (b : List CAdmin) :
    Admin.norm m (.handler n cs b) = .handler n cs (b.map (Admin.norm m)) := by
  simp [Admin.norm, Admin.normList_eq_map]

@[simp] theorem Admin.norm_frame (m : CModuleInst) (n : Nat) (f : CFrame) (b : List CAdmin) :
    Admin.norm m (.frame n f b) = .frame n (Frame.erase f) (b.map (Admin.norm f.module)) := by
  simp [Admin.norm, Admin.normList_eq_map]

/-- The image of a non-`CALL_REF` source instruction is already normal. -/
theorem Admin.norm_plainOrNull (m : CModuleInst) {c : Wasm.Instr}
    (h : ∀ x, c ≠ .callRef x) : Admin.norm m (plainOrNull c) = plainOrNull c := by
  by_cases h₂ : ∃ ht, c = .refNull ht
  · obtain ⟨ht, rfl⟩ := h₂; simp
  · push Not at h₂
    rw [plainOrNull_eq_plain h₂, Admin.norm_plain, normPlain_eq_plain m h h₂]

/-! ## `Rigid`: the elements normalisation does not produce from anything else

See the module docstring. Compared with `Lime1.Execution.ToCore.Rigid` the
`RETURN_CALL_REF` cases are gone (2.0 has no tail calls) and `.ref .null` is no
longer rigid (it is the normal form of `REF.NULL ht`). -/

/-- An administrative instruction that is its own only `Admin.norm` preimage. -/
def Rigid : CAdmin → Prop
  | .plain i => (∀ x, i ≠ .callRef x) ∧ (∀ ht, i ≠ .refNull ht)
  | .ref r => r ≠ .null
  | .trap => True
  | _ => False

theorem Rigid.norm {m : CModuleInst} {y : CAdmin} (hy : Rigid y) : Admin.norm m y = y := by
  cases y with
  | plain i => rw [Admin.norm_plain]; exact normPlain_eq_plain m hy.1 hy.2
  | ref => simp
  | trap => simp
  | _ => exact hy.elim

theorem Rigid.eq_of_norm {m : CModuleInst} {x y : CAdmin} (hy : Rigid y)
    (h : Admin.norm m x = y) : x = y := by
  cases x with
  | plain i =>
    by_cases h₁ : ∃ z, i = .callRef z
    · obtain ⟨z, rfl⟩ := h₁
      rw [Admin.norm_plain, normPlain_callRef] at h; subst h; exact hy.elim
    by_cases h₂ : ∃ ht, i = .refNull ht
    · obtain ⟨ht, rfl⟩ := h₂
      rw [Admin.norm_plain, normPlain_refNull] at h; subst h; exact absurd rfl hy
    push Not at h₁ h₂
    rwa [Admin.norm_plain, normPlain_eq_plain m h₁ h₂] at h
  | label => rw [Admin.norm_label] at h; subst h; exact hy.elim
  | frame => rw [Admin.norm_frame] at h; subst h; exact hy.elim
  | handler => rw [Admin.norm_handler] at h; subst h; exact hy.elim
  | callRefType => rw [Admin.norm_callRefType] at h; subst h; exact hy.elim
  | returnCallRefType => rw [Admin.norm_returnCallRefType] at h; subst h; exact hy.elim
  | ref => rwa [Admin.norm_ref] at h
  | trap => rwa [Admin.norm_trap] at h

/-- Every value but the null reference is rigid. -/
theorem Rigid.val {v : CVal} (h : v ≠ .ref .null) : Rigid v.toAdmin := by
  match v with
  | .num ⟨.int _, _⟩ => exact ⟨by simp, by simp⟩
  | .num ⟨.float _, _⟩ => exact ⟨by simp, by simp⟩
  | .vec _ => exact ⟨by simp, by simp⟩
  | .ref _ => exact fun hr => h (by rw [hr])

/-- The image of a 2.0 source instruction other than `REF.NULL` is rigid. -/
theorem Rigid.plainOrNull {c : Wasm.Instr} (h₁ : ∀ x, c ≠ .callRef x)
    (h₂ : ∀ ht, c ≠ .refNull ht) : Rigid (plainOrNull c) := by
  rw [plainOrNull_eq_plain h₂]; exact ⟨h₁, h₂⟩

theorem map_norm_eq_of_rigid {m : CModuleInst} {l L : List CAdmin} (hL : ∀ y ∈ L, Rigid y)
    (h : l.map (Admin.norm m) = L) : l = L := by
  induction L generalizing l with
  | nil => simpa using h
  | cons y L ih =>
    rcases l with _ | ⟨x, l⟩
    · simp at h
    · simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.mem_cons, forall_eq_or_imp] at hL
      rw [(hL.1).eq_of_norm h.1, ih hL.2 h.2]

/-! ## Inverting `Admin.norm` -/

/-- The null reference has two preimages: itself and the instruction
`REF.NULL ht`. This is the one place where 2.0 needs more than `Rigid`. -/
theorem norm_eq_null {m : CModuleInst} {x : CAdmin} (h : Admin.norm m x = .ref .null) :
    x = .ref .null ∨ ∃ ht, x = .plain (.refNull ht) := by
  cases x with
  | plain i =>
    by_cases h₁ : ∃ z, i = .callRef z
    · obtain ⟨z, rfl⟩ := h₁; rw [Admin.norm_plain, normPlain_callRef] at h; exact absurd h (by simp)
    by_cases h₂ : ∃ ht, i = .refNull ht
    · obtain ⟨ht, rfl⟩ := h₂; exact .inr ⟨ht, rfl⟩
    push Not at h₁ h₂
    rw [Admin.norm_plain, normPlain_eq_plain m h₁ h₂] at h; exact absurd h (by simp)
  | ref r => rw [Admin.norm_ref] at h; exact .inl h
  | label => rw [Admin.norm_label] at h; exact absurd h (by simp)
  | frame => rw [Admin.norm_frame] at h; exact absurd h (by simp)
  | handler => rw [Admin.norm_handler] at h; exact absurd h (by simp)
  | callRefType => rw [Admin.norm_callRefType] at h; exact absurd h (by simp)
  | returnCallRefType => rw [Admin.norm_returnCallRefType] at h; exact absurd h (by simp)
  | trap => rw [Admin.norm_trap] at h; exact absurd h (by simp)

theorem norm_eq_label {m : CModuleInst} {x : CAdmin} {n : Nat} {k : List Wasm.Instr}
    {b : List CAdmin} (h : Admin.norm m x = .label n k b) :
    ∃ b', x = .label n k b' ∧ b'.map (Admin.norm m) = b := by
  cases x with
  | plain i =>
    by_cases h₁ : ∃ z, i = .callRef z
    · obtain ⟨z, rfl⟩ := h₁; rw [Admin.norm_plain, normPlain_callRef] at h; exact absurd h (by simp)
    by_cases h₂ : ∃ ht, i = .refNull ht
    · obtain ⟨ht, rfl⟩ := h₂; rw [Admin.norm_plain, normPlain_refNull] at h
      exact absurd h (by simp)
    push Not at h₁ h₂
    rw [Admin.norm_plain, normPlain_eq_plain m h₁ h₂] at h; exact absurd h (by simp)
  | label n' k' b' =>
    rw [Admin.norm_label] at h
    obtain ⟨rfl, rfl, rfl⟩ := by simpa using h
    exact ⟨b', rfl, rfl⟩
  | ref => rw [Admin.norm_ref] at h; exact absurd h (by simp)
  | frame => rw [Admin.norm_frame] at h; exact absurd h (by simp)
  | handler => rw [Admin.norm_handler] at h; exact absurd h (by simp)
  | callRefType => rw [Admin.norm_callRefType] at h; exact absurd h (by simp)
  | returnCallRefType => rw [Admin.norm_returnCallRefType] at h; exact absurd h (by simp)
  | trap => rw [Admin.norm_trap] at h; exact absurd h (by simp)

theorem norm_eq_frame {m : CModuleInst} {x : CAdmin} {n : Nat} {f : CFrame} {b : List CAdmin}
    (h : Admin.norm m x = .frame n f b) :
    ∃ f' b', x = .frame n f' b' ∧ Frame.erase f' = f ∧ b'.map (Admin.norm f'.module) = b := by
  cases x with
  | plain i =>
    by_cases h₁ : ∃ z, i = .callRef z
    · obtain ⟨z, rfl⟩ := h₁; rw [Admin.norm_plain, normPlain_callRef] at h; exact absurd h (by simp)
    by_cases h₂ : ∃ ht, i = .refNull ht
    · obtain ⟨ht, rfl⟩ := h₂; rw [Admin.norm_plain, normPlain_refNull] at h
      exact absurd h (by simp)
    push Not at h₁ h₂
    rw [Admin.norm_plain, normPlain_eq_plain m h₁ h₂] at h; exact absurd h (by simp)
  | frame n' f' b' =>
    rw [Admin.norm_frame] at h
    obtain ⟨rfl, rfl, rfl⟩ := by simpa using h
    exact ⟨f', b', rfl, rfl, rfl⟩
  | ref => rw [Admin.norm_ref] at h; exact absurd h (by simp)
  | label => rw [Admin.norm_label] at h; exact absurd h (by simp)
  | handler => rw [Admin.norm_handler] at h; exact absurd h (by simp)
  | callRefType => rw [Admin.norm_callRefType] at h; exact absurd h (by simp)
  | returnCallRefType => rw [Admin.norm_returnCallRefType] at h; exact absurd h (by simp)
  | trap => rw [Admin.norm_trap] at h; exact absurd h (by simp)

theorem norm_eq_callRefType {m : CModuleInst} {x : CAdmin} {d : DefType}
    (h : Admin.norm m x = .callRefType d) :
    x = .callRefType d ∨ ∃ y, x = .plain (.callRef y) ∧ (m.types[y.toNat]?).getD default = d := by
  cases x with
  | plain i =>
    by_cases h₁ : ∃ z, i = .callRef z
    · obtain ⟨z, rfl⟩ := h₁
      rw [Admin.norm_plain, normPlain_callRef] at h
      exact .inr ⟨z, rfl, by simpa using h⟩
    by_cases h₂ : ∃ ht, i = .refNull ht
    · obtain ⟨ht, rfl⟩ := h₂; rw [Admin.norm_plain, normPlain_refNull] at h
      exact absurd h (by simp)
    push Not at h₁ h₂
    rw [Admin.norm_plain, normPlain_eq_plain m h₁ h₂] at h; exact absurd h (by simp)
  | callRefType d' => rw [Admin.norm_callRefType] at h; exact .inl h
  | ref => rw [Admin.norm_ref] at h; exact absurd h (by simp)
  | label => rw [Admin.norm_label] at h; exact absurd h (by simp)
  | frame => rw [Admin.norm_frame] at h; exact absurd h (by simp)
  | handler => rw [Admin.norm_handler] at h; exact absurd h (by simp)
  | returnCallRefType => rw [Admin.norm_returnCallRefType] at h; exact absurd h (by simp)
  | trap => rw [Admin.norm_trap] at h; exact absurd h (by simp)

mutual
/-- Normalisation only reads the enclosing module's types. -/
theorem Admin.norm_congr : (x : CAdmin) → {m m' : CModuleInst} → m.types = m'.types →
    Admin.norm m x = Admin.norm m' x
  | .plain i, m, m', h => by
    by_cases h₁ : ∃ z, i = .callRef z
    · obtain ⟨z, rfl⟩ := h₁; rw [Admin.norm_plain, Admin.norm_plain, normPlain_callRef,
        normPlain_callRef, h]
    by_cases h₂ : ∃ ht, i = .refNull ht
    · obtain ⟨ht, rfl⟩ := h₂; rw [Admin.norm_plain, Admin.norm_plain, normPlain_refNull,
        normPlain_refNull]
    push Not at h₁ h₂
    rw [Admin.norm_plain, Admin.norm_plain, normPlain_eq_plain m h₁ h₂,
      normPlain_eq_plain m' h₁ h₂]
  | .label n k b, _, _, h => by
    simp only [Admin.norm_label]; rw [Admin.map_norm_congr b h]
  | .handler n cs b, _, _, h => by
    simp only [Admin.norm_handler]; rw [Admin.map_norm_congr b h]
  | .frame _ _ _, _, _, _ => by simp
  | .ref _, _, _, _ => by simp
  | .callRefType _, _, _, _ => by simp
  | .returnCallRefType _, _, _, _ => by simp
  | .trap, _, _, _ => by simp

theorem Admin.map_norm_congr : (l : List CAdmin) → {m m' : CModuleInst} → m.types = m'.types →
    l.map (Admin.norm m) = l.map (Admin.norm m')
  | [], _, _, _ => rfl
  | x :: l, _, _, h => by
    simp only [List.map_cons]; rw [Admin.norm_congr x h, Admin.map_norm_congr l h]
end

end ToCore

/-! ## 2.0 images are normal -/

theorem ModuleInst.erase_toCore (m : ModuleInst) :
    ToCore.ModuleInst.erase m.toCore = m.toCore := rfl

theorem Frame.erase_toCore (f : Frame) : ToCore.Frame.erase f.toCore = f.toCore := rfl

/-- The module of a function instance's image has no tags. -/
theorem FuncInst.erase_module_toCore {fi : FuncInst H} {ci : ToCore.CFuncInst H}
    (h : fi.toCore = some ci) :
    { ci with module := ToCore.ModuleInst.erase ci.module } = ci := by
  unfold FuncInst.toCore at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    rfl
  · simp only [Option.some.injEq] at h
    subst h
    rfl

theorem mapM_funcInst_erase {l : List (FuncInst H)} {fs : List (ToCore.CFuncInst H)}
    (h : l.mapM FuncInst.toCore = some fs) :
    fs.map (fun fi => { fi with module := ToCore.ModuleInst.erase fi.module }) = fs := by
  induction l generalizing fs with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | cons a l ih =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨c, hc, cs, hcs, rfl⟩ := h
    simp [FuncInst.erase_module_toCore hc, ih hcs]

/-- Allocation addresses are preserved: the `a`-th function instance of the image
is the image of the `a`-th function instance. -/
theorem mapM_funcInst_type {l : List (FuncInst H)} {fs : List (ToCore.CFuncInst H)}
    (h : l.mapM FuncInst.toCore = some fs) (a : Nat) :
    (fs[a]?).map (fun fi => fi.type) = (l[a]?).map (fun fi => fi.type.toDefType) := by
  induction l generalizing fs a with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp
  | cons b l ih =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨c, hc, cs, hcs, rfl⟩ := h
    cases a with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.map_some]
      unfold FuncInst.toCore at hc
      split at hc
      · simp only [Option.map_eq_some_iff] at hc
        obtain ⟨_, _, rfl⟩ := hc
        rfl
      · simp only [Option.some.injEq] at hc
        subst hc
        rfl
    | succ a => simpa using ih hcs a

theorem Store.erase_toCore {s : Store H} {sc : ToCore.CStore H} (h : s.toCore = some sc) :
    ToCore.Store.erase sc = sc := by
  simp only [Store.toCore, Option.map_eq_some_iff] at h
  obtain ⟨fs, hfs, rfl⟩ := h
  simp only [ToCore.Store.erase, mapM_funcInst_erase hfs]

/-- The defined type recorded by the Core image of a store is the image of the
2.0 function type; this is what makes `Store.funcDefType` the annotation Core
3.0's `Step_read/call` computes. -/
theorem Store.toCore_funcs_type {s : Store H} {sc : ToCore.CStore H} (h : s.toCore = some sc)
    (a : FuncAddr) :
    (sc.funcs[a]?).map (fun fi => fi.type) =
      (s.funcs[a]?).map (fun fi => fi.type.toDefType) := by
  simp only [Store.toCore, Option.map_eq_some_iff] at h
  obtain ⟨fs, hfs, rfl⟩ := h
  exact mapM_funcInst_type hfs a

mutual
theorem map_norm_toCore (s : Store H) :
    (a : Admin) → (m : ToCore.CModuleInst) →
      (Admin.toCore s a).map (fun l => l.map (ToCore.Admin.norm m)) = Admin.toCore s a
  | .plain i, m => by
    cases h : Instr.toCore i with
    | none => simp [h]
    | some c => simp [h, ToCore.Admin.norm_plainOrNull m (fun x => Instr.toCore_ne_callRef h x)]
  | .refFuncAddr _, _ => by simp
  | .refHostAddr _, _ => by simp
  | .callAddr _, _ => by simp
  | .label n cont body, m => by
    have ih := map_norm_listToCore s body m
    cases hc : Expr.toCore cont with
    | none => simp [hc]
    | some c =>
      cases hb : Admin.listToCore s body with
      | none => simp [hb]
      | some b =>
        rw [hb] at ih
        simp only [Option.map_some, Option.some.injEq] at ih
        simp [hc, hb, ih]
  | .frame n f body, _ => by
    have ih := map_norm_listToCore s body (Frame.toCore f).module
    cases hb : Admin.listToCore s body with
    | none => simp [hb]
    | some b =>
      rw [hb] at ih
      simp only [Option.map_some, Option.some.injEq] at ih
      simp [hb, ih, Frame.erase_toCore]
  | .trap, _ => by simp

theorem map_norm_listToCore (s : Store H) :
    (l : List Admin) → (m : ToCore.CModuleInst) →
      (Admin.listToCore s l).map (fun x => x.map (ToCore.Admin.norm m)) = Admin.listToCore s l
  | [], _ => by simp
  | a :: as, m => by
    have iha := map_norm_toCore s a m
    have ihb := map_norm_listToCore s as m
    cases ha : Admin.toCore s a with
    | none => simp [ha]
    | some x =>
      cases hb : Admin.listToCore s as with
      | none => simp [ha, hb]
      | some y =>
        rw [ha] at iha; rw [hb] at ihb
        simp only [Option.map_some, Option.some.injEq] at iha ihb
        simp [ha, hb, List.map_append, iha, ihb]
end

/-- 2.0 images are normal: `Sim` holds between a well-formed 2.0 configuration
and its own Core 3.0 image. -/
theorem Sim.refl_toCore {a : Config H} {ac : ToCore.CConfig H} (h : a.toCore = some ac)
    (hwf : ConfigWF a) : Sim a ac := by
  refine ⟨?_, hwf⟩
  simp only [Config.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨sc, hsc, code, hcode, rfl⟩ := h
  have ih := map_norm_listToCore a.store a.code (Frame.toCore a.frame).module
  rw [hcode] at ih
  simp only [Option.map_some, Option.some.injEq] at ih
  simp only [Config.toCore, hsc, hcode, Option.bind_some, Option.map_some, ToCore.Config.norm,
    Store.erase_toCore hsc, Frame.erase_toCore, ToCore.Admin.normList_eq_map, ih]

end Silmaril.Wasm.V2.Execution
