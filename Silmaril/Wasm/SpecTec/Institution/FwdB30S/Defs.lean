module

public import Silmaril.Wasm.SpecTec.Institution.FwdB30X.Defs
public import Silmaril.Wasm.SpecTec.Institution.FwdX30Fin.Defs

/-!
# `Step` facts at `Wasm30.builtins` beyond `FwdB30X`: definitions

`FwdB30X` showed that every `FwdX30.PureHeadX`/`ReadHeadX` redex has its `Step_pure`/`Step_read`
fact at the choice-made primitives `Wasm30.builtins`, up to `CfgRel`. This topic names the data
for three further steps.

* **Store-changing `Step` rules.** `StoreW P c c'`: Core's variable, table, memory and aggregate
  steps whose instruction is a `Step` rule of fixed arity (`local.set`, `global.set`,
  `table.set`, `table.grow`, `elem.drop`, the stores, `memory.grow`, `data.drop`, `struct.set`,
  `array.set`). `stepOk k t` is the table check for a `FlatK k t` redex at which only a `Step`
  rule from rule 6 on can fire: every proper infix is inert, and at the whole redex no rule of
  `Step_pure` or `Step_read` and none of the three context rules `ctxt-label`, `ctxt-handler`,
  `ctxt-frame` fires. `stepCombos` lists the shapes of `StoreW`.
* **Exactness.** `ctxTags` are the constructors that `Bwd.AdminEq` may change (`CALL_REF` and
  the three contexts). `RigidV l`: no element of `l` has one of them at the top. A
  configuration whose code image is `RigidV` is the only one `CfgRel`-related to its image
  (`FwdB30S.cfgRel_exact`), so existence up to `CfgRel` becomes existence at `adminsToV`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30S

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Institution.FwdB30X

/-! ## The check for a store-changing redex -/

/-- **A `Step` redex of shape `FlatK k t`**: every proper infix is inert, and at the whole redex
no `Step_pure` rule, no `Step_read` rule and none of `Step` rules 3–5 (the context rules for
labels, handlers and frames) fires. -/
def stepOk (k : Nat) (t : MixopS) : Bool :=
  chkProper k t pureInfoT && chkProper k t readInfoT && chkProper k t stepRestT &&
    chkFull k t pureInfoT && chkFull k t readInfoT && chkFull k t (stepRestT.take 3)

/-- `stepOk`, on the `nonV` tables. -/
def stepOkN (k : Nat) (t : MixopS) : Bool :=
  chkProperN k t pureNVT && chkProperN k t readNVT && chkProperN k t (stepNVT.drop 3) &&
    chkFullN k t pureNVT && chkFullN k t readNVT && chkFullN k t ((stepNVT.drop 3).take 3)

/-- The shapes `(k, t)` of the store-changing `Step` redexes of fixed arity. -/
def stepCombos : List (Nat × MixopS) :=
  [(1, "LOCAL.SET"), (1, "GLOBAL.SET"), (2, "TABLE.SET"), (2, "TABLE.GROW"), (0, "ELEM.DROP"),
   (2, "STORE"), (2, "VSTORE"), (2, "VSTORE_LANE"), (1, "MEMORY.GROW"), (0, "DATA.DROP"),
   (2, "STRUCT.SET"), (3, "ARRAY.SET")]

/-! ## Exactness -/

/-- The constructors `Bwd.AdminEq` may change: `CALL_REF` and the three contexts. -/
def ctxTags : List MixopS := ["CALL_REF", "LABEL_%{%}%", "HANDLER_%{%}%", "FRAME_%{%}%"]

/-- No element of `l` has a constructor of `ctxTags` at the top. -/
def RigidV (l : List Value) : Prop :=
  ∀ x ∈ l, ∀ op w, x = .case op w → op ∉ ctxTags

/-! ## The store-changing Core steps -/

section Core

open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The variable instructions of `Step` rules: `local.set` and `global.set`. -/
def varWriteInstr : Instr → Bool
  | .localSet _ | .globalSet _ => true
  | _ => false

/-- The aggregate instructions of `Step` rules of fixed arity: `struct.set` and `array.set`
(`struct.new` and `array.new_fixed` take a value prefix of any length). -/
def aggWriteInstr : Instr → Bool
  | .structSet .. | .arraySet _ => true
  | _ => false

/-- **Core's store-changing steps of fixed arity**, each a `Step` rule of SpecTec (from rule 6
on): `local.set`, `global.set`; `table.set`, `table.grow`, `elem.drop` (every `TableStep` that
is not a `Step_read` rule); the stores, `memory.grow`, `data.drop` (every `MemoryStep` that is
not a `Step_read` rule); `struct.set` and `array.set`. -/
inductive StoreW (P : Profile) : Config H → Config H → Prop where
  /-- `local.set`, `global.set`. -/
  | var {c c' : Config H} (h : VariableStep c c') (hl : FwdX30.LastIs varWriteInstr c.code) :
      StoreW P c c'
  /-- `table.set`, `table.grow`, `elem.drop`. -/
  | table {c c' : Config H} (h : TableStep P c c')
      (hl : FwdX30.LastIs (fun i => !FwdX30.tableReadInstr i) c.code) : StoreW P c c'
  /-- The stores, `memory.grow`, `data.drop`. -/
  | memory {c c' : Config H} (h : MemoryStep P c c')
      (hl : FwdX30.LastIs (fun i => !FwdX30.memReadInstr i) c.code) : StoreW P c c'
  /-- `struct.set`, `array.set`. -/
  | aggregate {c c' : Config H} (h : AggregateStep c c') (hl : FwdX30.LastIs aggWriteInstr c.code) :
      StoreW P c c'

end Core

end Silmaril.Wasm.SpecTec.Institution.FwdB30S
