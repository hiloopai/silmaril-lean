module

public import Silmaril.Wasm.SpecTec.Sim.Integrate.Defs

/-!
# SpecTec ↔ Core 3.0, round 3, track refok: what stays open of `Residue` and `Extra`

Round 2 left two bundles of assumptions about the concrete `B := Prims.builtins prof hn host`
(`Integrate.Residue`, `Integrate.Extra`). Track refok discharges, for every profile and host:

* `Residue.instReftype`: `$inst_reftype(m, rt)` evaluates to the image of Core's
  `m.instRef rt` (`RefOk.instReftype_simEnv`, by evaluating `$subst_all_reftype`,
  `$subst_reftype`, `$subst_heaptype` and `$subst_typevar` on images; for every `B`);
* `Extra.grow`: `$growtable`/`$growmem` are the images of Core's `grow?`
  (`RefOk.growFuns_builtins`; `Prims.builtins` now answers both names).

What is left of the two bundles is stated here: `ResidueRest` (`Residue` without
`instReftype`) and `ExtraRest` (`Extra` without `grow`). `RefOk.residue_builtins` and
`RefOk.extra_builtins` rebuild the round-2 bundles from them.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.RefOk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation

open Silmaril.SpecTec.Equiv.Validation (tyV) in
/-- **`Integrate.Residue` without `instReftype`** (which track refok proves): the typing of the
runtime type syntax, of results and of function instances, and `RefOkBridge`. -/
structure ResidueRest {H : Type} (env : Env) (hn : H → String) : Prop where
  /-- Images of closed types inhabit `deftype`, `comptype`, `final?`, `typeuse*`. -/
  types : Prims.TypeTyping env
  /-- Images of closed value types are `valtype*`. -/
  valtypes : ∀ ts : Ty (.list .val), TypedV env valtypesT (.list (ts.toList.map tyV))
  /-- A result whose instructions are typed is a typed `result`. -/
  result : ∀ r : Result, TypedV env instrsT (.list (adminsToV r.toAdmin)) →
    TypedV env resultT (resultV r)
  /-- Function instances of a typed store are typed. -/
  funcinst : ∀ (s : Store H) (a : Nat) (fi : FuncInst H), TypedV env storeT (storeV hn s) →
    s.funcs[a]? = some fi → TypedV env funcinstT (funcInstV hn fi)
  /-- SpecTec's `Ref_ok` is Core's `RefOk`. -/
  refOk : RefsGC.RefOkBridge env

/-- **`Integrate.Extra` without `grow`** (which track refok proves): typing of table/memory
types and immediates, of grown instances, and the aggregate type facts. -/
structure ExtraRest (env : Env) : Prop where
  /-- Typing of table/memory types and memory immediates (family E). -/
  mem : Memory.MemTyping env
  /-- Grown table and memory instances are typed (family E). -/
  inst : Memory.InstTyping env
  /-- `Expand` on every composite type; storage-type, mutability and aggregate typing. -/
  agg : Aggregates.AggTypes env

open Silmaril.SpecTec.Equiv.Validation (tyV) in
/-- **What is left of `Residue` after tracks refok and configok**: configok discharges `result`
and `funcinst` (`ConfigOk.typedV_result`, `ConfigOk.funcinst_of_store`), refok `instReftype`.
`types` is refuted as stated (`ConfigOk.not_typeTyping`), so this structure is uninhabited
(`RefOk.not_residueCore`); it records the fields a restatement has to address. -/
structure ResidueCore (env : Env) : Prop where
  /-- Images of closed types inhabit `deftype`, `comptype`, `final?`, `typeuse*`. -/
  types : Prims.TypeTyping env
  /-- Images of closed value types are `valtype*`. -/
  valtypes : ∀ ts : Ty (.list .val), TypedV env valtypesT (.list (ts.toList.map tyV))
  /-- SpecTec's `Ref_ok` is Core's `RefOk`. -/
  refOk : RefsGC.RefOkBridge env

end Silmaril.Wasm.SpecTec.Sim.RefOk
