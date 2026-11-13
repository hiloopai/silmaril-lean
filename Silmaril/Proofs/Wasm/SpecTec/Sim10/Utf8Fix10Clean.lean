module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Fix10Ext
public import Silmaril.Wasm.SpecTec.Sim20.Utf8Else.Thms

/-!
# The 1.0 `$utf8` erratum: what never refers to `$utf8` evaluates alike

The 1.0 instance 's `Sim20.Utf8Else` facts (`clean20T`, `typsOffB_badU20`,
`hasTyp_u20T_iff`), for the pair `simEnv10T B`/`utf8Env10T B`:

* `refFree10T` (kernel): in `fixedT10`, only `$utf8`, the type `name` and the grammar `Bname`
  refer to `$utf8` (the 2.0 list `Utf8Else.utf8Users20` serves unchanged); so
  **`clean10T`**: `Utf8Else.Clean (simEnv10T B) "utf8"`.

The typing half is in `Utf8Fix10Typ`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Fix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evTyp mem_of_find? typDefEv
  findTyp?_envOfScript_item)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (TypOff GoodT typsOffB goodT_of_all)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Else (refFreeB utf8Users20 badU20 Clean clean_of_refFree
  TypFreeOff goodEvs_of_refFree goodEvs_append goodEvs_flatMap DefsOk GoodEvs hasTyp_iff
  typsOkT_nilU typsEv_nil)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T fixedT10)

set_option maxRecDepth 100000 in
/-- **Only `$utf8`, `name` and `Bname` refer to `$utf8` in `fixedT10`** (kernel). -/
theorem refFree10T : refFreeB "utf8" utf8Users20 fixedT10 = true := by
  decide +kernel

/-- **`simEnv10T B` never refers to `$utf8` outside `$utf8`.** -/
theorem clean10T (B : Builtins) : Clean (simEnv10T B) "utf8" :=
  clean_of_refFree refFree10T (fun x hx => by simp [utf8Users20, hx])
    (fun x => by simp [utf8Users20]) B

end Silmaril.Wasm.SpecTec.Sim10.Utf8Fix
