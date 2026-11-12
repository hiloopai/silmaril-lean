module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.RefOk.Never
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.RefOk.Core
public import Silmaril.Wasm.SpecTec.Sim.Round5.Pos.Thms

/-!
# Round 5: `Fwd.RefOkB` and its Core-valid restriction are false

The counterexample is `null` at `REF NULL ANY` on the empty store. The empty store is valid in
Core (`storeOk_empty`) and its image is a typed `store` (`typedV_storeEmpty`); `REF NULL ANY` is
bounded and valid in `{}`. Core types `null` there (`refOk_nullAny`), and SpecTec types `null`
at `REF NULL BOT` only (`eq_bot_of_dderives_null`).

So `RefOkBV` (Core-valid stores and closed types) fails (`not_refOkBV`), and with it `RefOkB`
(`not_refOkB`). On the nested type both sides fail at `null`, so it is no counterexample
(`refOkAt_nested_null`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.RefOk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)

variable {H : Type}

/-- The empty store is valid in Core. -/
theorem storeOk_empty : StoreOk ({} : Store H) := by
  constructor <;> simp

/-- An empty `t*` is typed. -/
theorem typedV_listNil {B : Builtins} {t : Typ} : TypedV (simEnv B) (.iterT t .list) (.list []) :=
  typedV_list_iff.2 fun _ hv => absurd hv List.not_mem_nil

/-- **The image of the empty store is a typed `store`.** -/
theorem typedV_storeEmpty (B : Builtins) (hn : H → String) :
    TypedV (simEnv B) storeT (storeV hn ({} : Store H)) :=
  Pos.typedV_struct ConfigOk.findTyp_store' <|
    Pos.hasTypFields_cons_of typedV_listNil <| Pos.hasTypFields_cons_of typedV_listNil <|
    Pos.hasTypFields_cons_of typedV_listNil <| Pos.hasTypFields_cons_of typedV_listNil <|
    Pos.hasTypFields_cons_of typedV_listNil <| Pos.hasTypFields_cons_of typedV_listNil <|
    Pos.hasTypFields_cons_of typedV_listNil <| Pos.hasTypFields_cons_of typedV_listNil <|
    Pos.hasTypFields_cons_of typedV_listNil <| Pos.hasTypFields_one typedV_listNil

/-- **`Ref_ok` is not `RefOk` at `REF NULL ANY`**, on any store: Core types `null` there,
SpecTec does not. -/
theorem not_refOkAt_nullAny (B : Builtins) (hn : H → String) (s : Store H) :
    ¬ Fwd.RefOkAt (simEnv B) hn s nullAny := fun K =>
  have hd : DDerives (simEnv B) noElse "Ref_ok" "%|-%:%" []
      (.tuple [storeV hn s, refToValue .null, tyV nullAny]) := (K noElse .null).2 (refOk_nullAny s)
  absurd (eq_bot_of_dderives_null B noElse _ nullAny hd) (by simp [nullAny])

/-- `RefOkB` gives its restriction `RefOkBV`. -/
theorem refOkBV_of_refOkB {env : Env} (K : Fwd.RefOkB env) : RefOkBV env where
  refOk hn s rt hs _ hb _ := K.refOk hn s rt hs hb

/-- **`Fwd.RefOkB` restricted to Core-valid stores and Core-valid closed types is false**, for
every builtins. -/
theorem not_refOkBV (B : Builtins) : ¬ RefOkBV (simEnv B) := fun K =>
  not_refOkAt_nullAny B (fun _ : Unit => "") {}
    (K.refOk _ {} nullAny (typedV_storeEmpty B _) storeOk_empty tyBnd_nullAny tyOk_nullAny)

/-- **`Fwd.RefOkB` is false**, for every builtins. -/
theorem not_refOkB (B : Builtins) : ¬ Fwd.RefOkB (simEnv B) := fun K =>
  not_refOkBV B (refOkBV_of_refOkB K)

/-- **The nested type is no counterexample at `null`**: on every store, neither SpecTec nor
Core types `null` at `REF NULL D_out`. -/
theorem refOkAt_nested_null (B : Builtins) (hn : H → String) (s : Store H) (O : ElseI) :
    ¬ DDerives (simEnv B) O "Ref_ok" "%|-%:%" []
        (.tuple [storeV hn s, refToValue .null, tyV nestedRT]) ∧
      ¬ RefOk s .null nestedRT :=
  ⟨fun h => absurd (eq_bot_of_dderives_null B O _ nestedRT h) (by simp [nestedRT]),
    not_refOk_null_nested s⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.RefOk
