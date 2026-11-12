module

public import Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.RefOkB.Nested

/-!
# Round 6: the restatement `RefOkBV`

* `refOkBV_of_refOkBB`: `RefOkBV` is no stronger than `RefOkBB`.
* `refOkBV_nested_excluded`: the refutation's witness `REF NULL D_out` is outside `RefOkBV`
  (it is bounded but not valid in `{}`), so `not_refOkBB` does not bear on it.
* `refOkAtB_nullAny`: round 5's counterexample type `REF NULL ANY`, which `RefOkBV` does cover
  (Core-valid, bounded), agrees at `null` on every typed store.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Round5.RefOk (nestedRT nullAny)

/-- `RefOkBV` is a weakening of `RefOkBB`. -/
theorem refOkBV_of_refOkBB {env : Env} (K : Reading.RefOkBB env) : RefOkBV env where
  refOk hn s rt hs _ hb _ := K.refOk hn s rt hs hb

/-- **The refutation's witness is outside `RefOkBV`**: `REF NULL D_out` is bounded, but not
valid in `{}`. -/
theorem refOkBV_nested_excluded : Round4.tyBnd nestedRT = true ∧ ¬ TyOk {} nestedRT :=
  ⟨tyBnd_nested, Round5.RefOk.not_tyOk_nested⟩

/-- **`REF NULL ANY` is covered by `RefOkBV`**, and both sides type `null` there. -/
theorem refOkAtB_nullAny {B : Builtins} {H : Type} (hn : H → String) (s : Store H)
    (hs : TypedV (simEnv B) storeT (storeV hn s)) (O : ElseI) :
    (Round4.tyBnd nullAny = true ∧ TyOk {} nullAny) ∧
      (Reading.DDerivesB (simEnv B) O "Ref_ok" "%|-%:%" []
        (.tuple [storeV hn s, Silmaril.SpecTec.Equiv.RuntimeBridge.refToValue .null,
          CT.elemType nullAny]) ∧ RefOk s .null nullAny) :=
  ⟨⟨Round5.RefOk.tyBnd_nullAny, Round5.RefOk.tyOk_nullAny⟩, Reading.refOkAtB_nullAny_null hn s hs O⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB
