module

public import Silmaril.Prelude.Trust.Elab.Defs

/-! # Test-only forgery helpers (imported by `Silmaril.Prelude.Trust.Examples` only)

`forge_native% tag p` proves the decidable proposition `p` by a native run whose axiom carries
an arbitrary tag (`<decl>._native.<tag>.ax_…`), and records a use of `proc` for it. It
exercises the audit's checks against forged provenance; nothing else may import it.
-/

public meta section

namespace Silmaril.Trust.TestForge

open Lean Elab Term Meta

syntax (name := forgeNative) "forge_native% " ident ident term : term

@[term_elab forgeNative] def elabForge : TermElab := fun stx _ => do
  let tag := stx[1].getId
  let proc := stx[2].getId
  let p ← elabTerm stx[3] (some (mkSort .zero))
  synthesizeSyntheticMVarsNoPostponing
  let p ← instantiateMVars p
  let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
  let e := mkApp2 (mkConst ``Decidable.decide) p inst
  match ← nativeEqTrue tag e with
  | .notTrue => throwError "forge_native%: false"
  | .success ax =>
    recordUse { decl := (← getDeclName?).getD .anonymous, module := (← getEnv).mainModule,
                proc, mode := .native, profile := "forged", ax := ax.constName? }
    return mkApp3 (mkConst ``of_decide_eq_true) p inst ax

end Silmaril.Trust.TestForge
