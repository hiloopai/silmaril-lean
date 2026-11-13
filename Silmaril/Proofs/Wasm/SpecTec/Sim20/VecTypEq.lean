module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.VecTyp.Typ
public import Silmaril.Wasm.SpecTec.Sim.Defs

/-!
# Builtins that agree away from `bad`: the agreements as statements about typing

From the fuel-indexed agreements `VecTyp.bagreeAt` and `VecTyp.tbagreeAt` (unrefined, in
`Raw/…/Sim20/VecTyp/`):

* `evalExp_withB`, `hasTyp_withB`: harmless syntax evaluates and types in `env.withBuiltins B'`
  whenever it does in `env`;
* **`typedV_withB`**: a value typed in `env` at a harmless type is typed in `env.withBuiltins B'`;
  `TypedV` quantifies over scopes that bind term variables only, whose definition and type
  variables trivially avoid `bad`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecTyp

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.RelFree (GoodEvs DefsOk TypsOk DefsGood TypsGood)
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evExp evTyp)

variable {bad : List String} {env : Env} {B' : Builtins}

theorem evalExp_withB (hDG : DefsGood bad env) (hB : BAgree bad env.builtins B') {ρ : VarEnv}
    {e : Exp} {v : Value} (hD : DefsOk bad ρ) (hG : GoodEvs bad (evExp e))
    (h : EvalExp env ρ e v) : EvalExp (env.withBuiltins B') ρ e v := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, ((bagreeAt bad env B' hDG hB n).exp ρ e hD hG).ok hn⟩

theorem hasTyp_withB (hDG : DefsGood bad env) (hB : BAgree bad env.builtins B')
    (hTG : TypsGood bad env) {ρ : VarEnv} {t : Typ} {v : Value} (hD : DefsOk bad ρ)
    (hT : TypsOk bad ρ) (hG : GoodEvs bad (evTyp t)) (h : HasTyp env ρ t v) :
    HasTyp (env.withBuiltins B') ρ t v := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, ((tbagreeAt bad env B' hDG hB hTG n).typ ρ t v hD hT hG).ok hn⟩

theorem defsOk_of_valsOnly {ρ : VarEnv} (h : ValsOnly ρ) : DefsOk bad ρ := fun p hp => by
  rw [h.2.1] at hp; cases hp

theorem typsOk_of_valsOnly {ρ : VarEnv} (h : ValsOnly ρ) : TypsOk bad ρ := fun p hp => by
  rw [h.1] at hp; cases hp

/-- **Typing at a harmless type moves to builtins that agree away from `bad`.** -/
theorem typedV_withB (hDG : DefsGood bad env) (hB : BAgree bad env.builtins B')
    (hTG : TypsGood bad env) {t : Typ} {v : Value} (hG : GoodEvs bad (evTyp t))
    (h : TypedV env t v) : TypedV (env.withBuiltins B') t v := fun ρ hρ =>
  hasTyp_withB hDG hB hTG (defsOk_of_valsOnly hρ) (typsOk_of_valsOnly hρ) hG (h ρ hρ)

end Silmaril.Wasm.SpecTec.Sim20.VecTyp
