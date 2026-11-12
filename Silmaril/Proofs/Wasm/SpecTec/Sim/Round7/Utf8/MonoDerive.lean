module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.Utf8.MonoTyp

/-!
# Round 7: what environment monotonicity moves from `simEnv B` to `utf8Env B`

The fuel-free consequences of `envMonoAt` and `envMonoTypAt`, for primitives `B` that leave
`$utf8` uninterpreted:

* values, arguments and iteration domains (`evalExp_utf8Env`, `evalArgs_utf8Env`,
  `evalDoms_utf8Env`);
* typing (`hasTyp_utf8Env`, `typedV_utf8Env`, `quantsOk_utf8Env`);
* **positive derivations** (`dderivesB_utf8Env`): a `DDerivesB` derivation in `simEnv B` is one in
  `utf8Env B`, for any two readings `O ≤ O'` of `otherwise`, in particular for `noElse`
  (`dderivesB_noElse_utf8Env`).

What is **not** moved is a derivation read with `otherwiseB`: `otherwiseB (utf8Env B)` asks that no
earlier rule fire in `utf8Env B`, which is a negative premise, and monotonicity runs the other
way. `SStepB (simEnv B) → SStepB (utf8Env B)` therefore does not follow from this file.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Sem.Res
open Round6.Reading (DDerivesB DPremB)

variable {B : Builtins}

theorem evalExp_utf8Env (hB : ∀ ws, B.call "utf8" ws = none) {ρ : VarEnv} {e : Exp} {v : Value}
    (h : EvalExp (simEnv B) ρ e v) : EvalExp (utf8Env B) ρ e v := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, (Res.Le.eq_of_ne_oof ((envMonoAt B hB n).exp ρ e) (by rw [hn]; simp)).trans hn⟩

theorem evalArgs_utf8Env (hB : ∀ ws, B.call "utf8" ws = none) {ρ : VarEnv} {as₀ : List Arg}
    {ws : List ArgV} (h : EvalArgs (simEnv B) ρ as₀ ws) : EvalArgs (utf8Env B) ρ as₀ ws := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, (Res.Le.eq_of_ne_oof ((envMonoAt B hB n).args ρ as₀) (by rw [hn]; simp)).trans hn⟩

theorem evalDoms_utf8Env (hB : ∀ ws, B.call "utf8" ws = none) {ρ : VarEnv} {ds : List Dom}
    {xvs : List (IL.Id × Value)} (h : EvalDoms (simEnv B) ρ ds xvs) :
    EvalDoms (utf8Env B) ρ ds xvs := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, (Res.Le.eq_of_ne_oof ((envMonoAt B hB n).doms ρ ds) (by rw [hn]; simp)).trans hn⟩

theorem hasTyp_utf8Env (hB : ∀ ws, B.call "utf8" ws = none) {ρ : VarEnv} {t : Typ} {v : Value}
    (h : HasTyp (simEnv B) ρ t v) : HasTyp (utf8Env B) ρ t v := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, (Res.Le.eq_of_ne_oof ((envMonoTypAt B hB n).typ ρ t v) (by rw [hn]; simp)).trans hn⟩

theorem typedV_utf8Env (hB : ∀ ws, B.call "utf8" ws = none) {t : Typ} {v : Value}
    (h : TypedV (simEnv B) t v) : TypedV (utf8Env B) t v :=
  fun ρ hρ => hasTyp_utf8Env hB (h ρ hρ)

theorem quantsOk_utf8Env (hB : ∀ ws, B.call "utf8" ws = none) {ρ : VarEnv} {qs : List Param}
    (h : QuantsOk (simEnv B) ρ qs) : QuantsOk (utf8Env B) ρ qs := fun x t hx => by
  obtain ⟨w, hw, ht⟩ := h x t hx
  exact ⟨w, hw, hasTyp_utf8Env hB ht⟩

mutual
/-- **Positive derivations move from `simEnv B` to `utf8Env B`**, along any inclusion of the
readings of `otherwise`. -/
theorem dderivesB_utf8Env (hB : ∀ ws, B.call "utf8" ws = none) {O O' : ElseI}
    (hO : ∀ x args i v, O x args i v → O' x args i v) :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value},
      DDerivesB (simEnv B) O x op args v → DDerivesB (utf8Env B) O' x op args v
  | _, _, _, _, .rule hrel hrule halt hps hq he hp =>
      .rule (by rw [findRel?_utf8Env]; exact hrel) hrule halt hps (quantsOk_utf8Env hB hq)
        (evalExp_utf8Env hB he) fun pr hpr => dpremB_utf8Env hB hO (hO _ _ _ _) (hp pr hpr)

/-- `dderivesB_utf8Env` for premises. -/
theorem dpremB_utf8Env (hB : ∀ ws, B.call "utf8" ws = none) {O O' : ElseI}
    (hO : ∀ x args i v, O x args i v → O' x args i v) {els els' : Prop} (hels : els → els') :
    ∀ {ρ : VarEnv} {pr : Prem}, DPremB (simEnv B) O els ρ pr → DPremB (utf8Env B) O' els' ρ pr
  | _, _, .ifPr h => .ifPr (evalExp_utf8Env hB h)
  | _, _, .elsePr h => .elsePr (hels h)
  | _, _, .letPr h₂ h₁ => .letPr (evalExp_utf8Env hB h₂) (evalExp_utf8Env hB h₁)
  | _, _, .rulePr ha he hd =>
      .rulePr (evalArgs_utf8Env hB ha) (evalExp_utf8Env hB he) (dderivesB_utf8Env hB hO hd)
  | _, _, .iterOptNone hd hne hall => .iterOptNone (evalDoms_utf8Env hB hd) hne hall
  | _, _, .iterOptSome hd hne hs hp =>
      .iterOptSome (evalDoms_utf8Env hB hd) hne hs (dpremB_utf8Env hB hO hels hp)
  | _, _, .iterList hit hd hne hl hk hp =>
      .iterList hit (evalDoms_utf8Env hB hd) hne hl hk fun r hr =>
        dpremB_utf8Env hB hO hels (hp r hr)
  | _, _, .iterListN hd he hk hl hlen hp =>
      .iterListN (evalDoms_utf8Env hB hd) (evalExp_utf8Env hB he) hk hl hlen fun r hr =>
        dpremB_utf8Env hB hO hels (hp r hr)
end

/-- Derivations without `otherwise` move from `simEnv B` to `utf8Env B`. -/
theorem dderivesB_noElse_utf8Env (hB : ∀ ws, B.call "utf8" ws = none) {x : IL.Id} {op : MixopS}
    {args : List ArgV} {v : Value} (h : DDerivesB (simEnv B) noElse x op args v) :
    DDerivesB (utf8Env B) noElse x op args v :=
  dderivesB_utf8Env hB (fun _ _ _ _ h => h) h

/-! ## Round 6's primitives -/

/-- The float primitives leave `$utf8` uninterpreted. -/
theorem floatCall_utf8 (P : Silmaril.Wasm.Numerics.Profile) (ws : List ArgV) :
    Floats.floatCall P "utf8" ws = none := by
  simp [Floats.floatCall, Floats.floatNames]
/-- The integer primitives leave `$utf8` uninterpreted. -/
theorem intCall_utf8 (ws : List ArgV) : IntNumeric.intCall "utf8" ws = none := by
  unfold IntNumeric.intCall
  split <;> simp_all
/-- **Round 6's concrete primitives leave `$utf8` uninterpreted**, so the monotonicity theorems
apply to `BI P hn host`. -/
theorem BI_utf8 {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) (ws : List ArgV) :
    (Round4Int.BI P hn host).call "utf8" ws = none := by
  simp [Round4Int.BI, Prims.builtins, Prims.call, floatCall_utf8, intCall_utf8]

end Silmaril.Wasm.SpecTec.Sim.Round7
