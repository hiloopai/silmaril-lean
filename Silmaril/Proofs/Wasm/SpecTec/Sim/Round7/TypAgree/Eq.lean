module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.TypAgree.Agree
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Utf8.MonoDerive

/-!
# Round 7: `simEnv B` and `utf8Env B` type alike away from `name`

Pass 5's `Round7.envMonoTypAt` says `utf8Env B` types at least what `simEnv B` types;
`Round7.TypAgree.tAgreeAt_A` and `tAgreeAt_B` say the converse on checked types. Together, for
primitives `B` that leave `$utf8` uninterpreted (as round 6's `BI` does, `Round7.BI_utf8`):

* at every type over `tyA` (no path to `name`), the two environments type every value alike
  (`hasTyp_utf8Env_eq_A`, `hasTyp_utf8Env_iff_A`);
* at every type over `tyB` (every reachable type except `name` and `exportinst`), they type every
  `ExpFree` value alike (`hasTyp_utf8Env_eq_B`, `hasTyp_utf8Env_iff_B`), in particular
  configurations (`hasTyp_config_iff`);
* so a rule's quantifiers, if their types are over `tyB` and their values `ExpFree`, are well
  typed in one environment exactly when they are in the other (`quantsOk_utf8Env_iff`).

This is the typing half of `Round7.Task.envAgreeNE`. Without `ExpFree` the statement is false:
`Round7.exportinst_erratum` is an export instance typed in `utf8Env B` and not in `simEnv B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.Script

variable {B : Builtins}

/-- **Types over `tyA` agree at every value**, at every fuel. -/
theorem hasTyp_utf8Env_eq_A (hB : ∀ ws, B.call "utf8" ws = none) (n : Nat) {ρ : VarEnv}
    {t : Typ} (v : Value) (hD : DefsOk ρ) (hT : TypsOk tyA ρ) (ht : tyOk tyA tyA t = true) :
    hasTyp n (utf8Env B) ρ t v = hasTyp n (simEnv B) ρ t v :=
  le_antisymm' ((tAgreeAt_A B n).typ ρ t v hD hT ht trivial) ((envMonoTypAt B hB n).typ ρ t v)

/-- **Types over `tyB` agree at `ExpFree` values**, at every fuel. -/
theorem hasTyp_utf8Env_eq_B (hB : ∀ ws, B.call "utf8" ws = none) (n : Nat) {ρ : VarEnv}
    {t : Typ} {v : Value} (hD : DefsOk ρ) (hT : TypsOk tyA ρ) (ht : tyOk tyA tyB t = true)
    (hv : ExpFree v) : hasTyp n (utf8Env B) ρ t v = hasTyp n (simEnv B) ρ t v :=
  le_antisymm' ((tAgreeAt_B B n).typ ρ t v hD hT ht hv) ((envMonoTypAt B hB n).typ ρ t v)

theorem hasTyp_utf8Env_iff_A (hB : ∀ ws, B.call "utf8" ws = none) {ρ : VarEnv} {t : Typ}
    (v : Value) (hD : DefsOk ρ) (hT : TypsOk tyA ρ) (ht : tyOk tyA tyA t = true) :
    HasTyp (utf8Env B) ρ t v ↔ HasTyp (simEnv B) ρ t v := by
  simp only [HasTyp, hasTyp_utf8Env_eq_A hB _ v hD hT ht]

theorem hasTyp_utf8Env_iff_B (hB : ∀ ws, B.call "utf8" ws = none) {ρ : VarEnv} {t : Typ}
    {v : Value} (hD : DefsOk ρ) (hT : TypsOk tyA ρ) (ht : tyOk tyA tyB t = true)
    (hv : ExpFree v) : HasTyp (utf8Env B) ρ t v ↔ HasTyp (simEnv B) ρ t v := by
  simp only [HasTyp, hasTyp_utf8Env_eq_B hB _ hD hT ht hv]

/-- **Configurations are typed alike** at `ExpFree` values, in any scope without type or
definition variables of its own. -/
theorem hasTyp_config_iff (hB : ∀ ws, B.call "utf8" ws = none) {ρ : VarEnv} {v : Value}
    (hD : DefsOk ρ) (hT : TypsOk tyA ρ) (hv : ExpFree v) :
    HasTyp (utf8Env B) ρ (.varT "config" []) v ↔ HasTyp (simEnv B) ρ (.varT "config" []) v :=
  hasTyp_utf8Env_iff_B hB hD hT (by decide) hv

/-- **Quantifiers are typed alike**, when their types are over `tyB` and their values are
`ExpFree`. -/
theorem quantsOk_utf8Env_iff (hB : ∀ ws, B.call "utf8" ws = none) {ρ : VarEnv} {qs : List Param}
    (hD : DefsOk ρ) (hT : TypsOk tyA ρ)
    (hq : ∀ x t, Param.expP x t ∈ qs → tyOk tyA tyB t = true)
    (hv : ∀ x t w, Param.expP x t ∈ qs → ρ.findVal? x = some w → ExpFree w) :
    QuantsOk (utf8Env B) ρ qs ↔ QuantsOk (simEnv B) ρ qs := by
  constructor
  · intro h x t hx
    obtain ⟨w, hw, ht⟩ := h x t hx
    exact ⟨w, hw, (hasTyp_utf8Env_iff_B hB hD hT (hq x t hx) (hv x t w hx hw)).1 ht⟩
  · intro h x t hx
    obtain ⟨w, hw, ht⟩ := h x t hx
    exact ⟨w, hw, (hasTyp_utf8Env_iff_B hB hD hT (hq x t hx) (hv x t w hx hw)).2 ht⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree
