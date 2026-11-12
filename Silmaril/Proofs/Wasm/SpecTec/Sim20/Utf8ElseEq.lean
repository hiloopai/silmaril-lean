module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.Utf8Else.Agree

/-!
# Away from `x₀`, the two environments of an `EnvExt` pair evaluate alike

`Utf8Mono.extMonoAt` (forward) and `Utf8Else.agreeAt` (converse, `Raw/…/Utf8Else/Agree.lean`)
together: at every fuel, `e₁` and `e₂` give the same answer on terms that never reach `x₀`, in
`DefsOk x₀` scopes, when `e₁` is `Clean` (`evalExp_eq`, `evalArgs_eq`, `evalDoms_eq`,
`premsHold_eq`). Fuel-free: `evalExp_iff`, `evalArgs_iff`, `evalDoms_iff`.

The 2.0 instance: **`clean20T`**, `simEnv20T B` never refers to `$utf8` outside `$utf8`, by one
kernel check over the items of `fixedT20` (`refFree20T`, with `refFreeB`): only `$utf8`, the type
`name` and the grammar `Bname` refer to it. `clean_of_refFree` turns the check into `Clean` for
any script.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Else

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (EvalDoms)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (Ev evExp evArgs evDoms evPrems evRefs evClause evRule
  items le_antisymm' defDefEv relDefEv findDef?_envOfScript_item findRel?_envOfScript_item)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (EnvExt extMonoAt)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T fixedT20)

section Generic

variable {e₁ e₂ : Env} {x₀ : String}

/-- **Expressions evaluate alike**, away from `x₀`. -/
theorem evalExp_eq (hS : EnvExt e₁ e₂ x₀) (hC : Clean e₁ x₀) (n : Nat) {ρ : VarEnv} {e : Exp}
    (hD : DefsOk x₀ ρ) (hG : GoodEvs x₀ (evExp e)) : evalExp n e₂ ρ e = evalExp n e₁ ρ e :=
  le_antisymm' ((agreeAt hS hC n).exp ρ e hD hG) ((extMonoAt hS n).exp ρ e)

/-- **Arguments evaluate alike.** -/
theorem evalArgs_eq (hS : EnvExt e₁ e₂ x₀) (hC : Clean e₁ x₀) (n : Nat) {ρ : VarEnv}
    {as₀ : List Arg} (hD : DefsOk x₀ ρ) (hG : GoodEvs x₀ (evArgs as₀)) :
    evalArgs n e₂ ρ as₀ = evalArgs n e₁ ρ as₀ :=
  le_antisymm' ((agreeAt hS hC n).args ρ as₀ hD hG) ((extMonoAt hS n).args ρ as₀)

/-- **Iteration domains evaluate alike.** -/
theorem evalDoms_eq (hS : EnvExt e₁ e₂ x₀) (hC : Clean e₁ x₀) (n : Nat) {ρ : VarEnv}
    {ds : List Dom} (hD : DefsOk x₀ ρ) (hG : GoodEvs x₀ (evDoms ds)) :
    evalDoms n e₂ ρ ds = evalDoms n e₁ ρ ds :=
  le_antisymm' ((agreeAt hS hC n).doms ρ ds hD hG) ((extMonoAt hS n).doms ρ ds)

/-- **Premises hold alike.** -/
theorem premsHold_eq (hS : EnvExt e₁ e₂ x₀) (hC : Clean e₁ x₀) (n : Nat) {ρ : VarEnv}
    {prs : List Prem} (hD : DefsOk x₀ ρ) (hG : GoodEvs x₀ (evPrems prs)) :
    premsHold n e₂ ρ prs = premsHold n e₁ ρ prs :=
  le_antisymm' ((agreeAt hS hC n).premsHold ρ prs hD hG) ((extMonoAt hS n).premsHold ρ prs)

/-- **Argument patterns match alike.** -/
theorem matchArgs_eq (hS : EnvExt e₁ e₂ x₀) (hC : Clean e₁ x₀) (n : Nat) {ρ : VarEnv}
    {as₀ : List Arg} {ws : List ArgV} (hD : DefsOk x₀ ρ) (hG : GoodEvs x₀ (evArgs as₀))
    (hW : ∀ w ∈ ws, ArgOk x₀ w) : matchArgs n e₂ ρ as₀ ws = matchArgs n e₁ ρ as₀ ws :=
  le_antisymm' ((agreeAt hS hC n).matchArgs ρ as₀ ws hD hG hW)
    ((extMonoAt hS n).matchArgs ρ as₀ ws)

theorem evalExp_iff (hS : EnvExt e₁ e₂ x₀) (hC : Clean e₁ x₀) {ρ : VarEnv} {e : Exp} {v : Value}
    (hD : DefsOk x₀ ρ) (hG : GoodEvs x₀ (evExp e)) : EvalExp e₂ ρ e v ↔ EvalExp e₁ ρ e v := by
  simp only [EvalExp, evalExp_eq hS hC _ hD hG]

theorem evalArgs_iff (hS : EnvExt e₁ e₂ x₀) (hC : Clean e₁ x₀) {ρ : VarEnv} {as₀ : List Arg}
    {ws : List ArgV} (hD : DefsOk x₀ ρ) (hG : GoodEvs x₀ (evArgs as₀)) :
    EvalArgs e₂ ρ as₀ ws ↔ EvalArgs e₁ ρ as₀ ws := by
  simp only [EvalArgs, evalArgs_eq hS hC _ hD hG]

theorem evalDoms_iff (hS : EnvExt e₁ e₂ x₀) (hC : Clean e₁ x₀) {ρ : VarEnv} {ds : List Dom}
    {xvs : List (IL.Id × Value)} (hD : DefsOk x₀ ρ) (hG : GoodEvs x₀ (evDoms ds)) :
    EvalDoms e₂ ρ ds xvs ↔ EvalDoms e₁ ρ ds xvs := by
  simp only [EvalDoms, evalDoms_eq hS hC _ hD hG]

end Generic

/-! ## `Clean` from a check on the items of a script -/

/-- An item allowed by `refFreeB` is free of `x₀`. -/
theorem goodEvs_of_refFree {x₀ : String} {allowed : List (Nat × String)} {s : Script}
    (h : refFreeB x₀ allowed s = true) {k : Nat} {x : String} {l : List Ev}
    (hm : (k, x, l) ∈ items s) (ha : allowed.contains (k, x) = false) : GoodEvs x₀ l := by
  have := List.all_eq_true.1 h _ hm
  simp only [ha, Bool.false_or, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  exact goodEvs_of_not_mem fun hx => by simp at this; exact this hx

/-- **`Clean` from `refFreeB`**, for the environment of a script with any primitives, when the
allowed items name no definition other than `x₀` and no relation. -/
theorem clean_of_refFree {x₀ : String} {allowed : List (Nat × String)} {s : Script}
    (h : refFreeB x₀ allowed s = true)
    (hd : ∀ x, x ≠ x₀ → allowed.contains (1, x) = false)
    (hr : ∀ x, allowed.contains (0, x) = false) (B : Builtins) :
    Clean ((envOfScript s).withBuiltins B) x₀ where
  defs x d hx hf c hc := by
    rw [Env.findDef?_withBuiltins] at hf
    have hG := goodEvs_of_refFree h (findDef?_envOfScript_item hf) (hd x hx)
    simp only [defDefEv, goodEvs_append, goodEvs_flatMap] at hG
    exact hG.2 c hc
  rels x d hf r hr' := by
    rw [Env.findRel?_withBuiltins] at hf
    have hG := goodEvs_of_refFree h (findRel?_envOfScript_item hf) (hr x)
    simp only [relDefEv, goodEvs_append, goodEvs_flatMap] at hG
    exact hG.2 r hr'

set_option maxRecDepth 100000 in
/-- **Only `$utf8`, `name` and `Bname` refer to `$utf8` in `fixedT20`** (kernel). -/
theorem refFree20T : refFreeB "utf8" utf8Users20 fixedT20 = true := by
  decide +kernel

/-- **`simEnv20T B` never refers to `$utf8` outside `$utf8`.** -/
theorem clean20T (B : Builtins) : Clean (simEnv20T B) "utf8" :=
  clean_of_refFree refFree20T (fun x hx => by simp [utf8Users20, hx])
    (fun x => by simp [utf8Users20]) B

end Silmaril.Wasm.SpecTec.Sim20.Utf8Else
