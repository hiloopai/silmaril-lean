module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.BackwardParam

/-!
# A finding for the float family, now fixed: `num_(Fnn)` held no float

The type family `num_` has two instances, `num_(Inn) = iN($sizenn(Inn))` and
`num_(Fnn) = fN($sizenn(Fnn))`, selected by the argument patterns `Inn` and `Fnn`, which the IL
writes as `SubE` patterns. In round 1, `Sem.matchArg` stripped a `SubE` without testing the
subtype, so the *first* instance matched every argument, `F32` and `F64` included, and
`hasTypInsts` committed to it: `num_(F32)` was read as `iN(32)`, whose only case is `%`, and no
float was typed (round 1's `not_hasTyp_num_float`, proved here at commit `0236b9f97`).

The typing track fixed the ported semantics (`Sem.argSubOk`: a top-level `SubE` argument pattern
tests its subtype when that is a closed variant). `Typing.hasTyp_num_float` now proves the
positive statement and `Typing.not_forall_not_hasTyp_num_float` refutes the old one. What remains
here are the two inversion lemmas the old proof used.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.IntNumeric

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-- A match at some fuel agrees with every successful match. -/
theorem matchArgs_det {env : Env} {pats : List Arg} {ws : List ArgV} {σ σ' : VarEnv} {n : Nat}
    (hm : MatchArgs env VarEnv.empty pats ws σ)
    (h : matchArgs n env VarEnv.empty pats ws = .ok σ') : σ' = σ := by
  obtain ⟨n₁, h₁⟩ := hm
  have e₁ : matchArgs (max n n₁) env VarEnv.empty pats ws = .ok σ' :=
    matchArgs_ok_of_le (Nat.le_max_left n n₁) h
  have e₂ : matchArgs (max n n₁) env VarEnv.empty pats ws = .ok σ :=
    matchArgs_ok_of_le (Nat.le_max_right n n₁) h₁
  rw [e₁] at e₂
  exact Except.ok.inj e₂

/-- A successful match never definitely fails at another fuel. -/
theorem matchArgs_not_undef {env : Env} {pats : List Arg} {ws : List ArgV} {σ : VarEnv} {n : Nat}
    (hm : MatchArgs env VarEnv.empty pats ws σ) :
    matchArgs n env VarEnv.empty pats ws ≠ .error .undef := by
  intro h
  obtain ⟨n₁, h₁⟩ := hm
  have e₁ := matchArgs_undef_of_le (Nat.le_max_left n n₁) h
  have e₂ := matchArgs_ok_of_le (Nat.le_max_right n n₁) h₁
  rw [e₁] at e₂
  cases e₂

/-- When the head instance's patterns match, a type family is that instance: the search does not
fall through on a failing definition (`eval.ml:142-143`). -/
theorem hasTypInsts_head_inv {env : Env} {qs : List Param} {pats : List Arg} {dt : DefTyp}
    {is : List Inst} {ws : List ArgV} {v : Value} {σ : VarEnv}
    (hm : MatchArgs env VarEnv.empty pats ws σ)
    (h : HasTypInsts env (.instD qs pats dt :: is) ws v) :
    HasTypDef env σ dt v := by
  obtain ⟨n, h⟩ := h
  cases n with
  | zero => rw [hasTypInsts_zero] at h; simp at h
  | succ n =>
      rw [hasTypInsts_succ_cons] at h
      cases hres : matchArgs n env VarEnv.empty pats ws with
      | ok σ' =>
          rw [hres, Res.elimUndef_ok, matchArgs_det hm hres] at h
          exact ⟨n, h⟩
      | error e =>
          cases e with
          | undef => exact absurd hres (matchArgs_not_undef hm)
          | outOfFuel => rw [hres] at h; simp [Res.elimUndef] at h

/-- `uN(N)` holds only `%`-injections. -/
theorem uN_case {ρ : VarEnv} {e : Exp} {v : Value}
    (h : HasTyp (simEnv B) ρ (.varT "uN" [.expA e]) v) : ∃ w, v = .case "%" w := by
  obtain ⟨ps, qs, htd⟩ := findTyp_uN (B := B)
  obtain ⟨td, ws, htd', hargs, hi⟩ := (hasTyp_varT_global_iff (localTyp?_cons _ _ _)).1 h
  rw [htd] at htd'
  cases htd'
  obtain ⟨u, -, rfl⟩ := evalArgs_expA_iff.1 hargs
  have hd := hasTypInsts_head_inv (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
    matchArgs_nil) hi
  obtain ⟨op, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 hd
  by_cases hop : op = "%"
  · exact ⟨w, by rw [hop]⟩
  · exact absurd hc (not_hasTypCase_of_findCase_none (by simp [findCase, instCases,
      Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d22, Ne.symm hop]))

end Silmaril.Wasm.SpecTec.Sim.IntNumeric
