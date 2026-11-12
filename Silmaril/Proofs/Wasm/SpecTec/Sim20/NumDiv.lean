module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.NumericsCore
public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Ops

/-!
# `$idiv_` and `$irem_` in any environment with the shared integer library

`Sim.IntNumeric.callDef_idiv`/`callDef_irem` evaluate the pinned `$idiv_`/`$irem_` in
`simEnv B`. The wasm-2.0 script carries the same two definitions, so the same proofs go through
in any `DivEnv`: the 24 shared definitions (`Equiv.NumEnvCore`), the integer primitives among the
builtins, and `$truncz` without clauses. The proofs are those of `Sim/IntNumeric/DivRem.lean`
and `Sim/IntNumeric/Ops.lean`, with `simEnv B` generalised to `env`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Pure

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV intV bvV optUNV)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric hiding evalExp_truncNat callDef_idiv_u callDef_irem_u
  callDef_irem_s evalExp_signedQ callDef_idiv_s callDef_idiv callDef_irem
open Silmaril.Wasm.Numerics

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {env : Env}

/-- What the `$idiv_`/`$irem_` lemmas need of an environment: the shared integer library
(`Equiv.NumEnvCore`, whose `$idiv_`/`$irem_` are wasm-2.0's and wasm-3.0's alike), the integer
primitives among its builtins, and `$truncz` declared without clauses. -/
structure DivEnv (env : Env) : Prop where
  /-- The shared integer library. -/
  num : Equiv.NumEnvCore env
  /-- The builtins extend `intCall`. -/
  prim : ∀ x ws v, intCall x ws = some v → env.builtins.call x ws = some v
  /-- `$truncz` is a `hint(builtin)`. -/
  truncz : NoClauses env "truncz"

namespace DivEnv

/-- A primitive with no clause, answered by the builtins of a `DivEnv`. -/
theorem callDef_prim (D : DivEnv env) {x : IL.Id} (hx : NoClauses env x)
    {ρ : VarEnv} {args : List Arg} {ws : List ArgV} {v : Value} (hρ : ρ.findDef? x = none)
    (ha : EvalArgs env ρ args ws) (hc : intCall x ws = some v) : CallDef env ρ x args v := by
  obtain ⟨ps, t, hd⟩ := hx
  exact Equiv.ExecBuiltins.callDef_of_builtin_nil hρ hd ha (D.prim _ _ _ hc)

/-- `$truncz(i_1 / i_2)` on the payloads of two bit patterns, with `i_2 ≠ 0`. -/
theorem evalExp_truncNat (D : DivEnv env) {N : Nat} (x y : BitVec N) (hy : y ≠ 0) :
    EvalExp env (scopeDiv N (bvV x) (bvV y))
      (.cvtE (.callE "truncz" [.expA (.binE .divOp (.numT .ratT)
        (.cvtE (.projE (.uncaseE (.varE "i_1") "%") 0) .natT .ratT)
        (.cvtE (.projE (.uncaseE (.varE "i_2") "%") 0) .natT .ratT))]) .intT .natT)
      (natV (x.toNat / y.toNat)) := by
  have hy' : y.toNat ≠ 0 := fun h => hy (BitVec.eq_of_toNat_eq (by simpa using h))
  have hx : EvalExp env (scopeDiv N (bvV x) (bvV y))
      (.cvtE (.projE (.uncaseE (.varE "i_1") "%") 0) .natT .ratT) (.num (.ratN (x.toNat : ℚ))) :=
    evalExp_cvtNum (Equiv.evalExp_uNV_payload (by simp [scopeDiv])) rfl
  have hyq : EvalExp env (scopeDiv N (bvV x) (bvV y))
      (.cvtE (.projE (.uncaseE (.varE "i_2") "%") 0) .natT .ratT) (.num (.ratN (y.toNat : ℚ))) :=
    evalExp_cvtNum (Equiv.evalExp_uNV_payload (by simp [scopeDiv])) rfl
  have hq : EvalExp env (scopeDiv N (bvV x) (bvV y))
      (.binE .divOp (.numT .ratT) (.cvtE (.projE (.uncaseE (.varE "i_1") "%") 0) .natT .ratT)
        (.cvtE (.projE (.uncaseE (.varE "i_2") "%") 0) .natT .ratT))
      (.num (.ratN ((x.toNat : ℚ) / (y.toNat : ℚ)))) :=
    evalExp_binNum hx hyq (by simp [Num.bin, hy'])
  have ht : CallDef env (scopeDiv N (bvV x) (bvV y)) "truncz"
      [.expA (.binE .divOp (.numT .ratT) (.cvtE (.projE (.uncaseE (.varE "i_1") "%") 0) .natT .ratT)
        (.cvtE (.projE (.uncaseE (.varE "i_2") "%") 0) .natT .ratT))]
      (.num (.intN ((x.toNat / y.toNat : ℕ) : ℤ))) := by
    refine D.callDef_prim D.truncz rfl (Equiv.evalArgs_cons hq Equiv.evalArgs_nil) ?_
    simp [intCall, truncQ_natDiv]
  exact evalExp_cvtNum (evalExp_callE_iff.2 ht)
    (by simp only [Num.cvt, Int.natCast_nonneg, ite_true, Int.toNat_natCast])

/-- **`$idiv_(N, U, i_1, i_2)`** at `i_2 ≠ 0`: `IntegerN.idiv_`, through `$truncz`. -/
theorem callDef_idiv_u (D : DivEnv env) {ρ : VarEnv} {args : List Arg} {N : Nat}
    (x y : BitVec N) (hy : y ≠ 0) (hρ : ρ.findDef? "idiv_" = none)
    (ha : EvalArgs env ρ args
      [.val (natV N), .val (Equiv.sxV .unsigned), .val (bvV x), .val (bvV y)]) :
    CallDef env ρ "idiv_" args (optUNV (idiv_ N .unsigned x y)) := by
  have hy' : y.toNat ≠ 0 := fun h => hy (BitVec.eq_of_toNat_eq (by simpa using h))
  have hlt : x.toNat / y.toNat < 2 ^ N := lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt
  have hv : optUNV (idiv_ N .unsigned x y) =
      .opt (some (.case "%" (.tuple [natV (x.toNat / y.toNat)]))) := by
    simp [optUNV, idiv_, hy', bvV_ofNat hlt]
  rw [hv]
  refine callDef_of_tryClauses hρ D.num.idivD ha ?_
  refine tryClauses_skip_match (matchArgs_zeroSkip hy) ?_
  exact tryClauses_hit matchArgs_divGen premsHold_nil (evalExp_optE_some_iff.2
    ⟨_, Equiv.evalExp_case_tup_one (D.evalExp_truncNat x y hy), rfl⟩)

/-- **`$irem_(N, U, i_1, i_2)`** at `i_2 ≠ 0`: `IntegerN.irem_`, through `$truncz`. -/
theorem callDef_irem_u (D : DivEnv env) {ρ : VarEnv} {args : List Arg} {N : Nat}
    (x y : BitVec N) (hy : y ≠ 0) (hρ : ρ.findDef? "irem_" = none)
    (ha : EvalArgs env ρ args
      [.val (natV N), .val (Equiv.sxV .unsigned), .val (bvV x), .val (bvV y)]) :
    CallDef env ρ "irem_" args (optUNV (irem_ N .unsigned x y)) := by
  have hy' : y.toNat ≠ 0 := fun h => hy (BitVec.eq_of_toNat_eq (by simpa using h))
  have hle : y.toNat * (x.toNat / y.toNat) ≤ x.toNat := Nat.mul_div_le _ _
  have hlt : x.toNat - y.toNat * (x.toNat / y.toNat) < 2 ^ N :=
    lt_of_le_of_lt (Nat.sub_le _ _) x.isLt
  have hv : optUNV (irem_ N .unsigned x y) =
      .opt (some (.case "%" (.tuple [natV (x.toNat - y.toNat * (x.toNat / y.toNat))]))) := by
    simp [optUNV, irem_, hy', bvV_ofNat hlt]
  rw [hv]
  refine callDef_of_tryClauses hρ D.num.iremD ha ?_
  refine tryClauses_skip_match (matchArgs_zeroSkip hy) ?_
  have hmul : EvalExp env (scopeDiv N (bvV x) (bvV y))
      (.binE .mulOp (.numT .natT) (.projE (.uncaseE (.varE "i_2") "%") 0)
        (.cvtE (.callE "truncz" [.expA (.binE .divOp (.numT .ratT)
          (.cvtE (.projE (.uncaseE (.varE "i_1") "%") 0) .natT .ratT)
          (.cvtE (.projE (.uncaseE (.varE "i_2") "%") 0) .natT .ratT))]) .intT .natT))
      (natV (y.toNat * (x.toNat / y.toNat))) :=
    evalExp_binNum (Equiv.evalExp_uNV_payload (by simp [scopeDiv])) (D.evalExp_truncNat x y hy)
      rfl
  have hsub : EvalExp env (scopeDiv N (bvV x) (bvV y))
      (.binE .subOp (.numT .intT) (.cvtE (.projE (.uncaseE (.varE "i_1") "%") 0) .natT .intT)
        (.cvtE (.binE .mulOp (.numT .natT) (.projE (.uncaseE (.varE "i_2") "%") 0)
          (.cvtE (.callE "truncz" [.expA (.binE .divOp (.numT .ratT)
            (.cvtE (.projE (.uncaseE (.varE "i_1") "%") 0) .natT .ratT)
            (.cvtE (.projE (.uncaseE (.varE "i_2") "%") 0) .natT .ratT))]) .intT .natT))
          .natT .intT))
      (intV ((x.toNat : ℤ) - ((y.toNat * (x.toNat / y.toNat) : ℕ) : ℤ))) :=
    evalExp_binNum (Equiv.evalExp_toInt (Equiv.evalExp_uNV_payload (by simp [scopeDiv])))
      (Equiv.evalExp_toInt hmul) rfl
  have hnat := Equiv.evalExp_toNat (by omega) hsub
  rw [show ((x.toNat : ℤ) - ((y.toNat * (x.toNat / y.toNat) : ℕ) : ℤ)).toNat =
    x.toNat - y.toNat * (x.toNat / y.toNat) by omega] at hnat
  exact tryClauses_hit matchArgs_divGen premsHold_nil (evalExp_optE_some_iff.2
    ⟨_, Equiv.evalExp_case_tup_one hnat, rfl⟩)

/-- **`$irem_(N, S, i_1, i_2)`** at `i_2 ≠ 0`: the script's clause cannot be evaluated, every
clause of `$irem_` definitely fails, and `callDef` takes `B`'s answer, `IntegerN.irem_`. -/
theorem callDef_irem_s (D : DivEnv env) {ρ : VarEnv} {args : List Arg} {N : Nat}
    (x y : BitVec N) (hy : y ≠ 0) (hρ : ρ.findDef? "irem_" = none)
    (ha : EvalArgs env ρ args
      [.val (natV N), .val (Equiv.sxV .signed), .val (bvV x), .val (bvV y)]) :
    CallDef env ρ "irem_" args (optUNV (irem_ N .signed x y)) := by
  have hb : env.builtins.call "irem_"
      [.val (natV N), .val (Equiv.sxV .signed), .val (bvV x), .val (bvV y)] =
      some (optUNV (irem_ N .signed x y)) :=
    D.prim _ _ _ (by simp [intCall, remBits, natV, asSx?, Equiv.sxV, optUNV])
  have hu : Equiv.ExecNumeric.TryClausesUndef env Equiv.iremDef.2.2
      [.val (natV N), .val (Equiv.sxV .signed), .val (bvV x), .val (bvV y)] := by
    refine tryClausesUndef_skip_match (matchArgs_sxSkip (by decide)) ?_
    refine tryClausesUndef_skip_match (matchArgs_sxSkip (by decide)) ?_
    refine tryClausesUndef_skip_match (matchArgs_zeroSkip hy) ?_
    exact tryClausesUndef_skip_prem matchArgs_divGen (premsUndef_unboundAnd (by simp [scopeDiv]))
      tryClausesUndef_nil
  exact Equiv.ExecNumeric.callDef_iff.2 ⟨_, _, _, _, ha, by rw [hρ]; exact
    D.num.iremD, Or.inr ⟨hu, by rw [hρ]; exact hb⟩⟩

/-- `$signed_(N, i!%.0)`, read as a rational, for a variable holding a bit pattern. -/
theorem evalExp_signedQ (D : DivEnv env) {ρ : VarEnv} {N : Nat} (hN : 0 < N) {x : BitVec N}
    {i : IL.Id}
    (hNv : ρ.findVal? "N" = some (natV N)) (hi : ρ.findVal? i = some (bvV x))
    (hρ : ρ.findDef? "signed_" = none) :
    EvalExp env ρ (.cvtE (.callE "signed_" [.expA (.varE "N"),
        .expA (.projE (.uncaseE (.varE i) "%") 0)]) .intT .ratT)
      (.num (.ratN ((signed_ N x.toNat : ℤ) : ℚ))) :=
  evalExp_cvtNum (evalExp_callE_iff.2 (D.num.callDef_signed hρ
    (Equiv.evalArgs_cons (evalExp_varE_iff.2 hNv)
      (Equiv.evalArgs_cons (Equiv.evalExp_uNV_payload hi) Equiv.evalArgs_nil)) hN x.isLt)) rfl

/-- **`$idiv_(N, S, i_1, i_2)`** at `i_2 ≠ 0`: `IntegerN.idiv_`. The overflow clause fires
exactly at `-2^(N-1) / -1`; otherwise the general clause computes through `$truncz` and
`$inv_signed_`. -/
theorem callDef_idiv_s (D : DivEnv env) {ρ : VarEnv} {args : List Arg} {N : Nat} (hN : 0 < N)
    (x y : BitVec N) (hy : y ≠ 0) (hρ : ρ.findDef? "idiv_" = none)
    (ha : EvalArgs env ρ args
      [.val (natV N), .val (Equiv.sxV .signed), .val (bvV x), .val (bvV y)]) :
    CallDef env ρ "idiv_" args (optUNV (idiv_ N .signed x y)) := by
  have hy' : y.toNat ≠ 0 := fun h => hy (BitVec.eq_of_toNat_eq (by simpa using h))
  have hj2 : signed_ N y.toNat ≠ 0 := by
    rw [signed_toNat]
    intro h
    exact hy (BitVec.toInt_inj.1 (by rw [h]; simp))
  obtain ⟨hx₁, hx₂⟩ := Equiv.signed_bounds hN x.isLt
  have hM : ((2 ^ (N - 1) : ℕ) : ℤ) = 2 ^ (N - 1) := by push_cast; rfl
  have hov := overflow_iff (2 ^ (N - 1)) (signed_ N x.toNat) (signed_ N y.toNat)
    (by rw [hM]; exact hx₁) (by rw [hM]; exact hx₂) hj2
  set σ := scopeDiv N (bvV x) (bvV y) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by simp [hσ, scopeDiv]
  have hq : EvalExp env σ
      (.binE .divOp (.numT .ratT)
        (.cvtE (.callE "signed_" [.expA (.varE "N"), .expA (.projE (.uncaseE (.varE "i_1") "%") 0)])
          .intT .ratT)
        (.cvtE (.callE "signed_" [.expA (.varE "N"), .expA (.projE (.uncaseE (.varE "i_2") "%") 0)])
          .intT .ratT))
      (.num (.ratN (((signed_ N x.toNat : ℤ) : ℚ) / ((signed_ N y.toNat : ℤ) : ℚ)))) :=
    evalExp_binNum (D.evalExp_signedQ (x := x) (i := "i_1") hN hNv (by simp [hσ, scopeDiv]) rfl)
      (D.evalExp_signedQ (x := y) (i := "i_2") hN hNv (by simp [hσ, scopeDiv]) rfl)
      (by simp [Num.bin, hj2])
  have hpow : EvalExp env σ
      (.cvtE (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.cvtE (.binE .subOp (.numT .intT)
        (.cvtE (.varE "N") .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT))
        .natT .ratT)
      (.num (.ratN (((2 ^ (N - 1) : ℕ) : ℚ)))) :=
    evalExp_cvtNum (Equiv.evalExp_twoPowPred hN hNv) rfl
  have hcmp := evalExp_eq (t := .boolT) hq hpow
  rw [ratV_beq] at hcmp
  refine callDef_of_tryClauses hρ D.num.idivD ha ?_
  refine tryClauses_skip_match (matchArgs_sxSkip (by decide)) ?_
  refine tryClauses_skip_match (matchArgs_sxSkip (by decide)) ?_
  refine tryClauses_skip_match (matchArgs_zeroSkip hy) ?_
  by_cases hq₀ : ((signed_ N x.toNat : ℤ) : ℚ) / ((signed_ N y.toNat : ℤ) : ℚ) =
      ((2 ^ (N - 1) : ℕ) : ℚ)
  · show TryClauses env _ _ (optUNV (idiv_ N .signed x y))
    have hnone : idiv_ N .signed x y = none := by
      have ht := hov.1 hq₀
      rw [hM] at ht
      simp [idiv_, hy', ht]
    rw [hnone]
    show TryClauses env _ _ (optUNV none)
    rw [decide_eq_true hq₀] at hcmp
    exact tryClauses_hit matchArgs_divGen
      (Equiv.Validation.premsHold_cons_iff.2 ⟨_, Equiv.Validation.premHolds_if_iff.2 ⟨rfl, hcmp⟩,
        Equiv.Validation.premsHold_nil_iff.2 rfl⟩)
      (evalExp_optE_none_iff.2 rfl)
  · show TryClauses env _ _ (optUNV (idiv_ N .signed x y))
    rw [decide_eq_false hq₀] at hcmp
    have ht : (signed_ N x.toNat).tdiv (signed_ N y.toNat) ≠ 2 ^ (N - 1) := by
      rw [← hM]; exact fun h => hq₀ (hov.2 h)
    have hab : ((signed_ N x.toNat).tdiv (signed_ N y.toNat)).natAbs ≤ 2 ^ (N - 1) := by
      have h1 := Int.natAbs_tdiv (signed_ N x.toNat) (signed_ N y.toNat)
      have h2 : (signed_ N x.toNat).natAbs ≤ 2 ^ (N - 1) := by
        have : ((2 ^ (N - 1) : ℕ) : ℤ) = 2 ^ (N - 1) := hM
        omega
      rw [h1]; exact le_trans (Nat.div_le_self _ _) h2
    have hr₁ : -2 ^ (N - 1) ≤ (signed_ N x.toNat).tdiv (signed_ N y.toNat) := by
      have : ((2 ^ (N - 1) : ℕ) : ℤ) = 2 ^ (N - 1) := hM
      omega
    have hr₂ : (signed_ N x.toNat).tdiv (signed_ N y.toNat) < 2 ^ (N - 1) := by
      have : ((2 ^ (N - 1) : ℕ) : ℤ) = 2 ^ (N - 1) := hM
      omega
    have hsome : optUNV (idiv_ N .signed x y) = .opt (some (.case "%" (.tuple
        [natV (invSigned_ N ((signed_ N x.toNat).tdiv (signed_ N y.toNat)))]))) := by
      simp [optUNV, idiv_, hy', ht, bvV_ofNat (Equiv.invSigned_lt _ _)]
    rw [hsome]
    refine tryClauses_skip_prem matchArgs_divGen (premsUndef_ifPr hcmp) ?_
    have htr : CallDef env σ "truncz" [.expA (.binE .divOp (.numT .ratT)
        (.cvtE (.callE "signed_" [.expA (.varE "N"), .expA (.projE (.uncaseE (.varE "i_1") "%") 0)])
          .intT .ratT)
        (.cvtE (.callE "signed_" [.expA (.varE "N"), .expA (.projE (.uncaseE (.varE "i_2") "%") 0)])
          .intT .ratT))]
        (intV ((signed_ N x.toNat).tdiv (signed_ N y.toNat))) := by
      refine D.callDef_prim D.truncz rfl (Equiv.evalArgs_cons hq Equiv.evalArgs_nil) ?_
      simp [intCall, truncQ_intDiv _ _ hj2, intV]
    have hinv := D.num.callDef_invSigned (ρ := σ) rfl
      (Equiv.evalArgs_cons (evalExp_varE_iff.2 hNv)
        (Equiv.evalArgs_cons (evalExp_callE_iff.2 htr) Equiv.evalArgs_nil)) hN hr₁ hr₂
    exact tryClauses_hit matchArgs_divGen premsHold_nil (evalExp_optE_some_iff.2
      ⟨_, Equiv.evalExp_case_tup_one (evalExp_callE_iff.2 hinv), rfl⟩)
/-- `$idiv_` at any divisor. -/
theorem callDef_idiv {env : Env} (D : DivEnv env) (t : Silmaril.Wasm.IntType)
    (s : Silmaril.Wasm.Signedness) (x y : BitVec t.width) {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "idiv_" = none)
    (ha : EvalArgs env ρ args
      [.val (natV t.width), .val (Equiv.sxV s), .val (bvV x), .val (bvV y)]) :
    CallDef env ρ "idiv_" args (optUNV (idiv_ t.width s x y)) := by
  by_cases hy : y = 0
  · subst hy
    exact D.num.callDef_idiv_zero hρ ha
  · cases s with
    | unsigned => exact D.callDef_idiv_u x y hy hρ ha
    | signed => exact D.callDef_idiv_s (by cases t <;> decide) x y hy hρ ha

/-- `$irem_` at any divisor. -/
theorem callDef_irem {env : Env} (D : DivEnv env) (t : Silmaril.Wasm.IntType)
    (s : Silmaril.Wasm.Signedness) (x y : BitVec t.width) {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "irem_" = none)
    (ha : EvalArgs env ρ args
      [.val (natV t.width), .val (Equiv.sxV s), .val (bvV x), .val (bvV y)]) :
    CallDef env ρ "irem_" args (optUNV (irem_ t.width s x y)) := by
  by_cases hy : y = 0
  · subst hy
    exact D.num.callDef_irem_zero hρ ha
  · cases s with
    | unsigned => exact D.callDef_irem_u x y hy hρ ha
    | signed => exact D.callDef_irem_s x y hy hρ ha

end DivEnv

end Silmaril.Wasm.SpecTec.Sim20.Pure
