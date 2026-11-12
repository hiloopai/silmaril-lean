module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.Numerics

/-!
# The integer library wasm-2.0 shares with wasm-3.0

`Equiv.NumEnv` asks for all 25 definitions of the wasm-3.0 numerics group, among them
`$iextend_`, which wasm-2.0 lacks (its `EXTEND` calls the builtin `$extend__`). `NumEnvCore` is
the other 24, which the wasm-2.0 script contains verbatim, and the lemmas below are the
`Equiv.callDef_*` lemmas the 2.0 dispatchers and the `$idiv_`/`$irem_` proofs need, restated
over `NumEnvCore` (`NumEnvCore.callDef_iadd` …). Their proofs are copied unchanged from
`Equiv/Numerics.lean`, which only ever reads the fields kept here.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv

open Silmaril.SpecTec.IL Silmaril.SpecTec.Sem

/-- The numerics group without `$iextend_`: the 24 definitions wasm-2.0 shares with wasm-3.0
verbatim (wasm-2.0 has no `$iextend_`; its `EXTEND` calls the builtin `$extend__`). Every
`Equiv.callDef_*` lemma except `callDef_iextend` reads only these fields. -/
structure NumEnvCore (env : Env) : Prop where
  /-- `$bool`. -/
  boolD : env.findDef? "bool" = some boolDef
  /-- `$signed_`. -/
  signedD : env.findDef? "signed_" = some signedDef
  /-- `$inv_signed_`. -/
  invSignedD : env.findDef? "inv_signed_" = some invSignedDef
  /-- `$sat_u_`. -/
  satUD : env.findDef? "sat_u_" = some satUDef
  /-- `$sat_s_`. -/
  satSD : env.findDef? "sat_s_" = some satSDef
  /-- `$ineg_`. -/
  inegD : env.findDef? "ineg_" = some inegDef
  /-- `$iabs_`. -/
  iabsD : env.findDef? "iabs_" = some iabsDef
  /-- `$iadd_`. -/
  iaddD : env.findDef? "iadd_" = some iaddDef
  /-- `$isub_`. -/
  isubD : env.findDef? "isub_" = some isubDef
  /-- `$imul_`. -/
  imulD : env.findDef? "imul_" = some imulDef
  /-- `$imin_`. -/
  iminD : env.findDef? "imin_" = some iminDef
  /-- `$imax_`. -/
  imaxD : env.findDef? "imax_" = some imaxDef
  /-- `$iadd_sat_`. -/
  iaddSatD : env.findDef? "iadd_sat_" = some iaddSatDef
  /-- `$isub_sat_`. -/
  isubSatD : env.findDef? "isub_sat_" = some isubSatDef
  /-- `$ieqz_`. -/
  ieqzD : env.findDef? "ieqz_" = some ieqzDef
  /-- `$inez_`. -/
  inezD : env.findDef? "inez_" = some inezDef
  /-- `$ieq_`. -/
  ieqD : env.findDef? "ieq_" = some ieqDef
  /-- `$ine_`. -/
  ineD : env.findDef? "ine_" = some ineDef
  /-- `$ilt_`. -/
  iltD : env.findDef? "ilt_" = some iltDef
  /-- `$igt_`. -/
  igtD : env.findDef? "igt_" = some igtDef
  /-- `$ile_`. -/
  ileD : env.findDef? "ile_" = some ileDef
  /-- `$ige_`. -/
  igeD : env.findDef? "ige_" = some igeDef
  /-- `$idiv_`. -/
  idivD : env.findDef? "idiv_" = some idivDef
  /-- `$irem_`. -/
  iremD : env.findDef? "irem_" = some iremDef

/-- A full `NumEnv` has the 24 shared definitions. -/
theorem NumEnv.core {env : Env} (h : NumEnv env) : NumEnvCore env :=
  ⟨h.boolD, h.signedD, h.invSignedD, h.satUD, h.satSD, h.inegD, h.iabsD, h.iaddD, h.isubD, h.imulD,
    h.iminD, h.imaxD, h.iaddSatD, h.isubSatD, h.ieqzD, h.inezD, h.ieqD, h.ineD, h.iltD, h.igtD,
    h.ileD, h.igeD, h.idivD, h.iremD⟩

namespace NumEnvCore

/-- **`$bool`** agrees with `Numerics.bool_`. -/
theorem callDef_bool {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "bool" = none) {args : List Arg} {b : Bool}
    (ha : EvalArgs env ρ args [.val (.bool b)]) :
    CallDef env ρ "bool" args (natV (Wasm.Numerics.bool_ b)) := by
  refine callDef_of_tryClauses hρ h.boolD ha ?_
  have hit : ∀ c : Bool, TryClauses env [.defD [] [.expA (.boolE c)]
      (.numE (.natN (Wasm.Numerics.bool_ c))) []] [.val (.bool c)]
      (natV (Wasm.Numerics.bool_ c)) := fun c =>
    tryClauses_hit (matchArgs_cons (matchArg_expA matchExp_boolE) matchArgs_nil)
      premsHold_nil evalExp_num
  cases b
  · exact tryClauses_hit (matchArgs_cons (matchArg_expA matchExp_boolE) matchArgs_nil)
      premsHold_nil evalExp_num
  · exact tryClauses_skip_match
      (matchArgs_cons_undef (matchArg_expA_undef
        (matchExp_boolE_undef (b := false) (v := .bool true) (by simp))))
      (hit true)

/-- `$bool` applied to a comparison, the shape every test and relation uses. -/
theorem evalExp_boolCall {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "bool" = none) {e : Exp} {b : Bool} (he : EvalExp env ρ e (.bool b)) :
    EvalExp env ρ (.callE "bool" [.expA e]) (natV (Wasm.Numerics.bool_ b)) :=
  evalExp_callE_iff.2 (h.callDef_bool hρ (evalArgs_cons he evalArgs_nil))

/-- **`$signed_`** agrees with `Numerics.signed_` on the whole domain the IL
definition covers: `0 < N` (below which `2^(N-1)` is stuck) and `i < 2^N`
(outside which no clause applies). -/
theorem callDef_signed {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "signed_" = none) {args : List Arg} {N i : Nat}
    (ha : EvalArgs env ρ args [.val (natV N), .val (natV i)]) (hN : 0 < N)
    (hi : i < 2 ^ N) : CallDef env ρ "signed_" args (intV (Wasm.Numerics.signed_ N i)) := by
  refine callDef_of_tryClauses hρ h.signedD ha ?_
  set σ : VarEnv := (VarEnv.empty.bindVal "N" (natV N)).bindVal "i" (natV i) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have hiv : σ.findVal? "i" = some (natV i) := by rw [hσ]; rfl
  have hmatch : MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.varE "i")] [.val (natV N), .val (natV i)] σ := by
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
  have hpow := evalExp_twoPowPred (env := env) hN hNv
  by_cases hlt : i < 2 ^ (N - 1)
  · refine tryClauses_hit hmatch (premsHold_ifPr (evalExp_cmpNum (op := .ltOp)
      (t := .numT .natT) (evalExp_var hiv) hpow (by simp [Num.cmp, hlt]))) ?_
    have := evalExp_toInt (env := env) (evalExp_var hiv)
    simpa [Wasm.Numerics.signed_, hlt] using this
  · refine tryClauses_skip_prem hmatch (premsUndef_ifPr (evalExp_cmpNum (op := .ltOp)
      (t := .numT .natT) (evalExp_var hiv) hpow (by simp [Num.cmp, hlt]))) ?_
    refine tryClauses_hit hmatch (premsHold_ifPr ?_) ?_
    · exact evalExp_and (b₁ := true) (b₂ := true)
        (evalExp_cmpNum (op := .leOp) (t := .numT .natT) hpow (evalExp_var hiv)
          (by simp [Num.cmp]; omega))
        (evalExp_cmpNum (op := .ltOp) (t := .numT .natT) (evalExp_var hiv)
          (evalExp_twoPow hNv) (by simp [Num.cmp, hi]))
    · have := evalExp_binNum (env := env) (op := .subOp) (t := .numT .intT)
        (evalExp_toInt (evalExp_var hiv)) (evalExp_toInt (evalExp_twoPow hNv)) rfl
      simpa [Wasm.Numerics.signed_, hlt, intV] using this

/-- **`$inv_signed_`** agrees with `Numerics.invSigned_` on the IL definition's
domain, `-2^(N-1) ≤ j < 2^(N-1)`. -/
theorem callDef_invSigned {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "inv_signed_" = none) {args : List Arg} {N : Nat} {j : Int}
    (ha : EvalArgs env ρ args [.val (natV N), .val (intV j)]) (hN : 0 < N)
    (h₁ : -2 ^ (N - 1) ≤ j) (h₂ : j < 2 ^ (N - 1)) :
    CallDef env ρ "inv_signed_" args (natV (Wasm.Numerics.invSigned_ N j)) := by
  refine callDef_of_tryClauses hρ h.invSignedD ha ?_
  set σ : VarEnv := (VarEnv.empty.bindVal "N" (natV N)).bindVal "i" (intV j) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have hiv : σ.findVal? "i" = some (intV j) := by rw [hσ]; rfl
  have hmatch : MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.varE "i")] [.val (natV N), .val (intV j)] σ := by
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
  have hpow : EvalExp env σ _ (intV ((2 ^ (N - 1) : Nat) : Int)) :=
    evalExp_toInt (evalExp_twoPowPred hN hNv)
  have hcast : (((2 ^ (N - 1) : Nat)) : Int) = 2 ^ (N - 1) := by push_cast; rfl
  have hpp : (2 : Int) ^ (N - 1) ≤ 2 ^ N := by
    have : (2 : Nat) ^ (N - 1) ≤ 2 ^ N := Nat.pow_le_pow_right (by omega) (by omega)
    exact_mod_cast this
  rw [hcast] at hpow
  by_cases hneg : 0 ≤ j
  · refine tryClauses_hit hmatch (premsHold_ifPr ?_) ?_
    · exact evalExp_and (b₁ := true) (b₂ := true)
        (evalExp_cmpNum (op := .leOp) (t := .numT .intT) evalExp_zeroInt
          (evalExp_var hiv) (by simp [Num.cmp]; omega))
        (evalExp_cmpNum (op := .ltOp) (t := .numT .intT) (evalExp_var hiv) hpow
          (by simp [Num.cmp, h₂]))
    · have := evalExp_toNat (env := env) hneg (evalExp_var hiv)
      rwa [Wasm.Numerics.invSigned_of_nonneg hneg h₂]
  · refine tryClauses_skip_prem hmatch (premsUndef_ifPr ?_) ?_
    · exact evalExp_and (b₁ := false) (b₂ := true)
        (evalExp_cmpNum (op := .leOp) (t := .numT .intT) evalExp_zeroInt
          (evalExp_var hiv) (by simp [Num.cmp]; omega))
        (evalExp_cmpNum (op := .ltOp) (t := .numT .intT) (evalExp_var hiv) hpow
          (by simp [Num.cmp, h₂]))
    refine tryClauses_hit hmatch (premsHold_ifPr ?_) ?_
    · refine evalExp_and (b₁ := true) (b₂ := true) ?_
        (evalExp_cmpNum (op := .ltOp) (t := .numT .intT) (evalExp_var hiv)
          evalExp_zeroInt (by simp [Num.cmp]; omega))
      exact evalExp_cmpNum (op := .leOp) (t := .numT .intT)
        (evalExp_unNum hpow rfl) (evalExp_var hiv) (by simp [Num.cmp]; omega)
    · have hsum := evalExp_binNum (env := env) (op := .addOp) (t := .numT .intT)
        (evalExp_var hiv) (evalExp_toInt (evalExp_twoPow hNv)) rfl
      have hnn : (0 : Int) ≤ j + ((2 ^ N : Nat) : Int) := by push_cast; omega
      have := evalExp_toNat (env := env) hnn hsum
      rw [Wasm.Numerics.invSigned_of_neg (by omega) (by omega)]
      convert this using 3
      push_cast
      rfl

/-- **`$iadd_`** agrees with `Numerics.iadd_`. -/
theorem callDef_iadd {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "iadd_" = none) {args : List Arg} {N : Nat} {i₁ i₂ : BitVec N}
    (ha : EvalArgs env ρ args [.val (natV N), .val (bvV i₁), .val (bvV i₂)]) :
    CallDef env ρ "iadd_" args (bvV (Wasm.Numerics.iadd_ N i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.iaddD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  refine tryClauses_hit (ρ₀ := σ) ?_ premsHold_nil ?_
  · rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil))
  · have hadd := evalExp_binNum (env := env) (op := .addOp) (t := .numT .natT)
      (evalExp_uNV_payload h1) (evalExp_uNV_payload h2) rfl
    have hc := evalExp_case_tup_one (op := "%")
      (evalExp_wrapNat hadd (evalExp_twoPow hNv) (Nat.two_pow_pos N).ne')
    simpa [bvV, natV, Wasm.Numerics.iadd_, Nat.mod_mod_of_dvd] using hc

/-- **`$imul_`** agrees with `Numerics.imul_`. -/
theorem callDef_imul {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "imul_" = none) {args : List Arg} {N : Nat} {i₁ i₂ : BitVec N}
    (ha : EvalArgs env ρ args [.val (natV N), .val (bvV i₁), .val (bvV i₂)]) :
    CallDef env ρ "imul_" args (bvV (Wasm.Numerics.imul_ N i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.imulD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  refine tryClauses_hit (ρ₀ := σ) ?_ premsHold_nil ?_
  · rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil))
  · have hmul := evalExp_binNum (env := env) (op := .mulOp) (t := .numT .natT)
      (evalExp_uNV_payload h1) (evalExp_uNV_payload h2) rfl
    have hc := evalExp_case_tup_one (op := "%")
      (evalExp_wrapNat hmul (evalExp_twoPow hNv) (Nat.two_pow_pos N).ne')
    simpa [bvV, natV, Wasm.Numerics.imul_, Nat.mod_mod_of_dvd] using hc

/-- **`$isub_`** agrees with `Numerics.isub_`.  The IL adds `2^N` before
subtracting, in `int`, and converts back; the Lean transcription subtracts in
`Nat`, where the same bias keeps the result non-negative. -/
theorem callDef_isub {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "isub_" = none) {args : List Arg} {N : Nat} {i₁ i₂ : BitVec N}
    (ha : EvalArgs env ρ args [.val (natV N), .val (bvV i₁), .val (bvV i₂)]) :
    CallDef env ρ "isub_" args (bvV (Wasm.Numerics.isub_ N i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.isubD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  refine tryClauses_hit (ρ₀ := σ) ?_ premsHold_nil ?_
  · rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil))
  · have hlt := i₂.isLt
    have hbias := evalExp_binNum (env := env) (op := .addOp) (t := .numT .natT)
      (evalExp_twoPow hNv) (evalExp_uNV_payload h1) rfl
    have hdiff := evalExp_binNum (env := env) (op := .subOp) (t := .numT .intT)
      (evalExp_toInt hbias) (evalExp_toInt (evalExp_uNV_payload h2)) rfl
    rw [show ((2 ^ N + i₁.toNat : Nat) : Int) - ((i₂.toNat : Nat) : Int)
        = ((2 ^ N + i₁.toNat - i₂.toNat : Nat) : Int) by omega] at hdiff
    have hc := evalExp_case_tup_one (op := "%")
      (evalExp_wrapInt hdiff (evalExp_toInt (evalExp_twoPow hNv))
        (Nat.two_pow_pos N).ne')
    simpa [bvV, natV, Wasm.Numerics.isub_, Nat.mod_mod_of_dvd] using hc

/-- The body shape `%( $bool(c) )` that every test and relation returns. -/
theorem evalExp_boolResult {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "bool" = none) {e : Exp} {b : Bool} (he : EvalExp env ρ e (.bool b)) :
    EvalExp env ρ (.caseE "%" (.tupE [.callE "bool" [.expA e]]))
      (bvV (Wasm.Numerics.u32OfBool b)) := by
  rw [uNV_u32OfBool]
  exact evalExp_case_tup_one (h.evalExp_boolCall hρ he)

/-- **`$ieqz_`** agrees with `Numerics.ieqz_`. -/
theorem callDef_ieqz {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "ieqz_" = none) {args : List Arg} {N : Nat} {i : BitVec N}
    (ha : EvalArgs env ρ args [.val (natV N), .val (bvV i)]) :
    CallDef env ρ "ieqz_" args (bvV (Wasm.Numerics.ieqz_ N i)) := by
  refine callDef_of_tryClauses hρ h.ieqzD ha ?_
  set σ : VarEnv := (VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i) with hσ
  have h1 : σ.findVal? "i_1" = some (bvV i) := by rw [hσ]; rfl
  have hb : σ.findDef? "bool" = none := by rw [hσ]; rfl
  refine tryClauses_hit (ρ₀ := σ) ?_ premsHold_nil ?_
  · rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
  · have hc := evalExp_eq (env := env) (t := .boolT) (evalExp_uNV_payload h1)
      (evalExp_natLit 0)
    rw [show (natV i.toNat == natV 0) = decide (i.toNat = 0) from natV_beq _ _] at hc
    exact h.evalExp_boolResult hb hc

/-- **`$ieq_`** agrees with `Numerics.ieq_`. -/
theorem callDef_ieq {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "ieq_" = none) {args : List Arg} {N : Nat} {i₁ i₂ : BitVec N}
    (ha : EvalArgs env ρ args [.val (natV N), .val (bvV i₁), .val (bvV i₂)]) :
    CallDef env ρ "ieq_" args (bvV (Wasm.Numerics.ieq_ N i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.ieqD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  have hb : σ.findDef? "bool" = none := by rw [hσ]; rfl
  refine tryClauses_hit (ρ₀ := σ) ?_ premsHold_nil ?_
  · rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil))
  · have hc := evalExp_eq (env := env) (t := .boolT) (evalExp_var h1) (evalExp_var h2)
    rw [show (bvV i₁ == bvV i₂) = decide (i₁ = i₂) from uNV_beq _ _] at hc
    exact h.evalExp_boolResult hb hc

/-- **`$ine_`** agrees with `Numerics.ine_`. -/
theorem callDef_ine {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "ine_" = none) {args : List Arg} {N : Nat} {i₁ i₂ : BitVec N}
    (ha : EvalArgs env ρ args [.val (natV N), .val (bvV i₁), .val (bvV i₂)]) :
    CallDef env ρ "ine_" args (bvV (Wasm.Numerics.ine_ N i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.ineD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  have hb : σ.findDef? "bool" = none := by rw [hσ]; rfl
  refine tryClauses_hit (ρ₀ := σ) ?_ premsHold_nil ?_
  · rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil))
  · have hc := evalExp_ne (env := env) (t := .boolT) (evalExp_var h1) (evalExp_var h2)
    rw [show (!(bvV i₁ == bvV i₂)) = decide (i₁ ≠ i₂) by rw [uNV_beq]; simp] at hc
    exact h.evalExp_boolResult hb hc

/-- **`$ilt_`** agrees with `Numerics.ilt_`.  The `0 < N` hypothesis is
needed only by the signed clause, which calls `$signed_`. -/
theorem callDef_ilt {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "ilt_" = none) {args : List Arg} {N : Nat} {sx : Wasm.Signedness}
    {i₁ i₂ : BitVec N} (ha : EvalArgs env ρ args
      [.val (natV N), .val (sxV sx), .val (bvV i₁), .val (bvV i₂)]) (hN : 0 < N) :
    CallDef env ρ "ilt_" args (bvV (Wasm.Numerics.ilt_ N sx i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.iltD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  have hb : σ.findDef? "bool" = none := by rw [hσ]; rfl
  have hs : σ.findDef? "signed_" = none := by rw [hσ]; rfl
  have hmatch : ∀ a : MixopS, MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.caseE a (.tupE [])), .expA (.varE "i_1"),
        .expA (.varE "i_2")]
      [.val (natV N), .val (.case a (.tuple [])), .val (bvV i₁), .val (bvV i₂)] σ := by
    intro a
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
          (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)))
  cases sx with
  | unsigned =>
      exact tryClauses_hit (hmatch "U") premsHold_nil
        (h.evalExp_boolResult hb (evalExp_cmpNum (op := .ltOp) (t := .numT .natT)
          (evalExp_uNV_payload h1) (evalExp_uNV_payload h2) rfl))
  | signed =>
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons_undef (matchArg_expA_undef
          (matchExp_caseE_undef (by decide))))) ?_
      refine tryClauses_hit (hmatch "S") premsHold_nil ?_
      have hsig₁ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_1") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₁.toNat)) :=
        evalExp_callE_iff.2 (h.callDef_signed hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h1) evalArgs_nil)) hN i₁.isLt)
      have hsig₂ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_2") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₂.toNat)) :=
        evalExp_callE_iff.2 (h.callDef_signed hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h2) evalArgs_nil)) hN i₂.isLt)
      exact h.evalExp_boolResult hb (evalExp_cmpNum (op := .ltOp) (t := .numT .intT)
        hsig₁ hsig₂ rfl)

/-- **`$igt_`** agrees with `Numerics.igt_`.  The `0 < N` hypothesis is
needed only by the signed clause, which calls `$signed_`. -/
theorem callDef_igt {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "igt_" = none) {args : List Arg} {N : Nat} {sx : Wasm.Signedness}
    {i₁ i₂ : BitVec N} (ha : EvalArgs env ρ args
      [.val (natV N), .val (sxV sx), .val (bvV i₁), .val (bvV i₂)]) (hN : 0 < N) :
    CallDef env ρ "igt_" args (bvV (Wasm.Numerics.igt_ N sx i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.igtD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  have hb : σ.findDef? "bool" = none := by rw [hσ]; rfl
  have hs : σ.findDef? "signed_" = none := by rw [hσ]; rfl
  have hmatch : ∀ a : MixopS, MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.caseE a (.tupE [])), .expA (.varE "i_1"),
        .expA (.varE "i_2")]
      [.val (natV N), .val (.case a (.tuple [])), .val (bvV i₁), .val (bvV i₂)] σ := by
    intro a
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
          (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)))
  cases sx with
  | unsigned =>
      exact tryClauses_hit (hmatch "U") premsHold_nil
        (h.evalExp_boolResult hb (evalExp_cmpNum (op := .gtOp) (t := .numT .natT)
          (evalExp_uNV_payload h1) (evalExp_uNV_payload h2) rfl))
  | signed =>
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons_undef (matchArg_expA_undef
          (matchExp_caseE_undef (by decide))))) ?_
      refine tryClauses_hit (hmatch "S") premsHold_nil ?_
      have hsig₁ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_1") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₁.toNat)) :=
        evalExp_callE_iff.2 (h.callDef_signed hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h1) evalArgs_nil)) hN i₁.isLt)
      have hsig₂ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_2") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₂.toNat)) :=
        evalExp_callE_iff.2 (h.callDef_signed hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h2) evalArgs_nil)) hN i₂.isLt)
      exact h.evalExp_boolResult hb (evalExp_cmpNum (op := .gtOp) (t := .numT .intT)
        hsig₁ hsig₂ rfl)

/-- **`$ile_`** agrees with `Numerics.ile_`.  The `0 < N` hypothesis is
needed only by the signed clause, which calls `$signed_`. -/
theorem callDef_ile {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "ile_" = none) {args : List Arg} {N : Nat} {sx : Wasm.Signedness}
    {i₁ i₂ : BitVec N} (ha : EvalArgs env ρ args
      [.val (natV N), .val (sxV sx), .val (bvV i₁), .val (bvV i₂)]) (hN : 0 < N) :
    CallDef env ρ "ile_" args (bvV (Wasm.Numerics.ile_ N sx i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.ileD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  have hb : σ.findDef? "bool" = none := by rw [hσ]; rfl
  have hs : σ.findDef? "signed_" = none := by rw [hσ]; rfl
  have hmatch : ∀ a : MixopS, MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.caseE a (.tupE [])), .expA (.varE "i_1"),
        .expA (.varE "i_2")]
      [.val (natV N), .val (.case a (.tuple [])), .val (bvV i₁), .val (bvV i₂)] σ := by
    intro a
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
          (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)))
  cases sx with
  | unsigned =>
      exact tryClauses_hit (hmatch "U") premsHold_nil
        (h.evalExp_boolResult hb (evalExp_cmpNum (op := .leOp) (t := .numT .natT)
          (evalExp_uNV_payload h1) (evalExp_uNV_payload h2) rfl))
  | signed =>
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons_undef (matchArg_expA_undef
          (matchExp_caseE_undef (by decide))))) ?_
      refine tryClauses_hit (hmatch "S") premsHold_nil ?_
      have hsig₁ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_1") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₁.toNat)) :=
        evalExp_callE_iff.2 (h.callDef_signed hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h1) evalArgs_nil)) hN i₁.isLt)
      have hsig₂ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_2") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₂.toNat)) :=
        evalExp_callE_iff.2 (h.callDef_signed hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h2) evalArgs_nil)) hN i₂.isLt)
      exact h.evalExp_boolResult hb (evalExp_cmpNum (op := .leOp) (t := .numT .intT)
        hsig₁ hsig₂ rfl)

/-- **`$ige_`** agrees with `Numerics.ige_`.  The `0 < N` hypothesis is
needed only by the signed clause, which calls `$signed_`. -/
theorem callDef_ige {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "ige_" = none) {args : List Arg} {N : Nat} {sx : Wasm.Signedness}
    {i₁ i₂ : BitVec N} (ha : EvalArgs env ρ args
      [.val (natV N), .val (sxV sx), .val (bvV i₁), .val (bvV i₂)]) (hN : 0 < N) :
    CallDef env ρ "ige_" args (bvV (Wasm.Numerics.ige_ N sx i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.igeD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  have hb : σ.findDef? "bool" = none := by rw [hσ]; rfl
  have hs : σ.findDef? "signed_" = none := by rw [hσ]; rfl
  have hmatch : ∀ a : MixopS, MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.caseE a (.tupE [])), .expA (.varE "i_1"),
        .expA (.varE "i_2")]
      [.val (natV N), .val (.case a (.tuple [])), .val (bvV i₁), .val (bvV i₂)] σ := by
    intro a
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
          (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)))
  cases sx with
  | unsigned =>
      exact tryClauses_hit (hmatch "U") premsHold_nil
        (h.evalExp_boolResult hb (evalExp_cmpNum (op := .geOp) (t := .numT .natT)
          (evalExp_uNV_payload h1) (evalExp_uNV_payload h2) rfl))
  | signed =>
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons_undef (matchArg_expA_undef
          (matchExp_caseE_undef (by decide))))) ?_
      refine tryClauses_hit (hmatch "S") premsHold_nil ?_
      have hsig₁ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_1") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₁.toNat)) :=
        evalExp_callE_iff.2 (h.callDef_signed hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h1) evalArgs_nil)) hN i₁.isLt)
      have hsig₂ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_2") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₂.toNat)) :=
        evalExp_callE_iff.2 (h.callDef_signed hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h2) evalArgs_nil)) hN i₂.isLt)
      exact h.evalExp_boolResult hb (evalExp_cmpNum (op := .geOp) (t := .numT .intT)
        hsig₁ hsig₂ rfl)

/-- **`$idiv_`** at divisor `0` agrees with `Numerics.idiv_`: both are
undefined, which the IL writes as the empty option `eps`. -/
theorem callDef_idiv_zero {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "idiv_" = none) {args : List Arg} {N : Nat} {sx : Wasm.Signedness}
    {i₁ : BitVec N} (ha : EvalArgs env ρ args
      [.val (natV N), .val (sxV sx), .val (bvV i₁), .val (bvV (0 : BitVec N))]) :
    CallDef env ρ "idiv_" args (optUNV (Wasm.Numerics.idiv_ N sx i₁ 0)) := by
  refine callDef_of_tryClauses hρ h.idivD ha ?_
  set σ : VarEnv := (VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁) with hσ
  have hmatch : ∀ a : MixopS, MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.caseE a (.tupE [])), .expA (.varE "i_1"),
        .expA (.caseE "%" (.tupE [.numE (.natN 0)]))]
      [.val (natV N), .val (.case a (.tuple [])), .val (bvV i₁),
        .val (.case "%" (.tuple [natV 0]))] σ := by
    intro a
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
          (matchArgs_cons (matchArg_expA (matchExp_caseE
            (matchExp_tupE_one matchExp_numE))) matchArgs_nil)))
  rw [show bvV (0 : BitVec N) = .case "%" (.tuple [natV 0]) by simp [bvV, natV],
    show Wasm.Numerics.idiv_ N sx i₁ 0 = none by cases sx <;> simp [Wasm.Numerics.idiv_]]
  have hbody : EvalExp env σ (Exp.optE none) (optUNV (N := N) none) :=
    evalExp_optE_none_iff.2 rfl
  cases sx with
  | unsigned => exact tryClauses_hit (hmatch "U") premsHold_nil hbody
  | signed =>
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons_undef
          (matchArg_expA_undef (matchExp_caseE_undef (by decide))))) ?_
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons_undef
          (matchArg_expA_undef (matchExp_caseE_undef (by decide))))) ?_
      exact tryClauses_hit (hmatch "S") premsHold_nil hbody

/-- **`$irem_`** at divisor `0` agrees with `Numerics.irem_`. -/
theorem callDef_irem_zero {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "irem_" = none) {args : List Arg} {N : Nat} {sx : Wasm.Signedness}
    {i₁ : BitVec N} (ha : EvalArgs env ρ args
      [.val (natV N), .val (sxV sx), .val (bvV i₁), .val (bvV (0 : BitVec N))]) :
    CallDef env ρ "irem_" args (optUNV (Wasm.Numerics.irem_ N sx i₁ 0)) := by
  refine callDef_of_tryClauses hρ h.iremD ha ?_
  set σ : VarEnv := (VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁) with hσ
  have hmatch : ∀ a : MixopS, MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.caseE a (.tupE [])), .expA (.varE "i_1"),
        .expA (.caseE "%" (.tupE [.numE (.natN 0)]))]
      [.val (natV N), .val (.case a (.tuple [])), .val (bvV i₁),
        .val (.case "%" (.tuple [natV 0]))] σ := by
    intro a
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
        (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
          (matchArgs_cons (matchArg_expA (matchExp_caseE
            (matchExp_tupE_one matchExp_numE))) matchArgs_nil)))
  rw [show bvV (0 : BitVec N) = .case "%" (.tuple [natV 0]) by simp [bvV, natV],
    show Wasm.Numerics.irem_ N sx i₁ 0 = none by cases sx <;> simp [Wasm.Numerics.irem_]]
  have hbody : EvalExp env σ (Exp.optE none) (optUNV (N := N) none) :=
    evalExp_optE_none_iff.2 rfl
  cases sx with
  | unsigned => exact tryClauses_hit (hmatch "U") premsHold_nil hbody
  | signed =>
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons_undef
          (matchArg_expA_undef (matchExp_caseE_undef (by decide))))) ?_
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons_undef
          (matchArg_expA_undef (matchExp_caseE_undef (by decide))))) ?_
      exact tryClauses_hit (hmatch "S") premsHold_nil hbody

end NumEnvCore

end Silmaril.SpecTec.Equiv
