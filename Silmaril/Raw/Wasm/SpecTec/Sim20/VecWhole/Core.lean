module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.NumericsCore

/-!
# The wasm-2.0 lane primitives with clauses, over `NumEnvCore` (unrefined copy)

`Equiv/NumericsCore.lean` restates over `Equiv.NumEnvCore` (the 24 definitions wasm-2.0 shares
with wasm-3.0 verbatim) only the `Equiv.callDef_*` lemmas the scalar 2.0 dispatchers need. The
vector lane functions of 2.0 also call `$ineg_`, `$iabs_`, `$imin_`, `$imax_`, `$iadd_sat_` and
`$isub_sat_` (and through them `$sat_u_`, `$sat_s_`). This file copies those eight lemmas from
`Equiv/Numerics.lean` unchanged except for the hypothesis `NumEnvCore env` in place of
`NumEnv env`; none of them reads `$iextend_`, the one definition 2.0 lacks. Kept in `Raw`, like
its model.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv

open Silmaril.SpecTec.IL Silmaril.SpecTec.Sem

namespace NumEnvCore

/-- **`$ineg_`** agrees with `Numerics.ineg_`. -/
theorem callDef_ineg {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "ineg_" = none) {args : List Arg} {N : Nat} {i : BitVec N}
    (ha : EvalArgs env ρ args [.val (natV N), .val (bvV i)]) :
    CallDef env ρ "ineg_" args (bvV (Wasm.Numerics.ineg_ N i)) := by
  refine callDef_of_tryClauses hρ h.inegD ha ?_
  set σ : VarEnv := (VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i) := by rw [hσ]; rfl
  refine tryClauses_hit (ρ₀ := σ) ?_ premsHold_nil ?_
  · rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
  · have hlt := i.isLt
    have hdiff := evalExp_binNum (env := env) (op := .subOp) (t := .numT .intT)
      (evalExp_toInt (evalExp_twoPow hNv)) (evalExp_toInt (evalExp_uNV_payload h1)) rfl
    rw [show ((2 ^ N : Nat) : Int) - ((i.toNat : Nat) : Int)
        = ((2 ^ N - i.toNat : Nat) : Int) by omega] at hdiff
    have hc := evalExp_case_tup_one (op := "%")
      (evalExp_wrapInt hdiff (evalExp_toInt (evalExp_twoPow hNv))
        (Nat.two_pow_pos N).ne')
    simpa [bvV, natV, Wasm.Numerics.ineg_, Nat.mod_mod_of_dvd] using hc

/-- **`$iabs_`** agrees with `Numerics.iabs_`. -/
theorem callDef_iabs {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "iabs_" = none) {args : List Arg} {N : Nat} {i : BitVec N}
    (ha : EvalArgs env ρ args [.val (natV N), .val (bvV i)]) (hN : 0 < N) :
    CallDef env ρ "iabs_" args (bvV (Wasm.Numerics.iabs_ N i)) := by
  refine callDef_of_tryClauses hρ h.iabsD ha ?_
  set σ : VarEnv := (VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i) := by rw [hσ]; rfl
  have hdefs : σ.findDef? "signed_" = none := by rw [hσ]; rfl
  have hdefn : σ.findDef? "ineg_" = none := by rw [hσ]; rfl
  have hmatch : MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.varE "i_1")] [.val (natV N), .val (bvV i)] σ := by
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
  have hsig : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
      .expA (.projE (.uncaseE (.varE "i_1") "%") 0)])
      (intV (Wasm.Numerics.signed_ N i.toNat)) :=
    evalExp_callE_iff.2 (callDef_signed h hdefs
      (evalArgs_cons (evalExp_var hNv)
        (evalArgs_cons (evalExp_uNV_payload h1) evalArgs_nil)) hN i.isLt)
  by_cases hge : Wasm.Numerics.signed_ N i.toNat ≥ 0
  · refine tryClauses_hit hmatch (premsHold_ifPr (evalExp_cmpNum (op := .geOp)
      (t := .numT .intT) hsig evalExp_zeroInt (by simp [Num.cmp]; omega))) ?_
    have := evalExp_var (env := env) h1
    simpa [Wasm.Numerics.iabs_, hge] using this
  · refine tryClauses_skip_prem hmatch (premsUndef_ifPr (evalExp_cmpNum (op := .geOp)
      (t := .numT .intT) hsig evalExp_zeroInt (by simp [Num.cmp]; omega))) ?_
    refine tryClauses_hit hmatch premsHold_elsePr ?_
    have := evalExp_callE_iff.2 (callDef_ineg (env := env) (ρ := σ) h hdefn
      (evalArgs_cons (evalExp_var hNv) (evalArgs_cons (evalExp_var h1) evalArgs_nil)))
    simpa [Wasm.Numerics.iabs_, hge] using this

/-- **`$imin_`** agrees with `Numerics.imin_`.  The `0 < N` hypothesis is
needed only by the signed clauses, which call `$signed_`. -/
theorem callDef_imin {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "imin_" = none) {args : List Arg} {N : Nat} {sx : Wasm.Signedness}
    {i₁ i₂ : BitVec N} (ha : EvalArgs env ρ args
      [.val (natV N), .val (sxV sx), .val (bvV i₁), .val (bvV i₂)]) (hN : 0 < N) :
    CallDef env ρ "imin_" args (bvV (Wasm.Numerics.imin_ N sx i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.iminD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
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
  have hskip : ∀ a b : MixopS, a ≠ b → MatchArgsUndef env VarEnv.empty
        [Arg.expA (.varE "N"), .expA (.caseE b (.tupE [])), .expA (.varE "i_1"),
          .expA (.varE "i_2")]
        [.val (natV N), .val (.case a (.tuple [])), .val (bvV i₁), .val (bvV i₂)] := by
    intro a b hab
    exact matchArgs_cons_undef_tail (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons_undef (matchArg_expA_undef (matchExp_caseE_undef hab)))
  cases sx with
  | unsigned =>
      by_cases hle : i₁.toNat ≤ i₂.toNat
      · exact tryClauses_hit (hmatch "U")
          (premsHold_ifPr (evalExp_cmpNum (op := .leOp) (t := .numT .natT)
            (evalExp_uNV_payload h1) (evalExp_uNV_payload h2) (by simp [Num.cmp, hle])))
          (by simpa [Wasm.Numerics.imin_, hle] using evalExp_var (env := env) h1)
      · refine tryClauses_skip_prem (hmatch "U")
          (premsUndef_ifPr (evalExp_cmpNum (op := .leOp) (t := .numT .natT)
            (evalExp_uNV_payload h1) (evalExp_uNV_payload h2)
            (by simp [Num.cmp, hle]))) ?_
        exact tryClauses_hit (hmatch "U")
          (premsHold_ifPr (evalExp_cmpNum (op := .gtOp) (t := .numT .natT)
            (evalExp_uNV_payload h1) (evalExp_uNV_payload h2)
            (by simp [Num.cmp]; omega)))
          (by simpa [Wasm.Numerics.imin_, hle] using evalExp_var (env := env) h2)
  | signed =>
      have hsig₁ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_1") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₁.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h1) evalArgs_nil)) hN i₁.isLt)
      have hsig₂ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_2") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₂.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h2) evalArgs_nil)) hN i₂.isLt)
      refine tryClauses_skip_match (hskip "S" "U" (by decide)) ?_
      refine tryClauses_skip_match (hskip "S" "U" (by decide)) ?_
      by_cases hle : Wasm.Numerics.signed_ N i₁.toNat ≤ Wasm.Numerics.signed_ N i₂.toNat
      · exact tryClauses_hit (hmatch "S")
          (premsHold_ifPr (evalExp_cmpNum (op := .leOp) (t := .numT .intT)
            hsig₁ hsig₂ (by simp [Num.cmp]; omega)))
          (by simpa [Wasm.Numerics.imin_, hle] using evalExp_var (env := env) h1)
      · refine tryClauses_skip_prem (hmatch "S")
          (premsUndef_ifPr (evalExp_cmpNum (op := .leOp) (t := .numT .intT)
            hsig₁ hsig₂ (by simp [Num.cmp]; omega))) ?_
        exact tryClauses_hit (hmatch "S") premsHold_elsePr
          (by simpa [Wasm.Numerics.imin_, hle] using evalExp_var (env := env) h2)

/-- **`$imax_`** agrees with `Numerics.imax_`.  The `0 < N` hypothesis is
needed only by the signed clauses, which call `$signed_`. -/
theorem callDef_imax {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "imax_" = none) {args : List Arg} {N : Nat} {sx : Wasm.Signedness}
    {i₁ i₂ : BitVec N} (ha : EvalArgs env ρ args
      [.val (natV N), .val (sxV sx), .val (bvV i₁), .val (bvV i₂)]) (hN : 0 < N) :
    CallDef env ρ "imax_" args (bvV (Wasm.Numerics.imax_ N sx i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.imaxD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
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
  have hskip : ∀ a b : MixopS, a ≠ b → MatchArgsUndef env VarEnv.empty
        [Arg.expA (.varE "N"), .expA (.caseE b (.tupE [])), .expA (.varE "i_1"),
          .expA (.varE "i_2")]
        [.val (natV N), .val (.case a (.tuple [])), .val (bvV i₁), .val (bvV i₂)] := by
    intro a b hab
    exact matchArgs_cons_undef_tail (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons_undef (matchArg_expA_undef (matchExp_caseE_undef hab)))
  cases sx with
  | unsigned =>
      by_cases hle : i₁.toNat ≥ i₂.toNat
      · exact tryClauses_hit (hmatch "U")
          (premsHold_ifPr (evalExp_cmpNum (op := .geOp) (t := .numT .natT)
            (evalExp_uNV_payload h1) (evalExp_uNV_payload h2) (by simp [Num.cmp, hle])))
          (by simpa [Wasm.Numerics.imax_, hle] using evalExp_var (env := env) h1)
      · refine tryClauses_skip_prem (hmatch "U")
          (premsUndef_ifPr (evalExp_cmpNum (op := .geOp) (t := .numT .natT)
            (evalExp_uNV_payload h1) (evalExp_uNV_payload h2)
            (by simp [Num.cmp, hle]))) ?_
        exact tryClauses_hit (hmatch "U")
          (premsHold_ifPr (evalExp_cmpNum (op := .ltOp) (t := .numT .natT)
            (evalExp_uNV_payload h1) (evalExp_uNV_payload h2)
            (by simp [Num.cmp]; omega)))
          (by simpa [Wasm.Numerics.imax_, hle] using evalExp_var (env := env) h2)
  | signed =>
      have hsig₁ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_1") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₁.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h1) evalArgs_nil)) hN i₁.isLt)
      have hsig₂ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_2") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₂.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h2) evalArgs_nil)) hN i₂.isLt)
      refine tryClauses_skip_match (hskip "S" "U" (by decide)) ?_
      refine tryClauses_skip_match (hskip "S" "U" (by decide)) ?_
      by_cases hle : Wasm.Numerics.signed_ N i₁.toNat ≥ Wasm.Numerics.signed_ N i₂.toNat
      · exact tryClauses_hit (hmatch "S")
          (premsHold_ifPr (evalExp_cmpNum (op := .geOp) (t := .numT .intT)
            hsig₁ hsig₂ (by simp [Num.cmp]; omega)))
          (by simpa [Wasm.Numerics.imax_, hle] using evalExp_var (env := env) h1)
      · refine tryClauses_skip_prem (hmatch "S")
          (premsUndef_ifPr (evalExp_cmpNum (op := .geOp) (t := .numT .intT)
            hsig₁ hsig₂ (by simp [Num.cmp]; omega))) ?_
        exact tryClauses_hit (hmatch "S") premsHold_elsePr
          (by simpa [Wasm.Numerics.imax_, hle] using evalExp_var (env := env) h2)

/-- **`$sat_u_`** agrees with `Numerics.sat_u_`. -/
theorem callDef_satU {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "sat_u_" = none) {args : List Arg} {N : Nat} {j : Int}
    (ha : EvalArgs env ρ args [.val (natV N), .val (intV j)]) :
    CallDef env ρ "sat_u_" args (natV (Wasm.Numerics.sat_u_ N j)) := by
  refine callDef_of_tryClauses hρ h.satUD ha ?_
  set σ : VarEnv := (VarEnv.empty.bindVal "N" (natV N)).bindVal "i" (intV j) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have hiv : σ.findVal? "i" = some (intV j) := by rw [hσ]; rfl
  have hmatch : MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.varE "i")] [.val (natV N), .val (intV j)] σ := by
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
  have hmax : EvalExp env σ (.binE .subOp (.numT .intT)
      (.cvtE (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")) .natT .intT)
      (.cvtE (.numE (.natN 1)) .natT .intT)) (intV (((2 ^ N : Nat) : Int) - 1)) :=
    evalExp_binNum (evalExp_toInt (evalExp_twoPow hNv)) evalExp_oneInt rfl
  have hpn := Nat.two_pow_pos N
  have hcastN : ((2 ^ N : Nat) : Int) = (2 : Int) ^ N := by push_cast; rfl
  by_cases hneg : j < 0
  · refine tryClauses_hit hmatch (premsHold_ifPr (evalExp_cmpNum (op := .ltOp)
      (t := .numT .intT) (evalExp_var hiv) evalExp_zeroInt
      (by simp [Num.cmp]; omega))) ?_
    have hz := evalExp_natLit (env := env) (ρ := σ) 0
    simpa [Wasm.Numerics.sat_u_, hneg, natV] using hz
  · refine tryClauses_skip_prem hmatch (premsUndef_ifPr (evalExp_cmpNum (op := .ltOp)
      (t := .numT .intT) (evalExp_var hiv) evalExp_zeroInt
      (by simp [Num.cmp]; omega))) ?_
    by_cases hbig : (2 : Int) ^ N - 1 < j
    · refine tryClauses_hit hmatch (premsHold_ifPr (evalExp_cmpNum (op := .gtOp)
        (t := .numT .intT) (evalExp_var hiv) hmax (by simp [Num.cmp]; omega))) ?_
      have hc := evalExp_toNat (env := env) (by omega) hmax
      rw [show (((2 ^ N : Nat) : Int) - 1).toNat = 2 ^ N - 1 by omega] at hc
      simpa [Wasm.Numerics.sat_u_, hneg, hbig, natV] using hc
    · refine tryClauses_skip_prem hmatch (premsUndef_ifPr (evalExp_cmpNum (op := .gtOp)
        (t := .numT .intT) (evalExp_var hiv) hmax (by simp [Num.cmp]; omega))) ?_
      refine tryClauses_hit hmatch premsHold_elsePr ?_
      have hc := evalExp_toNat (env := env) (show (0 : Int) ≤ j by omega) (evalExp_var hiv)
      simpa [Wasm.Numerics.sat_u_, hneg, hbig, natV] using hc

/-- **`$sat_s_`** agrees with `Numerics.sat_s_` for `0 < N`. -/
theorem callDef_satS {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "sat_s_" = none) {args : List Arg} {N : Nat} {j : Int}
    (ha : EvalArgs env ρ args [.val (natV N), .val (intV j)]) (hN : 0 < N) :
    CallDef env ρ "sat_s_" args (intV (Wasm.Numerics.sat_s_ N j)) := by
  refine callDef_of_tryClauses hρ h.satSD ha ?_
  set σ : VarEnv := (VarEnv.empty.bindVal "N" (natV N)).bindVal "i" (intV j) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have hiv : σ.findVal? "i" = some (intV j) := by rw [hσ]; rfl
  have hmatch : MatchArgs env VarEnv.empty
      [Arg.expA (.varE "N"), .expA (.varE "i")] [.val (natV N), .val (intV j)] σ := by
    rw [hσ]
    exact matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
  have hcast : (((2 ^ (N - 1) : Nat)) : Int) = 2 ^ (N - 1) := by push_cast; rfl
  have hpow : EvalExp env σ _ (intV ((2 ^ (N - 1) : Nat) : Int)) :=
    evalExp_toInt (evalExp_twoPowPred hN hNv)
  rw [hcast] at hpow
  have hlow : EvalExp env σ _ (intV (-2 ^ (N - 1))) :=
    evalExp_unNum (op := .minusOp) (t := .numT .intT) hpow rfl
  have hmax : EvalExp env σ _ (intV (2 ^ (N - 1) - 1)) :=
    evalExp_binNum (op := .subOp) (t := .numT .intT) hpow evalExp_oneInt rfl
  by_cases hlo : j < -2 ^ (N - 1)
  · exact tryClauses_hit hmatch (premsHold_ifPr (evalExp_cmpNum (op := .ltOp)
      (t := .numT .intT) (evalExp_var hiv) hlow (by simp [Num.cmp]; omega)))
      (by simpa [Wasm.Numerics.sat_s_, hlo] using hlow)
  · refine tryClauses_skip_prem hmatch (premsUndef_ifPr (evalExp_cmpNum (op := .ltOp)
      (t := .numT .intT) (evalExp_var hiv) hlow (by simp [Num.cmp]; omega))) ?_
    by_cases hhi : 2 ^ (N - 1) - 1 < j
    · exact tryClauses_hit hmatch (premsHold_ifPr (evalExp_cmpNum (op := .gtOp)
        (t := .numT .intT) (evalExp_var hiv) hmax (by simp [Num.cmp]; omega)))
        (by simpa [Wasm.Numerics.sat_s_, hlo, hhi] using hmax)
    · refine tryClauses_skip_prem hmatch (premsUndef_ifPr (evalExp_cmpNum (op := .gtOp)
        (t := .numT .intT) (evalExp_var hiv) hmax (by simp [Num.cmp]; omega))) ?_
      exact tryClauses_hit hmatch premsHold_elsePr
        (by simpa [Wasm.Numerics.sat_s_, hlo, hhi] using evalExp_var (env := env) hiv)

/-- **`$iadd_sat_`** agrees with `Numerics.iadd_sat_`.  The `0 < N` hypothesis is needed
only by the signed clause, which calls `$signed_` and `$inv_signed_`. -/
theorem callDef_iaddSat {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "iadd_sat_" = none) {args : List Arg} {N : Nat} {sx : Wasm.Signedness}
    {i₁ i₂ : BitVec N} (ha : EvalArgs env ρ args
      [.val (natV N), .val (sxV sx), .val (bvV i₁), .val (bvV i₂)]) (hN : 0 < N) :
    CallDef env ρ "iadd_sat_" args (bvV (Wasm.Numerics.iadd_sat_ N sx i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.iaddSatD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  have hs : σ.findDef? "signed_" = none := by rw [hσ]; rfl
  have hv : σ.findDef? "inv_signed_" = none := by rw [hσ]; rfl
  have hu : σ.findDef? "sat_u_" = none := by rw [hσ]; rfl
  have hw : σ.findDef? "sat_s_" = none := by rw [hσ]; rfl
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
      refine tryClauses_hit (hmatch "U") premsHold_nil ?_
      have harg : EvalExp env σ (.cvtE (.binE .addOp (.numT .natT)
            (.projE (.uncaseE (.varE "i_1") "%") 0)
            (.projE (.uncaseE (.varE "i_2") "%") 0)) .natT .intT)
          (intV ((i₁.toNat : Int) + i₂.toNat)) := by
        have := evalExp_toInt (env := env) (evalExp_binNum (op := .addOp)
          (t := .numT .natT) (evalExp_uNV_payload h1) (evalExp_uNV_payload h2) rfl)
        rw [show ((i₁.toNat + i₂.toNat : Nat) : Int) = (i₁.toNat : Int) + i₂.toNat by
          push_cast; rfl] at this
        exact this
      have hsat := evalExp_callE_iff.2 (callDef_satU (env := env) (ρ := σ) h hu
        (evalArgs_cons (evalExp_var hNv) (evalArgs_cons harg evalArgs_nil)))
      have hc := evalExp_case_tup_one (op := "%") hsat
      have hlt := sat_u_lt N ((i₁.toNat : Int) + i₂.toNat)
      simpa [bvV, natV, Wasm.Numerics.iadd_sat_, Nat.mod_eq_of_lt hlt] using hc
  | signed =>
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons_undef
          (matchArg_expA_undef (matchExp_caseE_undef (by decide))))) ?_
      refine tryClauses_hit (hmatch "S") premsHold_nil ?_
      have hsig₁ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_1") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₁.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h1) evalArgs_nil)) hN i₁.isLt)
      have hsig₂ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_2") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₂.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h2) evalArgs_nil)) hN i₂.isLt)
      have hcomb := evalExp_binNum (env := env) (op := .addOp) (t := .numT .intT)
        hsig₁ hsig₂ rfl
      have hsat := evalExp_callE_iff.2 (callDef_satS (env := env) (ρ := σ) h hw
        (evalArgs_cons (evalExp_var hNv) (evalArgs_cons hcomb evalArgs_nil)) hN)
      obtain ⟨hb₁, hb₂⟩ := sat_s_bounds N
        (Wasm.Numerics.signed_ N i₁.toNat + Wasm.Numerics.signed_ N i₂.toNat)
      have hinv := evalExp_callE_iff.2 (callDef_invSigned (env := env) (ρ := σ) h hv
        (evalArgs_cons (evalExp_var hNv) (evalArgs_cons hsat evalArgs_nil)) hN hb₁ hb₂)
      have hc := evalExp_case_tup_one (op := "%") hinv
      have hlt := invSigned_lt N (Wasm.Numerics.sat_s_ N
        (Wasm.Numerics.signed_ N i₁.toNat + Wasm.Numerics.signed_ N i₂.toNat))
      simpa [bvV, natV, Wasm.Numerics.iadd_sat_, Nat.mod_eq_of_lt hlt] using hc

/-- **`$isub_sat_`** agrees with `Numerics.isub_sat_`.  The `0 < N` hypothesis is needed
only by the signed clause, which calls `$signed_` and `$inv_signed_`. -/
theorem callDef_isubSat {env : Env} {ρ : VarEnv} (h : NumEnvCore env)
    (hρ : ρ.findDef? "isub_sat_" = none) {args : List Arg} {N : Nat} {sx : Wasm.Signedness}
    {i₁ i₂ : BitVec N} (ha : EvalArgs env ρ args
      [.val (natV N), .val (sxV sx), .val (bvV i₁), .val (bvV i₂)]) (hN : 0 < N) :
    CallDef env ρ "isub_sat_" args (bvV (Wasm.Numerics.isub_sat_ N sx i₁ i₂)) := by
  refine callDef_of_tryClauses hρ h.isubSatD ha ?_
  set σ : VarEnv := ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i_1" (bvV i₁)).bindVal
      "i_2" (bvV i₂) with hσ
  have hNv : σ.findVal? "N" = some (natV N) := by rw [hσ]; rfl
  have h1 : σ.findVal? "i_1" = some (bvV i₁) := by rw [hσ]; rfl
  have h2 : σ.findVal? "i_2" = some (bvV i₂) := by rw [hσ]; rfl
  have hs : σ.findDef? "signed_" = none := by rw [hσ]; rfl
  have hv : σ.findDef? "inv_signed_" = none := by rw [hσ]; rfl
  have hu : σ.findDef? "sat_u_" = none := by rw [hσ]; rfl
  have hw : σ.findDef? "sat_s_" = none := by rw [hσ]; rfl
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
      refine tryClauses_hit (hmatch "U") premsHold_nil ?_
      have harg : EvalExp env σ (.binE .subOp (.numT .intT)
            (.cvtE (.projE (.uncaseE (.varE "i_1") "%") 0) .natT .intT)
            (.cvtE (.projE (.uncaseE (.varE "i_2") "%") 0) .natT .intT))
          (intV ((i₁.toNat : Int) - i₂.toNat)) := evalExp_binNum (op := .subOp) (t := .numT .intT)
        (evalExp_toInt (evalExp_uNV_payload h1)) (evalExp_toInt (evalExp_uNV_payload h2)) rfl
      have hsat := evalExp_callE_iff.2 (callDef_satU (env := env) (ρ := σ) h hu
        (evalArgs_cons (evalExp_var hNv) (evalArgs_cons harg evalArgs_nil)))
      have hc := evalExp_case_tup_one (op := "%") hsat
      have hlt := sat_u_lt N ((i₁.toNat : Int) - i₂.toNat)
      simpa [bvV, natV, Wasm.Numerics.isub_sat_, Nat.mod_eq_of_lt hlt] using hc
  | signed =>
      refine tryClauses_skip_match (matchArgs_cons_undef_tail
        (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons_undef
          (matchArg_expA_undef (matchExp_caseE_undef (by decide))))) ?_
      refine tryClauses_hit (hmatch "S") premsHold_nil ?_
      have hsig₁ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_1") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₁.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h1) evalArgs_nil)) hN i₁.isLt)
      have hsig₂ : EvalExp env σ (.callE "signed_" [.expA (.varE "N"),
          .expA (.projE (.uncaseE (.varE "i_2") "%") 0)])
          (intV (Wasm.Numerics.signed_ N i₂.toNat)) :=
        evalExp_callE_iff.2 (callDef_signed h hs (evalArgs_cons (evalExp_var hNv)
          (evalArgs_cons (evalExp_uNV_payload h2) evalArgs_nil)) hN i₂.isLt)
      have hcomb := evalExp_binNum (env := env) (op := .subOp) (t := .numT .intT)
        hsig₁ hsig₂ rfl
      have hsat := evalExp_callE_iff.2 (callDef_satS (env := env) (ρ := σ) h hw
        (evalArgs_cons (evalExp_var hNv) (evalArgs_cons hcomb evalArgs_nil)) hN)
      obtain ⟨hb₁, hb₂⟩ := sat_s_bounds N
        (Wasm.Numerics.signed_ N i₁.toNat - Wasm.Numerics.signed_ N i₂.toNat)
      have hinv := evalExp_callE_iff.2 (callDef_invSigned (env := env) (ρ := σ) h hv
        (evalArgs_cons (evalExp_var hNv) (evalArgs_cons hsat evalArgs_nil)) hN hb₁ hb₂)
      have hc := evalExp_case_tup_one (op := "%") hinv
      have hlt := invSigned_lt N (Wasm.Numerics.sat_s_ N
        (Wasm.Numerics.signed_ N i₁.toNat - Wasm.Numerics.signed_ N i₂.toNat))
      simpa [bvV, natV, Wasm.Numerics.isub_sat_, Nat.mod_eq_of_lt hlt] using hc

end NumEnvCore

end Silmaril.SpecTec.Equiv
