module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read2.Common

/-!
# Round 5, pass 3, track read: the literal quantifier `c : lit_(zt)`, inverted

The data rules read a field literal `c : lit_(zt)`. For a vector or packed storage type its
image under `$const` is the image of a Core value only below `2 ^ |zt|`. That bound comes from
the quantifier's type: `lit_(V128) = vec_(V128) = vN($vsizenn(V128)) = uN(128)` and
`lit_(pt) = pack_(pt) = iN($psizenn(pt)) = uN(|pt|)`, whose one case has the premise
`i <= 2^N - 1` (`lt_of_hasTyp_uN`, `uN(32)` inversion at every `N`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Read2

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open ConfigOk (uNPrem uNCases evalExp_of_premsOk_if)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-! ## `uN(N)` -/

/-- The scope in which `uN(N)`'s premise is checked for the numeral `n`. -/
noncomputable def uNScopeN (N n : Nat) : VarEnv :=
  caseScope (VarEnv.empty.bindVal "N" (.num (.natN N)))
    (.tupT [.mk "i" (.numT .natT)]) (.tuple [.num (.natN n)])

theorem uNScopeN_N (N n : Nat) : (uNScopeN N n).findVal? "N" = some (Equiv.natV N) := by
  simp [uNScopeN, caseScope, typBinds, Equiv.natV]

theorem uNScopeN_i (N n : Nat) : (uNScopeN N n).findVal? "i" = some (.num (.natN n)) := by
  simp [uNScopeN, caseScope, typBinds]

/-- **`uN(N)`'s premise is false beyond the bound.** -/
theorem evalExp_uNPremN_false {N n : Nat} (hn : 2 ^ N ≤ n) :
    EvalExp (simEnv B) (uNScopeN N n) uNPrem (.bool false) := by
  have hge : EvalExp (simEnv B) (uNScopeN N n)
      (.cmpE .geOp (.numT .natT) (.varE "i") (.numE (.natN 0))) (.bool true) :=
    evalExp_cmpNum (evalExp_var (uNScopeN_i N n)) evalExp_num (by simp [Num.cmp])
  have hpow : EvalExp (simEnv B) (uNScopeN N n)
      (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")) (Equiv.natV (2 ^ N)) :=
    Equiv.evalExp_twoPow (uNScopeN_N N n)
  have hsub : EvalExp (simEnv B) (uNScopeN N n) (.binE .subOp (.numT .intT)
      (.cvtE (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")) .natT .intT)
      (.cvtE (.numE (.natN 1)) .natT .intT)) (.num (.intN ((2 ^ N : Nat) - 1))) :=
    evalExp_binNum (Equiv.evalExp_toInt hpow) Equiv.evalExp_oneInt rfl
  have hk := Equiv.evalExp_toNat (j := ((2 ^ N : Nat) : Int) - 1)
    (by have := Nat.one_le_two_pow (n := N); omega) hsub
  have hcmp : Num.cmp .leOp (.natN n) (.natN ((((2 ^ N : Nat) : Int) - 1).toNat)) =
      some false := by
    simp only [Num.cmp, Option.some.injEq, decide_eq_false_iff_not]
    have := Nat.one_le_two_pow (n := N)
    omega
  exact IntNumeric.evalExp_and hge (evalExp_cmpNum (evalExp_var (uNScopeN_i N n)) hk hcmp)

/-- **Inversion of `uN(N)`**: a typed value is a numeral below `2 ^ N`. -/
theorem lt_of_hasTyp_uN {σ : VarEnv} {e : Exp} {N : Nat} {v : Value}
    (he : EvalExp (simEnv B) σ e (.num (.natN N)))
    (h : HasTyp (simEnv B) σ (.varT "uN" [.expA e]) v) :
    ∃ n, v = pctV n ∧ n < 2 ^ N := by
  obtain ⟨ps, qs, htd⟩ := IntNumeric.findTyp_uN (B := B)
  obtain ⟨td, ws, htd', hargs, hi⟩ := (hasTyp_varT_global_iff (localTyp?_cons _ _ _)).1 h
  rw [htd] at htd'
  obtain rfl := (Option.some.inj htd').symm
  obtain ⟨u, hu, rfl⟩ := evalArgs_expA_iff.1 hargs
  obtain rfl := EvalExp.unique hu he
  have hm0 : MatchArgs (simEnv B) VarEnv.empty [.expA (.varE "N")] [.val (.num (.natN N))]
      (VarEnv.empty.bindVal "N" (.num (.natN N))) :=
    matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil
  have hd : HasTypDef (simEnv B) (VarEnv.empty.bindVal "N" (.num (.natN N)))
      (.variantT (IntNumeric.instCases Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d22 0)) v := by
    rcases hasTypInsts_cons_inv hi with ⟨σ', ⟨k, hk⟩, hd⟩ | hrest
    · rwa [IntNumeric.matchArgs_det hm0 hk] at hd
    · exact absurd hrest not_hasTypInsts_nil
  obtain ⟨op, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 hd
  rw [uNCases] at hc
  by_cases ho : "%" = op
  · subst ho
    obtain ⟨ht, hp⟩ := (hasTypCase_cons_hit_iff rfl).1 hc
    obtain ⟨vs, rfl, htup⟩ := hasTyp_tupT_iff.1 ht
    obtain ⟨x, vs', rfl, hx, hrest⟩ := hasTypTup_cons_iff.1 htup
    obtain rfl := hasTypTup_nil_iff.1 hrest
    obtain ⟨m, rfl, hm⟩ := hasTyp_numT_iff.1 hx
    cases m with
    | natN n =>
      refine ⟨n, rfl, Nat.lt_of_not_le fun hn => ?_⟩
      have htrue : EvalExp (simEnv B) (uNScopeN N n) uNPrem (.bool true) :=
        evalExp_of_premsOk_if hp
      cases htrue.unique (evalExp_uNPremN_false hn)
    | _ => simp [Num.subTyp, Num.toTyp] at hm
  · exact absurd ((hasTypCase_cons_miss_iff ho).1 hc) not_hasTypCase_nil

/-! ## Through the aliases -/

/-- **One alias instance with one variable pattern, inverted.** -/
theorem hasTyp_alias1 {σ : VarEnv} {x y : IL.Id} {args : List Arg} {ps q : List Param} {t : Typ}
    {a v : Value} (htd : (simEnv B).findTyp? x = some (ps, [.instD q [.expA (.varE y)] (.aliasT t)]))
    (hargs : EvalArgs (simEnv B) σ args [.val a]) (hl : localTyp? σ x args = none)
    (h : HasTyp (simEnv B) σ (.varT x args) v) :
    HasTyp (simEnv B) (VarEnv.empty.bindVal y a) t v := by
  obtain ⟨td, ws, htd', hargs', hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [htd] at htd'
  obtain rfl := (Option.some.inj htd').symm
  obtain rfl := Equiv.ExecNumeric.evalArgs_unique hargs' hargs
  have hm0 : MatchArgs (simEnv B) VarEnv.empty [.expA (.varE y)] [.val a]
      (VarEnv.empty.bindVal y a) :=
    matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil
  rcases hasTypInsts_cons_inv hi with ⟨σ', ⟨k, hk⟩, hd⟩ | hrest
  · rw [IntNumeric.matchArgs_det hm0 hk] at hd
    exact hasTypDef_aliasT_iff.1 hd
  · exact absurd hrest not_hasTypInsts_nil

set_option maxRecDepth 100000 in
/-- **A `lit_(V128)` literal is a numeral below `2 ^ 128`.** -/
theorem lit_vec_inv {ρ : VarEnv} {c : Value}
    (hz : ρ.findVal? "zt" = some (tyV (Ty.val (Ty.vec .v128) : CStorageType)))
    (h : HasTyp (simEnv B) ρ (.varT "lit_" [.expA (.varE "zt")]) c) :
    ∃ k, c = pctV k ∧ k < 2 ^ 128 := by
  obtain ⟨ps, q₁, q₂, q₃, htd⟩ := R4Fwd.findTyp_lit B
  obtain ⟨td, ws, htd', hargs, hi⟩ := (hasTyp_varT_global_iff (localTyp?_cons _ _ _)).1 h
  rw [htd] at htd'
  obtain rfl := (Option.some.inj htd').symm
  obtain rfl := Equiv.ExecNumeric.evalArgs_unique hargs
    (Equiv.evalArgs_cons (evalExp_var hz) Equiv.evalArgs_nil)
  rcases hasTypInsts_cons_inv hi with ⟨σ, hm, -⟩ | hi
  · exact (Prims.not_matchArgs_of_undef (matchArgs_cons_undef
      (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub rfl)) hm).elim
  have hm0 : MatchArgs (simEnv B) VarEnv.empty [.expA R4Fwd.vectypePatZ]
      [.val (tyV (Ty.val (Ty.vec .v128) : CStorageType))]
      (VarEnv.empty.bindVal "vectype" (caseNilV "V128")) :=
    matchArgs_cons (matchArg_expA (Aggregates.matchExp_subE (matchExp_varE rfl)) rfl)
      matchArgs_nil
  rcases hasTypInsts_cons_inv hi with ⟨σ, ⟨k, hk⟩, hd⟩ | hi
  · rw [IntNumeric.matchArgs_det hm0 hk] at hd
    have h₁ := hasTypDef_aliasT_iff.1 hd
    obtain ⟨ps', qs', htv⟩ := Typing.findTyp_vec (B := B)
    have h₂ := hasTyp_alias1 htv (Equiv.evalArgs_cons (evalExp_var (v := caseNilV "V128")
      (by simp)) Equiv.evalArgs_nil)
      (localTyp?_cons _ _ _) h₁
    obtain ⟨ps'', qs'', htN⟩ := Typing.findTyp_vN (B := B)
    have h₃ := hasTyp_alias1 htN (Equiv.evalArgs_cons (evalExp_callE_iff.2
      (Typing.callDef_vsizenn rfl (Equiv.evalArgs_cons (evalExp_var (by simp))
        Equiv.evalArgs_nil))) Equiv.evalArgs_nil) (localTyp?_cons _ _ _) h₂
    exact lt_of_hasTyp_uN (evalExp_var (by simp; rfl)) h₃
  · rcases hasTypInsts_cons_inv hi with ⟨σ, hm, -⟩ | hi
    · exact (Prims.not_matchArgs_of_undef (matchArgs_cons_undef
        (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub rfl)) hm).elim
    · exact absurd hi not_hasTypInsts_nil

set_option maxRecDepth 100000 in
/-- **A `lit_(pt)` literal is a numeral below `2 ^ |pt|`.** -/
theorem lit_pack_inv {ρ : VarEnv} {c : Value} {p : PackType}
    (hz : ρ.findVal? "zt" = some (tyV (Ty.pack p : CStorageType)))
    (h : HasTyp (simEnv B) ρ (.varT "lit_" [.expA (.varE "zt")]) c) :
    ∃ k, c = pctV k ∧ k < 2 ^ p.width := by
  obtain ⟨ps, q₁, q₂, q₃, htd⟩ := R4Fwd.findTyp_lit B
  obtain ⟨td, ws, htd', hargs, hi⟩ := (hasTyp_varT_global_iff (localTyp?_cons _ _ _)).1 h
  rw [htd] at htd'
  obtain rfl := (Option.some.inj htd').symm
  obtain rfl := Equiv.ExecNumeric.evalArgs_unique hargs
    (Equiv.evalArgs_cons (evalExp_var hz) Equiv.evalArgs_nil)
  rcases hasTypInsts_cons_inv hi with ⟨σ, hm, -⟩ | hi
  · exact (Prims.not_matchArgs_of_undef (matchArgs_cons_undef
      (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub (by cases p <;> rfl))) hm).elim
  rcases hasTypInsts_cons_inv hi with ⟨σ, hm, -⟩ | hi
  · exact (Prims.not_matchArgs_of_undef (matchArgs_cons_undef
      (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub (by cases p <;> rfl))) hm).elim
  have hm0 : MatchArgs (simEnv B) VarEnv.empty [.expA R4Fwd.packtypePat]
      [.val (tyV (Ty.pack p : CStorageType))]
      (VarEnv.empty.bindVal "packtype" (tyV (Ty.pack p : CStorageType))) :=
    matchArgs_cons (matchArg_expA (Aggregates.matchExp_subE (matchExp_varE rfl))
      (R4Fwd.argSubOk_packtypePat_pack p rfl)) matchArgs_nil
  rcases hasTypInsts_cons_inv hi with ⟨σ, ⟨k, hk⟩, hd⟩ | hi
  · rw [IntNumeric.matchArgs_det hm0 hk] at hd
    have h₁ := hasTypDef_aliasT_iff.1 hd
    obtain ⟨ps', qs', htp⟩ := R4Fwd.findTyp_pack B
    have h₂ := hasTyp_alias1 htp (Equiv.evalArgs_cons
      (evalExp_var (v := tyV (Ty.pack p : CStorageType)) (by simp)) Equiv.evalArgs_nil)
      (localTyp?_cons _ _ _) h₁
    obtain ⟨ps'', qs'', htN⟩ := IntNumeric.findTyp_iN (B := B)
    have h₃ := hasTyp_alias1 htN (Equiv.evalArgs_cons (Vec.evalExp_call rfl
      (Equiv.evalArgs_cons (evalExp_var (by simp)) Equiv.evalArgs_nil) (R4Fwd.applies_psizenn p))
      Equiv.evalArgs_nil) (localTyp?_cons _ _ _) h₂
    exact lt_of_hasTyp_uN (evalExp_var (by simp; rfl)) h₃
  · exact absurd hi not_hasTypInsts_nil

end Silmaril.Wasm.SpecTec.Sim.Round5.Read2
