module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecFixBase

/-!
# The vector errata: `uN` in `simEnv20V B`

`hasTyp_uN_of`: `uN(N)` holds every natural below `2^N`, in any environment whose `uN` is the
2.0 one. `findTyp_uN20V`: the
lookup in `simEnv20V B` (kernel `rfl`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecFix

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm
open Silmaril.Wasm.SpecTec.Scripts.Wasm20 (Original.d17)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (instCases findCase quantFreeAt hasTypCase_of_findCase
  premsOk_if evalExp_and)
open Silmaril.Wasm.SpecTec.Sim (ValsOnly TypedV)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-- `uN(N)` holds every natural below `2^N`, in any environment with the 2.0 `uN`. -/
theorem hasTyp_uN_of {env : Env} {ps : List Param} {qs : List Param}
    (htd : env.findTyp? "uN" =
      some (ps, [.instD qs [.expA (.varE "N")] (.variantT (instCases Original.d17 0))]))
    {ρ : VarEnv} {e : Exp} {N n : Nat} (he : EvalExp env ρ e (natV N)) (hn : n < 2 ^ N) :
    HasTyp env ρ (.varT "uN" [.expA e]) (.case "%" (.tuple [natV n])) := by
  have htup : HasTyp env (VarEnv.empty.bindVal "N" (natV N))
      (.tupT [.mk "i" (.numT .natT)]) (.tuple [natV n]) :=
    hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_numT_iff.2 ⟨_, rfl, rfl⟩,
      hasTypTup_nil_iff.2 rfl⟩⟩
  have hpow : EvalExp env ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i" (natV n))
      (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N")) (natV (2 ^ N)) :=
    Equiv.evalExp_twoPow (by simp)
  have hsub : EvalExp env ((VarEnv.empty.bindVal "N" (natV N)).bindVal "i" (natV n))
      (.binE .subOp (.numT .intT) (.cvtE (.binE .powOp (.numT .natT) (.numE (.natN 2))
        (.varE "N")) .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT))
      (.num (.intN ((2 ^ N : Nat) - 1))) :=
    evalExp_binNum (Equiv.evalExp_toInt hpow) Equiv.evalExp_oneInt rfl
  have hk := Equiv.evalExp_toNat (j := ((2 ^ N : Nat) : Int) - 1)
    (by have := Nat.one_le_two_pow (n := N); omega) hsub
  refine hasTyp_varT_case (localTyp?_cons _ _ _) htd
    (Equiv.evalArgs_cons he Equiv.evalArgs_nil)
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
    (hasTypCase_of_findCase rfl htup (premsOk_if (evalExp_and ?_ ?_)))
  · exact evalExp_cmpNum (Sim.evalExp_var (v := natV n) rfl) evalExp_num (by simp [Num.cmp])
  · refine evalExp_cmpNum (Sim.evalExp_var (v := natV n) rfl) hk ?_
    simp only [Num.cmp, Option.some.injEq, decide_eq_true_eq]
    omega

set_option maxRecDepth 100000 in
theorem findTyp_uN20V : ∃ ps qs, (simEnv20V B).findTyp? "uN" =
    some (ps, [.instD qs [.expA (.varE "N")] (.variantT (instCases Original.d17 0))]) :=
  ⟨_, _, rfl⟩

end Silmaril.Wasm.SpecTec.Sim20.VecFix
