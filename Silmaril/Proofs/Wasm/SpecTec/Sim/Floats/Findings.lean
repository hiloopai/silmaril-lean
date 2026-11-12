module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Floats.ConvCall
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Floats.Dispatch
public import Silmaril.Wasm.SpecTec.Sim.Whole.Defs

/-!
# Float track: family R's `RFuns`, refuted as first stated and proved in term-only scopes

`RefsGC.RFuns` asks `$wrap__(32, 31, e)` and `$extend__(31, 32, es, e)` to evaluate in **every**
scope `ρ`. A call first resolves its name through the scope's definition variables
(`Sem.callDef`: `(ρ.findDef? x).getD x`), so in a scope that binds `wrap__` to a name with no
definition the call has no value. Hence round 1's `RFuns (simEnv B)` was false for every `B`
(`not_rFuns_unrestricted`), and with it round 1's `Whole.Assumptions B hn host`. The rules only
ever call the primitives in term-only scopes (`ValsOnly`); restricted to those, the two facts hold
for every `B` extending the float primitives (`rFunsVals_of_floatB`). The integration branch
restricts every field of `RefsGC.RFuns` and `RefsGC.RStoreFuns` to `ValsOnly` scopes (the fix of
the aggregates track), so `RFuns` is now `RFunsVals` up to argument order.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Floats

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics

variable {B : Builtins} {P : Profile}

/-- A scope binding the definition variable `wrap__` to a name with no definition. -/
abbrev redirectScope : VarEnv := VarEnv.empty.bindDef "wrap__" "wrap__#"

set_option maxRecDepth 100000 in
theorem findDef_redirect : (simEnv B).findDef? "wrap__#" = none := rfl

/-- In `redirectScope`, no call of `wrap__` has a value. -/
theorem not_evalExp_wrap_redirect {args : List Arg} {v : Value} :
    ¬ EvalExp (simEnv B) redirectScope (.callE "wrap__" args) v := by
  intro h
  obtain ⟨ws, ps, t, cs, -, hd, -⟩ := Equiv.ExecNumeric.callDef_iff.1 (evalExp_callE_iff.1 h)
  have hx : (redirectScope.findDef? "wrap__").getD "wrap__" = "wrap__#" := rfl
  rw [hx, findDef_redirect] at hd
  exact nomatch hd

/-- The `u32` literal `%(0)`. -/
theorem evalExp_pct0 {ρ : VarEnv} :
    EvalExp (simEnv B) ρ (.caseE "%" (.tupE [.numE (.natN 0)])) (pctV (0 : BitVec 32).toNat) :=
  evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[natV 0],
    Equiv.Validation.evalExps_cons_iff.2 ⟨_, _, rfl, evalExp_num,
      Equiv.Validation.evalExps_nil_iff.2 rfl⟩, rfl⟩, rfl⟩

/-- **The round-1 statement of `RFuns.wrap` is false in every `simEnv B`**: quantified over every
scope, it fails in `redirectScope`. (Round 1's `RefsGC.RFuns` had this shape; the integration
branch restricts its fields to term-only scopes, `ValsOnly`, which `rFunsVals_of_floatB` proves.) -/
theorem not_rFuns_unrestricted (B : Builtins) :
    ¬ ∀ (ρ : VarEnv) (e : Exp) (i : BitVec 32), EvalExp (simEnv B) ρ e (pctV i.toNat) →
      EvalExp (simEnv B) ρ
        (.callE "wrap__" [.expA (.numE (.natN 32)), .expA (.numE (.natN 31)), .expA e])
        (pctV (i.setWidth 31).toNat) := fun F =>
  not_evalExp_wrap_redirect (F redirectScope _ 0 evalExp_pct0)

/-- `RFuns` restricted to the term-only scopes the rules use. -/
structure RFunsVals (env : Env) : Prop where
  /-- `$wrap__(32, 31, i)`. -/
  wrap : ∀ (ρ : VarEnv), ValsOnly ρ → ∀ (e : Exp) (i : BitVec 32), EvalExp env ρ e (pctV i.toNat) →
    EvalExp env ρ (.callE "wrap__" [.expA (.numE (.natN 32)), .expA (.numE (.natN 31)), .expA e])
      (pctV (i.setWidth 31).toNat)
  /-- `$extend__(31, 32, sx, i)`. -/
  extend : ∀ (ρ : VarEnv), ValsOnly ρ → ∀ (es e : Exp) (s : Signedness) (i : BitVec 31),
    EvalExp env ρ es (sxV s) → EvalExp env ρ e (pctV i.toNat) →
    EvalExp env ρ (.callE "extend__" [.expA (.numE (.natN 31)), .expA (.numE (.natN 32)),
      .expA es, .expA e])
      (pctV (match s with | .signed => i.signExtend 32 | .unsigned => i.setWidth 32).toNat)

/-- A term-only scope binds no definition variable. -/
theorem findDef_valsOnly {ρ : VarEnv} (hρ : ValsOnly ρ) (x : IL.Id) : ρ.findDef? x = none := by
  simp [VarEnv.findDef?, hρ.2.1]

set_option maxRecDepth 100000 in
/-- **`RFuns` in term-only scopes**, for every `B` extending the float primitives. -/
theorem rFunsVals_of_floatB (hB : FloatB P B) : RFunsVals (simEnv B) where
  wrap _ hρ _ i he := evalExp_callE_iff.2 (callDef_floatPrim hB ⟨_, _, rfl⟩
    (findDef_valsOnly hρ _)
    (Equiv.evalArgs_cons evalExp_num (Equiv.evalArgs_cons evalExp_num
      (Equiv.evalArgs_cons he Equiv.evalArgs_nil)))
    (floatCall_wrap P 32 31 i))
  extend _ hρ _ _ s i hs he := evalExp_callE_iff.2 (callDef_floatPrim hB ⟨_, _, rfl⟩
    (findDef_valsOnly hρ _)
    (Equiv.evalArgs_cons evalExp_num (Equiv.evalArgs_cons evalExp_num
      (Equiv.evalArgs_cons hs (Equiv.evalArgs_cons he Equiv.evalArgs_nil))))
    (floatCall_extend P 31 32 s i))

end Silmaril.Wasm.SpecTec.Sim.Floats
