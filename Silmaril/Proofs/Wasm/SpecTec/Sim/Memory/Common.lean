module

public import Silmaril.Wasm.SpecTec.Sim.Memory.Defs
public import Silmaril.Wasm.SpecTec.Sim.State.Thms
public import Silmaril.Wasm.SpecTec.Sim.RefsGC.Thms

/-!
# Shared facts

Bit-vector arithmetic without wrap, inversions of the `CONST at i` patterns the table and memory
rules use (for any address-type expression), and evaluation of the store accessors in the
assignment of an arbitrary rule body.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Memory

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-! ## Bit vectors without wrap -/

/-- `(i + 1).toNat`, when it does not wrap. -/
theorem toNat_add_one {w : Nat} {i : BitVec w} (h : i.toNat + 1 < 2 ^ w) :
    (i + 1).toNat = i.toNat + 1 := by
  have h1 : (1 : BitVec w).toNat = 1 := by
    change (BitVec.ofNat w 1).toNat = 1
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add, h1]
  exact Nat.mod_eq_of_lt h

/-- `(n - 1).toNat` for `n ≠ 0`. -/
theorem toNat_sub_one {w : Nat} {n : BitVec w} (h : n ≠ 0) : (n - 1).toNat = n.toNat - 1 := by
  have hn : n.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
  have hw : 1 < 2 ^ w := by
    have := n.isLt
    rcases Nat.lt_or_ge 1 (2 ^ w) with h₁ | h₁
    · exact h₁
    · omega
  have h1 : (1 : BitVec w).toNat = 1 := by
    change (BitVec.ofNat w 1).toNat = 1
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hw
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1]; omega), h1]

/-- `BitVec.ofNat w k` is `k` below `2 ^ w`. -/
theorem toNat_ofNat_of_lt {w k : Nat} (h : k < 2 ^ w) : (BitVec.ofNat w k).toNat = k := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

/-! ## Rule bodies have no definition bindings -/

/-- A rule body's assignment binds values only. -/
theorem findDef_bindVals_empty (σ : List (IL.Id × Value)) (x : IL.Id) :
    (VarEnv.empty.bindVals σ).findDef? x = none := rfl

/-- The parameters of a parameterless rule bind nothing. -/
theorem bindParams_nil {ρ₀ : VarEnv} (h : bindParams VarEnv.empty [] [] = some ρ₀) :
    ρ₀ = VarEnv.empty := by
  simpa [bindParams] using h.symm

/-! ## Inverting `CONST` patterns -/

variable {env : Env} {ρ : VarEnv}

/-- `CONST t x`, inverted, for any type expression `t`. -/
theorem const_inv {e : Exp} {x : IL.Id} {t v : Value}
    (h : EvalExp env ρ (.caseE "CONST" (.tupE [e, .varE x])) (.case "CONST" (.tuple [t, v]))) :
    EvalExp env ρ (.varE x) v :=
  (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv
    (RefsGC.elems_of_tup (RefsGC.case_inv h))).2).1

/-- `CONST t (% x)`, inverted, for any type expression `t`. -/
theorem const_pct_inv {e : Exp} {x : IL.Id} {t v : Value}
    (h : EvalExp env ρ (.caseE "CONST" (.tupE [e, .caseE "%" (.tupE [.varE x])]))
      (.case "CONST" (.tuple [t, .case "%" (.tuple [v])]))) :
    EvalExp env ρ (.varE x) v :=
  have hp := (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv
    (RefsGC.elems_of_tup (RefsGC.case_inv h))).2).1
  (RefsGC.evalExps_cons_inv (RefsGC.elems_of_tup (RefsGC.case_inv hp))).1

/-- The components of a pair. -/
theorem tup2_inv {e₁ e₂ : Exp} {v₁ v₂ : Value}
    (h : EvalExp env ρ (.tupE [e₁, e₂]) (.tuple [v₁, v₂])) :
    EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ := by
  have hs := RefsGC.elems_of_tup h
  exact ⟨(RefsGC.evalExps_cons_inv hs).1,
    (RefsGC.evalExps_cons_inv (RefsGC.evalExps_cons_inv hs).2).1⟩

/-- A `%`-wrapped natural, as the rules build it: `% e`. -/
theorem evalExp_pct {e : Exp} {n : Nat} (h : EvalExp env ρ e (.num (.natN n))) :
    EvalExp env ρ (.caseE "%" (.tupE [e])) (State.idxV n) :=
  evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons h evalExps_nil, rfl⟩)

/-- An address-type variable coerced to `numtype`, as the rules write `CONST at …`. -/
theorem evalExp_subAt {x : IL.Id} {v : Value} (h : ρ.findVal? x = some v) :
    EvalExp env ρ (.subE (.varE x) (.varT "addrtype" []) (.varT "numtype" [])) v :=
  RefsGC.evalExp_sub_of (evalExp_var h)

/-- `CONST t (% e)`. -/
theorem evalExp_constPct {et e : Exp} {t : Value} {n : Nat} (ht : EvalExp env ρ et t)
    (h : EvalExp env ρ e (.num (.natN n))) :
    EvalExp env ρ (.caseE "CONST" (.tupE [et, .caseE "%" (.tupE [e])]))
      (State.aconstV t n) :=
  evalExp_case (evalExp_tup2 ht (evalExp_pct h))

end Silmaril.Wasm.SpecTec.Sim.Memory

namespace Silmaril.Wasm.SpecTec.Sim.Memory

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

variable {env : Env} {ρ : VarEnv}

/-- The empty option. -/
theorem evalExp_optNone : EvalExp env ρ (.optE none) (.opt none) := evalExp_optE_none_iff.2 rfl

/-- A present option. -/
theorem evalExp_optSome {e : Exp} {w : Value} (h : EvalExp env ρ e w) :
    EvalExp env ρ (.optE (some e)) (.opt (some w)) := evalExp_optE_some_iff.2 ⟨w, h, rfl⟩

end Silmaril.Wasm.SpecTec.Sim.Memory

/-- `eval_tac`, also through option expressions. -/
macro "mem_eval_tac" : tactic =>
  `(tactic| repeat (first
    | exact Silmaril.Wasm.SpecTec.Sim.RefsGC.evalExps_nil'
    | exact Silmaril.Wasm.SpecTec.Sim.Memory.evalExp_optNone
    | apply Silmaril.Wasm.SpecTec.Sim.Memory.evalExp_optSome
    | apply Silmaril.Wasm.SpecTec.Sim.RefsGC.evalExps_cons'
    | apply Silmaril.Wasm.SpecTec.Sim.RefsGC.evalExp_tupE_of
    | apply Silmaril.Wasm.SpecTec.Sim.RefsGC.evalExp_listE_of
    | apply Silmaril.Wasm.SpecTec.Sim.evalExp_case
    | apply Silmaril.Wasm.SpecTec.Sim.RefsGC.evalExp_sub_of
    | exact Silmaril.Wasm.SpecTec.Sim.RefsGC.evalExp_num'
    | (apply Silmaril.Wasm.SpecTec.Sim.evalExp_var; rfl)))
