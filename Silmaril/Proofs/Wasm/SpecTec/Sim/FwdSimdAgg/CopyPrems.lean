module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.FwdSimdAgg.NewDefault

/-!
# Track `fwd-simd-agg`: `$sx`, and the earlier `array.copy` rules refuted

Shared lemmas of `Copy.lean` and `InitElem.lean` (split for elaboration time).

# Track `fwd-simd-agg`: `array.copy-le`, `array.copy-gt`, `array.init_elem-succ`, forward

The three `otherwise` rules of `array.copy` and `array.init_elem` that family R left open
(`Step_read` 91, 92, 97). The pattern is family R's `array.fill-succ` (`RefsGC.sread_arrayFillSucc`):
the `otherwise` premise is discharged by opcode (`RefsGC.otherwise_of_ruleAt`), refuting by hand the
earlier rules with the same tags (`*-oob*` by the bounds, `*-zero` by `n ≠ 0`, `copy-le` by
`i₂ < i₁`), and the successor indices are read off the store bounds (`Aggregates.Bounded`).

`array.copy`'s rules read the element signedness as `sx? = $sx(zt_2)`. For an unpacked
`zt_2 = t` this is `ε`: by `$sx`'s `consttype` clause for numeric and vector types, and, for a
reference type (where `$sx` has no clause, `FwdSimdAgg/Defs.lean`), by `B` (`VVB`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_nil)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV mutV)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open RefsGC

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins} {H : Type} {hn : H → String}

/-! ## `$sx` on unpacked storage types -/

/-- The pattern `consttype <: storagetype` of `$sx`'s first clause. -/
abbrev consttypePat : Exp := .subE (.varE "consttype") (.varT "consttype" []) (.varT "storagetype" [])

/-- The pattern `packtype <: storagetype` of `$sx`'s second clause. -/
abbrev packtypePat : Exp := .subE (.varE "packtype") (.varT "packtype" []) (.varT "storagetype" [])

set_option maxRecDepth 100000 in
theorem findDef_sx (B : Builtins) : (simEnv B).findDef? "sx" = some ([.expP "storagetype"
    (.varT "storagetype" [])], .iterT (.varT "sx" []) .opt,
    [.defD [.expP "consttype" (.varT "consttype" [])] [.expA consttypePat] (.optE none) [],
     .defD [.expP "packtype" (.varT "packtype" [])] [.expA packtypePat]
       (.optE (some (.caseE "S" (.tupE [])))) []]) := rfl

set_option maxRecDepth 100000 in
/-- **`$sx(t) = ε`** at the image of every unpacked storage type, given `VVB B` (for reference
types and `BOT`, where `$sx` has no clause). -/
theorem applies_sx_val (hV : VVB B) (t : CValType) :
    Applies (simEnv B) "sx" [.val (tyV (Ty.val t : CStorageType))] (.opt none) := by
  have hhit : ∀ w : Value, argSubOk (simEnv B) VarEnv.empty consttypePat w = true →
      TryClauses (simEnv B) [.defD [.expP "consttype"
        (.varT "consttype" [])] [.expA consttypePat] (.optE none) [],
        .defD [.expP "packtype" (.varT "packtype" [])] [.expA packtypePat]
          (.optE (some (.caseE "S" (.tupE [])))) []] [.val w] (.opt none) := fun w hs =>
    tryClauses_hit (matchArgs_cons (matchArg_expA (Prims.matchExp_subE (matchExp_varE (by simp)))
      hs) matchArgs_nil) premsHold_nil (by simpa using (evalExp_optE_none_iff (env := simEnv B)
        (ρ := VarEnv.empty.bindVal "consttype" w)).2 rfl)
  have hmiss : ∀ w : Value, argSubOk (simEnv B) VarEnv.empty consttypePat w = false →
      argSubOk (simEnv B) VarEnv.empty packtypePat w = false →
      Applies (simEnv B) "sx" [.val w] (.opt none) := fun w h₁ h₂ =>
    ⟨_, _, _, findDef_sx B, Or.inr ⟨IntNumeric.tryClausesUndef_skip_match
      (matchArgs_cons_undef (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub h₁))
      (IntNumeric.tryClausesUndef_skip_match
        (matchArgs_cons_undef (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub h₂))
        IntNumeric.tryClausesUndef_nil), hV _ _ _ rfl⟩⟩
  cases t with
  | num t =>
    refine ⟨_, _, _, findDef_sx B, Or.inl (hhit (tyV (Ty.val (Ty.num t) : CStorageType)) ?_)⟩
    rcases t with t | t <;> cases t <;> rfl
  | vec t =>
    refine ⟨_, _, _, findDef_sx B, Or.inl (hhit (tyV (Ty.val (Ty.vec t) : CStorageType)) ?_)⟩
    cases t
    rfl
  | refv r =>
    show Applies (simEnv B) "sx" [.val (tyV r)] (.opt none)
    obtain ⟨b, h⟩ := r
    refine hmiss _ ?_ ?_
    · show argSubOk (simEnv B) VarEnv.empty consttypePat (.case "REF" _) = false
      rw [argSubOk, Aggregates.subCaseOk_case]
      rfl
    · show argSubOk (simEnv B) VarEnv.empty packtypePat (.case "REF" _) = false
      rw [argSubOk, Aggregates.subCaseOk_case]
      rfl
  | botv => exact hmiss _ rfl rfl

/-! ## Refuting the earlier `array.copy` rules -/

/-- `array.copy-zero` does not fire for `n ≠ 0`. -/
theorem not_arrayCopyZero {env : Env} {D : Interp} {els : Prop} {s : Store H} {f : Frame}
    {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32} {a₁ a₂ : Nat} (hn0 : n ≠ 0) {c : Value} :
    ¬ RuleBody env D els [] [] "%~>%" arrayCopyZeroRule
      (.tuple [configV hn ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 n,
        .plain (.arrayCopy x₁ x₂)]⟩, c]) := by
  rintro ⟨-, ρ₀, σ, -, -, he, hp⟩
  obtain ⟨-, hl⟩ := cfgz_inv (lhs_of_concl he)
  obtain ⟨-, -, -, -, hn'⟩ := binds_arrayCopy hl
  have hif := premW_if (hp _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have h0 : Value.num (.natN n.toNat) = .num (.natN 0) := eq_of_evalExp_eq hif hn' evalExp_num'
  simp only [Value.num.injEq, Num.natN.injEq] at h0
  exact hn0 (BitVec.eq_of_toNat_eq (by simpa using h0))

/-- A conjunction whose left conjunct is false is not true. -/
theorem not_and_true_of_left {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {t : OpTyp}
    (h₁ : EvalExp env ρ e₁ (.bool false)) : ¬ EvalExp env ρ (.binE .andOp t e₁ e₂) (.bool true) := by
  intro h
  obtain ⟨v₁, hv₁, hrest⟩ := evalExp_binE_iff.1 h
  obtain rfl := EvalExp.unique hv₁ h₁
  simp_all [boolShort]

/-- `array.copy-le` does not fire when the destination is above the source. -/
theorem not_arrayCopyLe {env : Env} {D : Interp} {els : Prop} {s : Store H} {f : Frame}
    {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32} {a₁ a₂ : Nat} (hgt : i₂.toNat < i₁.toNat) {c : Value} :
    ¬ RuleBody env D els [] [] "%~>%" arrayCopyLeRule
      (.tuple [configV hn ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 n,
        .plain (.arrayCopy x₁ x₂)]⟩, c]) := by
  rintro ⟨-, ρ₀, σ, -, -, he, hp⟩
  obtain ⟨-, hl⟩ := cfgz_inv (lhs_of_concl he)
  obtain ⟨-, hi₁, -, hi₂, -⟩ := binds_arrayCopy hl
  have hif := premW_if (hp _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_singleton_self _))))
  exact not_and_true_of_left (evalExp_cmpNat (evalExp_unpct hi₁) (evalExp_unpct hi₂)
    (by simp [Num.cmp]; omega)) hif

/-- The left-hand side of an `array.copy` step. -/
theorem lhsIn_arrayCopy {s : Store H} {f : Frame} {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32}
    {a₁ a₂ : Nat} :
    LhsIn ["ARRAY.COPY", "REF.ARRAY_ADDR", "CONST"]
      (configV hn ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 n,
        .plain (.arrayCopy x₁ x₂)]⟩) :=
  .inr ⟨_, _, rfl, tagsIn_cons (tag_case (by decide)) (tagsIn_cons (tag_case (by decide))
    (tagsIn_cons (tag_case (by decide)) (tagsIn_cons (tag_case (by decide))
    (tagsIn_cons (tag_case (by decide)) (tagsIn_cons (tag_case (by decide)) tagsIn_nil)))))⟩

/-- A store-bounded successor index. -/
theorem toNat_succ {i n : BitVec 32} {m : Nat} (h : i.toNat + n.toNat ≤ m) (hm : m < 2 ^ 32)
    (hn0 : n ≠ 0) : (i + 1).toNat = i.toNat + 1 := by
  have : n.toNat ≠ 0 := fun h' => hn0 (BitVec.eq_of_toNat_eq (by simpa using h'))
  exact toNat_add_one (by omega)

/-- `i + n - 1` without wrap, for a store-bounded range. -/
theorem toNat_last {i n : BitVec 32} {m : Nat} (h : i.toNat + n.toNat ≤ m) (hm : m < 2 ^ 32)
    (hn0 : n ≠ 0) : (i + n - 1).toNat = i.toNat + n.toNat - 1 := by
  have : n.toNat ≠ 0 := fun h' => hn0 (BitVec.eq_of_toNat_eq (by simpa using h'))
  simp only [BitVec.toNat_sub, BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl]
  omega

end Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg
