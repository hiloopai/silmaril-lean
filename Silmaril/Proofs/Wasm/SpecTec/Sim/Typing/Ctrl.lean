module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Float
public import Silmaril.Proofs.Wasm.SpecTec.Sim.IntNumeric.Parametric
public import Silmaril.Wasm.SpecTec.Sim.Control.Thms

/-!
# Family C's typing interface `CtrlTyping` holds in every `simEnv B`

`ctrlTyping_simEnv`: naturals are `n`, `m`, `addr`; indices are `idx`/`labelidx`; 32-bit patterns
are `num_(I32)`; `_IDX y` is a `typeuse`; and the components of a typed `IF`, `BLOCK`, `LOOP`,
`CALL_REF`, `RETURN_CALL_REF` are typed. Everything is read off the fixed script's type
definitions (`instr`, `typeuse`, `idx`, `u32`, `n`, `m`, `addr`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Typing

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV)
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d95)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-- A closed alias of `nat` holds every natural. -/
theorem typedV_natAlias {x : IL.Id}
    (htd : (simEnv B).findTyp? x = some ([], [.instD [] [] (.aliasT (.numT .natT))]))
    (k : Nat) : TypedV (simEnv B) (.varT x []) (.num (.natN k)) := fun ρ hρ =>
  hasTyp_varT_of_insts (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) htd Equiv.evalArgs_nil
    (hasTypInsts_head matchArgs_nil (hasTypDef_aliasT_iff.2 (hasTyp_numT_iff.2 ⟨_, rfl, rfl⟩)))

/-- A closed alias of a closed type name. -/
theorem typedV_alias {x y : IL.Id}
    (htd : (simEnv B).findTyp? x = some ([], [.instD [] [] (.aliasT (.varT y []))]))
    {v : Value} (h : TypedV (simEnv B) (.varT y []) v) : TypedV (simEnv B) (.varT x []) v :=
  fun ρ hρ =>
    hasTyp_varT_of_insts (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) htd Equiv.evalArgs_nil
      (hasTypInsts_head matchArgs_nil (hasTypDef_aliasT_iff.2 (h VarEnv.empty ⟨rfl, rfl, rfl⟩)))

set_option maxRecDepth 100000 in
theorem findTyp_n : (simEnv B).findTyp? "n" = some ([], [.instD [] [] (.aliasT (.numT .natT))]) :=
  rfl
set_option maxRecDepth 100000 in
theorem findTyp_addr :
    (simEnv B).findTyp? "addr" = some ([], [.instD [] [] (.aliasT (.numT .natT))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_idx :
    (simEnv B).findTyp? "idx" = some ([], [.instD [] [] (.aliasT (.varT "u32" []))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_labelidx :
    (simEnv B).findTyp? "labelidx" = some ([], [.instD [] [] (.aliasT (.varT "idx" []))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_typeidx :
    (simEnv B).findTyp? "typeidx" = some ([], [.instD [] [] (.aliasT (.varT "idx" []))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_u32 : (simEnv B).findTyp? "u32" =
    some ([], [.instD [] [] (.aliasT (.varT "uN" [.expA (.numE (.natN 32))]))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_typeuse : (simEnv B).findTyp? "typeuse" =
    some ([], [.instD [] [] (.variantT (IntNumeric.recCases Original.d95 0 0))]) := rfl

/-- `u32` holds every natural below `2^32`. -/
theorem typedV_u32 {k : Nat} (hk : k < 2 ^ 32) :
    TypedV (simEnv B) (.varT "u32" []) (Equiv.Execution.pctV k) := fun ρ hρ =>
  hasTyp_varT_of_insts (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) findTyp_u32
    Equiv.evalArgs_nil (hasTypInsts_head matchArgs_nil
      (hasTypDef_aliasT_iff.2 (IntNumeric.hasTyp_uN evalExp_num hk)))

/-- Every index is an `idx`. -/
theorem typedV_idx {k : Silmaril.Wasm.IndexKind} (x : Silmaril.Wasm.Idx k) :
    TypedV (simEnv B) (.varT "idx" []) (Encode.toValue x) :=
  typedV_alias findTyp_idx (typedV_u32 x.value.isLt)

/-- A term-only scope's view of a closed type is every term-only scope's. -/
theorem typedV_of_hasTyp {ρ : VarEnv} (hρ : ValsOnly ρ) {x : IL.Id} {v : Value}
    (h : HasTyp (simEnv B) ρ (.varT x []) v) : TypedV (simEnv B) (.varT x []) v :=
  fun _ hρ' => IntNumeric.hasTyp_varT_nil_congr hρ hρ' h

/-- The same, for a list type. -/
theorem typedV_list_of_hasTyp {ρ : VarEnv} (hρ : ValsOnly ρ) {x : IL.Id} {v : Value}
    (h : HasTyp (simEnv B) ρ (.iterT (.varT x []) .list) v) :
    TypedV (simEnv B) (.iterT (.varT x []) .list) v := fun _ hρ' => by
  obtain ⟨l, rfl, hl⟩ := hasTyp_iterT_list_iff.1 h
  exact hasTyp_iterT_list_iff.2 ⟨l, rfl, hasTypList_iff.2 fun u hu =>
    IntNumeric.hasTyp_varT_nil_congr hρ hρ' (hasTypList_iff.1 hl u hu)⟩

/-- The scopes a tuple's binders build stay term-only. -/
theorem valsOnly_empty_bind (x : IL.Id) (v : Value) : ValsOnly (VarEnv.empty.bindVal x v) :=
  ⟨rfl, rfl, rfl⟩

/-- **Family C's typing interface holds in every `simEnv B`.** -/
theorem ctrlTyping_simEnv (B : Builtins) : CtrlTyping (simEnv B) where
  nat := typedV_natAlias findTyp_n
  natM := typedV_natAlias findTyp_m
  addr := typedV_natAlias findTyp_addr
  labelidx l := typedV_alias findTyp_labelidx (typedV_idx l)
  idx x := typedV_idx x
  i32 c := fun ρ _ => IntNumeric.hasTyp_num (t := .i32) c (evalExp_caseE_iff.2 ⟨_,
    evalExp_tupE_iff.2 ⟨[], Equiv.Validation.evalExps_nil_iff.2 rfl, rfl⟩, rfl⟩)
  typeuseIdx y := fun ρ hρ =>
    hasTyp_varT_case (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) findTyp_typeuse
      Equiv.evalArgs_nil matchArgs_nil
      (IntNumeric.hasTypCase_of_findCase rfl
        (typedV_alias findTyp_typeidx (typedV_idx y) VarEnv.empty ⟨rfl, rfl, rfl⟩) premsOk_nil)
  ifInv bt b₁ b₂ h := by
    have hi := IntNumeric.hasTyp_instr_inv ⟨rfl, rfl, rfl⟩ (h VarEnv.empty ⟨rfl, rfl, rfl⟩) rfl
    obtain ⟨_, he, ht⟩ := hasTyp_tupT_iff.1 hi
    obtain rfl := (Value.tuple.inj he).symm
    obtain ⟨_, _, he₁, h₁, ht₁⟩ := hasTypTup_cons_iff.1 ht
    obtain ⟨rfl, rfl⟩ := List.cons.inj he₁
    obtain ⟨_, _, he₂, h₂, ht₂⟩ := hasTypTup_cons_iff.1 ht₁
    obtain ⟨rfl, rfl⟩ := List.cons.inj he₂
    obtain ⟨_, _, he₃, h₃, -⟩ := hasTypTup_cons_iff.1 ht₂
    obtain ⟨rfl, -⟩ := List.cons.inj he₃
    exact ⟨typedV_of_hasTyp ⟨rfl, rfl, rfl⟩ h₁, typedV_list_of_hasTyp ⟨rfl, rfl, rfl⟩ h₂,
      typedV_list_of_hasTyp ⟨rfl, rfl, rfl⟩ h₃⟩
  blockInv bt b h := by
    have hi := IntNumeric.hasTyp_instr_inv ⟨rfl, rfl, rfl⟩ (h VarEnv.empty ⟨rfl, rfl, rfl⟩) rfl
    obtain ⟨_, he, ht⟩ := hasTyp_tupT_iff.1 hi
    obtain rfl := (Value.tuple.inj he).symm
    obtain ⟨_, _, he₁, h₁, ht₁⟩ := hasTypTup_cons_iff.1 ht
    obtain ⟨rfl, rfl⟩ := List.cons.inj he₁
    obtain ⟨_, _, he₂, h₂, -⟩ := hasTypTup_cons_iff.1 ht₁
    obtain ⟨rfl, -⟩ := List.cons.inj he₂
    exact ⟨typedV_of_hasTyp ⟨rfl, rfl, rfl⟩ h₁, typedV_list_of_hasTyp ⟨rfl, rfl, rfl⟩ h₂⟩
  loopInv bt b h := by
    have hi := IntNumeric.hasTyp_instr_inv ⟨rfl, rfl, rfl⟩ (h VarEnv.empty ⟨rfl, rfl, rfl⟩) rfl
    obtain ⟨_, he, ht⟩ := hasTyp_tupT_iff.1 hi
    obtain rfl := (Value.tuple.inj he).symm
    obtain ⟨_, _, he₁, h₁, ht₁⟩ := hasTypTup_cons_iff.1 ht
    obtain ⟨rfl, rfl⟩ := List.cons.inj he₁
    obtain ⟨_, _, he₂, h₂, -⟩ := hasTypTup_cons_iff.1 ht₁
    obtain ⟨rfl, -⟩ := List.cons.inj he₂
    exact ⟨typedV_of_hasTyp ⟨rfl, rfl, rfl⟩ h₁, typedV_list_of_hasTyp ⟨rfl, rfl, rfl⟩ h₂⟩
  callRefInv yy h := typedV_of_hasTyp ⟨rfl, rfl, rfl⟩
    (IntNumeric.hasTyp_instr_inv ⟨rfl, rfl, rfl⟩ (h VarEnv.empty ⟨rfl, rfl, rfl⟩) rfl)
  retCallRefInv yy h := typedV_of_hasTyp ⟨rfl, rfl, rfl⟩
    (IntNumeric.hasTyp_instr_inv ⟨rfl, rfl, rfl⟩ (h VarEnv.empty ⟨rfl, rfl, rfl⟩) rfl)

end Silmaril.Wasm.SpecTec.Sim.Typing
