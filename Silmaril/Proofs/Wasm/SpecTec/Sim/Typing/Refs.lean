module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Values
public import Silmaril.Wasm.SpecTec.Sim.RefsGC.Thms

/-!
# Family R's typing interface `RTyping` holds in every `simEnv B`

`rTyping_simEnv`: references and values are typed outright (`typedV_ref`, `typedV_val`); the
numerals, flags and indices through the script's type definitions; the immediates of a typed
`REF.NULL`/`REF.FUNC`/`REF.TEST`/`REF.CAST`/`BR_ON_CAST`/`BR_ON_CAST_FAIL` by inverting `instr`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Typing

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

set_option maxRecDepth 100000 in
theorem findTyp_fieldidx :
    (simEnv B).findTyp? "fieldidx" = some ([], [.instD [] [] (.aliasT (.varT "idx" []))]) := rfl
set_option maxRecDepth 100000 in
theorem findTyp_funcidx :
    (simEnv B).findTyp? "funcidx" = some ([], [.instD [] [] (.aliasT (.varT "idx" []))]) := rfl

/-- The payload of a closed alias. -/
theorem typedV_of_alias {x y : IL.Id}
    (htd : (simEnv B).findTyp? x = some ([], [.instD [] [] (.aliasT (.varT y []))]))
    {v : Value} (h : TypedV (simEnv B) (.varT x []) v) : TypedV (simEnv B) (.varT y []) v :=
  fun ρ hρ => by
    have hl : localTyp? ρ x [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
    obtain ⟨td, ws, htd', -, hi⟩ := (hasTyp_varT_global_iff hl).1 (h ρ hρ)
    rw [htd] at htd'
    obtain rfl := (Option.some.inj htd').symm
    rcases hasTypInsts_cons_inv hi with ⟨σ, hm, hd⟩ | hrest
    · obtain rfl := IntNumeric.matchArgs_nil_scope hm
      exact IntNumeric.hasTyp_varT_nil_congr ⟨rfl, rfl, rfl⟩ hρ (hasTypDef_aliasT_iff.1 hd)
    · exact absurd hrest not_hasTypInsts_nil

/-- The single instruction of a typed one-element `instr*`. -/
theorem hasTyp_instr_of_single {w : Value} (h : TypedV (simEnv B) instrsT (.list [w])) :
    HasTyp (simEnv B) VarEnv.empty (.varT "instr" []) w := by
  obtain ⟨l, hl, hall⟩ := hasTyp_iterT_list_iff.1 (h VarEnv.empty ⟨rfl, rfl, rfl⟩)
  cases hl
  exact hasTypList_iff.1 hall _ (by simp)

/-- A one-immediate `instr` case's payload, at a closed case type. -/
theorem typedV_arg {op : MixopS} {x : IL.Id} {w : Value}
    (hf : IntNumeric.findCase (IntNumeric.recCases
      Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d271 0 0) op = some (.varT x [], []))
    (h : TypedV (simEnv B) instrsT (.list [.case op w])) : TypedV (simEnv B) (.varT x []) w :=
  typedV_of_hasTyp ⟨rfl, rfl, rfl⟩
    (IntNumeric.hasTyp_instr_inv ⟨rfl, rfl, rfl⟩ (hasTyp_instr_of_single h) hf)

/-- A three-immediate `instr` case's payload, at closed component types. -/
theorem typedV_arg3 {op : MixopS} {x₁ x₂ x₃ y₁ y₂ y₃ : IL.Id} {w₁ w₂ w₃ : Value}
    (hf : IntNumeric.findCase (IntNumeric.recCases
      Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d271 0 0) op =
      some (.tupT [.mk y₁ (.varT x₁ []), .mk y₂ (.varT x₂ []), .mk y₃ (.varT x₃ [])], []))
    (h : TypedV (simEnv B) instrsT (.list [.case op (.tuple [w₁, w₂, w₃])])) :
    TypedV (simEnv B) (.varT x₁ []) w₁ ∧ TypedV (simEnv B) (.varT x₂ []) w₂ ∧
      TypedV (simEnv B) (.varT x₃ []) w₃ := by
  have hi := IntNumeric.hasTyp_instr_inv ⟨rfl, rfl, rfl⟩ (hasTyp_instr_of_single h) hf
  obtain ⟨_, he, ht⟩ := hasTyp_tupT_iff.1 hi
  obtain rfl := (Value.tuple.inj he).symm
  obtain ⟨_, _, he₁, h₁, ht₁⟩ := hasTypTup_cons_iff.1 ht
  obtain ⟨rfl, rfl⟩ := List.cons.inj he₁
  obtain ⟨_, _, he₂, h₂, ht₂⟩ := hasTypTup_cons_iff.1 ht₁
  obtain ⟨rfl, rfl⟩ := List.cons.inj he₂
  obtain ⟨_, _, he₃, h₃, -⟩ := hasTypTup_cons_iff.1 ht₂
  obtain ⟨rfl, -⟩ := List.cons.inj he₃
  exact ⟨typedV_of_hasTyp ⟨rfl, rfl, rfl⟩ h₁, typedV_of_hasTyp ⟨rfl, rfl, rfl⟩ h₂,
    typedV_of_hasTyp ⟨rfl, rfl, rfl⟩ h₃⟩

/-- **Family R's typing interface holds in every `simEnv B`.** -/
theorem rTyping_simEnv (B : Builtins) : RefsGC.RTyping (simEnv B) where
  ref r _ := typedV_ref r
  externArg r _ := typedV_ref r
  val v _ := typedV_val v
  i32 b := fun _ _ => IntNumeric.hasTyp_num (t := .i32) b (evalExp_caseE_iff.2 ⟨_,
    evalExp_tupE_iff.2 ⟨[], Equiv.Validation.evalExps_nil_iff.2 rfl, rfl⟩, rfl⟩)
  u31 b := fun ρ hρ => hasTyp_varT_of_insts (by simp [localTyp?, VarEnv.findTyp?, hρ.1])
    findTyp_u31 Equiv.evalArgs_nil (hasTypInsts_head matchArgs_nil
      (hasTypDef_aliasT_iff.2 (IntNumeric.hasTyp_uN evalExp_num b.isLt)))
  sx s := fun ρ hρ => IntNumeric.hasTyp_sx hρ s
  idx n hn := typedV_alias findTyp_idx (typedV_u32 hn)
  fieldidx n hn := typedV_alias findTyp_fieldidx (typedV_alias findTyp_idx (typedV_u32 hn))
  nat := typedV_natAlias findTyp_n
  addr := typedV_natAlias findTyp_addr
  sxOpt o := fun ρ hρ => by
    cases o with
    | none => exact hasTyp_iterT_opt_iff.2 (.inl rfl)
    | some s => exact hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl, IntNumeric.hasTyp_sx hρ s⟩)
  arg op w t hmem h := by
    simp only [RefsGC.argTypes, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact typedV_arg rfl h
    · exact typedV_of_alias findTyp_funcidx (typedV_arg rfl h)
    · exact typedV_arg rfl h
    · exact typedV_arg rfl h
  arg3 op w₁ w₂ w₃ t₁ t₂ t₃ hmem h := by
    simp only [RefsGC.argTypes3, List.mem_cons, Prod.mk.injEq, List.cons.injEq,
      List.not_mem_nil, or_false, and_true] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact typedV_arg3 rfl h
    · exact typedV_arg3 rfl h

end Silmaril.Wasm.SpecTec.Sim.Typing
