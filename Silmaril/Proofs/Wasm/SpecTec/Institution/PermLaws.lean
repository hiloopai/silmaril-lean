module

public import Silmaril.Wasm.SpecTec.Institution.Perm.Defs

/-!
# Renaming IL syntax: the laws

`rn` is functorial: `rn g ∘ rn f = rn (g ∘ f)` (`rnTyp_comp`, …) and `rn id = id` (`rnTyp_id`,
…), one mutual induction each over the IL's mutual block. So a permutation's inverse undoes it
(`rnTyp_symm`, …, `rnVarEnv_symm`, `rnEnv_symm`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Perm

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim

section Comp

variable (f g : IL.Id → IL.Id)

mutual
theorem rnIter_comp : ∀ x : Iter, rnIter g (rnIter f x) = rnIter (g ∘ f) x
  | .opt => by simp only [rnIter]
  | .list => by simp only [rnIter]
  | .list1 => by simp only [rnIter]
  | .listN a0 a1 => by simp only [rnIter, rnExp_comp a0, rnIdOpt_comp a1]

theorem rnIdOpt_comp : ∀ x : Option IL.Id, rnIdOpt g (rnIdOpt f x) = rnIdOpt (g ∘ f) x
  | none => by simp only [rnIdOpt]
  | some a0 => by simp only [rnIdOpt, Function.comp_apply]

theorem rnTyp_comp : ∀ x : Typ, rnTyp g (rnTyp f x) = rnTyp (g ∘ f) x
  | .varT a0 a1 => by simp only [rnTyp, rnArgs_comp a1, Function.comp_apply]
  | .boolT => by simp only [rnTyp]
  | .numT a0 => by simp only [rnTyp]
  | .textT => by simp only [rnTyp]
  | .tupT a0 => by simp only [rnTyp, rnTypBinds_comp a0]
  | .iterT a0 a1 => by simp only [rnTyp, rnTyp_comp a0, rnIter_comp a1]

theorem rnTypBind_comp : ∀ x : TypBind, rnTypBind g (rnTypBind f x) = rnTypBind (g ∘ f) x
  | .mk a0 a1 => by simp only [rnTypBind, rnTyp_comp a1, Function.comp_apply]

theorem rnTypBinds_comp : ∀ x : List TypBind, rnTypBinds g (rnTypBinds f x) = rnTypBinds (g ∘ f) x
  | [] => by simp only [rnTypBinds]
  | a0 :: a1 => by simp only [rnTypBinds, rnTypBind_comp a0, rnTypBinds_comp a1]

theorem rnDefTyp_comp : ∀ x : DefTyp, rnDefTyp g (rnDefTyp f x) = rnDefTyp (g ∘ f) x
  | .aliasT a0 => by simp only [rnDefTyp, rnTyp_comp a0]
  | .structT a0 => by simp only [rnDefTyp, rnTypFields_comp a0]
  | .variantT a0 => by simp only [rnDefTyp, rnTypCases_comp a0]

theorem rnTypField_comp : ∀ x : TypField, rnTypField g (rnTypField f x) = rnTypField (g ∘ f) x
  | .mk a0 a1 a2 a3 => by simp only [rnTypField, rnTyp_comp a1, rnParams_comp a2, rnPrems_comp a3]

theorem rnTypFields_comp : ∀ x : List TypField, rnTypFields g (rnTypFields f x) = rnTypFields (g ∘ f) x
  | [] => by simp only [rnTypFields]
  | a0 :: a1 => by simp only [rnTypFields, rnTypField_comp a0, rnTypFields_comp a1]

theorem rnTypCase_comp : ∀ x : TypCase, rnTypCase g (rnTypCase f x) = rnTypCase (g ∘ f) x
  | .mk a0 a1 a2 a3 => by simp only [rnTypCase, rnTyp_comp a1, rnParams_comp a2, rnPrems_comp a3]

theorem rnTypCases_comp : ∀ x : List TypCase, rnTypCases g (rnTypCases f x) = rnTypCases (g ∘ f) x
  | [] => by simp only [rnTypCases]
  | a0 :: a1 => by simp only [rnTypCases, rnTypCase_comp a0, rnTypCases_comp a1]

theorem rnExp_comp : ∀ x : Exp, rnExp g (rnExp f x) = rnExp (g ∘ f) x
  | .varE a0 => by simp only [rnExp, Function.comp_apply]
  | .boolE a0 => by simp only [rnExp]
  | .numE a0 => by simp only [rnExp]
  | .textE a0 => by simp only [rnExp]
  | .unE a0 a1 a2 => by simp only [rnExp, rnExp_comp a2]
  | .binE a0 a1 a2 a3 => by simp only [rnExp, rnExp_comp a2, rnExp_comp a3]
  | .cmpE a0 a1 a2 a3 => by simp only [rnExp, rnExp_comp a2, rnExp_comp a3]
  | .tupE a0 => by simp only [rnExp, rnExps_comp a0]
  | .projE a0 a1 => by simp only [rnExp, rnExp_comp a0]
  | .caseE a0 a1 => by simp only [rnExp, rnExp_comp a1]
  | .uncaseE a0 a1 => by simp only [rnExp, rnExp_comp a0]
  | .optE a0 => by simp only [rnExp, rnExpOpt_comp a0]
  | .theE a0 => by simp only [rnExp, rnExp_comp a0]
  | .strE a0 => by simp only [rnExp, rnExpFields_comp a0]
  | .dotE a0 a1 => by simp only [rnExp, rnExp_comp a0]
  | .compE a0 a1 => by simp only [rnExp, rnExp_comp a0, rnExp_comp a1]
  | .listE a0 => by simp only [rnExp, rnExps_comp a0]
  | .liftE a0 => by simp only [rnExp, rnExp_comp a0]
  | .memE a0 a1 => by simp only [rnExp, rnExp_comp a0, rnExp_comp a1]
  | .lenE a0 => by simp only [rnExp, rnExp_comp a0]
  | .catE a0 a1 => by simp only [rnExp, rnExp_comp a0, rnExp_comp a1]
  | .idxE a0 a1 => by simp only [rnExp, rnExp_comp a0, rnExp_comp a1]
  | .sliceE a0 a1 a2 => by simp only [rnExp, rnExp_comp a0, rnExp_comp a1, rnExp_comp a2]
  | .updE a0 a1 a2 => by simp only [rnExp, rnExp_comp a0, rnPath_comp a1, rnExp_comp a2]
  | .extE a0 a1 a2 => by simp only [rnExp, rnExp_comp a0, rnPath_comp a1, rnExp_comp a2]
  | .callE a0 a1 => by simp only [rnExp, rnArgs_comp a1, Function.comp_apply]
  | .iterE a0 a1 => by simp only [rnExp, rnExp_comp a0, rnIterExp_comp a1]
  | .cvtE a0 a1 a2 => by simp only [rnExp, rnExp_comp a0]
  | .subE a0 a1 a2 => by simp only [rnExp, rnExp_comp a0, rnTyp_comp a1, rnTyp_comp a2]

theorem rnExpOpt_comp : ∀ x : Option Exp, rnExpOpt g (rnExpOpt f x) = rnExpOpt (g ∘ f) x
  | none => by simp only [rnExpOpt]
  | some a0 => by simp only [rnExpOpt, rnExp_comp a0]

theorem rnExps_comp : ∀ x : List Exp, rnExps g (rnExps f x) = rnExps (g ∘ f) x
  | [] => by simp only [rnExps]
  | a0 :: a1 => by simp only [rnExps, rnExp_comp a0, rnExps_comp a1]

theorem rnExpField_comp : ∀ x : ExpField, rnExpField g (rnExpField f x) = rnExpField (g ∘ f) x
  | .mk a0 a1 => by simp only [rnExpField, rnExp_comp a1]

theorem rnExpFields_comp : ∀ x : List ExpField, rnExpFields g (rnExpFields f x) = rnExpFields (g ∘ f) x
  | [] => by simp only [rnExpFields]
  | a0 :: a1 => by simp only [rnExpFields, rnExpField_comp a0, rnExpFields_comp a1]

theorem rnPath_comp : ∀ x : Path, rnPath g (rnPath f x) = rnPath (g ∘ f) x
  | .rootP => by simp only [rnPath]
  | .idxP a0 a1 => by simp only [rnPath, rnPath_comp a0, rnExp_comp a1]
  | .sliceP a0 a1 a2 => by simp only [rnPath, rnPath_comp a0, rnExp_comp a1, rnExp_comp a2]
  | .dotP a0 a1 => by simp only [rnPath, rnPath_comp a0]

theorem rnIterExp_comp : ∀ x : IterExp, rnIterExp g (rnIterExp f x) = rnIterExp (g ∘ f) x
  | .mk a0 a1 => by simp only [rnIterExp, rnIter_comp a0, rnDoms_comp a1]

theorem rnDom_comp : ∀ x : Dom, rnDom g (rnDom f x) = rnDom (g ∘ f) x
  | .mk a0 a1 => by simp only [rnDom, rnExp_comp a1, Function.comp_apply]

theorem rnDoms_comp : ∀ x : List Dom, rnDoms g (rnDoms f x) = rnDoms (g ∘ f) x
  | [] => by simp only [rnDoms]
  | a0 :: a1 => by simp only [rnDoms, rnDom_comp a0, rnDoms_comp a1]

theorem rnSym_comp : ∀ x : Sym, rnSym g (rnSym f x) = rnSym (g ∘ f) x
  | .varG a0 a1 => by simp only [rnSym, rnArgs_comp a1, Function.comp_apply]
  | .numG a0 => by simp only [rnSym]
  | .textG a0 => by simp only [rnSym]
  | .epsG => by simp only [rnSym]
  | .seqG a0 => by simp only [rnSym, rnSyms_comp a0]
  | .altG a0 => by simp only [rnSym, rnSyms_comp a0]
  | .rangeG a0 a1 => by simp only [rnSym, rnSym_comp a0, rnSym_comp a1]
  | .iterG a0 a1 => by simp only [rnSym, rnSym_comp a0, rnIterExp_comp a1]
  | .attrG a0 a1 => by simp only [rnSym, rnExp_comp a0, rnSym_comp a1]

theorem rnSyms_comp : ∀ x : List Sym, rnSyms g (rnSyms f x) = rnSyms (g ∘ f) x
  | [] => by simp only [rnSyms]
  | a0 :: a1 => by simp only [rnSyms, rnSym_comp a0, rnSyms_comp a1]

theorem rnArg_comp : ∀ x : Arg, rnArg g (rnArg f x) = rnArg (g ∘ f) x
  | .expA a0 => by simp only [rnArg, rnExp_comp a0]
  | .typA a0 => by simp only [rnArg, rnTyp_comp a0]
  | .defA a0 => by simp only [rnArg, Function.comp_apply]
  | .gramA a0 => by simp only [rnArg, rnSym_comp a0]

theorem rnArgs_comp : ∀ x : List Arg, rnArgs g (rnArgs f x) = rnArgs (g ∘ f) x
  | [] => by simp only [rnArgs]
  | a0 :: a1 => by simp only [rnArgs, rnArg_comp a0, rnArgs_comp a1]

theorem rnParam_comp : ∀ x : Param, rnParam g (rnParam f x) = rnParam (g ∘ f) x
  | .expP a0 a1 => by simp only [rnParam, rnTyp_comp a1, Function.comp_apply]
  | .typP a0 => by simp only [rnParam, Function.comp_apply]
  | .defP a0 a1 a2 => by simp only [rnParam, rnParams_comp a1, rnTyp_comp a2, Function.comp_apply]
  | .gramP a0 a1 a2 => by simp only [rnParam, rnParams_comp a1, rnTyp_comp a2, Function.comp_apply]

theorem rnParams_comp : ∀ x : List Param, rnParams g (rnParams f x) = rnParams (g ∘ f) x
  | [] => by simp only [rnParams]
  | a0 :: a1 => by simp only [rnParams, rnParam_comp a0, rnParams_comp a1]

theorem rnPrem_comp : ∀ x : Prem, rnPrem g (rnPrem f x) = rnPrem (g ∘ f) x
  | .rulePr a0 a1 a2 a3 => by simp only [rnPrem, rnArgs_comp a1, rnExp_comp a3, Function.comp_apply]
  | .ifPr a0 => by simp only [rnPrem, rnExp_comp a0]
  | .letPr a0 a1 => by simp only [rnPrem, rnExp_comp a0, rnExp_comp a1]
  | .elsePr => by simp only [rnPrem]
  | .iterPr a0 a1 => by simp only [rnPrem, rnPrem_comp a0, rnIterExp_comp a1]

theorem rnPrems_comp : ∀ x : List Prem, rnPrems g (rnPrems f x) = rnPrems (g ∘ f) x
  | [] => by simp only [rnPrems]
  | a0 :: a1 => by simp only [rnPrems, rnPrem_comp a0, rnPrems_comp a1]

theorem rnInst_comp : ∀ x : Inst, rnInst g (rnInst f x) = rnInst (g ∘ f) x
  | .instD a0 a1 a2 => by simp only [rnInst, rnParams_comp a0, rnArgs_comp a1, rnDefTyp_comp a2]

theorem rnInsts_comp : ∀ x : List Inst, rnInsts g (rnInsts f x) = rnInsts (g ∘ f) x
  | [] => by simp only [rnInsts]
  | a0 :: a1 => by simp only [rnInsts, rnInst_comp a0, rnInsts_comp a1]

theorem rnRule_comp : ∀ x : Rule, rnRule g (rnRule f x) = rnRule (g ∘ f) x
  | .ruleD a0 a1 a2 a3 a4 => by simp only [rnRule, rnParams_comp a1, rnExp_comp a3, rnPrems_comp a4, Function.comp_apply]

theorem rnRules_comp : ∀ x : List Rule, rnRules g (rnRules f x) = rnRules (g ∘ f) x
  | [] => by simp only [rnRules]
  | a0 :: a1 => by simp only [rnRules, rnRule_comp a0, rnRules_comp a1]

theorem rnClause_comp : ∀ x : Clause, rnClause g (rnClause f x) = rnClause (g ∘ f) x
  | .defD a0 a1 a2 a3 => by simp only [rnClause, rnParams_comp a0, rnArgs_comp a1, rnExp_comp a2, rnPrems_comp a3]

theorem rnClauses_comp : ∀ x : List Clause, rnClauses g (rnClauses f x) = rnClauses (g ∘ f) x
  | [] => by simp only [rnClauses]
  | a0 :: a1 => by simp only [rnClauses, rnClause_comp a0, rnClauses_comp a1]

theorem rnProd_comp : ∀ x : IL.Prod, rnProd g (rnProd f x) = rnProd (g ∘ f) x
  | .prodD a0 a1 a2 a3 => by simp only [rnProd, rnParams_comp a0, rnSym_comp a1, rnExp_comp a2, rnPrems_comp a3]

theorem rnProds_comp : ∀ x : List IL.Prod, rnProds g (rnProds f x) = rnProds (g ∘ f) x
  | [] => by simp only [rnProds]
  | a0 :: a1 => by simp only [rnProds, rnProd_comp a0, rnProds_comp a1]

end

end Comp

mutual
theorem rnIter_id : ∀ x : Iter, rnIter id x = x
  | .opt => by simp only [rnIter]
  | .list => by simp only [rnIter]
  | .list1 => by simp only [rnIter]
  | .listN a0 a1 => by simp only [rnIter, rnExp_id a0, rnIdOpt_id a1]

theorem rnIdOpt_id : ∀ x : Option IL.Id, rnIdOpt id x = x
  | none => by simp only [rnIdOpt]
  | some a0 => by simp only [rnIdOpt, id_eq]

theorem rnTyp_id : ∀ x : Typ, rnTyp id x = x
  | .varT a0 a1 => by simp only [rnTyp, rnArgs_id a1, id_eq]
  | .boolT => by simp only [rnTyp]
  | .numT a0 => by simp only [rnTyp]
  | .textT => by simp only [rnTyp]
  | .tupT a0 => by simp only [rnTyp, rnTypBinds_id a0]
  | .iterT a0 a1 => by simp only [rnTyp, rnTyp_id a0, rnIter_id a1]

theorem rnTypBind_id : ∀ x : TypBind, rnTypBind id x = x
  | .mk a0 a1 => by simp only [rnTypBind, rnTyp_id a1, id_eq]

theorem rnTypBinds_id : ∀ x : List TypBind, rnTypBinds id x = x
  | [] => by simp only [rnTypBinds]
  | a0 :: a1 => by simp only [rnTypBinds, rnTypBind_id a0, rnTypBinds_id a1]

theorem rnDefTyp_id : ∀ x : DefTyp, rnDefTyp id x = x
  | .aliasT a0 => by simp only [rnDefTyp, rnTyp_id a0]
  | .structT a0 => by simp only [rnDefTyp, rnTypFields_id a0]
  | .variantT a0 => by simp only [rnDefTyp, rnTypCases_id a0]

theorem rnTypField_id : ∀ x : TypField, rnTypField id x = x
  | .mk a0 a1 a2 a3 => by simp only [rnTypField, rnTyp_id a1, rnParams_id a2, rnPrems_id a3]

theorem rnTypFields_id : ∀ x : List TypField, rnTypFields id x = x
  | [] => by simp only [rnTypFields]
  | a0 :: a1 => by simp only [rnTypFields, rnTypField_id a0, rnTypFields_id a1]

theorem rnTypCase_id : ∀ x : TypCase, rnTypCase id x = x
  | .mk a0 a1 a2 a3 => by simp only [rnTypCase, rnTyp_id a1, rnParams_id a2, rnPrems_id a3]

theorem rnTypCases_id : ∀ x : List TypCase, rnTypCases id x = x
  | [] => by simp only [rnTypCases]
  | a0 :: a1 => by simp only [rnTypCases, rnTypCase_id a0, rnTypCases_id a1]

theorem rnExp_id : ∀ x : Exp, rnExp id x = x
  | .varE a0 => by simp only [rnExp, id_eq]
  | .boolE a0 => by simp only [rnExp]
  | .numE a0 => by simp only [rnExp]
  | .textE a0 => by simp only [rnExp]
  | .unE a0 a1 a2 => by simp only [rnExp, rnExp_id a2]
  | .binE a0 a1 a2 a3 => by simp only [rnExp, rnExp_id a2, rnExp_id a3]
  | .cmpE a0 a1 a2 a3 => by simp only [rnExp, rnExp_id a2, rnExp_id a3]
  | .tupE a0 => by simp only [rnExp, rnExps_id a0]
  | .projE a0 a1 => by simp only [rnExp, rnExp_id a0]
  | .caseE a0 a1 => by simp only [rnExp, rnExp_id a1]
  | .uncaseE a0 a1 => by simp only [rnExp, rnExp_id a0]
  | .optE a0 => by simp only [rnExp, rnExpOpt_id a0]
  | .theE a0 => by simp only [rnExp, rnExp_id a0]
  | .strE a0 => by simp only [rnExp, rnExpFields_id a0]
  | .dotE a0 a1 => by simp only [rnExp, rnExp_id a0]
  | .compE a0 a1 => by simp only [rnExp, rnExp_id a0, rnExp_id a1]
  | .listE a0 => by simp only [rnExp, rnExps_id a0]
  | .liftE a0 => by simp only [rnExp, rnExp_id a0]
  | .memE a0 a1 => by simp only [rnExp, rnExp_id a0, rnExp_id a1]
  | .lenE a0 => by simp only [rnExp, rnExp_id a0]
  | .catE a0 a1 => by simp only [rnExp, rnExp_id a0, rnExp_id a1]
  | .idxE a0 a1 => by simp only [rnExp, rnExp_id a0, rnExp_id a1]
  | .sliceE a0 a1 a2 => by simp only [rnExp, rnExp_id a0, rnExp_id a1, rnExp_id a2]
  | .updE a0 a1 a2 => by simp only [rnExp, rnExp_id a0, rnPath_id a1, rnExp_id a2]
  | .extE a0 a1 a2 => by simp only [rnExp, rnExp_id a0, rnPath_id a1, rnExp_id a2]
  | .callE a0 a1 => by simp only [rnExp, rnArgs_id a1, id_eq]
  | .iterE a0 a1 => by simp only [rnExp, rnExp_id a0, rnIterExp_id a1]
  | .cvtE a0 a1 a2 => by simp only [rnExp, rnExp_id a0]
  | .subE a0 a1 a2 => by simp only [rnExp, rnExp_id a0, rnTyp_id a1, rnTyp_id a2]

theorem rnExpOpt_id : ∀ x : Option Exp, rnExpOpt id x = x
  | none => by simp only [rnExpOpt]
  | some a0 => by simp only [rnExpOpt, rnExp_id a0]

theorem rnExps_id : ∀ x : List Exp, rnExps id x = x
  | [] => by simp only [rnExps]
  | a0 :: a1 => by simp only [rnExps, rnExp_id a0, rnExps_id a1]

theorem rnExpField_id : ∀ x : ExpField, rnExpField id x = x
  | .mk a0 a1 => by simp only [rnExpField, rnExp_id a1]

theorem rnExpFields_id : ∀ x : List ExpField, rnExpFields id x = x
  | [] => by simp only [rnExpFields]
  | a0 :: a1 => by simp only [rnExpFields, rnExpField_id a0, rnExpFields_id a1]

theorem rnPath_id : ∀ x : Path, rnPath id x = x
  | .rootP => by simp only [rnPath]
  | .idxP a0 a1 => by simp only [rnPath, rnPath_id a0, rnExp_id a1]
  | .sliceP a0 a1 a2 => by simp only [rnPath, rnPath_id a0, rnExp_id a1, rnExp_id a2]
  | .dotP a0 a1 => by simp only [rnPath, rnPath_id a0]

theorem rnIterExp_id : ∀ x : IterExp, rnIterExp id x = x
  | .mk a0 a1 => by simp only [rnIterExp, rnIter_id a0, rnDoms_id a1]

theorem rnDom_id : ∀ x : Dom, rnDom id x = x
  | .mk a0 a1 => by simp only [rnDom, rnExp_id a1, id_eq]

theorem rnDoms_id : ∀ x : List Dom, rnDoms id x = x
  | [] => by simp only [rnDoms]
  | a0 :: a1 => by simp only [rnDoms, rnDom_id a0, rnDoms_id a1]

theorem rnSym_id : ∀ x : Sym, rnSym id x = x
  | .varG a0 a1 => by simp only [rnSym, rnArgs_id a1, id_eq]
  | .numG a0 => by simp only [rnSym]
  | .textG a0 => by simp only [rnSym]
  | .epsG => by simp only [rnSym]
  | .seqG a0 => by simp only [rnSym, rnSyms_id a0]
  | .altG a0 => by simp only [rnSym, rnSyms_id a0]
  | .rangeG a0 a1 => by simp only [rnSym, rnSym_id a0, rnSym_id a1]
  | .iterG a0 a1 => by simp only [rnSym, rnSym_id a0, rnIterExp_id a1]
  | .attrG a0 a1 => by simp only [rnSym, rnExp_id a0, rnSym_id a1]

theorem rnSyms_id : ∀ x : List Sym, rnSyms id x = x
  | [] => by simp only [rnSyms]
  | a0 :: a1 => by simp only [rnSyms, rnSym_id a0, rnSyms_id a1]

theorem rnArg_id : ∀ x : Arg, rnArg id x = x
  | .expA a0 => by simp only [rnArg, rnExp_id a0]
  | .typA a0 => by simp only [rnArg, rnTyp_id a0]
  | .defA a0 => by simp only [rnArg, id_eq]
  | .gramA a0 => by simp only [rnArg, rnSym_id a0]

theorem rnArgs_id : ∀ x : List Arg, rnArgs id x = x
  | [] => by simp only [rnArgs]
  | a0 :: a1 => by simp only [rnArgs, rnArg_id a0, rnArgs_id a1]

theorem rnParam_id : ∀ x : Param, rnParam id x = x
  | .expP a0 a1 => by simp only [rnParam, rnTyp_id a1, id_eq]
  | .typP a0 => by simp only [rnParam, id_eq]
  | .defP a0 a1 a2 => by simp only [rnParam, rnParams_id a1, rnTyp_id a2, id_eq]
  | .gramP a0 a1 a2 => by simp only [rnParam, rnParams_id a1, rnTyp_id a2, id_eq]

theorem rnParams_id : ∀ x : List Param, rnParams id x = x
  | [] => by simp only [rnParams]
  | a0 :: a1 => by simp only [rnParams, rnParam_id a0, rnParams_id a1]

theorem rnPrem_id : ∀ x : Prem, rnPrem id x = x
  | .rulePr a0 a1 a2 a3 => by simp only [rnPrem, rnArgs_id a1, rnExp_id a3, id_eq]
  | .ifPr a0 => by simp only [rnPrem, rnExp_id a0]
  | .letPr a0 a1 => by simp only [rnPrem, rnExp_id a0, rnExp_id a1]
  | .elsePr => by simp only [rnPrem]
  | .iterPr a0 a1 => by simp only [rnPrem, rnPrem_id a0, rnIterExp_id a1]

theorem rnPrems_id : ∀ x : List Prem, rnPrems id x = x
  | [] => by simp only [rnPrems]
  | a0 :: a1 => by simp only [rnPrems, rnPrem_id a0, rnPrems_id a1]

theorem rnInst_id : ∀ x : Inst, rnInst id x = x
  | .instD a0 a1 a2 => by simp only [rnInst, rnParams_id a0, rnArgs_id a1, rnDefTyp_id a2]

theorem rnInsts_id : ∀ x : List Inst, rnInsts id x = x
  | [] => by simp only [rnInsts]
  | a0 :: a1 => by simp only [rnInsts, rnInst_id a0, rnInsts_id a1]

theorem rnRule_id : ∀ x : Rule, rnRule id x = x
  | .ruleD a0 a1 a2 a3 a4 => by simp only [rnRule, rnParams_id a1, rnExp_id a3, rnPrems_id a4, id_eq]

theorem rnRules_id : ∀ x : List Rule, rnRules id x = x
  | [] => by simp only [rnRules]
  | a0 :: a1 => by simp only [rnRules, rnRule_id a0, rnRules_id a1]

theorem rnClause_id : ∀ x : Clause, rnClause id x = x
  | .defD a0 a1 a2 a3 => by simp only [rnClause, rnParams_id a0, rnArgs_id a1, rnExp_id a2, rnPrems_id a3]

theorem rnClauses_id : ∀ x : List Clause, rnClauses id x = x
  | [] => by simp only [rnClauses]
  | a0 :: a1 => by simp only [rnClauses, rnClause_id a0, rnClauses_id a1]

theorem rnProd_id : ∀ x : IL.Prod, rnProd id x = x
  | .prodD a0 a1 a2 a3 => by simp only [rnProd, rnParams_id a0, rnSym_id a1, rnExp_id a2, rnPrems_id a3]

theorem rnProds_id : ∀ x : List IL.Prod, rnProds id x = x
  | [] => by simp only [rnProds]
  | a0 :: a1 => by simp only [rnProds, rnProd_id a0, rnProds_id a1]

end


/-! ## Maps, scopes, environments; inverses -/

theorem rnArgV_comp (f g : IL.Id → IL.Id) (a : ArgV) : rnArgV g (rnArgV f a) = rnArgV (g ∘ f) a := by
  cases a <;> simp only [rnArgV, rnTyp_comp, rnSym_comp, Function.comp_apply]

theorem rnArgV_id (a : ArgV) : rnArgV id a = a := by
  cases a <;> simp only [rnArgV, rnTyp_id, rnSym_id, id_eq]

theorem rnMap_comp {α : Type} (f g : IL.Id → IL.Id) (h k : α → α) (m : Map α) :
    rnMap g k (rnMap f h m) = rnMap (g ∘ f) (k ∘ h) m := by
  simp only [rnMap, List.map_map]
  rfl

theorem rnMap_id {α : Type} (m : Map α) : rnMap id id m = m := by
  simp [rnMap]

theorem rnVarEnv_comp (f g : IL.Id → IL.Id) (ρ : VarEnv) :
    rnVarEnv g (rnVarEnv f ρ) = rnVarEnv (g ∘ f) ρ := by
  simp only [rnVarEnv, rnMap_comp]
  congr 1 <;> congr 1 <;> funext x <;> simp [rnTyp_comp, rnSym_comp]

theorem rnVarEnv_id (ρ : VarEnv) : rnVarEnv id ρ = ρ := by
  have ht : rnTyp id = id := funext rnTyp_id
  have hs : rnSym id = id := funext rnSym_id
  simp only [rnVarEnv, ht, hs, rnMap_id]

section Symm

variable (π : Equiv.Perm IL.Id)

theorem symm_comp_self : (π.symm : IL.Id → IL.Id) ∘ π = id := funext π.symm_apply_apply

theorem self_comp_symm : (π : IL.Id → IL.Id) ∘ π.symm = id := funext π.apply_symm_apply

theorem rnTyp_symm (t : Typ) : rnTyp π.symm (rnTyp π t) = t := by
  rw [rnTyp_comp, symm_comp_self, rnTyp_id]

theorem rnTyp_symm' (t : Typ) : rnTyp π (rnTyp π.symm t) = t := by
  rw [rnTyp_comp, self_comp_symm, rnTyp_id]

theorem rnSym_symm (g : Sym) : rnSym π.symm (rnSym π g) = g := by
  rw [rnSym_comp, symm_comp_self, rnSym_id]

theorem rnSym_symm' (g : Sym) : rnSym π (rnSym π.symm g) = g := by
  rw [rnSym_comp, self_comp_symm, rnSym_id]

theorem rnArgV_symm (a : ArgV) : rnArgV π.symm (rnArgV π a) = a := by
  rw [rnArgV_comp, symm_comp_self, rnArgV_id]

theorem rnArgV_symm' (a : ArgV) : rnArgV π (rnArgV π.symm a) = a := by
  rw [rnArgV_comp, self_comp_symm, rnArgV_id]

theorem rnArgVs_symm (l : List ArgV) : (l.map (rnArgV π)).map (rnArgV π.symm) = l := by
  simp [List.map_map, Function.comp_def, rnArgV_symm]

theorem rnArgVs_symm' (l : List ArgV) : (l.map (rnArgV π.symm)).map (rnArgV π) = l := by
  simp [List.map_map, Function.comp_def, rnArgV_symm']

theorem rnVarEnv_symm (ρ : VarEnv) : rnVarEnv π.symm (rnVarEnv π ρ) = ρ := by
  rw [rnVarEnv_comp, symm_comp_self, rnVarEnv_id]

theorem rnVarEnv_symm' (ρ : VarEnv) : rnVarEnv π (rnVarEnv π.symm ρ) = ρ := by
  rw [rnVarEnv_comp, self_comp_symm, rnVarEnv_id]

/-- Renaming a map back along the inverse. -/
theorem rnMap_symm {α : Type} (h : (IL.Id → IL.Id) → α → α) (hh : ∀ a, h π.symm (h π a) = a)
    (m : Map α) : rnMap π.symm (h π.symm) (rnMap π (h π) m) = m := by
  have hp : (fun p : IL.Id × α => (π.symm p.1, h π.symm p.2)) ∘ (fun p => (π p.1, h π p.2)) =
      id := by
    funext p
    simp only [Function.comp_apply, Equiv.symm_apply_apply, hh, id_eq]
  simp only [rnMap, List.map_map, hp, List.map_id]

theorem rnTypDef_symm (d : TypDef) : rnTypDef π.symm (rnTypDef π d) = d := by
  simp only [rnTypDef, rnParams_comp, rnInsts_comp, symm_comp_self, rnParams_id, rnInsts_id]

theorem rnDefDef_symm (d : DefDef) : rnDefDef π.symm (rnDefDef π d) = d := by
  simp only [rnDefDef, rnParams_comp, rnTyp_comp, rnClauses_comp, symm_comp_self, rnParams_id,
    rnTyp_id, rnClauses_id]

theorem rnRelDef_symm (d : RelDef) : rnRelDef π.symm (rnRelDef π d) = d := by
  simp only [rnRelDef, rnParams_comp, rnTyp_comp, rnRules_comp, symm_comp_self, rnParams_id,
    rnTyp_id, rnRules_id]

theorem rnGramDef_symm (d : GramDef) : rnGramDef π.symm (rnGramDef π d) = d := by
  simp only [rnGramDef, rnParams_comp, rnTyp_comp, rnProds_comp, symm_comp_self, rnParams_id,
    rnTyp_id, rnProds_id]

/-- A permutation's inverse undoes the renaming of an environment. -/
theorem rnEnv_symm (env : Env) : rnEnv π.symm (rnEnv π env) = env := by
  obtain ⟨vars, typs, defs, rels, grams, ⟨b⟩⟩ := env
  have hb : (fun x ws => b (π.symm (π x))
      ((ws.map (rnArgV π)).map (rnArgV π.symm))) = b := by
    funext x ws
    rw [Equiv.symm_apply_apply, rnArgVs_symm]
  simp only [rnEnv, Equiv.symm_symm, rnMap_symm π (fun f => rnTyp f) (rnTyp_symm π),
    rnMap_symm π (fun f => rnTypDef f) (rnTypDef_symm π),
    rnMap_symm π (fun f => rnDefDef f) (rnDefDef_symm π),
    rnMap_symm π (fun f => rnRelDef f) (rnRelDef_symm π),
    rnMap_symm π (fun f => rnGramDef f) (rnGramDef_symm π), hb]

/-- `rnI π.symm` undoes `rnI π`. -/
theorem rnI_symm (D : Interp) : rnI π.symm (rnI π D) = D := by
  funext x op avs v
  simp only [rnI, Equiv.symm_symm, Equiv.symm_apply_apply, rnArgVs_symm]

end Symm

end Silmaril.Wasm.SpecTec.Institution.Perm
