module

public import Silmaril.Wasm.SpecTec.Sim20.VecAgree.Defs
public import Silmaril.Wasm.SpecTec.Sim20.StoreAgree.Thms
public import Silmaril.Raw.Wasm.SpecTec.Sim20.VecAgree.Typ

/-!
# `simEnv20T` against `simEnv20X`: the `VEXTRACT_LANE` repair

`simEnv20X B` is `simEnv20T B` with the `VEXTRACT_LANE` case of `instr` and `admininstr` replaced
by `VecFix.extractCaseFix`. The original case is uninhabited (`deadCase_extract`: its premise reads
the quantifier `numtype`, which no defining conjunct binds), so round 4's repair transfer applies:

* `envSameX`: the evaluator cannot tell the two environments apart;
* `typRepairX`: the type tables are related by `VecFix.fixExtractCase` (`StoreAgree.TypRepair`);
* `hasTyp_toX`: typing grows from `simEnv20T B` to `simEnv20X B`, at every value.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T fixCase)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (fixExtractCase extractCaseFix extractPayT instrFixV20
  adminFixV20)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (repl typsOfDefs_replaceTyp defsOfDefs_replaceTyp
  relsOfDefs_replaceTyp gramsOfDefs_replaceTyp find?_map_repl instrCasesS adminCasesS
  instrFix20_eq adminFix20_eq findTyp?_simEnv20T caseOp DeadCase TypRepair EnvSame)

/-- The cases of `instr` in `simEnv20T`. -/
noncomputable def instrCasesT : List TypCase := instrCasesS.map fixCase

/-- The cases of `admininstr` in `simEnv20T`. -/
noncomputable def adminCasesT : List TypCase := adminCasesS.map fixCase

theorem instrFixV20_eq :
    instrFixV20 = .typD "instr" [] [.instD [] [] (.variantT (instrCasesT.map fixExtractCase))] := by
  rw [instrFixV20, instrFix20_eq]; rfl

theorem adminFixV20_eq : adminFixV20 =
    .typD "admininstr" [] [.instD [] [] (.variantT (adminCasesT.map fixExtractCase))] := by
  rw [adminFixV20, adminFix20_eq]; rfl

theorem simEnv20X_tables (B : Builtins) :
    (simEnv20X B).typs = ((simEnv20T B).typs.map
        (repl "instr" ([], [.instD [] [] (.variantT (instrCasesT.map fixExtractCase))]))).map
        (repl "admininstr" ([], [.instD [] [] (.variantT (adminCasesT.map fixExtractCase))])) ∧
      (simEnv20X B).defs = (simEnv20T B).defs ∧ (simEnv20X B).rels = (simEnv20T B).rels ∧
      (simEnv20X B).grams = (simEnv20T B).grams ∧ (simEnv20X B).builtins = B ∧
      (simEnv20T B).builtins = B := by
  simp only [simEnv20X, simEnv20T, fixedX20, Env.withBuiltins, envOfScript, envOfDefs_eq,
    adminFixV20_eq, instrFixV20_eq]
  refine ⟨?_, ?_, ?_, ?_, trivial, trivial⟩
  · rw [typsOfDefs_replaceTyp _ _ _ (by decide), typsOfDefs_replaceTyp _ _ _ (by decide)]
    simp [Env.empty, Map.empty]
  · rw [defsOfDefs_replaceTyp, defsOfDefs_replaceTyp]
  · rw [relsOfDefs_replaceTyp, relsOfDefs_replaceTyp]
  · rw [gramsOfDefs_replaceTyp, gramsOfDefs_replaceTyp]

theorem findTyp_instr20T (B : Builtins) :
    (simEnv20T B).findTyp? "instr" = some ([], [.instD [] [] (.variantT instrCasesT)]) := by
  have h := StoreAgree.findTyp_instr20S B
  simp only [Env.findTyp?] at h ⊢
  rw [(StoreAgree.simEnv20T_tables B).1, find?_map_repl, find?_map_repl, h]
  rfl

theorem findTyp_admin20T (B : Builtins) :
    (simEnv20T B).findTyp? "admininstr" = some ([], [.instD [] [] (.variantT adminCasesT)]) := by
  have h := StoreAgree.findTyp_admin20S B
  simp only [Env.findTyp?] at h ⊢
  rw [(StoreAgree.simEnv20T_tables B).1, find?_map_repl, find?_map_repl, h]
  rfl

/-- **What `simEnv20X B` finds**: at `instr` and `admininstr` the declaration of `simEnv20T B`
with `fixExtractCase` applied to its cases, elsewhere what `simEnv20T B` finds. -/
theorem findTyp?_simEnv20X (B : Builtins) (y : IL.Id) :
    (simEnv20X B).findTyp? y = (simEnv20T B).findTyp? y ∨
      ∃ cs, (simEnv20T B).findTyp? y = some ([], [.instD [] [] (.variantT cs)]) ∧
        (simEnv20X B).findTyp? y = some ([], [.instD [] [] (.variantT (cs.map fixExtractCase))]) ∧
        (cs = instrCasesT ∨ cs = adminCasesT) := by
  have ht := (simEnv20X_tables B).1
  by_cases ha : y = "admininstr"
  · subst ha
    refine Or.inr ⟨adminCasesT, findTyp_admin20T B, ?_, Or.inr rfl⟩
    have h := findTyp_admin20T B
    simp only [Env.findTyp?] at h ⊢
    rw [ht, find?_map_repl, find?_map_repl, h]
    rfl
  · by_cases hi : y = "instr"
    · subst hi
      refine Or.inr ⟨instrCasesT, findTyp_instr20T B, ?_, Or.inl rfl⟩
      have h := findTyp_instr20T B
      simp only [Env.findTyp?] at h ⊢
      rw [ht, find?_map_repl, find?_map_repl, h]
      rfl
    · left
      simp only [Env.findTyp?]
      rw [ht, find?_map_repl, find?_map_repl]
      simp [ha, hi]

/-! ## The evaluator cannot tell them apart -/

theorem caseOp_fixExtractCase (c : TypCase) : caseOp (fixExtractCase c) = caseOp c := by
  unfold fixExtractCase
  split <;> rfl

theorem fixExtractCase_of_ne {c : TypCase} (h : caseOp c ≠ "VEXTRACT_LANE") :
    fixExtractCase c = c := by
  unfold fixExtractCase
  split
  · exact absurd rfl h
  · rfl

theorem any_fixExtractCase (cs : List TypCase) (op : MixopS) :
    ((cs.map fixExtractCase).any fun | .mk op' _ _ _ => decide (op' = op)) =
      (cs.any fun | .mk op' _ _ _ => decide (op' = op)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.any_cons, ih]
    congr 1
    have h := caseOp_fixExtractCase c
    revert h
    rcases fixExtractCase c with ⟨o₁, _, _, _⟩
    rcases c with ⟨o₂, _, _, _⟩
    simp only [caseOp]
    rintro rfl
    rfl

theorem memTyp_simEnv20X (B : Builtins) (x : IL.Id) :
    (simEnv20X B).memTyp x = (simEnv20T B).memTyp x := by
  simp only [Env.memTyp, Map.mem]
  rcases findTyp?_simEnv20X B x with h | ⟨cs, h₁, h₂, -⟩
  · exact congrArg Option.isSome h
  · simp only [Env.findTyp?] at h₁ h₂
    rw [h₁, h₂]; rfl

theorem subCaseOk_simEnv20X (B : Builtins) :
    subCaseOk (simEnv20X B) = subCaseOk (simEnv20T B) := by
  funext ρ t v
  unfold subCaseOk
  split
  · rename_i x op w
    split
    · rfl
    · rcases findTyp?_simEnv20X B x with h | ⟨cs, h₁, h₂, -⟩
      · rw [h]
      · rw [h₁, h₂]
        exact any_fixExtractCase cs op
  · rfl

/-- **The evaluator cannot tell `simEnv20T B` and `simEnv20X B` apart.** -/
theorem envSameX (B : Builtins) : EnvSame (simEnv20T B) (simEnv20X B) := by
  obtain ⟨-, hd, hr, hg, hb, hb'⟩ := simEnv20X_tables B
  refine ⟨fun x => ?_, fun x => ?_, hb.trans hb'.symm, ?_, ?_, ?_⟩
  · simp only [Env.findDef?, hd]
  · simp only [Env.findRel?, hr]
  · funext ρ pat t
    simp only [matchTypV, memTyp_simEnv20X]
  · funext ρ pat g
    have hm : ∀ x, (simEnv20X B).memGram x = (simEnv20T B).memGram x := by
      intro x; simp only [Env.memGram, hg]
    simp only [matchSymV, hm]
  · funext ρ e v
    simp only [argSubOk, subCaseOk_simEnv20X]

/-! ## The original `VEXTRACT_LANE` case is dead -/

/-- No payload scope of `VEXTRACT_LANE` binds `numtype`. -/
theorem findVal_numtype_caseScope (w : Value) :
    (caseScope VarEnv.empty extractPayT w).findVal? "numtype" = none := by
  cases w with
  | tuple vs =>
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
      simp [caseScope, typBinds, extractPayT, VarEnv.bindVal, VarEnv.findVal?, VarEnv.empty,
        Map.bind, Map.empty, Map.find?]
  | _ => rfl

/-- A premise `(e₁ = numtype) <=> e₂` with `numtype` unbound does not hold. -/
theorem not_premsOk_numtype {env : Env} {ρ : VarEnv} {a b : Exp} {t₁ t₂ : Typ} {n : Nat}
    (hρ : ρ.findVal? "numtype" = none) :
    premsOk n env ρ [.ifPr (.binE .equivOp .boolT
      (.cmpE .eqOp .boolT a (.subE (.varE "numtype") t₁ t₂)) b)] ≠ .ok true := by
  intro h
  rcases n with _ | _ | _ | _ | _ | n <;>
    simp [premsOk, premsHold, premHolds, evalExp, Res.elimUndef, List.foldlM] at h
  revert h
  split <;> simp_all [Res.bind_eq_ok]
  rename_i heq
  obtain ⟨_, -, v, hv, -⟩ := heq
  rcases n with _ | n <;> simp [evalExp, hρ] at hv

/-- The premise of the original `VEXTRACT_LANE` case. -/
def extractPremOrig (a b : Exp) : Prem :=
  .ifPr (.binE .equivOp .boolT
    (.cmpE .eqOp .boolT a (.subE (.varE "numtype") (.varT "numtype" []) (.varT "lanetype" []))) b)

/-- **The original `VEXTRACT_LANE` case is uninhabited**, in every environment. -/
theorem deadCase_extract {env : Env} {qs : List Param} {a b : Exp} :
    DeadCase env (.mk "VEXTRACT_LANE" extractPayT qs [extractPremOrig a b]) := by
  intro n w h
  cases n with
  | zero => simp [hasTypCase] at h
  | succ n =>
    have hq : quantDefs qs [extractPremOrig a b] = [] := by
      simp [quantDefs, extractPremOrig, quantEqs]
    simp only [hasTypCase, caseOp, ↓reduceIte, hq, bindQuants, Res.elimUndef_ok] at h
    obtain ⟨-, h⟩ := bindIf_true.1 h
    exact not_premsOk_numtype (findVal_numtype_caseScope w) h

set_option maxRecDepth 100000 in
theorem extract_instrCasesT : ∃ qs a b, instrCasesT.filter (fun c => caseOp c == "VEXTRACT_LANE") =
    [.mk "VEXTRACT_LANE" extractPayT qs [extractPremOrig a b]] :=
  ⟨_, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem extract_adminCasesT : ∃ qs a b, adminCasesT.filter (fun c => caseOp c == "VEXTRACT_LANE") =
    [.mk "VEXTRACT_LANE" extractPayT qs [extractPremOrig a b]] :=
  ⟨_, _, _, rfl⟩

/-- Every case of a list with one `VEXTRACT_LANE` case, the dead one, is kept or dead. -/
theorem fixExtractCase_or_dead {env : Env} {cs : List TypCase}
    (hs : ∃ qs a b, cs.filter (fun c => caseOp c == "VEXTRACT_LANE") =
      [.mk "VEXTRACT_LANE" extractPayT qs [extractPremOrig a b]]) :
    ∀ c ∈ cs, fixExtractCase c = c ∨ DeadCase env c := by
  intro c hc
  by_cases ho : caseOp c = "VEXTRACT_LANE"
  · right
    obtain ⟨qs, a, b, hf⟩ := hs
    have hm : c ∈ cs.filter (fun c => caseOp c == "VEXTRACT_LANE") := by simp [hc, ho]
    rw [hf, List.mem_singleton] at hm
    subst hm
    exact deadCase_extract
  · exact Or.inl (fixExtractCase_of_ne ho)

/-- **The type tables are related by `fixExtractCase`.** -/
theorem typRepairX (B : Builtins) : TypRepair (simEnv20T B) (simEnv20X B) fixExtractCase := by
  refine ⟨caseOp_fixExtractCase, fun x td h => ?_⟩
  rcases findTyp?_simEnv20X B x with h₂ | ⟨cs, h₁, h₂, hcs⟩
  · exact Or.inl (h₂.trans h)
  · rw [h₁] at h
    obtain rfl := (Option.some.inj h).symm
    refine Or.inr ⟨cs, rfl, h₂, ?_⟩
    rcases hcs with rfl | rfl
    · exact fixExtractCase_or_dead extract_instrCasesT
    · exact fixExtractCase_or_dead extract_adminCasesT

/-- **Typing grows from `simEnv20T B` to `simEnv20X B`**, at every value. -/
theorem hasTyp_toX {B : Builtins} {ρ : VarEnv} {t : Typ} {v : Value}
    (h : HasTyp (simEnv20T B) ρ t v) : HasTyp (simEnv20X B) ρ t v :=
  StoreAgree.hasTyp_repair (envSameX B) (typRepairX B) h

end Silmaril.Wasm.SpecTec.Sim20.VecAgree
