module

public import Silmaril.Wasm.SpecTec.Sim20.StoreAgree.Thms
public import Silmaril.Wasm.SpecTec.Sim10.StoreFix.Thms

/-!
# The tables of `simEnv10T B` against those of `simEnv10 B`

The 1.0 `STORE` erratum replaces two type declarations, `instr` and `admininstr`, by declarations
of the same name, as 2.0's does. 2.0's structural lemmas (`Sim20.StoreAgree.typsOfDefs_replaceTyp`
and its siblings) apply unchanged, so:

* `findTyp?_simEnv10T`: `simEnv10T B` finds at `instr` and `admininstr` the declaration of
  `simEnv10 B` with `fixCase10` applied to its cases, and elsewhere the same declaration;
* **`envSame10T`**: the evaluator cannot tell `simEnv10 B` and `simEnv10T B` apart
  (`Sim20.StoreAgree.EnvSame`);
* **`typRepair10T`**: the type tables are related by `fixCase10` (`Sim20.StoreAgree.TypRepair`),
  since the original `STORE` cases of `instr` and `admininstr` are uninhabited (2.0's
  `deadCase_store`, with 1.0's payload `valtype; sz?; memarg`).

So evaluation agrees and typing grows from `simEnv10 B` to `simEnv10T B`
(`Sim20.StoreAgree.evalExp_eq`, `Sim20.StoreAgree.hasTyp_repair`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.StoreAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim10.StoreFix
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (repl typsOfDefs_replaceTyp defsOfDefs_replaceTyp
  relsOfDefs_replaceTyp gramsOfDefs_replaceTyp find?_map_repl caseOp DeadCase TypRepair EnvSame
  deadCase_store)
open Silmaril.Wasm.SpecTec.Scripts.Wasm10 (Original.d67 Original.d170)

/-! ## The two corrected declarations -/

/-- The cases of the original 1.0 `instr`. -/
noncomputable def instrCases10 : List TypCase := Sim.IntNumeric.recCases Original.d67 0 0

/-- The cases of the original 1.0 `admininstr`. -/
noncomputable def adminCases10 : List TypCase := Sim.IntNumeric.recCases Original.d170 0 0

set_option maxRecDepth 8000000 in
theorem instrFix10_eq :
    instrFix10 = .typD "instr" [] [.instD [] [] (.variantT (instrCases10.map fixCase10))] := by
  with_unfolding_all rfl

set_option maxRecDepth 8000000 in
theorem adminFix10_eq :
    adminFix10 = .typD "admininstr" [] [.instD [] [] (.variantT (adminCases10.map fixCase10))] := by
  with_unfolding_all rfl

set_option maxRecDepth 8000000 in
theorem findTyp_instr10 (B : Builtins) :
    (simEnv10 B).findTyp? "instr" = some ([], [.instD [] [] (.variantT instrCases10)]) := by
  with_unfolding_all rfl

set_option maxRecDepth 8000000 in
theorem findTyp_admin10 (B : Builtins) :
    (simEnv10 B).findTyp? "admininstr" = some ([], [.instD [] [] (.variantT adminCases10)]) := by
  with_unfolding_all rfl

/-! ## The tables of `simEnv10T B` -/

theorem simEnv10T_tables (B : Builtins) :
    (simEnv10T B).typs = ((simEnv10 B).typs.map
        (repl "instr" ([], [.instD [] [] (.variantT (instrCases10.map fixCase10))]))).map
        (repl "admininstr" ([], [.instD [] [] (.variantT (adminCases10.map fixCase10))])) ∧
      (simEnv10T B).defs = (simEnv10 B).defs ∧ (simEnv10T B).rels = (simEnv10 B).rels ∧
      (simEnv10T B).grams = (simEnv10 B).grams ∧ (simEnv10T B).builtins = B ∧
      (simEnv10 B).builtins = B := by
  simp only [simEnv10T, simEnv10, baseEnv10, fixedT10, Env.withBuiltins, envOfScript,
    envOfDefs_eq, adminFix10_eq, instrFix10_eq]
  refine ⟨?_, ?_, ?_, ?_, trivial, trivial⟩
  · rw [typsOfDefs_replaceTyp _ _ _ (by decide), typsOfDefs_replaceTyp _ _ _ (by decide)]
    simp [Env.empty, Map.empty]
  · rw [defsOfDefs_replaceTyp, defsOfDefs_replaceTyp]
  · rw [relsOfDefs_replaceTyp, relsOfDefs_replaceTyp]
  · rw [gramsOfDefs_replaceTyp, gramsOfDefs_replaceTyp]

/-- **What `simEnv10T B` finds**: at `instr` and `admininstr` the original declaration with
`fixCase10` applied to its cases, elsewhere what `simEnv10 B` finds. -/
theorem findTyp?_simEnv10T (B : Builtins) (y : IL.Id) :
    (simEnv10T B).findTyp? y = (simEnv10 B).findTyp? y ∨
      ∃ cs, (simEnv10 B).findTyp? y = some ([], [.instD [] [] (.variantT cs)]) ∧
        (simEnv10T B).findTyp? y = some ([], [.instD [] [] (.variantT (cs.map fixCase10))]) ∧
        (cs = instrCases10 ∨ cs = adminCases10) := by
  have ht := (simEnv10T_tables B).1
  simp only [Env.findTyp?, ht, find?_map_repl]
  by_cases ha : y = "admininstr"
  · subst ha
    refine Or.inr ⟨adminCases10, findTyp_admin10 B, ?_, Or.inr rfl⟩
    have h := findTyp_admin10 B
    simp only [Env.findTyp?] at h
    simp [h]
  · by_cases hi : y = "instr"
    · subst hi
      refine Or.inr ⟨instrCases10, findTyp_instr10 B, ?_, Or.inl rfl⟩
      have h := findTyp_instr10 B
      simp only [Env.findTyp?] at h
      simp [h]
    · left
      simp [ha, hi]

/-! ## The evaluator cannot tell them apart -/

theorem caseOp_fixCase10 (c : TypCase) : caseOp (fixCase10 c) = caseOp c := by
  unfold fixCase10
  split <;> rfl

theorem fixCase10_of_ne {c : TypCase} (h : caseOp c ≠ "STORE") : fixCase10 c = c := by
  unfold fixCase10
  split
  · exact absurd rfl h
  · rfl

theorem any_fixCase10 (cs : List TypCase) (op : MixopS) :
    ((cs.map fixCase10).any fun | .mk op' _ _ _ => decide (op' = op)) =
      (cs.any fun | .mk op' _ _ _ => decide (op' = op)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.any_cons, ih]
    congr 1
    have h := caseOp_fixCase10 c
    revert h
    rcases fixCase10 c with ⟨o₁, _, _, _⟩
    rcases c with ⟨o₂, _, _, _⟩
    simp only [caseOp]
    rintro rfl
    rfl

theorem memTyp_simEnv10T (B : Builtins) (x : IL.Id) :
    (simEnv10T B).memTyp x = (simEnv10 B).memTyp x := by
  simp only [Env.memTyp, Map.mem]
  rcases findTyp?_simEnv10T B x with h | ⟨cs, h₁, h₂, -⟩
  · exact congrArg Option.isSome h
  · simp only [Env.findTyp?] at h₁ h₂
    rw [h₁, h₂]; rfl

theorem subCaseOk_simEnv10T (B : Builtins) : subCaseOk (simEnv10T B) = subCaseOk (simEnv10 B) := by
  funext ρ t v
  unfold subCaseOk
  split
  · rename_i x op w
    split
    · rfl
    · rcases findTyp?_simEnv10T B x with h | ⟨cs, h₁, h₂, -⟩
      · rw [h]
      · rw [h₁, h₂]
        exact any_fixCase10 cs op
  · rfl

/-- **The evaluator cannot tell `simEnv10 B` and `simEnv10T B` apart.** -/
theorem envSame10T (B : Builtins) : EnvSame (simEnv10 B) (simEnv10T B) := by
  obtain ⟨-, hd, hr, hg, hb, hb'⟩ := simEnv10T_tables B
  refine ⟨fun x => ?_, fun x => ?_, hb.trans hb'.symm, ?_, ?_, ?_⟩
  · simp only [Env.findDef?, hd]
  · simp only [Env.findRel?, hr]
  · funext ρ pat t
    simp only [matchTypV, memTyp_simEnv10T]
  · funext ρ pat g
    have hm : ∀ x, (simEnv10T B).memGram x = (simEnv10 B).memGram x := by
      intro x; simp only [Env.memGram, hg]
    simp only [matchSymV, hm]
  · funext ρ e v
    simp only [argSubOk, subCaseOk_simEnv10T]

/-- The two environments have the same relations. -/
theorem findRel?_simEnv10T (B : Builtins) (x : IL.Id) :
    (simEnv10T B).findRel? x = (simEnv10 B).findRel? x :=
  (envSame10T B).rels x

/-! ## The original `STORE` cases are dead -/

set_option maxRecDepth 100000 in
theorem store_instrCases10 : ∃ qs pr ds, instrCases10.filter (fun c => caseOp c == "STORE") =
    [.mk "STORE" Whole.storeT10 qs [.iterPr pr (.mk .opt (.mk "Inn" (.varE "Inn?") :: ds))]] :=
  ⟨_, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem store_adminCases10 : ∃ qs pr ds, adminCases10.filter (fun c => caseOp c == "STORE") =
    [.mk "STORE" Whole.storeT10 qs [.iterPr pr (.mk .opt (.mk "Inn" (.varE "Inn?") :: ds))]] :=
  ⟨_, _, _, rfl⟩

/-- Every case of a list whose one `STORE` case is the original one is kept by `fixCase10` or
dead. -/
theorem fixCase10_or_dead {env : Env} {cs : List TypCase}
    (hs : ∃ qs pr ds, cs.filter (fun c => caseOp c == "STORE") =
      [.mk "STORE" Whole.storeT10 qs [.iterPr pr (.mk .opt (.mk "Inn" (.varE "Inn?") :: ds))]]) :
    ∀ c ∈ cs, fixCase10 c = c ∨ DeadCase env c := by
  intro c hc
  by_cases ho : caseOp c = "STORE"
  · right
    obtain ⟨qs, pr, ds, hf⟩ := hs
    have hm : c ∈ cs.filter (fun c => caseOp c == "STORE") := by
      simp [hc, ho]
    rw [hf, List.mem_singleton] at hm
    subst hm
    exact deadCase_store Whole.findVal_innOpt_caseScope10
  · exact Or.inl (fixCase10_of_ne ho)

/-- **The type tables are related by `fixCase10`.** -/
theorem typRepair10T (B : Builtins) : TypRepair (simEnv10 B) (simEnv10T B) fixCase10 := by
  refine ⟨caseOp_fixCase10, fun x td h => ?_⟩
  rcases findTyp?_simEnv10T B x with h₂ | ⟨cs, h₁, h₂, hcs⟩
  · exact Or.inl (h₂.trans h)
  · rw [h₁] at h
    obtain rfl := (Option.some.inj h).symm
    refine Or.inr ⟨cs, rfl, h₂, ?_⟩
    rcases hcs with rfl | rfl
    · exact fixCase10_or_dead store_instrCases10
    · exact fixCase10_or_dead store_adminCases10

end Silmaril.Wasm.SpecTec.Sim10.StoreAgree
