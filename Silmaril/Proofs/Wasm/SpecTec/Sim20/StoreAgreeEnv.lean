module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.StoreAgree.Typ
public import Silmaril.Wasm.SpecTec.Sim20.StoreFix.Thms
public import Silmaril.Wasm.SpecTec.Sim20.RelFree.Thms

/-!
# The tables of `simEnv20T B` against those of `simEnv20S B`

The `STORE` erratum replaces two type declarations, `instr` and `admininstr`, by declarations
of the same name. So:

* `typsOfDefs_replaceTyp`, `defsOfDefs_replaceTyp`, `relsOfDefs_replaceTyp`,
  `gramsOfDefs_replaceTyp` (structural): replacing a type declaration rewrites the type table
  entry by entry and leaves the definition, relation and grammar tables alone;
* `findTyp?_simEnv20T`: `simEnv20T B` finds at `instr` and `admininstr` the declaration of
  `simEnv20S B` with `fixCase` applied to its cases, and elsewhere the same declaration;
* **`envSame20T`**: the evaluator cannot tell `simEnv20S B` and `simEnv20T B` apart
  (`StoreAgree.EnvSame`): same definitions, relations and primitives, same type names, and
  `subCaseOk` reads only case names, which `fixCase` keeps;
* **`typRepair20T`**: the type tables are related by `fixCase` (`StoreAgree.TypRepair`), since the
  original `STORE` cases of `instr` and `admininstr` are uninhabited (`deadCase_store`, the
  premise iterates over the unbound `Inn?`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.StoreFix
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S fixedS20)
open Silmaril.Wasm.SpecTec.Scripts.Wasm20 (Original.d133 Original.d295)

/-! ## Replacing a type declaration -/

/-- Rewrite the entry of `x` in a type table. -/
def repl (x : IL.Id) (v : TypDef) (p : IL.Id × TypDef) : IL.Id × TypDef :=
  if p.1 = x then (x, v) else p

mutual
theorem typsOfDef_replaceTyp (x ps insts) (hx : x ≠ "_") : ∀ d : Def,
    typsOfDef (replaceDef (.typD x ps insts) d) = (typsOfDef d).map (repl x (ps, insts))
  | .recD ds => by
    simp only [replaceDef, typsOfDef]; exact typsOfDefs_replaceTyp x ps insts hx ds
  | .typD y ps' insts' => by
    by_cases hy : x = y
    · subst hy
      simp [replaceDef, matchesDecl, declKind?, typsOfDef, Map.bind, Map.empty, hx, repl]
    · have hy' : ¬ y = x := fun h => hy h.symm
      by_cases h_ : y = "_"
      · subst h_
        simp [replaceDef, matchesDecl, declKind?, typsOfDef, Map.bind, Map.empty, hx]
      · simp [replaceDef, matchesDecl, declKind?, typsOfDef, Map.bind, Map.empty, hy, h_, repl,
          hy']
  | .decD _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?, typsOfDef, Map.empty]
  | .gramD _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?, typsOfDef, Map.empty]
  | .relD _ _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?, typsOfDef, Map.empty]
theorem typsOfDefs_replaceTyp (x ps insts) (hx : x ≠ "_") : ∀ ds : List Def,
    typsOfDefs (replaceDefs (.typD x ps insts) ds) = (typsOfDefs ds).map (repl x (ps, insts))
  | [] => rfl
  | d :: ds => by
    simp only [replaceDefs, typsOfDefs, List.map_append]
    rw [typsOfDef_replaceTyp x ps insts hx d, typsOfDefs_replaceTyp x ps insts hx ds]
end

mutual
theorem defsOfDef_replaceTyp (x ps insts) : ∀ d : Def,
    defsOfDef (replaceDef (.typD x ps insts) d) = defsOfDef d
  | .recD ds => by simp only [replaceDef, defsOfDef]; exact defsOfDefs_replaceTyp x ps insts ds
  | .typD _ _ _ => by simp only [replaceDef]; split <;> rfl
  | .decD _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
  | .gramD _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
  | .relD _ _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
theorem defsOfDefs_replaceTyp (x ps insts) : ∀ ds : List Def,
    defsOfDefs (replaceDefs (.typD x ps insts) ds) = defsOfDefs ds
  | [] => rfl
  | d :: ds => by
    simp only [replaceDefs, defsOfDefs]
    rw [defsOfDef_replaceTyp x ps insts d, defsOfDefs_replaceTyp x ps insts ds]
end

mutual
theorem relsOfDef_replaceTyp (x ps insts) : ∀ d : Def,
    relsOfDef (replaceDef (.typD x ps insts) d) = relsOfDef d
  | .recD ds => by simp only [replaceDef, relsOfDef]; exact relsOfDefs_replaceTyp x ps insts ds
  | .typD _ _ _ => by simp only [replaceDef]; split <;> rfl
  | .decD _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
  | .gramD _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
  | .relD _ _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
theorem relsOfDefs_replaceTyp (x ps insts) : ∀ ds : List Def,
    relsOfDefs (replaceDefs (.typD x ps insts) ds) = relsOfDefs ds
  | [] => rfl
  | d :: ds => by
    simp only [replaceDefs, relsOfDefs]
    rw [relsOfDef_replaceTyp x ps insts d, relsOfDefs_replaceTyp x ps insts ds]
end

mutual
theorem gramsOfDef_replaceTyp (x ps insts) : ∀ d : Def,
    gramsOfDef (replaceDef (.typD x ps insts) d) = gramsOfDef d
  | .recD ds => by simp only [replaceDef, gramsOfDef]; exact gramsOfDefs_replaceTyp x ps insts ds
  | .typD _ _ _ => by simp only [replaceDef]; split <;> rfl
  | .decD _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
  | .gramD _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
  | .relD _ _ _ _ _ => by simp [replaceDef, matchesDecl, declKind?]
theorem gramsOfDefs_replaceTyp (x ps insts) : ∀ ds : List Def,
    gramsOfDefs (replaceDefs (.typD x ps insts) ds) = gramsOfDefs ds
  | [] => rfl
  | d :: ds => by
    simp only [replaceDefs, gramsOfDefs]
    rw [gramsOfDef_replaceTyp x ps insts d, gramsOfDefs_replaceTyp x ps insts ds]
end

/-- Looking up a rewritten table. -/
theorem find?_map_repl (x : IL.Id) (v : TypDef) (y : IL.Id) :
    ∀ m : Map TypDef, Map.find? (m.map (repl x v)) y =
      if y = x then (Map.find? m y).map (fun _ => v) else Map.find? m y
  | [] => by simp [Map.find?]
  | (z, w) :: m => by
    have ih := find?_map_repl x v y m
    by_cases hz : z = x
    · subst hz
      by_cases hy : y = z
      · subst hy; simp [Map.find?, repl]
      · simp [Map.find?, repl, hy, Ne.symm hy, ih]
    · by_cases hy : y = x
      · subst hy
        by_cases hzy : z = y
        · exact absurd hzy hz
        · simp [Map.find?, repl, hz, ih]
      · simp [Map.find?, repl, hz, hy, ih]

/-! ## The two corrected declarations -/

/-- The cases of the original `instr`. -/
noncomputable def instrCasesS : List TypCase := Sim.IntNumeric.recCases Original.d133 0 0

/-- The cases of the original `admininstr`. -/
noncomputable def adminCasesS : List TypCase := Sim.IntNumeric.recCases Original.d295 0 0

set_option maxRecDepth 8000000 in
theorem instrFix20_eq :
    instrFix20 = .typD "instr" [] [.instD [] [] (.variantT (instrCasesS.map fixCase))] := by
  with_unfolding_all rfl

set_option maxRecDepth 8000000 in
theorem adminFix20_eq :
    adminFix20 = .typD "admininstr" [] [.instD [] [] (.variantT (adminCasesS.map fixCase))] := by
  with_unfolding_all rfl

set_option maxRecDepth 8000000 in
theorem findTyp_instr20S (B : Builtins) :
    (simEnv20S B).findTyp? "instr" = some ([], [.instD [] [] (.variantT instrCasesS)]) := by
  with_unfolding_all rfl

set_option maxRecDepth 8000000 in
theorem findTyp_admin20S (B : Builtins) :
    (simEnv20S B).findTyp? "admininstr" = some ([], [.instD [] [] (.variantT adminCasesS)]) := by
  with_unfolding_all rfl

/-! ## The tables of `simEnv20T B` -/

theorem simEnv20T_tables (B : Builtins) :
    (simEnv20T B).typs = ((simEnv20S B).typs.map
        (repl "instr" ([], [.instD [] [] (.variantT (instrCasesS.map fixCase))]))).map
        (repl "admininstr" ([], [.instD [] [] (.variantT (adminCasesS.map fixCase))])) ∧
      (simEnv20T B).defs = (simEnv20S B).defs ∧ (simEnv20T B).rels = (simEnv20S B).rels ∧
      (simEnv20T B).grams = (simEnv20S B).grams ∧ (simEnv20T B).builtins = B ∧
      (simEnv20S B).builtins = B := by
  simp only [simEnv20T, simEnv20S, fixedT20, Env.withBuiltins, envOfScript, envOfDefs_eq,
    adminFix20_eq, instrFix20_eq]
  refine ⟨?_, ?_, ?_, ?_, trivial, trivial⟩
  · rw [typsOfDefs_replaceTyp _ _ _ (by decide), typsOfDefs_replaceTyp _ _ _ (by decide)]
    simp [Env.empty, Map.empty]
  · rw [defsOfDefs_replaceTyp, defsOfDefs_replaceTyp]
  · rw [relsOfDefs_replaceTyp, relsOfDefs_replaceTyp]
  · rw [gramsOfDefs_replaceTyp, gramsOfDefs_replaceTyp]

/-- **What `simEnv20T B` finds**: at `instr` and `admininstr` the original declaration with
`fixCase` applied to its cases, elsewhere what `simEnv20S B` finds. -/
theorem findTyp?_simEnv20T (B : Builtins) (y : IL.Id) :
    (simEnv20T B).findTyp? y = (simEnv20S B).findTyp? y ∨
      ∃ cs, (simEnv20S B).findTyp? y = some ([], [.instD [] [] (.variantT cs)]) ∧
        (simEnv20T B).findTyp? y = some ([], [.instD [] [] (.variantT (cs.map fixCase))]) ∧
        (cs = instrCasesS ∨ cs = adminCasesS) := by
  have ht := (simEnv20T_tables B).1
  simp only [Env.findTyp?, ht, find?_map_repl]
  by_cases ha : y = "admininstr"
  · subst ha
    refine Or.inr ⟨adminCasesS, findTyp_admin20S B, ?_, Or.inr rfl⟩
    have h := findTyp_admin20S B
    simp only [Env.findTyp?] at h
    simp [h]
  · by_cases hi : y = "instr"
    · subst hi
      refine Or.inr ⟨instrCasesS, findTyp_instr20S B, ?_, Or.inl rfl⟩
      have h := findTyp_instr20S B
      simp only [Env.findTyp?] at h
      simp [h]
    · left
      simp [ha, hi]

/-! ## The evaluator cannot tell them apart -/

theorem caseOp_fixCase (c : TypCase) : caseOp (fixCase c) = caseOp c := by
  unfold fixCase
  split <;> rfl

theorem fixCase_of_ne {c : TypCase} (h : caseOp c ≠ "STORE") : fixCase c = c := by
  unfold fixCase
  split
  · exact absurd rfl h
  · rfl

theorem any_fixCase (cs : List TypCase) (op : MixopS) :
    ((cs.map fixCase).any fun | .mk op' _ _ _ => decide (op' = op)) =
      (cs.any fun | .mk op' _ _ _ => decide (op' = op)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.any_cons, ih]
    congr 1
    have h := caseOp_fixCase c
    revert h
    rcases fixCase c with ⟨o₁, _, _, _⟩
    rcases c with ⟨o₂, _, _, _⟩
    simp only [caseOp]
    rintro rfl
    rfl

theorem memTyp_simEnv20T (B : Builtins) (x : IL.Id) :
    (simEnv20T B).memTyp x = (simEnv20S B).memTyp x := by
  simp only [Env.memTyp, Map.mem]
  rcases findTyp?_simEnv20T B x with h | ⟨cs, h₁, h₂, -⟩
  · exact congrArg Option.isSome h
  · simp only [Env.findTyp?] at h₁ h₂
    rw [h₁, h₂]; rfl

theorem subCaseOk_simEnv20T (B : Builtins) : subCaseOk (simEnv20T B) = subCaseOk (simEnv20S B) := by
  funext ρ t v
  unfold subCaseOk
  split
  · rename_i x op w
    split
    · rfl
    · rcases findTyp?_simEnv20T B x with h | ⟨cs, h₁, h₂, -⟩
      · rw [h]
      · rw [h₁, h₂]
        exact any_fixCase cs op
  · rfl

/-- **The evaluator cannot tell `simEnv20S B` and `simEnv20T B` apart.** -/
theorem envSame20T (B : Builtins) : EnvSame (simEnv20S B) (simEnv20T B) := by
  obtain ⟨-, hd, hr, hg, hb, hb'⟩ := simEnv20T_tables B
  refine ⟨fun x => ?_, fun x => ?_, hb.trans hb'.symm, ?_, ?_, ?_⟩
  · simp only [Env.findDef?, hd]
  · simp only [Env.findRel?, hr]
  · funext ρ pat t
    simp only [matchTypV, memTyp_simEnv20T]
  · funext ρ pat g
    have hm : ∀ x, (simEnv20T B).memGram x = (simEnv20S B).memGram x := by
      intro x; simp only [Env.memGram, hg]
    simp only [matchSymV, hm]
  · funext ρ e v
    simp only [argSubOk, subCaseOk_simEnv20T]

/-! ## The original `STORE` cases are dead -/

/-- A case whose premise iterates over the unbound `Inn?` is dead. -/
theorem deadCase_store {env : Env} {t : Typ} {qs : List Param} {pr : Prem} {x : IL.Id}
    {ds : List Dom} (ht : ∀ w, (caseScope VarEnv.empty t w).findVal? "Inn?" = none) :
    DeadCase env (.mk "STORE" t qs [.iterPr pr (.mk .opt (.mk x (.varE "Inn?") :: ds))]) := by
  intro n w h
  cases n with
  | zero => simp [hasTypCase] at h
  | succ n =>
    have hq : quantDefs qs [.iterPr pr (.mk .opt (.mk x (.varE "Inn?") :: ds))] = [] := by
      simp [quantDefs]
    simp only [hasTypCase, caseOp, ↓reduceIte, hq, bindQuants, Res.elimUndef_ok,
      Res.bind_eq_ok] at h
    obtain ⟨b, -, h⟩ := h
    cases b
    · simp at h
    · simp only [↓reduceIte] at h
      exact Whole.not_premsOk_unboundOpt (ht w) ⟨n, h⟩

set_option maxRecDepth 100000 in
theorem store_instrCasesS : ∃ qs pr ds, instrCasesS.filter (fun c => caseOp c == "STORE") =
    [.mk "STORE" (.tupT [.mk "numtype" (.varT "numtype" []), .mk "sz?" (.iterT (.varT "sz" []) .opt),
      .mk "memarg" (.varT "memarg" [])]) qs [.iterPr pr (.mk .opt (.mk "Inn" (.varE "Inn?") :: ds))]] :=
  ⟨_, _, _, rfl⟩

set_option maxRecDepth 100000 in
theorem store_adminCasesS : ∃ qs pr ds, adminCasesS.filter (fun c => caseOp c == "STORE") =
    [.mk "STORE" (.tupT [.mk "numtype" (.varT "numtype" []), .mk "sz?" (.iterT (.varT "sz" []) .opt),
      .mk "memarg" (.varT "memarg" [])]) qs [.iterPr pr (.mk .opt (.mk "Inn" (.varE "Inn?") :: ds))]] :=
  ⟨_, _, _, rfl⟩

/-- Every case of a list with one `STORE` case, the dead one, is kept by `fixCase` or dead. -/
theorem fixCase_or_dead {env : Env} {cs : List TypCase}
    (hs : ∃ qs pr ds, cs.filter (fun c => caseOp c == "STORE") =
      [.mk "STORE" (.tupT [.mk "numtype" (.varT "numtype" []),
        .mk "sz?" (.iterT (.varT "sz" []) .opt), .mk "memarg" (.varT "memarg" [])]) qs
        [.iterPr pr (.mk .opt (.mk "Inn" (.varE "Inn?") :: ds))]]) :
    ∀ c ∈ cs, fixCase c = c ∨ DeadCase env c := by
  intro c hc
  by_cases ho : caseOp c = "STORE"
  · right
    obtain ⟨qs, pr, ds, hf⟩ := hs
    have hm : c ∈ cs.filter (fun c => caseOp c == "STORE") := by
      simp [hc, ho]
    rw [hf, List.mem_singleton] at hm
    subst hm
    exact deadCase_store Whole.findVal_innOpt_caseScope
  · exact Or.inl (fixCase_of_ne ho)

/-- **The type tables are related by `fixCase`.** -/
theorem typRepair20T (B : Builtins) : TypRepair (simEnv20S B) (simEnv20T B) fixCase := by
  refine ⟨caseOp_fixCase, fun x td h => ?_⟩
  rcases findTyp?_simEnv20T B x with h₂ | ⟨cs, h₁, h₂, hcs⟩
  · exact Or.inl (h₂.trans h)
  · rw [h₁] at h
    obtain rfl := (Option.some.inj h).symm
    refine Or.inr ⟨cs, rfl, h₂, ?_⟩
    rcases hcs with rfl | rfl
    · exact fixCase_or_dead store_instrCasesS
    · exact fixCase_or_dead store_adminCasesS

end Silmaril.Wasm.SpecTec.Sim20.StoreAgree
