module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxClause.Clause

/-!
# Round 8, REH route 2: the clause half on the script, and `Task.clauseErase` (unrefined)

`defsE_all`: by induction on fuel, `DefsE env n` at every `n` in an environment with the static
facts `EnvFactsE`, conforming definitions and primitives that commute with erasure.
`envFactsE_utf8Env`: `utf8Env B` has the static facts, from round 7's flow check
(`NxFlow.flowItems_fixed`, `auxItems_fixed`), round 7's site check in the clause signatures
(`NxErase.xItems_fixed`), round 3's syntactic check (`EraseAll.defs_utf8Env`) and this round's
`yItems_fixed`. `clauseErase'`: `NxErase.Task.clauseErase`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxClause

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSound
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
open Silmaril.Wasm.SpecTec.Sim.Round7.NxErase (QT clauseX xItem xItems)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseA AllIn)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (ER ArgIn BIErase gdE grE)
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (fixed)

/-! ## The clause list and every fuel -/

section
variable (hF : SigFacts) {env : Env} (hE : EnvFactsE env) (hBI : BIErase QT gdE env)
  (hDV : ∀ m, DefsVT sigX tsigFixed env m)
include hF hE hBI hDV

/-- **The clauses of a definition commute with erasure.** -/
theorem tryClauses_erase {f : String} {ps : List Param} {t : Typ} {cls : List Clause}
    (hD : DefFactsE f ps t cls) {ws : List ArgV}
    (hargs : ArgsVT sigX tsigFixed ws
      ((paramPTs ps).map (substPT (typParams ps) (fillV sigX ws))))
    (hw : ∀ w ∈ ws, ArgIn QT gdE w) :
    ∀ (n : Nat) (cs : List Clause), (∀ c ∈ cs, c ∈ cls) → (∀ m < n, DefsE env m) →
      ER eraseV (AllIn QT) (tryClauses n env cs ws) (tryClauses n env cs (ws.map eraseA))
  | 0, _, _, _ => by simp only [tryClauses]; exact EraseAll.ER.error _
  | n + 1, [], _, _ => by simp only [tryClauses]; exact EraseAll.ER.error _
  | n + 1, .defD qs args e prems :: cs, hcs, ih => by
    simp only [tryClauses]
    exact clause_erase hF hE hBI hDV (fun m hm => ih m (by omega)) hD
      (hcs _ (List.mem_cons_self ..)) hargs hw
      (tryClauses_erase hD hargs hw n cs (fun c hc => hcs c (List.mem_cons_of_mem _ hc))
        (fun m hm => ih m (by omega)))

/-- **One step of the induction on fuel.** -/
theorem defsE_of_lt (n : Nat) (ih : ∀ m < n, DefsE env m) : DefsE env n := by
  intro f d pts ws hg hd hp hargs hw
  obtain ⟨⟨tps', pts'⟩, hl, hpe⟩ := Option.map_eq_some_iff.1 hp
  rcases hE.defs f d hg hd with hnil | hD
  · rw [hnil]
    cases n <;> simp only [tryClauses] <;> exact EraseAll.ER.error _
  · obtain ⟨h1, h2⟩ := tsig_params hD.base.tsig hl
    subst h1 h2
    simp only at hpe
    subst hpe
    exact tryClauses_erase hF hE hBI hDV hD hargs hw n d.2.2 (fun c hc => hc) ih

/-- **Clause bodies commute with erasure at every fuel.** -/
theorem defsE_all : ∀ n, DefsE env n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih => exact defsE_of_lt hF hE hBI hDV n ih

end

/-! ## The script -/

theorem reach_of_gdE {x : String} (h : gdE x = true) : reach 1 x = true := by
  simp only [gdE, EraseAll.stepReachE, reach, List.contains_iff_mem, List.mem_filter] at h ⊢
  exact h.1

mutual
theorem yFacts_def : ∀ d : Def, yItem d = true → ∀ p ∈ defsOfDef d, gdE p.1 = true →
    (tsigFixed.params.lookup p.1).isSome = true ∧ ∀ c ∈ p.2.2.2, clauseY p.2.1 c = true
  | .decD f ps t cls, h, p, hp, hg => by
    simp only [defsOfDef, Map.bind, Map.empty] at hp
    split at hp
    · simp at hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      simp only [yItem, hg, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        List.all_eq_true] at h
      exact h
  | .recD ds, h, p, hp, hg => by
    simp only [yItem] at h
    simp only [defsOfDef] at hp
    exact yFacts_defs ds h p hp hg
  | .typD _ _ _, _, p, hp, _ => by simp [defsOfDef, Map.empty] at hp
  | .relD _ _ _ _ _, _, p, hp, _ => by simp [defsOfDef, Map.empty] at hp
  | .gramD _ _ _ _, _, p, hp, _ => by simp [defsOfDef, Map.empty] at hp

theorem yFacts_defs : ∀ ds : List Def, yItems ds = true → ∀ p ∈ defsOfDefs ds, gdE p.1 = true →
    (tsigFixed.params.lookup p.1).isSome = true ∧ ∀ c ∈ p.2.2.2, clauseY p.2.1 c = true
  | [], _, p, hp, _ => by simp [defsOfDefs, Map.empty] at hp
  | d :: ds, h, p, hp, hg => by
    simp only [yItems, Bool.and_eq_true] at h
    simp only [defsOfDefs, List.mem_append] at hp
    rcases hp with hp | hp
    · exact yFacts_defs ds h.2 p hp hg
    · exact yFacts_def d h.1 p hp hg
end

mutual
theorem xFacts_def : ∀ d : Def, xItem d = true → ∀ p ∈ defsOfDef d, reach 1 p.1 = true →
    ∀ b ∈ modes (typParams p.2.1), ∀ c ∈ p.2.2.2, clauseX (typParams p.2.1) b c = true
  | .decD f ps t cls, h, p, hp, hr => by
    simp only [defsOfDef, Map.bind, Map.empty] at hp
    split at hp
    · simp at hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      simp only [xItem, hr, Bool.not_true, Bool.false_or, List.all_eq_true] at h
      exact h
  | .recD ds, h, p, hp, hr => by
    simp only [xItem] at h
    simp only [defsOfDef] at hp
    exact xFacts_defs ds h p hp hr
  | .typD _ _ _, _, p, hp, _ => by simp [defsOfDef, Map.empty] at hp
  | .relD _ _ _ _ _, _, p, hp, _ => by simp [defsOfDef, Map.empty] at hp
  | .gramD _ _ _ _, _, p, hp, _ => by simp [defsOfDef, Map.empty] at hp

theorem xFacts_defs : ∀ ds : List Def, xItems ds = true → ∀ p ∈ defsOfDefs ds,
    reach 1 p.1 = true →
    ∀ b ∈ modes (typParams p.2.1), ∀ c ∈ p.2.2.2, clauseX (typParams p.2.1) b c = true
  | [], _, p, hp, _ => by simp [defsOfDefs, Map.empty] at hp
  | d :: ds, h, p, hp, hr => by
    simp only [xItems, Bool.and_eq_true] at h
    simp only [defsOfDefs, List.mem_append] at hp
    rcases hp with hp | hp
    · exact xFacts_defs ds h.2 p hp hr
    · exact xFacts_def d h.1 p hp hr
end

theorem params_utf8 : (tsigFixed.params.lookup "utf8").isSome = true := by
  decide

/-- **The static facts hold in the round-7 environment.** -/
theorem envFactsE_utf8Env (B : Builtins) : EnvFactsE (utf8Env B) where
  memX := memTyp_utf8Env_X B
  params := by
    intro f d hg hd
    by_cases hu : f = "utf8"
    · subst hu; exact params_utf8
    · rw [findDef?_utf8Env_of_ne B hu] at hd
      exact (yFacts_defs fixed yItems_fixed _ (mem_defs_of_findDef' hd) hg).1
  defs := by
    intro f d hg hd
    by_cases hu : f = "utf8"
    · subst hu
      rw [findDef?_utf8Env] at hd
      cases hd
      exact .inl rfl
    · refine .inr ?_
      have hd' := hd
      rw [findDef?_utf8Env_of_ne B hu] at hd'
      have hm := mem_defs_of_findDef' hd'
      have hr := reach_of_gdE hg
      exact {
        base := defFacts_defs fixed flowItems_fixed auxItems_fixed _ hm hr
        x := xFacts_defs fixed NxErase.xItems_fixed _ hm hr
        xc := EraseAll.defs_utf8Env B f d hg hd
        y := (yFacts_defs fixed yItems_fixed _ hm hg).2 }

/-- **`NxErase.Task.clauseErase` holds**: in `utf8Env B`, with primitives that conform and that
commute with erasure on `gdE`, clause bodies commute with erasure at every checked call in a scope
without definition and type bindings. -/
theorem clauseErase' : NxErase.Task.clauseErase := by
  intro B hB hBI ρ k hd ht
  have hF := sigFacts sigsAux_fixed
  have hE := envFactsE_utf8Env B
  exact callE_nil hF hE.params (fun m _ => defsE_all hF hE hBI (NxFlow.flowSound B hB) m) hd ht

end Silmaril.Wasm.SpecTec.Sim.Round7.NxClause
