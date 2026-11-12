module

public import Silmaril.Wasm.SpecTec.Sim.Round7.NxRule.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxRule.Check00
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxRule.Check01
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxRule.Check02
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxRule.Check03
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxRule.Check04
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxRule.Check05
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxRule.Check06
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxRule.Check07
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxRule.Check08
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxRule.Check09
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxRule.Check10
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxRule.Check11
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxRule.Check12
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxRule.Check13
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxRule.Check14
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.NxRule.Check15

/-!
# Round 7, REH route 2, part (a) at runtime: the scope of a rule instance (unrefined)

* `ruleAuxRels_fixed`: the sixteen kernel slices together.
* `scopeVT_qScope`: the quantifier part of a scope typed by `Sim.QuantsOk` conforms.
* `agreeOn_qScope`: on the free variables of a rule closed over its quantifiers, a scope and its
  quantifier part agree.
* `callH_nil`: in a scope without definition and type bindings, calls conform.
* `rFacts`: what the kernel checks say about one rule of a reachable relation.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxRule

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSound
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (quantNames)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer (varsIn ruleClosed closedRels closedRels_fixed)

/-! ## The kernel slices -/

theorem ruleAuxRels_of_slices (m : Map RelDef)
    (h : ∀ i < 16, ruleAuxRelsAt m (7 * i) 7 = true) : ruleAuxRels m = true := by
  simp only [ruleAuxRels, List.all_eq_true]
  intro p hp
  by_cases hr : reach 0 p.1 = true
  · have hs : ∀ i < 16, p.2.1.isEmpty = true ∧ p.2.2.2.2.length ≤ 112 ∧
        ((p.2.2.2.2.drop (7 * i)).take 7).all
          (ruleAux sigX tsigFixed (toAT p.2.2.2.1) (matchedRel p.1)) = true := by
      intro i hi
      have hi' := List.all_eq_true.1 (h i hi) p hp
      simp only [hr, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hi'
      exact ⟨hi'.1.1, hi'.1.2, hi'.2⟩
    simp only [hr, Bool.not_true, Bool.false_or, Bool.and_eq_true]
    exact ⟨(hs 0 (by omega)).1, EraseAll.all_chunks _ 7 16 _ (hs 0 (by omega)).2.1
      fun i hi => (hs i hi).2.2⟩
  · simp [hr]

/-- **Every rule `Step` reaches passes the side conditions** (`NxRule.ruleAux`). -/
theorem ruleAuxRels_fixed :
    ruleAuxRels (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = true := by
  refine ruleAuxRels_of_slices _ fun i hi => ?_
  match i, hi with
  | 0, _ => exact ruleAux00
  | 1, _ => exact ruleAux01
  | 2, _ => exact ruleAux02
  | 3, _ => exact ruleAux03
  | 4, _ => exact ruleAux04
  | 5, _ => exact ruleAux05
  | 6, _ => exact ruleAux06
  | 7, _ => exact ruleAux07
  | 8, _ => exact ruleAux08
  | 9, _ => exact ruleAux09
  | 10, _ => exact ruleAux10
  | 11, _ => exact ruleAux11
  | 12, _ => exact ruleAux12
  | 13, _ => exact ruleAux13
  | 14, _ => exact ruleAux14
  | 15, _ => exact ruleAux15
  | n + 16, h => omega

/-! ## The quantifier part of a scope -/

theorem find?_filter {α : Type} (P : IL.Id × α → Bool) (x : IL.Id) :
    ∀ m : Map α, (∀ v, P (x, v) = true) → Map.find? (m.filter P) x = Map.find? m x
  | [], _ => rfl
  | (y, v) :: m, hP => by
    by_cases hy : y = x
    · subst hy
      simp [List.filter, hP v, Map.find?]
    · cases hp : P (y, v) <;>
        simp [List.filter, hp, Map.find?, hy, find?_filter P x m hP]

theorem find?_filter_none {α : Type} (P : IL.Id × α → Bool) (x : IL.Id) :
    ∀ m : Map α, (∀ v, P (x, v) = false) → Map.find? (m.filter P) x = none
  | [], _ => rfl
  | (y, v) :: m, hP => by
    by_cases hy : y = x
    · subst hy
      simp [List.filter, hP v, find?_filter_none P y m hP]
    · cases hp : P (y, v) <;>
        simp [List.filter, hp, hy, find?_filter_none P x m hP]

theorem findVal?_qScope_of_mem {qs : List Param} {ρ : VarEnv} {x : IL.Id}
    (hx : x ∈ quantNames qs) : (qScope qs ρ).findVal? x = ρ.findVal? x := by
  simp only [qScope, VarEnv.findVal?]
  exact find?_filter (fun p : IL.Id × Value => (quantNames qs).contains p.1) x ρ.vals
    fun _ => by simpa using hx

theorem findVal?_qScope_of_not_mem {qs : List Param} {ρ : VarEnv} {x : IL.Id}
    (hx : x ∉ quantNames qs) : (qScope qs ρ).findVal? x = none := by
  simp only [qScope, VarEnv.findVal?]
  exact find?_filter_none (fun p : IL.Id × Value => (quantNames qs).contains p.1) x ρ.vals
    fun _ => by simpa using hx

theorem mem_quantNames_of_findVal? {qs : List Param} {ρ : VarEnv} {x : IL.Id} {v : Value}
    (h : (qScope qs ρ).findVal? x = some v) : x ∈ quantNames qs := by
  by_contra hx
  rw [findVal?_qScope_of_not_mem hx] at h
  cases h

theorem lookup_quantsΓ {x : String} {a : AT} : ∀ {qs : List Param},
    (quantsΓ qs).lookup x = some a → ∃ t, Param.expP x t ∈ qs ∧ a = toAT t
  | [], h => by simp [quantsΓ] at h
  | q :: qs, h => by
    cases q with
    | expP y t =>
      simp only [quantsΓ, List.lookup] at h
      split at h
      · rename_i hy
        cases h
        exact ⟨t, by rw [beq_iff_eq.1 hy]; exact List.mem_cons_self .., rfl⟩
      · obtain ⟨t', ht', ha⟩ := lookup_quantsΓ h
        exact ⟨t', List.mem_cons_of_mem _ ht', ha⟩
    | typP _ =>
      obtain ⟨t', ht', ha⟩ := lookup_quantsΓ (qs := qs) (by simpa [quantsΓ] using h)
      exact ⟨t', List.mem_cons_of_mem _ ht', ha⟩
    | defP _ _ _ =>
      obtain ⟨t', ht', ha⟩ := lookup_quantsΓ (qs := qs) (by simpa [quantsΓ] using h)
      exact ⟨t', List.mem_cons_of_mem _ ht', ha⟩
    | gramP _ _ _ =>
      obtain ⟨t', ht', ha⟩ := lookup_quantsΓ (qs := qs) (by simpa [quantsΓ] using h)
      exact ⟨t', List.mem_cons_of_mem _ ht', ha⟩

theorem isSome_lookup_quantsΓ {x : String} : ∀ {qs : List Param},
    x ∈ quantNames qs → ((quantsΓ qs).lookup x).isSome = true
  | [], h => by simp [quantNames] at h
  | q :: qs, h => by
    cases q with
    | expP y t =>
      simp only [quantsΓ, List.lookup]
      split
      · rfl
      · rename_i hy
        have : x ∈ quantNames qs := by
          simp only [quantNames, List.filterMap_cons, List.mem_cons] at h
          rcases h with h | h
          · subst h; simp at hy
          · exact h
        exact isSome_lookup_quantsΓ this
    | typP _ => exact isSome_lookup_quantsΓ (qs := qs) (by simpa [quantNames] using h)
    | defP _ _ _ => exact isSome_lookup_quantsΓ (qs := qs) (by simpa [quantNames] using h)
    | gramP _ _ _ => exact isSome_lookup_quantsΓ (qs := qs) (by simpa [quantNames] using h)

/-- **The quantifier part of a typed scope conforms.** -/
theorem scopeVT_qScope {B : Builtins} {qs : List Param} {ρ : VarEnv}
    (hT : TypsNx sigX.good ρ) (hq : Sim.QuantsOk (utf8Env B) ρ qs)
    (hw : "_" ∉ quantNames qs) : ScopeVT sigX (quantsΓ qs) (qScope qs ρ) where
  val := by
    intro x a v hx hv
    have hm := mem_quantNames_of_findVal? hv
    rw [findVal?_qScope_of_mem hm] at hv
    obtain ⟨t, ht, rfl⟩ := lookup_quantsΓ hx
    obtain ⟨w, hw', hvt⟩ := NxQuant.vtB_of_quantsOk hT hq ht
    rw [hv] at hw'
    cases hw'
    exact hvt
  dom := fun x v hv => isSome_lookup_quantsΓ (mem_quantNames_of_findVal? hv)
  wild := findVal?_qScope_of_not_mem hw

/-- **A scope and its quantifier part agree on the variables of a closed rule.** -/
theorem agreeOn_qScope {qs : List Param} {ρ : VarEnv} {s : Sets}
    (hs : varsIn (quantNames qs) s = true) : VarEnv.AgreeOn s ρ (qScope qs ρ) := by
  refine ⟨fun x hx => (findVal?_qScope_of_mem (EraseDer.varsIn_mem hs x hx)).symm,
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-! ## Calls in a rule's scope -/

theorem clauseCtx_nil {ρ : VarEnv} (hd : ρ.defs = []) (ht : ρ.typs = []) :
    ClauseCtx ρ [] [] .unk where
  defs := fun y g' h => by simp [VarEnv.findDef?, hd] at h
  defsIn := fun y h => by simp [defQuants] at h
  typs := fun x t h => by simp [VarEnv.findTyp?, ht] at h
  typsIn := fun x h => by simp at h

theorem clauseSig_nil : clauseSig sigX [] .unk [] = sigX := by
  simp [clauseSig, defQuants]

theorem clauseTSig_nil : clauseTSig tsigFixed [] .unk [] = tsigFixed := by
  simp [clauseTSig, defQuants]

/-- **Calls conform in a scope without definition and type bindings.** -/
theorem callH_nil {env : Env} (hD : ∀ m, DefsVT sigX tsigFixed env m) {ρ : VarEnv}
    (hd : ρ.defs = []) (ht : ρ.typs = []) (k : Nat) : CallH sigX tsigFixed ctx0 env ρ k := by
  have h := callH_clause (sigFacts sigsAux_fixed) (k := k) (fun m _ => hD m) (qs := [])
    (tps := []) (b := .unk) (.inl rfl) (.inl rfl) (.inl rfl)
    (fun y c hc => by simp [defQuants] at hc) (clauseCtx_nil hd ht)
  rw [clauseSig_nil, clauseTSig_nil] at h
  simpa [defQuants] using h

/-! ## What the kernel checks say about one rule -/

/-- The facts about one rule of a reachable relation. -/
structure RFacts (x : IL.Id) (ps : List Param) (t : Typ) (qs : List Param) (e : Exp)
    (prems : List Prem) : Prop where
  params : ps = []
  wild : "_" ∉ quantNames qs
  alts : ∀ e' ∈ Round6.Reading.conclAlts e,
    altOk sigX tsigFixed (quantsΓ qs) e' = true ∧ varsIn (quantNames qs) (freeExp e') = true
  premsOk : ∀ pr ∈ prems, premTy sigX tsigFixed (quantsΓ qs) pr = true ∧ premAuxR pr = true ∧
    varsIn (quantNames qs) (freePrem pr) = true
  sites : (ruleSites sigX [] (matchedRel x) (.ruleD "" qs "" e prems)).2 = 0
  pat : matchedRel x = true → patTy sigX tsigFixed (quantsΓ qs) (toAT t) e = true

theorem ruleSites_name (S : Sig) (ps : List Param) (m : Bool) (nm nm' : IL.Id) (op op' : MixopS)
    (qs : List Param) (e : Exp) (prems : List Prem) :
    ruleSites S ps m (.ruleD nm qs op e prems) = ruleSites S ps m (.ruleD nm' qs op' e prems) := by
  simp [ruleSites]

theorem rFacts {B : Builtins} {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param} {op' : MixopS} {e : Exp}
    {prems : List Prem} (hx : reach 0 x = true)
    (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op' e prems)) : RFacts x ps t qs e prems := by
  have hrel' := hrel
  rw [findRel?_utf8Env] at hrel'
  have hm := EraseAll.mem_rels_of_findRel' hrel'
  have hr : Rule.ruleD nm qs op' e prems ∈ rules := List.mem_of_getElem? hrule
  have hreach : Script.stepReach.contains (0, x) = true := hx
  have hc := List.all_eq_true.1 closedRels_fixed _ hm
  simp only [hreach, Bool.not_true, Bool.false_or] at hc
  have hcl := List.all_eq_true.1 hc _ hr
  simp only [ruleClosed, Bool.and_eq_true, List.all_eq_true] at hcl
  have ha := List.all_eq_true.1 ruleAuxRels_fixed _ hm
  simp only [hx, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.isEmpty_iff,
    List.all_eq_true] at ha
  obtain ⟨hps, ha⟩ := ha
  have hra := ha _ hr
  simp only [ruleAux, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, beq_iff_eq,
    Bool.or_eq_true] at hra
  obtain ⟨⟨⟨⟨hw, halts⟩, hprems⟩, hsites⟩, hpat⟩ := hra
  refine ⟨hps, ?_, fun e' he' => ⟨halts e' he', hcl.1.1 e' he'⟩,
    fun pr hpr => ⟨(hprems pr hpr).1, (hprems pr hpr).2, hcl.1.2 pr hpr⟩, ?_, ?_⟩
  · simpa using hw
  · rw [ruleSites_name _ _ _ "" nm "" op']; exact hsites
  · intro hmr
    rcases hpat with h | h
    · simp [hmr] at h
    · exact h

end Silmaril.Wasm.SpecTec.Sim.Round7.NxRule
