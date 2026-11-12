module

public import Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HAgree.Eq
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HAgree.CheckR0
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HAgree.CheckR1
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HAgree.CheckR2
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HAgree.CheckR3
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HAgree.CheckR4

/-!
# Round 7, `BD`: the invariants of the declarative transfer off `$vbytes_` and `$hostcall`

`Round7.VDecl`'s `Basic` with `HAgree.RefOk` (which also excludes `$hostcall`):

* `RG` is closed under the parts of a list of events (`rg_append`, `rg_cons`), and implies
  `HAgree.GoodEvs` (`goodEvs_of_rg`).
* The items `Step` reaches, other than `Step` and `Step_read`, are `RG` (`rg_item`). So are the
  instances of a type `simEnv B` finds under a reachable name (`rg_inst`) and the rules of a
  `GoodRel` relation (`rg_rule`).
* `relFacts_fixed` (five kernel chunks): every relation `Step` reaches has no parameters, and its
  rules have `RG` quantifier types and conclusion alternatives (`relFacts_of_find`).
* `TypsG` survives what typing does to a scope (`typsG_bindTyp`, `matchArgs_typsG`), and evaluated
  type arguments are `RG` (`evalArgs_argTyG`). The defining conjuncts of an `RG` variant case are
  `RG` (`quantDefs_rg`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round7.Script (Ev Item items evRefs evTyp evExp evArg evArgs evPrem evPrems evParam evParams
  evRule evInst evBinds evDefTyp evTFields evTCases evIter stepReach mem_evRefs stepReach_closed
  relDefEv typDefEv findRel?_simEnv_item findTyp?_simEnv_item mem_of_find? mapM_ok_mem)
open Round7.VAgree (GoodRel)

/-! ## `RG` -/

theorem evRefs_append : ∀ (a b : List Ev), evRefs (a ++ b) = evRefs a ++ evRefs b
  | [], _ => rfl
  | .ref k x :: a, b => by simp only [List.cons_append, evRefs, evRefs_append a b]
  | .atom _ :: a, b => by simp only [List.cons_append, evRefs, evRefs_append a b]
  | .comp :: a, b => by simp only [List.cons_append, evRefs, evRefs_append a b]
  | .upd _ _ :: a, b => by simp only [List.cons_append, evRefs, evRefs_append a b]

@[simp] theorem rg_nil : RG [] := fun _ h => by simp [evRefs] at h

@[simp] theorem rg_append {a b : List Ev} : RG (a ++ b) ↔ RG a ∧ RG b := by
  simp only [RG, evRefs_append, List.mem_append]
  exact ⟨fun h => ⟨fun r hr => h r (.inl hr), fun r hr => h r (.inr hr)⟩,
    fun h r hr => hr.elim (h.1 r) (h.2 r)⟩

@[simp] theorem rg_cons_ref {k : Nat} {x : String} {l : List Ev} :
    RG (.ref k x :: l) ↔ RefOk (k, x) ∧ RG l := by
  simp only [RG, evRefs, List.mem_cons, forall_eq_or_imp]

@[simp] theorem rg_cons_atom {a : String} {l : List Ev} : RG (.atom a :: l) ↔ RG l := Iff.rfl

@[simp] theorem rg_cons_comp {l : List Ev} : RG (.comp :: l) ↔ RG l := Iff.rfl

@[simp] theorem rg_cons_upd {e : Exp} {ats : List String} {l : List Ev} :
    RG (.upd e ats :: l) ↔ RG l := Iff.rfl

@[simp] theorem rg_flatMap {α : Type} {f : α → List Ev} {l : List α} :
    RG (l.flatMap f) ↔ ∀ x ∈ l, RG (f x) := by
  induction l with
  | nil => simp
  | cons y l ih => simp only [List.flatMap_cons, rg_append, ih, List.forall_mem_cons]

/-- **`RG` events are `GoodEvs`.** -/
theorem goodEvs_of_rg {l : List Ev} (h : RG l) : GoodEvs l := by
  intro e he
  cases e with
  | ref k x =>
    have hk : RefOk (k, x) := h _ (mem_evRefs he)
    rcases k with _ | _ | k
    · exact ⟨hk.1, fun hx => hk.2.2.2.1 (by rw [hx]), fun hx => hk.2.2.2.2 (by rw [hx])⟩
    · exact ⟨hk.1, fun hx => hk.2.1 (by rw [hx]), fun hx => hk.2.2.1 (by rw [hx])⟩
    · trivial
  | atom a => trivial
  | comp => trivial
  | upd r ats => trivial

theorem rg_of_rgB {l : List Ev} (h : rgB l = true) : RG l := by
  intro r hr
  have hb : refOkB r = true := List.all_eq_true.1 h r hr
  simp only [refOkB, Bool.and_eq_true, bne_iff_ne, ne_eq, List.contains_eq_mem,
    decide_eq_true_eq] at hb
  exact ⟨hb.1.1.1.1, hb.1.1.1.2, hb.1.1.2, hb.1.2, hb.2⟩

/-! ## Items -/

/-- **An item `Step` reaches, other than `Step` and `Step_read`, is `RG`.** -/
theorem rg_item {it : Item} (h : it ∈ items Scripts.Wasm30.fixed) (hR : (it.1, it.2.1) ∈ stepReach)
    (hx : ¬ (it.1 = 0 ∧ (it.2.1 = "Step_read" ∨ it.2.1 = "Step"))) : RG it.2.2 := by
  intro r hr
  have hreach : r ∈ stepReach := stepReach_closed h hR r hr
  refine ⟨hreach, fun hv => VBytes.item_noVBytes h hx (hv ▸ hr),
    fun hh => item_noHostcall h (fun h' => hx ⟨h'.1, Or.inr h'.2⟩) (hh ▸ hr), fun hs => ?_,
    fun hs => ?_⟩
  · exact VAgree.item_noStepRel h hR hx (Or.inl rfl) (hs ▸ hr)
  · exact VAgree.item_noStepRel h hR hx (Or.inr rfl) (hs ▸ hr)

/-- The instances of a type found under a reachable name are `RG`. -/
theorem rg_inst {B : Builtins} {x : IL.Id} {td : TypDef} (h : (simEnv B).findTyp? x = some td)
    (hx : (2, x) ∈ stepReach) : ∀ i ∈ td.2, RG (evInst i) := by
  have hI : RG (typDefEv td) := rg_item (findTyp?_simEnv_item h) hx (by simp)
  have hI' : RG (evParams td.1) ∧ ∀ i ∈ td.2, RG (evInst i) := by
    simpa only [typDefEv, rg_append, rg_flatMap] using hI
  exact hI'.2

/-- The rules of a `GoodRel` relation are `RG`. -/
theorem rg_rule {B : Builtins} {x : IL.Id} (hx : GoodRel x) {d : RelDef}
    (h : (simEnv B).findRel? x = some d) : ∀ r ∈ d.2.2.2, RG (evRule r) := by
  have hI : RG (relDefEv d) := rg_item (findRel?_simEnv_item h) hx.1
    (by simp only [not_and, not_or]; exact fun _ => ⟨hx.2.2, hx.2.1⟩)
  have hI' : (RG (evParams d.1) ∧ RG (evTyp d.2.2.1)) ∧ ∀ r ∈ d.2.2.2, RG (evRule r) := by
    simpa only [relDefEv, rg_append, rg_flatMap] using hI
  exact hI'.2

/-! ## The relation facts -/

theorem relFactsB_append (a b : Map RelDef) :
    relFactsB (a ++ b) = (relFactsB a && relFactsB b) := by
  simp only [relFactsB, List.all_append]

/-- **The relation facts on the whole fixed script**, from the five kernel chunks. -/
theorem relFacts_fixed : relFactsB (relsOfDefs Scripts.Wasm30.fixed) = true := by
  have e₁ := List.take_append_drop 40 (relsOfDefs Scripts.Wasm30.fixed)
  have e₂ := List.take_append_drop 10 ((relsOfDefs Scripts.Wasm30.fixed).drop 40)
  have e₃ := List.take_append_drop 10 ((relsOfDefs Scripts.Wasm30.fixed).drop 50)
  have e₄ := List.take_append_drop 20 ((relsOfDefs Scripts.Wasm30.fixed).drop 60)
  simp only [List.drop_drop, Nat.reduceAdd] at e₂ e₃ e₄
  rw [← e₁, ← e₂, ← e₃, ← e₄]
  simp only [relFactsB_append, relFacts_chunk0, relFacts_chunk1, relFacts_chunk4, relFacts_chunk3,
    relFacts_chunk2, Bool.and_self]

theorem mem_rels_of_findRel {B : Builtins} {x : IL.Id} {v : RelDef}
    (h : (simEnv B).findRel? x = some v) : (x, v) ∈ relsOfDefs Scripts.Wasm30.fixed := by
  unfold simEnv baseEnv at h
  rw [Env.findRel?_withBuiltins, envOfScript, envOfDefs_eq] at h
  rcases List.mem_append.1 (mem_of_find? h) with hm | hm
  · exact hm
  · simp [Env.empty, Map.empty] at hm

/-- **A relation `Step` reaches has no parameters, and its rules pass `ruleFactsB`.** -/
theorem relFacts_of_find {B : Builtins} {x : IL.Id} {d : RelDef}
    (h : (simEnv B).findRel? x = some d) (hx : (0, x) ∈ stepReach) :
    d.1 = [] ∧ ∀ r ∈ d.2.2.2, ruleFactsB r = true := by
  have hm := List.all_eq_true.1 relFacts_fixed _ (mem_rels_of_findRel h)
  have hc : stepReach.contains (0, x) = true := List.contains_iff_mem.2 hx
  simp only [hc, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.isEmpty_iff,
    List.all_eq_true] at hm
  exact hm

/-- The quantifier types of a rule passing `ruleFactsB` are `RG`. -/
theorem quant_rg {nm : IL.Id} {qs : List Param} {op : MixopS} {e : Exp} {prems : List Prem}
    (h : ruleFactsB (.ruleD nm qs op e prems) = true) : ∀ x t, Param.expP x t ∈ qs → RG (evTyp t) := by
  intro x t hq
  have hq' : quantsRgB qs = true := by
    simp only [ruleFactsB, Bool.and_eq_true] at h; exact h.1
  have := List.all_eq_true.1 hq' _ hq
  exact rg_of_rgB (by simpa using this)

/-- The conclusion alternatives of a rule passing `ruleFactsB` are `RG`. -/
theorem alt_rg {nm : IL.Id} {qs : List Param} {op : MixopS} {e : Exp} {prems : List Prem}
    (h : ruleFactsB (.ruleD nm qs op e prems) = true) :
    ∀ e' ∈ Round6.Reading.conclAlts e, RG (evExp e') := by
  intro e' he'
  have ha : (Round6.Reading.conclAlts e).all (fun e' => rgB (evExp e')) = true := by
    simp only [ruleFactsB, Bool.and_eq_true] at h; exact h.2
  exact rg_of_rgB (List.all_eq_true.1 ha e' he')

/-! ## Scopes -/

theorem typsG_empty : TypsG VarEnv.empty := by simp [TypsG, VarEnv.empty, Map.empty]

theorem typsG_of_typs {ρ ρ' : VarEnv} (h : TypsG ρ) (he : ρ'.typs = ρ.typs) : TypsG ρ' := by
  intro p hp; rw [he] at hp; exact h p hp

theorem typsG_bindVals {ρ : VarEnv} (h : TypsG ρ) (xs : List (IL.Id × Value)) :
    TypsG (ρ.bindVals xs) := h

theorem typsG_bindTyp {ρ : VarEnv} (h : TypsG ρ) (x : IL.Id) {t : Typ} (ht : RG (evTyp t)) :
    TypsG (ρ.bindTyp x t) := by
  intro p hp
  simp only [VarEnv.bindTyp, Map.bind] at hp
  split at hp
  · exact h p hp
  · rcases List.mem_cons.1 hp with rfl | hp
    · exact ht
    · exact h p hp

theorem matchTypV_typsG {env : Env} {ρ ρ' : VarEnv} {pat t : Typ} (h : TypsG ρ)
    (ht : RG (evTyp t)) (hm : matchTypV env ρ pat t = .ok ρ') : TypsG ρ' := by
  unfold matchTypV at hm
  repeat (first | (split at hm) | (cases hm; exact h) | (cases hm; exact typsG_bindTyp h _ ht) |
    (cases hm))

theorem matchArg_typsG {env : Env} {n : Nat} {ρ ρ' : VarEnv} {a : Arg} {w : ArgV} (h : TypsG ρ)
    (hw : ArgTyG w) (hm : matchArg n env ρ a w = .ok ρ') : TypsG ρ' := by
  rcases n with _ | n
  · simp [matchArg] at hm
  cases a <;> cases w <;> simp only [matchArg] at hm
  case expA.val e v =>
    split at hm
    · exact typsG_of_typs h ((TypAgree.typsPres env n).matchExp _ _ _ _ hm)
    · cases hm
  case typA.typ => exact matchTypV_typsG h hw hm
  case defA.defName y x => cases hm; exact h
  case gramA.gram => exact typsG_of_typs h (TypAgree.matchSymV_typs hm)
  all_goals cases hm

theorem matchArgs_typsG {env : Env} :
    ∀ (n : Nat) {ρ ρ' : VarEnv} {ags : List Arg} {ws : List ArgV}, TypsG ρ →
      (∀ w ∈ ws, ArgTyG w) → matchArgs n env ρ ags ws = .ok ρ' → TypsG ρ'
  | 0, _, _, _, _, _, _, hm => by simp [matchArgs] at hm
  | n + 1, ρ, ρ', ags, ws, h, hw, hm => by
    cases ags with
    | nil => cases ws <;> simp only [matchArgs] at hm <;> cases hm; exact h
    | cons a ags =>
      cases ws with
      | nil => simp only [matchArgs] at hm; cases hm
      | cons w ws =>
        simp only [matchArgs, Res.bind_eq_ok] at hm
        obtain ⟨ρ₁, h₁, h₂⟩ := hm
        exact matchArgs_typsG n (matchArg_typsG h (hw w List.mem_cons_self) h₁)
          (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw')) h₂

theorem resolveTyp_rg {ρ : VarEnv} (h : TypsG ρ) {t : Typ} (ht : RG (evTyp t)) :
    RG (evTyp (resolveTyp ρ t)) := by
  unfold resolveTyp
  split
  · rename_i x
    cases hf : ρ.findTyp? x with
    | none => exact ht
    | some t' => exact h (x, t') (mem_of_find? hf)
  · exact ht

theorem rg_typA {t : Typ} : ∀ {ags : List Arg}, RG (evArgs ags) → Arg.typA t ∈ ags → RG (evTyp t)
  | [], _, ha => by simp at ha
  | b :: ags, hA, ha => by
    have hA' : RG (evArg b) ∧ RG (evArgs ags) := by simpa only [evArgs, rg_append] using hA
    rcases List.mem_cons.1 ha with rfl | ha'
    · simpa only [evArg] using hA'.1
    · exact rg_typA hA'.2 ha'

/-- **Evaluated type arguments are `RG`.** -/
theorem evalArgs_argTyG {env : Env} {n : Nat} {ρ : VarEnv} {ags : List Arg} {ws : List ArgV}
    (h : TypsG ρ) (hA : RG (evArgs ags)) (he : evalArgs n env ρ ags = .ok ws) :
    ∀ w ∈ ws, ArgTyG w := by
  rcases n with _ | n
  · simp [evalArgs] at he
  simp only [evalArgs] at he
  intro w hw
  obtain ⟨a, ha, hfa⟩ := mapM_ok_mem he w hw
  rcases n with _ | n
  · simp [evalArg] at hfa
  cases a <;> simp only [evalArg] at hfa
  case expA e =>
    obtain ⟨_, _, rfl⟩ := Res.map_eq_ok.1 hfa
    trivial
  case typA t => cases hfa; exact resolveTyp_rg h (rg_typA hA ha)
  case defA x => cases hfa; trivial
  case gramA => cases hfa; trivial

/-! ## Defining conjuncts of variant cases -/

theorem quantEqs_rg {qs : List Param} {e : Exp} (hG : RG (evExp e)) :
    ∀ d ∈ quantEqs qs e, RG (evExp d.2.2) ∧ Param.expP d.1 d.2.1 ∈ qs := by
  fun_induction quantEqs qs e with
  | case1 τ a b iha ihb =>
    have hG' : RG (evExp a) ∧ RG (evExp b) := by simpa only [evExp, rg_append] using hG
    intro d hd
    rcases List.mem_append.1 hd with hd₁ | hd₂
    · exact iha hG'.1 d hd₁
    · exact ihb hG'.2 d hd₂
  | case2 τ a b x t hq =>
    have hG' : RG (evExp a) ∧ RG (evExp b) := by simpa only [evExp, rg_append] using hG
    intro d hd
    rw [List.mem_singleton.1 hd]
    exact ⟨hG'.1, TypAgree.quantOf_mem hq⟩
  | case3 τ a b _ x t hq =>
    have hG' : RG (evExp a) ∧ RG (evExp b) := by simpa only [evExp, rg_append] using hG
    intro d hd
    rw [List.mem_singleton.1 hd]
    exact ⟨hG'.2, TypAgree.quantOf_mem hq⟩
  | case4 => intro d hd; simp at hd
  | case5 => intro d hd; simp at hd

theorem rg_prems : ∀ {ps : List Prem}, RG (evPrems ps) → ∀ p ∈ ps, RG (evPrem p)
  | [], _ => by simp
  | p :: ps, h => by
    have h' : RG (evPrem p) ∧ RG (evPrems ps) := by simpa only [evPrems, rg_append] using h
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact h'.1
    · exact rg_prems h'.2 q hq

theorem rg_params : ∀ {qs : List Param}, RG (evParams qs) → ∀ x t, Param.expP x t ∈ qs →
    RG (evTyp t)
  | [], _ => by simp
  | q :: qs, h => by
    have h' : RG (evParam q) ∧ RG (evParams qs) := by simpa only [evParams, rg_append] using h
    intro x t hq
    rcases List.mem_cons.1 hq with rfl | hq
    · simpa only [evParam] using h'.1
    · exact rg_params h'.2 x t hq

theorem quantDefs_rg {qs : List Param} {prems : List Prem} (hG : RG (evPrems prems))
    (hq : RG (evParams qs)) : ∀ d ∈ quantDefs qs prems, RG (evExp d.2.2) ∧ RG (evTyp d.2.1) := by
  intro d hd
  simp only [quantDefs, List.mem_flatMap] at hd
  obtain ⟨pr, hpr, hd⟩ := hd
  have hGpr := rg_prems hG pr hpr
  cases pr with
  | ifPr e =>
    obtain ⟨h₁, h₂⟩ := quantEqs_rg (by simpa only [evPrem] using hGpr) d hd
    exact ⟨h₁, rg_params hq _ _ h₂⟩
  | rulePr _ _ _ _ => simp at hd
  | letPr _ _ => simp at hd
  | elsePr => simp at hd
  | iterPr _ _ => simp at hd

end Silmaril.Wasm.SpecTec.Sim.Round7.HAgree
