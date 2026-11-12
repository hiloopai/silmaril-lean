module

public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Det.Thms

/-!
# Round 7, moving derivations across erasure: related scopes (unrefined)

`ErRel Q gd S ρ ρ'` relates a scope to its erasure on the identifiers `S`. Evaluation of a
checked expression whose free variables are in `S` goes across it in both directions
(`evalExp_fwd`, `evalExp_bwd`, and the same for arguments and domains), by locality
(`Silmaril.SpecTec.Sem.EvalExp.agreeOn`) and the whole-evaluator erasure
(`Round7.EraseAll.evalExp_erase_iff`) at the swap-set part `aiPart Q ρ`. The relation is kept by
binding a row of swap-set values on one side and its erasure on the other (`ErRel.bindVals`),
and holds at a rule instance on the rule's quantifiers (`erRel_inst`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope ScopeIn find?_eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (DefsG SG Hyps ER eraseAt ArgIn eraseP)

variable {Q : Value → Prop} {gr gd : String → Bool} {env : Env}

theorem aiPart_eq (ρ : VarEnv) : aiPart Q ρ = EraseAll.aiPart Q ρ := rfl

theorem sg_aiPart {ρ : VarEnv} (hD : DefsG gd ρ) : SG Q gd (aiPart Q ρ) :=
  ⟨EraseAll.scopeIn_aiPart ρ, hD⟩

/-! ## The relation -/

theorem ErRel.mono {S T : Sets} {ρ ρ' : VarEnv} (h : ErRel Q gd S ρ ρ') (hT : T ⊆ S) :
    ErRel Q gd T ρ ρ' :=
  ⟨h.ai.mono hT, h.er.mono hT, h.defs⟩

open Classical in
theorem filter_binds_ai : ∀ (r : List (IL.Id × Value)) (m : Map Value), (∀ p ∈ r, AllIn Q p.2) →
    (Map.binds m r).filter (fun p => decide (AllIn Q p.2)) =
      Map.binds (m.filter fun p => decide (AllIn Q p.2)) r
  | [], _, _ => rfl
  | (y, v) :: r, m, h => by
    have hv : AllIn Q v := h (y, v) List.mem_cons_self
    have ih := filter_binds_ai r (m.bind y v) fun p hp => h p (List.mem_cons_of_mem _ hp)
    have hb : (m.bind y v).filter (fun p => decide (AllIn Q p.2)) =
        Map.bind (m.filter fun p => decide (AllIn Q p.2)) y v := by
      unfold Map.bind
      split <;> simp [hv]
    show (Map.binds (m.bind y v) r).filter _ = Map.binds (Map.bind _ y v) r
    rw [ih, hb]

theorem aiPart_bindVals {ρ : VarEnv} {r : List (IL.Id × Value)} (h : ∀ p ∈ r, AllIn Q p.2) :
    aiPart Q (ρ.bindVals r) = (aiPart Q ρ).bindVals r := by
  simp only [aiPart, VarEnv.bindVals, filter_binds_ai r ρ.vals h]

theorem rowSet_map_eraseP (r : List (IL.Id × Value)) :
    EvalFree.rowSet (r.map eraseP) = EvalFree.rowSet r := by
  simp [EvalFree.rowSet, List.map_map, eraseP, Function.comp_def]

/-- **Binding a swap-set row on one side and its erasure on the other.** -/
theorem ErRel.bindVals {S B T : Sets} {ρ ρ' : VarEnv} {r : List (IL.Id × Value)}
    (h : ErRel Q gd S ρ ρ') (hr : ∀ p ∈ r, AllIn Q p.2) (hB : B ⊆ EvalFree.rowSet r)
    (hT : T.diff B ⊆ S) : ErRel Q gd T (ρ.bindVals r) (ρ'.bindVals (r.map eraseP)) := by
  refine ⟨?_, ?_, EraseAll.defsG_bindVals h.defs r⟩
  · rw [aiPart_bindVals hr]
    exact EvalFree.agreeOn_body h.ai hB hT
  · rw [aiPart_bindVals hr, EraseAll.eraseScope_bindVals]
    exact EvalFree.agreeOn_body h.er (rowSet_map_eraseP r ▸ hB) hT

/-! ## Evaluation across the relation -/

theorem evalExp_fwd (H : Hyps Q gr gd env) {ρ ρ' : VarEnv} {e : Exp} {v : Value}
    (h : ErRel Q gd (freeExp e) ρ ρ') (hx : EraseAll.xExp gr gd e = true)
    (he : EvalExp env ρ e v) : EvalExp env ρ' e (eraseV v) ∧ AllIn Q v := by
  have ha : EvalExp env (aiPart Q ρ) e v := he.agreeOn h.ai
  have hs := sg_aiPart (Q := Q) h.defs
  refine ⟨?_, EraseAll.allIn_of_evalExp H hs hx ha⟩
  exact ((EraseAll.evalExp_erase_iff H hs hx).2 ⟨v, ha, rfl⟩).agreeOn h.er.symm

theorem evalExp_bwd (H : Hyps Q gr gd env) {ρ ρ' : VarEnv} {e : Exp} {w : Value}
    (h : ErRel Q gd (freeExp e) ρ ρ') (hx : EraseAll.xExp gr gd e = true)
    (he : EvalExp env ρ' e w) : ∃ v, EvalExp env ρ e v ∧ eraseV v = w ∧ AllIn Q v := by
  have hs := sg_aiPart (Q := Q) h.defs
  obtain ⟨v, hv, rfl⟩ := (EraseAll.evalExp_erase_iff H hs hx).1 (he.agreeOn h.er)
  exact ⟨v, hv.agreeOn h.ai.symm, rfl, EraseAll.allIn_of_evalExp H hs hx hv⟩

theorem evalArgs_fwd (H : Hyps Q gr gd env) {ρ ρ' : VarEnv} {l : List Arg} {ws : List ArgV}
    (h : ErRel Q gd (freeArgs l) ρ ρ') (hx : EraseAll.xArgs gr gd l = true)
    (he : EvalArgs env ρ l ws) :
    EvalArgs env ρ' l (ws.map eraseA) ∧ ∀ w ∈ ws, ArgIn Q gd w := by
  obtain ⟨n, hn⟩ := he
  have hs := sg_aiPart (Q := Q) h.defs
  have ha : evalArgs n env (aiPart Q ρ) l = .ok ws := (evalArgs_agreeOn h.ai).symm.trans hn
  have hE := (eraseAt H n).args _ l hs hx
  refine ⟨⟨n, (evalArgs_agreeOn h.er).trans ((EraseAll.ER.ok_iff hE).2 ⟨ws, ha, rfl⟩)⟩, ?_⟩
  exact hE.2 ws ha

theorem evalArgs_bwd (H : Hyps Q gr gd env) {ρ ρ' : VarEnv} {l : List Arg} {ws' : List ArgV}
    (h : ErRel Q gd (freeArgs l) ρ ρ') (hx : EraseAll.xArgs gr gd l = true)
    (he : EvalArgs env ρ' l ws') :
    ∃ ws, EvalArgs env ρ l ws ∧ ws.map eraseA = ws' ∧ ∀ w ∈ ws, ArgIn Q gd w := by
  obtain ⟨n, hn⟩ := he
  have hs := sg_aiPart (Q := Q) h.defs
  have hE := (eraseAt H n).args _ l hs hx
  obtain ⟨ws, hws, rfl⟩ := (EraseAll.ER.ok_iff hE).1 ((evalArgs_agreeOn h.er).symm.trans hn)
  exact ⟨ws, ⟨n, (evalArgs_agreeOn h.ai).trans hws⟩, rfl, hE.2 ws hws⟩

theorem evalDoms_fwd (H : Hyps Q gr gd env) {ρ ρ' : VarEnv} {ds : List Dom}
    {xvs : List (IL.Id × Value)} (h : ErRel Q gd (freeDoms ds) ρ ρ')
    (hx : EraseAll.xDoms gr gd ds = true) (he : EvalDoms env ρ ds xvs) :
    EvalDoms env ρ' ds (xvs.map eraseP) ∧ ∀ p ∈ xvs, AllIn Q p.2 := by
  obtain ⟨n, hn⟩ := he
  have hs := sg_aiPart (Q := Q) h.defs
  have ha : evalDoms n env (aiPart Q ρ) ds = .ok xvs := (evalDoms_agreeOn h.ai).symm.trans hn
  have hE := (eraseAt H n).doms _ ds hs hx
  refine ⟨⟨n, (evalDoms_agreeOn h.er).trans ((EraseAll.ER.ok_iff hE).2 ⟨xvs, ha, rfl⟩)⟩, ?_⟩
  exact hE.2 xvs ha

theorem evalDoms_bwd (H : Hyps Q gr gd env) {ρ ρ' : VarEnv} {ds : List Dom}
    {xvs' : List (IL.Id × Value)} (h : ErRel Q gd (freeDoms ds) ρ ρ')
    (hx : EraseAll.xDoms gr gd ds = true) (he : EvalDoms env ρ' ds xvs') :
    ∃ xvs, EvalDoms env ρ ds xvs ∧ xvs.map eraseP = xvs' ∧ ∀ p ∈ xvs, AllIn Q p.2 := by
  obtain ⟨n, hn⟩ := he
  have hs := sg_aiPart (Q := Q) h.defs
  have hE := (eraseAt H n).doms _ ds hs hx
  obtain ⟨xvs, hx', rfl⟩ := (EraseAll.ER.ok_iff hE).1 ((evalDoms_agreeOn h.er).symm.trans hn)
  exact ⟨xvs, ⟨n, (evalDoms_agreeOn h.ai).trans hx'⟩, rfl, hE.2 xvs hx'⟩

/-! ## A rule instance -/

theorem find?_map_eraseP : ∀ (m : Map Value) (x : IL.Id),
    Map.find? (m.map eraseP) x = (Map.find? m x).map eraseV
  | [], _ => rfl
  | (y, v) :: m, x => by
    simp only [List.map_cons, eraseP, Map.find?]
    split
    · rfl
    · exact find?_map_eraseP m x

/-- **At a rule instance**, the scope binding `σ` and the scope binding its erasure are related on
every set of identifiers whose term variables are bound to swap-set values. -/
theorem erRel_inst {S : Sets} {σ : List (IL.Id × Value)}
    (hS : ∀ x ∈ S.varid, ∀ w, (VarEnv.empty.bindVals σ).findVal? x = some w → AllIn Q w) :
    ErRel Q gd S (VarEnv.empty.bindVals σ) (VarEnv.empty.bindVals (σ.map eraseP)) := by
  refine ⟨⟨fun x hx => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩,
    ⟨fun x hx => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, fun _ hp => by cases hp⟩
  · exact (EraseAll.find?_filter_ai _ (hS x hx)).symm
  · have h₁ : (VarEnv.empty.bindVals (σ.map eraseP)).vals =
        (VarEnv.empty.bindVals σ).vals.map eraseP := by
      simp only [VarEnv.bindVals, VarEnv.empty, Map.empty]
      exact (EraseAll.map_binds σ []).symm
    show Map.find? _ x = (eraseScope (aiPart Q _)).findVal? x
    rw [find?_eraseScope, h₁, find?_map_eraseP]
    show _ = Option.map eraseV (Map.find? (List.filter _ _) x)
    rw [EraseAll.find?_filter_ai _ (hS x hx)]

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
