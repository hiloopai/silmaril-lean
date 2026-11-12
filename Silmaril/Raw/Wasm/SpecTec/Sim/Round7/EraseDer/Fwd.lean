module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseDer.Rows
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseDer.CheckClosed
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseDer.CheckQuant

/-!
# Round 7, moving derivations across erasure: the forward direction (unrefined)

`dderivesB_fwd`: a derivation of a checked relation (`grE`) whose rule instances bind every
quantifier to a swap-set value (`DDerivesBQ (AllIn Q)`, as `Round7.EraseAll.dderivesB_AI`
produces) gives a derivation of the erased value from the erased arguments, provided typing goes
to the erased side (`TypFwd`) and every `otherwise` premise read on the original side is read on
the erased side (`hO`).

The proof is by structural recursion on the derivation. At a rule instance the original scope
binds `σ`; the erased scope binds `σ` erased. The two are related (`ErRel`) on every set of
identifiers whose term variables are quantifiers (`erRel_inst`), and the closure check
(`closedRels_fixed`) puts the free variables of the conclusion, the premises and the quantifier
types there. Iterated premises bind a swap-set row on one side and its erasure on the other
(`ErRel.bindVals`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (DDerivesBQ DPremBQ QuantsP grE gdE Hyps xPrem xExp
  eraseP)
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (tyA tyB tyOk)
open Silmaril.Wasm.SpecTec.Sim.Round7.Determ (quantNames)
open Round6.Reading (DDerivesB DPremB conclAlts)

variable {Q : Value → Prop} {B : Builtins}

/-! ## The facts about one rule -/

/-- What the kernel checks say about one rule of a checked relation. -/
structure RFacts (gr gd : String → Bool) (ps qs : List Param) (e : Exp) (prems : List Prem) :
    Prop where
  params : ps = []
  prems : ∀ pr ∈ prems, xPrem gr gd pr = true ∧ varsIn (quantNames qs) (freePrem pr) = true
  alts : ∀ e' ∈ conclAlts e, xExp gr gd e' = true ∧ varsIn (quantNames qs) (freeExp e') = true
  quants : ∀ y t, Param.expP y t ∈ qs →
    xTy tyB t = true ∧ varsIn (quantNames qs) (freeTyp t) = true

theorem rFacts {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat}
    {nm : IL.Id} {qs : List Param} {e : Exp} {prems : List Prem} (hx : grE x = true)
    (hrel : (utf8Env B).findRel? x = some (ps, op, t, rules))
    (hrule : rules[i]? = some (.ruleD nm qs op e prems)) : RFacts grE gdE ps qs e prems := by
  have hX := EraseAll.xFacts hx hrel hrule
  have hrel' := hrel
  rw [findRel?_utf8Env] at hrel'
  have hF := Determ.detFacts (EraseAll.reach_of_grE hx) hrel' hrule
  have hr : Rule.ruleD nm qs op e prems ∈ rules := List.mem_of_getElem? hrule
  have hc := List.all_eq_true.1 closedRels_fixed _ (EraseAll.mem_rels_of_findRel' hrel')
  have hreach : Script.stepReach.contains (0, x) = true :=
    List.contains_iff_mem.2 (EraseAll.reach_of_grE hx)
  simp only [hreach, Bool.not_true, Bool.false_or] at hc
  have hcl := List.all_eq_true.1 hc _ hr
  simp only [ruleClosed, Bool.and_eq_true, List.all_eq_true] at hcl
  have hq := List.all_eq_true.1 xRelQuants_fixed _ (EraseAll.mem_rels_of_findRel' hrel')
  simp only [hreach, Bool.not_true, Bool.false_or, List.all_eq_true] at hq
  have hq' := hq _ hr
  simp only [List.all_eq_true] at hq'
  refine ⟨hF.params, fun pr hpr => ⟨hX.prems pr hpr, hcl.1.2 pr hpr⟩,
    fun e' he' => ⟨hX.alts e' he', hcl.1.1 e' he'⟩, fun y ty hy => ⟨?_, ?_⟩⟩
  · have := hq' _ hy
    simpa using this
  · simpa using hcl.2 _ hy

theorem varsIn_mem {K : List IL.Id} {S : Sets} (h : varsIn K S = true) : ∀ x ∈ S.varid, x ∈ K := by
  simpa [varsIn] using h

/-- The quantifiers are bound to swap-set values, hence so is every variable of a closed set. -/
theorem ai_of_varsIn {ρ : VarEnv} {qs : List Param} (hx : QuantsP (AllIn Q) ρ qs) {S : Sets}
    (hS : varsIn (quantNames qs) S = true) :
    ∀ x ∈ S.varid, ∀ w, ρ.findVal? x = some w → AllIn Q w := by
  intro y hy w hw
  have hq := varsIn_mem hS y hy
  simp only [quantNames, List.mem_filterMap] at hq
  obtain ⟨q, hq, hqy⟩ := hq
  cases q with
  | expP z t =>
    simp only [Option.some.injEq] at hqy
    subst hqy
    exact hx z t w hq hw
  | _ => simp at hqy

theorem bindParams_nil_args {ρ ρ' : VarEnv} {args : List ArgV}
    (h : bindParams ρ [] args = some ρ') : args = [] ∧ ρ' = ρ := by
  cases args with
  | nil => exact ⟨rfl, (Option.some.inj h).symm⟩
  | cons _ _ => simp [bindParams] at h

theorem findVal?_inst (σ : List (IL.Id × Value)) (x : IL.Id) :
    (VarEnv.empty.bindVals (σ.map eraseP)).findVal? x =
      ((VarEnv.empty.bindVals σ).findVal? x).map eraseV := by
  have h₁ : (VarEnv.empty.bindVals (σ.map eraseP)).vals =
      (VarEnv.empty.bindVals σ).vals.map eraseP := by
    simp only [VarEnv.bindVals, VarEnv.empty, Map.empty]
    exact (EraseAll.map_binds σ []).symm
  simp only [VarEnv.findVal?, h₁, find?_map_eraseP]

/-! ## The forward transfer -/

section Fwd

set_option linter.unusedSectionVars false

/-- Every rule of a `gr` relation passes the checks at `gr`, `gd`. -/
def AllRFacts (gr gd : String → Bool) (env : Env) : Prop :=
  ∀ {x : IL.Id} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat}
    {nm : IL.Id} {qs : List Param} {e : Exp} {prems : List Prem}, gr x = true →
    env.findRel? x = some (ps, op, t, rules) → rules[i]? = some (.ruleD nm qs op e prems) →
    RFacts gr gd ps qs e prems

theorem allRFacts_E : AllRFacts grE gdE (utf8Env B) := fun hx hrel hrule => rFacts hx hrel hrule

variable {gr gd : String → Bool} {env : Env}
variable (H : Hyps Q gr gd env) (hF : AllRFacts gr gd env) (hT : TypFwd Q gd env) {O₁ O' : ElseI}
  (hO : ∀ x args i v, O₁ x args i v → O' x (args.map eraseA) i (eraseV v))
include H hF hT hO

mutual
/-- **A swap-set derivation goes to the erased side.** -/
theorem dderivesB_fwd :
    ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}, gr x = true →
      DDerivesBQ (AllIn Q) env O₁ x op args v →
      DDerivesB env O' x op (args.map eraseA) (eraseV v)
  | _, _, args, _, hx, .rule (σ := σ) (ρ₀ := ρ₀) (qs := qs) (ps := ps) hrel hrule halt hps hq hxq he hp => by
    have hF := hF hx hrel hrule
    have hargs : args = [] := (bindParams_nil_args (hF.params ▸ hps)).1
    have hρ : ρ₀ = VarEnv.empty := (bindParams_nil_args (hF.params ▸ hps)).2
    have hR : ∀ S : Sets, varsIn (quantNames qs) S = true →
        ErRel Q gd S (ρ₀.bindVals σ) (ρ₀.bindVals (σ.map eraseP)) := by
      intro S hS
      subst hρ
      exact erRel_inst (ai_of_varsIn hxq hS)
    have hpar : bindParams VarEnv.empty ps (args.map eraseA) = some ρ₀ := by
      rw [hargs]; rw [hargs] at hps; exact hps
    obtain ⟨hxe, hfe⟩ := hF.alts _ halt
    refine .rule (σ := σ.map eraseP) hrel hrule halt hpar ?_
      (evalExp_fwd H (hR _ hfe) hxe he).1 fun pr hpr => ?_
    · intro y ty hy
      obtain ⟨w, hw, hty⟩ := hq y ty hy
      obtain ⟨ht, hft⟩ := hF.quants y ty hy
      refine ⟨eraseV w, ?_,
        hT _ _ _ _ (hR _ hft) rfl (by subst hρ; rfl) (by subst hρ; rfl) rfl rfl ht (hxq y ty w hy hw) hty⟩
      have h₁ := hρ ▸ findVal?_inst σ y
      rw [h₁, hw]; rfl
    · exact dpremB_fwd (hF.prems pr hpr).1 (hR _ (hF.prems pr hpr).2) (hO _ _ _ _) (hp pr hpr)
termination_by structural _ _ _ _ _ hd => hd

/-- **A premise goes to the erased side.** -/
theorem dpremB_fwd :
    ∀ {els els' : Prop} {ρ ρ' : VarEnv} {pr : Prem}, xPrem gr gd pr = true →
      ErRel Q gd (freePrem pr) ρ ρ' → (els → els') →
      DPremBQ (AllIn Q) env O₁ els ρ pr → DPremB env O' els' ρ' pr
  | _, _, _, _, _, hX, hR, _, .ifPr h => by
    simp only [xPrem] at hX
    exact .ifPr (evalExp_fwd H hR hX h).1
  | _, _, _, _, _, _, _, hels, .elsePr h => .elsePr (hels h)
  | _, _, _, _, _, hX, hR, _, .letPr h₂ h₁ => by
    simp only [xPrem, Bool.and_eq_true] at hX
    exact .letPr (evalExp_fwd H (hR.mono (sub_let_right _ _)) hX.2 h₂).1
      (evalExp_fwd H (hR.mono (sub_let_left _ _)) hX.1 h₁).1
  | _, _, _, _, .rulePr x args op e, hX, hR, _, .rulePr ha he hd => by
    simp only [xPrem, Bool.and_eq_true] at hX
    exact .rulePr (evalArgs_fwd H (hR.mono (sub_rule_args x args op e)) hX.1.2 ha).1
      (evalExp_fwd H (hR.mono (sub_rule_exp x args op e)) hX.2 he).1
      (dderivesB_fwd hX.1.1 hd)
  | _, _, _, _, .iterPr pr (.mk _ ds), hX, hR, _, .iterOptNone hd hne hall => by
    simp only [xPrem, Bool.and_eq_true] at hX
    obtain ⟨hd', -⟩ := evalDoms_fwd H (hR.mono (sub_iter_doms pr _ ds)) hX.2 hd
    refine .iterOptNone hd' hne fun p hp => ?_
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    simp [eraseP, hall q hq]
  | _, _, _, _, .iterPr pr (.mk _ ds), hX, hR, hels, .iterOptSome (xvs := xvs) (row := row) hd hne hs hp => by
    simp only [xPrem, Bool.and_eq_true] at hX
    obtain ⟨hd', hai⟩ := evalDoms_fwd H (hR.mono (sub_iter_doms pr _ ds)) hX.2 hd
    have hs' : domSomes (xvs.map eraseP) = some (row.map eraseP) := by
      rw [domSomes_erase, hs]; rfl
    have hrow := EraseAll.ai_domSomes hai hs
    have hkeys : row.map Prod.fst = ds.map domVar ++ ([] : List IL.Id) := by
      rw [map_fst_domSomes hs, map_fst_EvalDoms hd, List.append_nil]
    have hR' := hR.bindVals hrow (bound_sub_rowSet hkeys (boundIter_plain (.inl rfl)))
      (sub_iter_body pr _)
    exact .iterOptSome hd' hne hs' (dpremB_fwd hX.1.1 hR' hels hp)
  | _, _, _, _, .iterPr pr (.mk it ds), hX, hR, hels,
      .iterList (xvs := xvs) (dls := dls) (k := k) hit hd hne hl hlen hp => by
    simp only [xPrem, Bool.and_eq_true] at hX
    obtain ⟨hd', hai⟩ := evalDoms_fwd H (hR.mono (sub_iter_doms pr _ ds)) hX.2 hd
    have hl' : domLists (xvs.map eraseP) =
        some (dls.map fun p => (p.1, p.2.map eraseV)) := by
      rw [domLists_erase, hl]; rfl
    refine .iterList hit hd' hne hl' (lens_erase hlen) fun r' hr' => ?_
    rw [EraseAll.iterRows_erase] at hr'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hr'
    have hrow := EraseAll.ai_rows hai hl none k r hr
    have hkeys : r.map Prod.fst = ds.map domVar ++ ([] : List IL.Id) := by
      rw [map_fst_row hlen hr, map_fst_domLists hl, map_fst_EvalDoms hd]; rfl
    have hplain : it = .opt ∨ it = .list ∨ it = .list1 := by
      rcases hit with h | ⟨h, _⟩ <;> simp [h]
    have hR' := hR.bindVals hrow (bound_sub_rowSet hkeys (boundIter_plain hplain))
      (sub_iter_body pr _)
    exact dpremB_fwd hX.1.1 hR' hels (hp r hr)
  | _, _, _, _, .iterPr pr (.mk (.listN eₙ ido) ds), hX, hR, hels,
      .iterListN (xvs := xvs) (dls := dls) (k := k) hd he hk hl hlen hp => by
    simp only [xPrem, Bool.and_eq_true] at hX
    obtain ⟨hd', hai⟩ := evalDoms_fwd H (hR.mono (sub_iter_doms pr _ ds)) hX.2 hd
    have hXn : xExp gr gd eₙ = true := by simpa [EraseAll.xIter] using hX.1.2
    have he' := (evalExp_fwd H (hR.mono (sub_iter_n pr eₙ ido ds)) hXn he).1
    have hl' : domLists (xvs.map eraseP) =
        some (dls.map fun p => (p.1, p.2.map eraseV)) := by
      rw [domLists_erase, hl]; rfl
    refine .iterListN hd' he' (by rw [asNat?_eraseV]; exact hk) hl' (lens_erase hlen)
      fun r' hr' => ?_
    rw [EraseAll.iterRows_erase] at hr'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hr'
    have hrow := EraseAll.ai_rows hai hl ido k r hr
    have hkeys : r.map Prod.fst = ds.map domVar ++ ido.toList := by
      rw [map_fst_row hlen hr, map_fst_domLists hl, map_fst_EvalDoms hd]
    have hR' := hR.bindVals hrow
      (bound_sub_rowSet hkeys (EvalFree.boundIter_listN_subset_keySet eₙ ido))
      (sub_iter_body pr _)
    exact dpremB_fwd hX.1.1 hR' hels (hp r hr)
termination_by structural _ _ _ _ _ _ _ _ hd => hd
end

end Fwd

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
