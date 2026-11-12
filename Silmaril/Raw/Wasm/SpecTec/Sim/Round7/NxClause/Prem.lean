module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxClause.Bridge

/-!
# Round 8, REH route 2: the premises of a clause commute with erasure (unrefined)

A premise that passes `premY` (`if e`, `otherwise`, `(if e)^iter`) holds on the erased scope
exactly when it holds on the original one, and returns the scope unchanged (`prems_erase`). The
conditions are evaluated by round 7's expression half (`NxErase.nAt`); the rounds of an iterated
premise conform by `NxFlow.rowScope_opt`/`rowScope_list`, as in `NxErase.step_iter`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxClause

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
open Silmaril.Wasm.SpecTec.Sim.Round7.NxErase (QT NCalls nAt NCalls.mono NCalls.bindVals auxX
  premX auxXI auxXD)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope)

variable {gr gd : String → Bool} {env : Env}
variable {S : Sig} {T : TSig} {Γ : List (String × AT)} {c : AuxCtx}

theorem ER.weaken {α : Type} {f : α → α} {P P' : α → Prop} {r r' : Res α} (h : ER f P r r')
    (hP : ∀ a, P a → P' a) : ER f P' r r' :=
  ⟨h.1, fun a ha => hP a (h.2 a ha)⟩

theorem ER.foldlM_fix {ρ : VarEnv} {step step' : VarEnv → Prem → Res VarEnv} :
    ∀ prs : List Prem,
      (∀ pr ∈ prs, ER eraseScope (· = ρ) (step ρ pr) (step' (eraseScope ρ) pr)) →
      ER eraseScope (· = ρ) (prs.foldlM step ρ) (prs.foldlM step' (eraseScope ρ))
  | [], _ => ER.ok rfl
  | pr :: prs, hs => by
    simp only [List.foldlM_cons]
    refine ER.bind (hs pr (List.mem_cons_self ..)) fun σ _ hσ => ?_
    subst hσ
    exact ER.foldlM_fix prs fun pr' hpr' => hs pr' (List.mem_cons_of_mem _ hpr')

/-- **A condition.** -/
theorem ifPr_erase (hBI : BIErase QT gd env) {σ : VarEnv} {n : Nat} (hσ : ScopeVT S Γ σ)
    (hc : NCalls gd S T c env σ n) {e : Exp} (ht : tyOk S T Γ e = true) (ha : auxE c e = true)
    (hX : auxX c e = true) (hb : badE S Γ e = 0) (hx : xExp gr gd e = true) :
    ∀ m ≤ n, ER eraseScope (· = σ) (premHolds m env σ (.ifPr e))
      (premHolds m env (eraseScope σ) (.ifPr e))
  | 0, _ => by simp only [premHolds]; exact ER.error _
  | m + 1, hm => by
    simp only [premHolds]
    refine ER.bind ((nAt (gr := gr) hBI m).exp S T Γ c σ e hσ (hc.mono (by omega)) ht ha hX hb hx)
      fun v _ _ => ?_
    exact ER.assert eraseV_eq_bool.symm fun _ => ER.ok rfl

/-- **The rounds of an iterated condition.** -/
theorem premRounds_erase (hBI : BIErase QT gd env) {ρ : VarEnv} {n : Nat} {Γi : List (String × AT)}
    (hc : NCalls gd S T c env ρ n) {e : Exp} (ht : tyOk S T Γi e = true) (ha : auxE c e = true)
    (hX : auxX c e = true) (hb : badE S Γi e = 0) (hx : xExp gr gd e = true)
    (xvs : List (IL.Id × Value)) (ido : Option IL.Id) (k : Nat)
    (hr : ∀ ds, xvs.mapM (fun p => p.2.asList?.map fun l => (p.1, l)) = some ds →
      (∀ p ∈ ds, p.2.length = k) → ∀ i < k, ScopeVT S Γi (ρ.bindVals (iterRow ds ido i))) :
    ∀ m ≤ n, ER eraseScope (· = ρ) (premRounds m env ρ (.ifPr e) xvs ido k)
      (premRounds m env (eraseScope ρ) (.ifPr e) (xvs.map eraseP) ido k)
  | 0, _ => by simp only [premRounds]; exact ER.error _
  | m + 1, hm => by
    simp only [premRounds, mapM_asList_erase]
    cases hds : (xvs.mapM fun (p : IL.Id × Value) => p.2.asList?.map fun l => (p.1, l)) with
    | none => exact ER.error _
    | some ds =>
      simp only [Option.map_some, Res.ofOption_some, bind, Except.bind]
      refine ER.assert (by simp [List.all_map, Function.comp_def]) fun hall => ?_
      have hlen : ∀ p ∈ ds, p.2.length = k := fun p hp => by
        have := List.all_eq_true.1 hall p hp
        simpa using this
      rw [iterRows_erase]
      refine ER.bind (ER.mapM (f := eraseScope) (P := fun _ => True) (h := List.map eraseP) _
        fun r hrm => ?_) fun _ _ _ => ER.ok rfl
      rw [← eraseScope_bindVals]
      simp only [iterRows, List.mem_map, List.mem_range] at hrm
      obtain ⟨i, hi, rfl⟩ := hrm
      exact ER.weaken (ifPr_erase hBI (hr ds hds hlen i hi) (hc.bindVals _) ht ha hX hb hx m
        (by omega)) fun _ _ => trivial

set_option maxHeartbeats 1000000 in
/-- **An iterated condition.** -/
theorem premIter_erase (hBI : BIErase QT gd env) {ρ : VarEnv} {n : Nat} (hρ : ScopeVT S Γ ρ)
    (hc : NCalls gd S T c env ρ n) {e : Exp} {it : Iter} {ds : List Dom}
    (ht : tyOk S T (iterΓ S Γ it ds) e = true) (hti : tyOkI S T Γ it = true)
    (htd : tyOkD S T Γ ds = true) (hnd : nodupB (ds.map domVar) = true)
    (ha : auxE c e = true) (hai : auxI c it = true) (had : auxD c ds = true)
    (hX : auxX c e = true) (hXi : auxXI c it = true) (hXd : auxXD c ds = true)
    (hb : badE S (iterΓ S Γ it ds) e = 0) (hbi : badI S Γ it = 0) (hbd : badDs S Γ ds = 0)
    (hx : xExp gr gd e = true) (hxi : xIter gr gd it = true) (hxd : xDoms gr gd ds = true) :
    ∀ m ≤ n, ER eraseScope (· = ρ) (premIter m env ρ (.ifPr e) it ds)
      (premIter m env (eraseScope ρ) (.ifPr e) it ds)
  | 0, _ => by simp only [premIter]; exact ER.error _
  | m + 1, hm => by
    have hc' := hc.mono (show m ≤ n by omega)
    have hD := (nAt (gr := gr) hBI m).doms S T Γ c ρ ds hρ hc' htd had hXd hbd hxd
    have hE := fun xvs (h : evalDoms m env ρ ds = .ok xvs) =>
      (expAt env m).doms S T Γ c ρ ds xvs hρ hc'.callH htd had h
    cases it with
    | opt =>
      simp only [premIter]
      refine ER.bind hD fun xvs hxvs _ => ER.assert Iff.rfl fun _ => ?_
      rw [mapM_asOpt_erase]
      cases hos : (xvs.mapM fun (p : IL.Id × Value) => p.2.asOpt?.map fun o => (p.1, o)) with
      | none => exact ER.error _
      | some os =>
        simp only [Option.map_some, Res.ofOption_some, bind, Except.bind]
        have hn : ((os.map fun (p : IL.Id × Option Value) => (p.1, p.2.map eraseV)).all
            fun p => p.2.isNone) = os.all fun p => p.2.isNone := by
          simp [List.all_map, Function.comp_def]
        have hs : ((os.map fun (p : IL.Id × Option Value) => (p.1, p.2.map eraseV)).all
            fun p => p.2.isSome) = os.all fun p => p.2.isSome := by
          simp [List.all_map, Function.comp_def]
        rw [hn, hs, filterMap_opt_erase]
        split
        · exact ER.ok rfl
        · split
          · rename_i hsome
            rw [← eraseScope_bindVals]
            refine ER.bind (ER.weaken (ifPr_erase hBI (rowScope_opt hρ hnd (hE xvs hxvs) hos hsome)
              (hc.bindVals _) ht ha hX hb hx m (by omega)) fun _ _ => trivial)
              fun _ _ _ => ER.ok rfl
          · exact ER.error _
    | list =>
      simp only [premIter]
      refine ER.bind hD fun xvs hxvs _ => ER.assert Iff.rfl fun _ => ?_
      rw [headLen_erase]
      cases (xvs.head?.bind fun p => p.2.asList?.map List.length) with
      | none => exact ER.error _
      | some k =>
        simp only [Res.ofOption_some, bind, Except.bind]
        exact premRounds_erase hBI hc ht ha hX hb hx xvs none k
          (fun ds' hl hlen i hi => rowScope_list hρ hnd (hE xvs hxvs) (by simp [counterΓ]) hl
            hlen hi) m (by omega)
    | list1 =>
      simp only [premIter]
      refine ER.bind hD fun xvs hxvs _ => ER.assert Iff.rfl fun _ => ?_
      rw [headLen_erase]
      cases (xvs.head?.bind fun p => p.2.asList?.map List.length) with
      | none => exact ER.error _
      | some k =>
        simp only [Res.ofOption_some, bind, Except.bind]
        exact ER.assert Iff.rfl fun _ => premRounds_erase hBI hc ht ha hX hb hx xvs none k
          (fun ds' hl hlen i hi => rowScope_list hρ hnd (hE xvs hxvs) (by simp [counterΓ]) hl
            hlen hi) m (by omega)
    | listN eₙ ido =>
      simp only [tyOkI] at hti
      simp only [auxI] at hai
      simp only [auxXI] at hXi
      simp only [badI] at hbi
      simp only [xIter] at hxi
      simp only [premIter]
      refine ER.bind hD fun xvs hxvs _ =>
        ER.bind ((nAt (gr := gr) hBI m).exp S T Γ c ρ eₙ hρ hc' hti hai hXi hbi hxi)
          fun kv _ _ => ?_
      rw [asNat?_eraseV]
      cases kv.asNat? with
      | none => exact ER.error _
      | some k =>
        simp only [Res.ofOption_some, bind, Except.bind]
        exact premRounds_erase hBI hc ht ha hX hb hx xvs ido k
          (fun ds' hl hlen i hi => rowScope_list hρ hnd (hE xvs hxvs)
            (by cases ido <;> simp [counterΓ]) hl hlen hi) m (by omega)

/-- **A premise that passes `premY`.** -/
theorem prem_erase (hBI : BIErase QT gd env) {ρ : VarEnv} {n : Nat} (hρ : ScopeVT S Γ ρ)
    (hc : NCalls gd S T c env ρ n) (pr : Prem) (hy : premY c pr = true)
    (ht : premTy S T Γ pr = true) (hb : badPr S Γ pr = 0) (hX : premX c pr = true)
    (hx : xPrem gr gd pr = true) :
    ∀ m ≤ n, ER eraseScope (· = ρ) (premHolds m env ρ pr) (premHolds m env (eraseScope ρ) pr) := by
  intro m hm
  cases pr with
  | ifPr e =>
    simp only [premY] at hy
    simp only [premTy] at ht
    simp only [badPr] at hb
    simp only [premX] at hX
    simp only [xPrem] at hx
    exact ifPr_erase hBI hρ hc ht hy hX hb hx m hm
  | elsePr =>
    cases m with
    | zero => simp only [premHolds]; exact ER.error _
    | succ m => simp only [premHolds]; exact ER.ok rfl
  | iterPr pr ie =>
    obtain ⟨it, ds⟩ := ie
    cases pr with
    | ifPr e =>
      simp only [premY, Bool.and_eq_true] at hy
      obtain ⟨⟨⟨ha, hnd⟩, hai⟩, had⟩ := hy
      simp only [premTy, Bool.and_eq_true] at ht
      obtain ⟨⟨hte, hti⟩, htd⟩ := ht
      simp only [badPr, Nat.add_eq_zero_iff] at hb
      obtain ⟨⟨hbe, hbi⟩, hbd⟩ := hb
      simp only [premX, Bool.and_eq_true] at hX
      obtain ⟨⟨hXe, hXi⟩, hXd⟩ := hX
      simp only [xPrem, Bool.and_eq_true] at hx
      obtain ⟨⟨hxe, hxi⟩, hxd⟩ := hx
      cases m with
      | zero => simp only [premHolds]; exact ER.error _
      | succ m =>
        simp only [premHolds]
        exact premIter_erase hBI hρ hc hte hti htd hnd ha hai had hXe hXi hXd hbe hbi hbd
          hxe hxi hxd m (by omega)
    | _ => simp [premY] at hy
  | _ => simp [premY] at hy

/-- **The premises of a clause that pass `premY`** hold on the erased scope exactly when they hold
on the original one, and return the scope unchanged. -/
theorem prems_erase (hBI : BIErase QT gd env) {ρ : VarEnv} {n : Nat} (hρ : ScopeVT S Γ ρ)
    (hc : NCalls gd S T c env ρ n) (prems : List Prem)
    (hp : ∀ pr ∈ prems, premY c pr = true ∧ premTy S T Γ pr = true ∧ badPr S Γ pr = 0 ∧
      premX c pr = true ∧ xPrem gr gd pr = true) :
    ER eraseScope (· = ρ) (premsHold n env ρ prems) (premsHold n env (eraseScope ρ) prems) := by
  cases n with
  | zero => simp only [premsHold]; exact ER.error _
  | succ m =>
    simp only [premsHold]
    refine ER.foldlM_fix prems fun pr hpr => ?_
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hp pr hpr
    exact prem_erase hBI hρ hc pr h₁ h₂ h₃ h₄ h₅ m (by omega)

end Silmaril.Wasm.SpecTec.Sim.Round7.NxClause
