module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.PermType

/-!
# Renaming identifiers: equivariance of satisfaction

Premises (`Sim.PremW`), well-typed quantifiers (`Sim.QuantsOk`), rule bodies (`Sim.RuleBody`,
`RuleBodyA` at an equivariant reading) and satisfaction of sentences (`SSen.Sat`) are equivariant
under a permutation `π` of identifiers fixing `"_"`: renaming the environment, the
interpretation and the sentence changes nothing (`sat_rnS_iff`). Each is proved in the forward
direction; the converse is the forward direction for `π.symm`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Perm

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim

variable {π : Equiv.Perm IL.Id}

theorem symm_fix (hπ : π "_" = "_") : π.symm "_" = "_" := by
  rw [Equiv.symm_apply_eq, hπ]

theorem rnI_rn (D : Interp) (x : IL.Id) (op : MixopS) (avs : List ArgV) (w : Value) :
    rnI π D (π x) op (avs.map (rnArgV π)) w ↔ D x op avs w := by
  simp only [rnI, Equiv.symm_apply_apply, rnArgVs_symm]

/-- The content of a present option value. -/
def optSome : Value → Option Value
  | .opt (some w) => some w
  | _ => none

theorem domSomes_eq (xvs : List (IL.Id × Value)) :
    domSomes xvs = xvs.mapM fun p => (optSome p.2).map fun w => (p.1, w) := by
  unfold domSomes
  congr 1
  funext p
  obtain ⟨x, v⟩ := p
  rcases v with _ | _ | _ | _ | _ | _ | _ | (_ | _) <;> rfl

theorem domSomes_rn (xvs : List (IL.Id × Value)) :
    domSomes (rnMap π id xvs) = (domSomes xvs).map (rnMap π id) := by
  rw [domSomes_eq, domSomes_eq]
  exact mapM_keys_rn optSome xvs

theorem domLists_rn (xvs : List (IL.Id × Value)) :
    domLists (rnMap π id xvs) = (domLists xvs).map (rnMap π id) :=
  mapM_asList_rn xvs

theorem rnDoms_ne_nil {ds : List Dom} (h : ds ≠ []) : rnDoms π ds ≠ [] := by
  rw [rnDoms_eq]
  exact fun e => h (List.map_eq_nil_iff.mp e)

/-- Domain lengths survive renaming the keys. -/
theorem lens_rn {dls : List (IL.Id × List Value)} {k : Nat} (h : ∀ d ∈ dls, d.2.length = k) :
    ∀ d ∈ rnMap π id dls, d.2.length = k := by
  intro d hd
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd
  exact h q hq

/-- Every round of a renamed iteration is a renamed round. -/
theorem rows_rn (hπ : π "_" = "_") {Q : VarEnv → Prop} {ρ : VarEnv}
    {dls : List (IL.Id × List Value)} {ido : Option IL.Id} {k : Nat}
    (h : ∀ r ∈ iterRows dls ido k, Q (rnVarEnv π (ρ.bindVals r))) :
    ∀ r ∈ iterRows (rnMap π id dls) (ido.map π) k, Q ((rnVarEnv π ρ).bindVals r) := by
  intro r hr
  have hr' : r ∈ (iterRows dls ido k).map (rnMap π id) := iterRows_rn dls ido k ▸ hr
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr'
  have he : (rnVarEnv π ρ).bindVals (rnMap π id r₀) = rnVarEnv π (ρ.bindVals r₀) :=
    bindVals_rn hπ ρ r₀
  exact he ▸ h r₀ hr₀

theorem domLists_rn_some {xvs : List (IL.Id × Value)} {dls : List (IL.Id × List Value)}
    (h : domLists xvs = some dls) : domLists (rnMap π id xvs) = some (rnMap π id dls) := by
  rw [domLists_rn, h]
  rfl

theorem rnIter_of_list {it : Iter} {k : Nat} (h : it = .list ∨ (it = .list1 ∧ 1 ≤ k)) :
    rnIter π it = it := by
  rcases h with h | ⟨h, _⟩ <;> exact h ▸ rfl

/-- **Premises are equivariant** (forward direction). -/
theorem premW_rn_of (hπ : π "_" = "_") {env : Env} {D : Interp} {els : Prop} {ρ : VarEnv}
    {pr : Prem} (h : PremW env D els ρ pr) :
    PremW (rnEnv π env) (rnI π D) els (rnVarEnv π ρ) (rnPrem π pr) := by
  induction h with
  | ifPr he => exact .ifPr ((evalExp_rn hπ _ _ _ _).mpr he)
  | elsePr h => exact .elsePr h
  | letPr h₁ h₂ => exact .letPr ((evalExp_rn hπ _ _ _ _).mpr h₁) ((evalExp_rn hπ _ _ _ _).mpr h₂)
  | rulePr ha he hd =>
    exact .rulePr ((evalArgs_rn hπ _ _ _ _).mpr ha) ((evalExp_rn hπ _ _ _ _).mpr he)
      ((rnI_rn _ _ _ _ _).mpr hd)
  | iterOptNone hd hne hall =>
    exact .iterOptNone ((evalDoms_rn hπ _ _ _ _).mpr hd) (rnDoms_ne_nil hne)
      fun p hp => (List.mem_map.mp hp).elim fun q hq => hq.2 ▸ hall q hq.1
  | @iterOptSome _ _ _ xvs row hd hne hs _ ih =>
    have hs' : domSomes (rnMap π id xvs) = some (rnMap π id row) := by rw [domSomes_rn, hs]; rfl
    have ih' : PremW (rnEnv π env) (rnI π D) els ((rnVarEnv π _).bindVals (rnMap π id row))
        (rnPrem π _) := (bindVals_rn hπ _ row).symm ▸ ih
    exact .iterOptSome ((evalDoms_rn hπ _ _ _ _).mpr hd) (rnDoms_ne_nil hne) hs' ih'
  | @iterList ρ' pr' it _ _ _ k hit hd hne hl hlen _ ih =>
    show PremW _ _ _ _ (.iterPr _ (.mk (rnIter π it) (rnDoms π _)))
    rw [rnIter_of_list hit]
    exact .iterList hit ((evalDoms_rn hπ _ _ _ _).mpr hd) (rnDoms_ne_nil hne)
      (domLists_rn_some hl) (lens_rn hlen)
      (rows_rn (Q := fun ρ'' => PremW (rnEnv π env) (rnI π D) els ρ'' (rnPrem π pr')) (ρ := ρ')
        (ido := none) hπ ih)
  | @iterListN ρ' pr' _ ido _ _ dls _ k hd he hk hl hlen _ ih =>
    have hrows : ∀ r ∈ iterRows (rnMap π id dls) (rnIdOpt π ido) k,
        PremW (rnEnv π env) (rnI π D) els ((rnVarEnv π ρ').bindVals r) (rnPrem π pr') := by
      rw [rnIdOpt_eq]
      exact rows_rn (Q := fun ρ'' => PremW (rnEnv π env) (rnI π D) els ρ'' (rnPrem π pr'))
        (ρ := ρ') (ido := ido) hπ ih
    exact .iterListN ((evalDoms_rn hπ _ _ _ _).mpr hd) ((evalExp_rn hπ _ _ _ _).mpr he) hk
      (domLists_rn_some hl) (lens_rn hlen) hrows

/-- **Well-typed quantifiers are equivariant** (forward direction). -/
theorem quantsOk_rn_of (hπ : π "_" = "_") {env : Env} {ρ : VarEnv} {qs : List Param}
    (h : QuantsOk env ρ qs) : QuantsOk (rnEnv π env) (rnVarEnv π ρ) (rnParams π qs) := by
  intro x t hx
  have hx' : Param.expP x t ∈ qs.map (rnParam π) := rnParams_eq π qs ▸ hx
  obtain ⟨p, hp, he⟩ := List.mem_map.mp hx'
  cases p with
  | expP y t₀ =>
    obtain ⟨rfl, rfl⟩ : π y = x ∧ rnTyp π t₀ = t := by simpa only [rnParam, Param.expP.injEq] using he
    obtain ⟨w, hw, ht⟩ := h y t₀ hp
    exact ⟨w, by rw [findVal?_rn, hw], (hasTyp_rn hπ _ _ _ _).mpr ht⟩
  | _ => simp only [rnParam, reduceCtorEq] at he

theorem bindParams_rn_some (hπ : π "_" = "_") {ps : List Param} {args : List ArgV} {ρ₀ : VarEnv}
    (h : bindParams VarEnv.empty ps args = some ρ₀) :
    bindParams VarEnv.empty (rnParams π ps) (args.map (rnArgV π)) = some (rnVarEnv π ρ₀) := by
  rw [bindParams_rn_empty hπ, h, Option.map_some]

/-- **Rule bodies are equivariant** (forward direction). -/
theorem ruleBody_rn_of (hπ : π "_" = "_") {env : Env} {D : Interp} {els : Prop}
    {ps : List Param} {args : List ArgV} {op : MixopS} {r : Rule} {v : Value}
    (h : RuleBody env D els ps args op r v) :
    RuleBody (rnEnv π env) (rnI π D) els (rnParams π ps) (args.map (rnArgV π)) op (rnRule π r) v := by
  obtain ⟨nm, qs, op', e, prems⟩ := r
  obtain ⟨hop, ρ₀, σ, hb, hq, he, hp⟩ := h
  have hρ : (rnVarEnv π ρ₀).bindVals (rnMap π id σ) = rnVarEnv π (ρ₀.bindVals σ) :=
    bindVals_rn hπ ρ₀ σ
  refine ⟨hop, rnVarEnv π ρ₀, rnMap π id σ, bindParams_rn_some hπ hb, ?_, ?_, ?_⟩
  · rw [hρ]
    exact quantsOk_rn_of hπ hq
  · rw [hρ]
    exact (evalExp_rn hπ _ _ _ _).mpr he
  · intro pr' hpr'
    have hpr'' : pr' ∈ prems.map (rnPrem π) := rnPrems_eq π prems ▸ hpr'
    obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp hpr''
    rw [hρ]
    exact premW_rn_of hπ (hp pr hpr)

/-- The declarative reading is equivariant. -/
theorem decl_equivariant : Equivariant decl := by
  intro g e e' he
  rw [List.mem_singleton.mp he]
  exact List.mem_singleton_self _

/-- **Rule bodies at an equivariant reading are equivariant** (forward direction). -/
theorem ruleBodyA_rn_of (hπ : π "_" = "_") {alts : Reading} (ha : Equivariant alts) {env : Env}
    {D : Interp} {els : Prop} {ps : List Param} {args : List ArgV} {op : MixopS} {r : Rule}
    {v : Value} (h : RuleBodyA alts env D els ps args op r v) :
    RuleBodyA alts (rnEnv π env) (rnI π D) els (rnParams π ps) (args.map (rnArgV π)) op
      (rnRule π r) v := by
  obtain ⟨nm, qs, op', e, prems⟩ := r
  obtain ⟨e', he', hb⟩ := h
  exact ⟨rnExp π e', ha π e e' he', ruleBody_rn_of hπ hb⟩

theorem rnRule_symm (r : Rule) : rnRule π.symm (rnRule π r) = r := by
  rw [rnRule_comp, symm_comp_self, rnRule_id]

theorem rnParams_symm (ps : List Param) : rnParams π.symm (rnParams π ps) = ps := by
  rw [rnParams_comp, symm_comp_self, rnParams_id]

/-- A rule body over a renamed environment and interpretation is a renamed rule body. -/
theorem ruleBodyA_rn_iff (hπ : π "_" = "_") {alts : Reading} (ha : Equivariant alts) {env : Env}
    {D : Interp} {ps : List Param} {args : List ArgV} {op : MixopS} {r : Rule} {v : Value} :
    RuleBodyA alts (rnEnv π env) (rnI π D) False (rnParams π ps) args op (rnRule π r) v ↔
      RuleBodyA alts env D False ps (args.map (rnArgV π.symm)) op r v := by
  constructor
  · intro h
    have h' := ruleBodyA_rn_of (π := π.symm) (symm_fix hπ) ha h
    rwa [rnEnv_symm, rnI_symm, rnParams_symm, rnRule_symm] at h'
  · intro h
    have h' := ruleBodyA_rn_of (π := π) hπ ha h
    rwa [rnArgVs_symm'] at h'

/-- **Satisfaction is equivariant**: a renamed sentence holds in the renamed environment and
interpretation iff the sentence holds. -/
theorem sat_rnS_iff (hπ : π "_" = "_") {alts : Reading} (ha : Equivariant alts) (env : Env)
    (D : Interp) (φ : SSen) : (rnS π φ).Sat alts (rnEnv π env) (rnI π D) ↔ φ.Sat alts env D := by
  cases φ with
  | fact x op args v => exact rnI_rn D x op args v
  | rule d r =>
    obtain ⟨x, ps, op, t⟩ := d
    show (∀ args v, RuleBodyA alts (rnEnv π env) (rnI π D) False (rnParams π ps) args op
        (rnRule π r) v → rnI π D (π x) op args v) ↔
      ∀ args v, RuleBodyA alts env D False ps args op r v → D x op args v
    constructor
    · intro h args v hb
      have hb' := (ruleBodyA_rn_iff hπ ha).mpr ((rnArgVs_symm π args).symm ▸ hb)
      exact (rnI_rn D x op args v).mp (h _ v hb')
    · intro h args v hb
      have hr : rnI π D (π x) op ((args.map (rnArgV π.symm)).map (rnArgV π)) v :=
        (rnI_rn D x op _ v).mpr (h _ v ((ruleBodyA_rn_iff hπ ha).mp hb))
      rwa [rnArgVs_symm'] at hr

end Silmaril.Wasm.SpecTec.Institution.Perm
