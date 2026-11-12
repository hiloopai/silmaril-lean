module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.TyElim.SubRules

/-!
# Round 6: `AgreeTy.subElim` on the concrete `B`

* `rs_dsRefl`, `rs_dsSuper`: the two rules of `Deftype_sub` in `{}` (`refl` never fires,
  because `$clos_deftype` has no value);
* `subM_of_dderivesB`: by the recursor of the mutual `DDerivesB`/`DPremB`, every derivation of
  `Heaptype_sub {}` or `Deftype_sub {}` satisfies the claim `SubM`;
* `subElim_BI`: `Reftype_sub {}` from the image of a reference type `p` is `SubE` to the image
  of a reference type.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.TyElim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV tyV_inj natV nullV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Round6.Reading
open Round6.RefOkV (SubE)

variable {prof : Silmaril.Wasm.Numerics.Profile} {H : Type} {hn : H → String}
  {host : Silmaril.Wasm.Execution.Core.HostSemantics H}

local notation "𝔼" => simEnv (Prims.builtins prof hn host)

/-! ## `Deftype_sub` -/

theorem rs_dsRefl : RS 𝔼 DsRes dsRefl := by
  intro e' halt O els σ hq a b he hp ih
  obtain ⟨hC, ha, -⟩ := concl_C ((concl_eq halt rfl) ▸ he)
  cases hp _ (List.mem_singleton_self _) with
  | ifPr hc =>
    obtain ⟨v₁, -, hv₁, -, -⟩ := evalExp_cmpE_iff.1 hc
    exact absurd (applies_of_call ⟨rfl, rfl, rfl⟩ (Equiv.evalArgs_cons (evalExp_var hC)
      (Equiv.evalArgs_cons (evalExp_var (evalExp_varE_iff.1 ha)) Equiv.evalArgs_nil)) hv₁)
      (not_applies_closDeftype hn host _ _ _)

/-- `$unrolldt(deftype_1) = SUB final? typeuse* ct`, read at the image of a defined type. -/
theorem super_unroll {ρ : VarEnv} (hρ : ValsOnly ρ) {d₁ : DefType}
    (hA : ρ.findVal? "deftype_1" = some (tyV d₁)) {X : Exp}
    (hc : EvalExp 𝔼 ρ (.cmpE .eqOp .boolT (.callE "unrolldt" [.expA (.varE "deftype_1")])
      (.caseE "SUB" (.tupE [X, .iterE (.varE "typeuse") (.mk .list [.mk "typeuse"
        (.varE "typeuse*")]), .varE "ct"]))) (.bool true)) :
    ∃ fin sups ct, unrolldt d₁ = some (.sub fin sups ct) ∧
      ρ.findVal? "typeuse*" = some (.list (sups.toList.map tyV)) := by
  obtain ⟨v₁, v₂, hv₁, hv₂, hcv⟩ := evalExp_cmpE_iff.1 hc
  have e₁₂ : v₁ = v₂ := Silmaril.SpecTec.Equiv.ExecNumeric.cmpValues_eq_true_iff.1 hcv
  obtain ⟨st, hst, hv⟩ := Option.map_eq_some_iff.1 ((Prims.applies_unrolldt hn host d₁ v₁).1
    (applies_of_call hρ (Equiv.evalArgs_cons (evalExp_var hA) Equiv.evalArgs_nil) hv₁))
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 hv₂
  obtain ⟨x, y, z, rfl, -, hy, -⟩ := RefOkV.evalExp_tup3_ex hw
  obtain ⟨ws, hU, rfl⟩ := Round5.Target.evalExp_iterList_inv
    (Round5.Target.bodyReads_sound (x := "typeuse") (b := .varE "typeuse") rfl) (by decide) hy
  obtain ⟨fin, sups, ct, rfl⟩ : ∃ fin sups ct, st = Ty.sub fin sups ct := by
    cases st; exact ⟨_, _, _, rfl⟩
  have hws : tyV sups = .list ws := by
    have e : tyV (Ty.sub fin sups ct) = _ := hv.trans e₁₂
    simp only [tyV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and] at e
    exact e.2.1
  rw [Equiv.Validation.tyV_list] at hws
  exact ⟨fin, sups, ct, hst, by rw [hU, hws]⟩

/-- `typeuse*[i]`, read at the images of a sequence of type uses. -/
theorem super_idx {ρ : VarEnv} {sups : Ty (.list .use)} {x : Value}
    (hU : ρ.findVal? "typeuse*" = some (.list (sups.toList.map tyV)))
    (h : EvalExp 𝔼 ρ (.idxE (.iterE (.varE "typeuse") (.mk .list [.mk "typeuse"
      (.varE "typeuse*")])) (.varE "i")) x) :
    ∃ (j : Nat) (u : CTypeUse), sups.toList[j]? = some u ∧ x = tyV u := by
  obtain ⟨w, j, hw, -, hidx⟩ := evalExp_idxE_iff.1 h
  obtain ⟨ws, hU', rfl⟩ := Round5.Target.evalExp_iterList_inv
    (Round5.Target.bodyReads_sound (x := "typeuse") (b := .varE "typeuse") rfl) (by decide) hw
  have e : ws = sups.toList.map tyV := Value.list.inj (Option.some.inj (hU'.symm.trans hU))
  rw [e] at hidx
  obtain ⟨u, hu, rfl⟩ := RefOkV.idx_map_inv hidx
  exact ⟨j, u, hu, rfl⟩

/-- `Deftype_sub/super`'s `if` premise, at the image of a defined type. -/
theorem super_unroll_prem {O : ElseI} {els : Prop} {σ : List (IL.Id × Value)} {d₁ : DefType}
    (hA : (VarEnv.empty.bindVals σ).findVal? "deftype_1" = some (tyV d₁))
    (h : DPremB 𝔼 O els (VarEnv.empty.bindVals σ) (.ifPr (.cmpE .eqOp .boolT
      (.callE "unrolldt" [.expA (.varE "deftype_1")]) (.caseE "SUB" (.tupE [.iterE (.varE "final")
        (.mk .opt [.mk "final" (.varE "final?")]), .iterE (.varE "typeuse") (.mk .list
          [.mk "typeuse" (.varE "typeuse*")]), .varE "ct"]))))) :
    ∃ fin sups ct, unrolldt d₁ = some (.sub fin sups ct) ∧
      (VarEnv.empty.bindVals σ).findVal? "typeuse*" = some (.list (sups.toList.map tyV)) := by
  cases h with
  | ifPr hc => exact super_unroll (valsOnly_bind σ) hA hc

theorem rs_dsSuper : RS 𝔼 DsRes dsSuper := by
  intro e' halt O els σ hq a b he hp ih
  obtain ⟨hC, ha, hb⟩ := concl_C ((concl_eq halt rfl) ▸ he)
  obtain ⟨d₁, rfl⟩ := quant_def hq (x := "deftype_1") (by simp) (evalExp_varE_iff.1 ha)
  obtain ⟨d₂, rfl⟩ := quant_def hq (x := "deftype_2") (by simp) (evalExp_varE_iff.1 hb)
  obtain ⟨fin, sups, ct, hst, hU⟩ :=
    super_unroll_prem (evalExp_varE_iff.1 ha) (hp _ (List.mem_cons_self ..))
  obtain ⟨v, hv, -⟩ := prem_rule (hp _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  obtain ⟨c, x, y, rfl, h₁, h₂, h₃⟩ := RefOkV.evalExp_tup3_ex hv
  have ec : c = ctx0V := h₁.unique (evalExp_var hC)
  have ey : y = tyV d₂ := (evalExp_subE_iff.1 h₃).unique hb
  obtain ⟨j, u, hj, rfl⟩ := super_idx hU (evalExp_subE_iff.1 h₂)
  have hR : HsRes (tyV u) (tyV d₂) := (ih _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _
    hv).1 rfl _ _ (by rw [ec, ey])
  obtain ⟨h₂', e₂, hs⟩ := hR.1 (.use u) rfl
  exact ⟨d₁, d₂, rfl, rfl, .defSuper hst hj (heap_of_def e₂.symm ▸ hs)⟩

/-! ## The recursion -/

/-- Every rule of `Heaptype_sub` establishes `HsRes` in `{}`. -/
theorem hs_sound : ∀ r ∈ heaptypeSubRules, RS 𝔼 HsRes r := by
  unfold heaptypeSubRules
  exact List.forall_mem_cons.2 ⟨rs_refl, List.forall_mem_cons.2 ⟨rs_trans, List.forall_mem_cons.2 ⟨rs_eqAny, List.forall_mem_cons.2 ⟨rs_i31Eq, List.forall_mem_cons.2 ⟨rs_structEq, List.forall_mem_cons.2 ⟨rs_arrayEq, List.forall_mem_cons.2 ⟨rs_struct, List.forall_mem_cons.2 ⟨rs_array, List.forall_mem_cons.2 ⟨rs_func, List.forall_mem_cons.2 ⟨rs_def, List.forall_mem_cons.2 ⟨rs_idxL, List.forall_mem_cons.2 ⟨rs_idxR, List.forall_mem_cons.2 ⟨rs_recStruct, List.forall_mem_cons.2 ⟨rs_recArray, List.forall_mem_cons.2 ⟨rs_recFunc, List.forall_mem_cons.2 ⟨rs_recSub, List.forall_mem_cons.2 ⟨rs_none, List.forall_mem_cons.2 ⟨rs_nofunc, List.forall_mem_cons.2 ⟨rs_noexn, List.forall_mem_cons.2 ⟨rs_noextern, List.forall_mem_cons.2 ⟨rs_bot, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- Every rule of `Deftype_sub` establishes `DsRes` in `{}`. -/
theorem ds_sound : ∀ r ∈ deftypeSubRules, RS 𝔼 DsRes r := by
  unfold deftypeSubRules
  exact List.forall_mem_cons.2 ⟨rs_dsRefl, List.forall_mem_cons.2 ⟨rs_dsSuper, fun _ h => absurd h List.not_mem_nil⟩⟩

/-- A rule of a relation whose rules all establish `P`, at a parameterless instance. -/
theorem rs_apply {P : Value → Value → Prop} {x : IL.Id} {rules : List Rule}
    (hrules : ∃ t, (simEnv (Prims.builtins prof hn host)).findRel? x =
      some ([], "%|-%<:%", t, rules))
    (hsound : ∀ r ∈ rules, RS 𝔼 P r) {O : ElseI} {op : MixopS} {args : List ArgV} {v : Value}
    {ps : List Param} {t : Typ} {rules' : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param}
    {e e' : Exp} {prems : List Prem} {ρ₀ : VarEnv} {σ : List (IL.Id × Value)}
    (hrel : (simEnv (Prims.builtins prof hn host)).findRel? x = some (ps, op, t, rules'))
    (hrule : rules'[i]? = some (.ruleD nm qs op e prems)) (halt : e' ∈ conclAlts e)
    (hps : bindParams VarEnv.empty ps args = some ρ₀) (hq : QuantsOk 𝔼 (ρ₀.bindVals σ) qs)
    (he : EvalExp 𝔼 (ρ₀.bindVals σ) e' v)
    (hp : ∀ pr ∈ prems, DPremB 𝔼 O (O x args i v) (ρ₀.bindVals σ) pr)
    (ih : ∀ pr ∈ prems, PremS 𝔼 (ρ₀.bindVals σ) pr) :
    ∀ a b, v = .tuple [ctx0V, a, b] → P a b := by
  intro a b hv
  obtain ⟨t₀, h₀⟩ := hrules
  have hr : ([], "%|-%<:%", t₀, rules) = (ps, op, t, rules') := Option.some.inj (h₀.symm.trans hrel)
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl, -, rfl⟩ := hr
  have hρ : ρ₀ = VarEnv.empty := by
    cases args with
    | nil => exact (Option.some.inj hps).symm
    | cons _ _ => simp [bindParams] at hps
  subst hρ hv
  exact hsound _ (List.mem_of_getElem? hrule) e' halt O _ σ hq a b he hp ih

/-- **Every derivation of `Heaptype_sub {}` or `Deftype_sub {}` satisfies the claim**, on the
concrete `B`. -/
theorem subM_of_dderivesB {O : ElseI} {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}
    (h : DDerivesB 𝔼 O x op args v) : SubM x v := by
  refine DDerivesB.rec (motive_1 := fun x _ _ v _ => SubM x v)
    (motive_2 := fun _ ρ pr _ => PremS 𝔼 ρ pr) ?_ (by intros; trivial) (by intros; trivial)
    (by intros; trivial) ?_ (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) h
  · intro x op args v ps t rules i nm qs e e' prems ρ₀ σ hrel hrule halt hps hq he hp ih
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · subst hx
      exact rs_apply findRel_heaptypeSub hs_sound hrel hrule halt hps hq he hp ih
    · subst hx
      exact rs_apply findRel_deftypeSub ds_sound hrel hrule halt hps hq he hp ih
  · intro els ρ x args op e avs w _ he _ ih v hv
    exact (hv.unique he) ▸ ih

/-! ## `Reftype_sub` -/

/-- `REF X ht`, evaluated. -/
theorem ev_ref {ρ : VarEnv} {X : Exp} {ht : IL.Id} {w : Value}
    (h : EvalExp 𝔼 ρ (.caseE "REF" (.tupE [X, .varE ht])) w) :
    ∃ m hv, w = .case "REF" (.tuple [m, hv]) ∧ EvalExp 𝔼 ρ X m ∧ ρ.findVal? ht = some hv := by
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨m, hv, rfl, h₁, h₂⟩ := RefOkV.evalExp_tup2_inv hu
  exact ⟨m, hv, rfl, h₁, evalExp_varE_iff.1 h₂⟩

/-- One rule of `Reftype_sub` in `{}`: `REF X ht_1 <: REF Y ht_2` from `ht_1 <: ht_2`, when `Y`
fixes the target's nullability `n₂` and the result is `SubE`. -/
theorem refSub_rule {O : ElseI} {els : Prop} {σ : List (IL.Id × Value)} {X Y : Exp}
    {p : CRefType} {w : Value} {n₂ : Bool}
    (hY : ∀ m, EvalExp 𝔼 (VarEnv.empty.bindVals σ) Y m → m = nullV n₂)
    (hmk : ∀ n₁ (h₁ h₂ : CHeapType), p = .ref n₁ h₁ → EvalExp 𝔼 (VarEnv.empty.bindVals σ) X
      (nullV n₁) → SubE h₁ h₂ → SubE p (.ref n₂ h₂))
    (he : EvalExp 𝔼 (VarEnv.empty.bindVals σ) (.tupE [.varE "C", .caseE "REF" (.tupE [X,
      .varE "ht_1"]), .caseE "REF" (.tupE [Y, .varE "ht_2"])]) (.tuple [ctx0V, tyV p, w]))
    (hp : DPremB 𝔼 O els (VarEnv.empty.bindVals σ) (.rulePr "Heaptype_sub" [] "%|-%<:%"
      (.tupE [.varE "C", .varE "ht_1", .varE "ht_2"]))) :
    ∃ rt, w = tyV rt ∧ SubE p rt := by
  obtain ⟨hC, h₂, h₃⟩ := concl_C he
  obtain ⟨n₁, h₁, rfl⟩ : ∃ n₁ h₁, p = Ty.ref n₁ h₁ := by cases p; exact ⟨_, _, rfl⟩
  obtain ⟨m₁, hv₁, e₁, hX, hH₁⟩ := ev_ref h₂
  simp only [tyV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, and_true,
    true_and] at e₁
  obtain ⟨m₂, hv₂, rfl, hY', hH₂⟩ := ev_ref h₃
  have hR : HsRes hv₁ hv₂ := (subM_of_dderivesB (prem_rule3 hC hH₁ hH₂ hp)).1 rfl _ _ rfl
  obtain ⟨h₂', e₂, hs⟩ := hR.1 h₁ e₁.2.symm
  refine ⟨.ref n₂ h₂', ?_, hmk n₁ h₁ h₂' rfl (e₁.1 ▸ hX) hs⟩
  rw [hY m₂ hY', e₂]
  rfl

/-- `Reftype_sub/nonnull` in `{}`. -/
theorem refSub_nonnull {O : ElseI} {els : Prop} {σ : List (IL.Id × Value)} {p : CRefType}
    {w : Value}
    (he : EvalExp 𝔼 (VarEnv.empty.bindVals σ) (.tupE [.varE "C", .caseE "REF" (.tupE [.optE none,
      .varE "ht_1"]), .caseE "REF" (.tupE [.optE none, .varE "ht_2"])]) (.tuple [ctx0V, tyV p, w]))
    (hp : DPremB 𝔼 O els (VarEnv.empty.bindVals σ) (.rulePr "Heaptype_sub" [] "%|-%<:%"
      (.tupE [.varE "C", .varE "ht_1", .varE "ht_2"]))) :
    ∃ rt, w = tyV rt ∧ SubE p rt := by
  refine refSub_rule (n₂ := false) (fun m hm => evalExp_optE_none_iff.1 hm) ?_ he hp
  intro n₁ h₁ h₂ hp' hX hs
  have hn : nullV n₁ = .opt none := evalExp_optE_none_iff.1 hX
  have hn₁ : n₁ = false := by cases n₁ <;> simp_all [nullV]
  rw [hp', hn₁]
  exact .refNonNull hs

/-- `Reftype_sub/null` in `{}`, at any alternative `X` of `NULL?`. -/
theorem refSub_null {O : ElseI} {els : Prop} {σ : List (IL.Id × Value)} {p : CRefType}
    {w : Value} {X : Exp}
    (he : EvalExp 𝔼 (VarEnv.empty.bindVals σ) (.tupE [.varE "C", .caseE "REF" (.tupE [X,
      .varE "ht_1"]), .caseE "REF" (.tupE [.optE (some (.caseE "NULL" (.tupE []))),
        .varE "ht_2"])]) (.tuple [ctx0V, tyV p, w]))
    (hp : DPremB 𝔼 O els (VarEnv.empty.bindVals σ) (.rulePr "Heaptype_sub" [] "%|-%<:%"
      (.tupE [.varE "C", .varE "ht_1", .varE "ht_2"]))) :
    ∃ rt, w = tyV rt ∧ SubE p rt :=
  refSub_rule (n₂ := true) (fun _ hm => hm.unique (evalExp_optE_some_iff.2
    ⟨_, evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩), rfl⟩))
    (fun _ _ _ hp' _ hs => hp' ▸ .refNull hs) he hp

/-- **`AgreeTy.subElim`, on the concrete `B`**: `Reftype_sub {}` from the image of a reference
type `p` is `SubE` to the image of a reference type. -/
theorem subElim_BI (O : ElseI) (p : CRefType) (w : Value)
    (h : DDerivesB 𝔼 O "Reftype_sub" "%|-%<:%" [] (.tuple [RefOkV.ctxEmptyV, tyV p, w])) :
    ∃ rt, w = tyV rt ∧ SubE p rt := by
  obtain ⟨i, nm, qs, e, e', prems, σ, hr, halt, -, he, hp⟩ := dderivesB_inv findRel_reftypeSub h
  rcases i with _ | _ | i
  all_goals simp only [reftypeSubRules, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq, Rule.ruleD.injEq, List.getElem?_nil, reduceCtorEq] at hr
  all_goals obtain ⟨rfl, rfl, -, rfl, rfl⟩ := hr
  · exact refSub_nonnull ((concl_eq halt rfl) ▸ he) (hp _ (List.mem_singleton_self _))
  · simp [conclAlts, hasOptNil, hasOptNilL, hasOptNilO, optAlts, optAltsL, optAltsO,
      prod2] at halt
    obtain ⟨X, rfl⟩ : ∃ X, e' = .tupE [.varE "C", .caseE "REF" (.tupE [X, .varE "ht_1"]),
        .caseE "REF" (.tupE [.optE (some (.caseE "NULL" (.tupE []))), .varE "ht_2"])] := by
      rcases halt with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
    exact refSub_null he (hp _ (List.mem_singleton_self _))

end Silmaril.Wasm.SpecTec.Sim.Round6.TyElim
