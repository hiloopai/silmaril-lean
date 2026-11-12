module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.Read2.Common

/-!
# Round 5, pass 3, track read: `struct.new_default` (69), backward

`z; (STRUCT.NEW_DEFAULT x) ~> val* (STRUCT.NEW x)` with `Expand($type(z, x), STRUCT (%% mut? zt)*)`
and the iterated premise `($default_($unpack(zt)) = ?(val))*` over `val*`, `zt*`. Read back:

* the `Expand` premise gives the struct type and binds `zt*` to the images of its fields' storage
  types (`BwdStep.ztStar_of_expand`);
* `$default_(t)` is `?(v)` for Core's default `v` and `ε` (`REF ht`) or undefined (`BOT`) for a
  type without one (`default_inv`), so each round of the premise gives a Core default and the
  matching `val` (`default_row`);
* the defaults of all fields exist, so Core's `mapM` succeeds, and `val*` is its image.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Read2

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies TryClausesUndef applies_iff_callDef)
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Integrate (applies_default_of vkPat skip_vk)
open Round4Int (BI)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}

/-! ## `$default_`, inverted -/

/-- `$default_(REF ht) = ε`, at any heap-type value `ht`. -/
theorem applies_default_refNonNull {B : Builtins} (hv : Value) :
    Applies (simEnv B) "default_" [.val (.case "REF" (.tuple [.opt none, hv]))] (.opt none) :=
  applies_default_of (skip_vk (FwdSimdAgg.argSubOk_vk_refC "Inn" (.inl rfl) _)
    (skip_vk (FwdSimdAgg.argSubOk_vk_refC "Fnn" (.inr (.inl rfl)) _)
      (skip_vk (FwdSimdAgg.argSubOk_vk_refC "Vnn" (.inr (.inr rfl)) _)
        (tryClauses_skip_match (matchArgs_cons_undef
          (Silmaril.SpecTec.Equiv.ExecBuiltins.matchArg_expA_undef (Integrate.matchUndef_refNull _)))
          (tryClauses_hit (matchArgs_cons (matchArg_expA (Integrate.match_ref _)) matchArgs_nil)
            premsHold_nil (by simpa using (evalExp_optE_none_iff (env := simEnv B)
              (ρ := VarEnv.empty.bindVal "ht" hv)).2 rfl))))))

theorem call_default_none (ws : List ArgV) : (BI P hn host).call "default_" ws = none := by
  simp [Round4Int.BI, Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall,
    Floats.floatNames]

set_option maxRecDepth 100000 in
/-- `$default_(BOT)` is undefined: no clause matches and `B` does not answer. -/
theorem not_applies_default_bot {u : Value} :
    ¬ Applies (simEnv (BI P hn host)) "default_" [.val (tyV (Ty.botv : CValType))] u := by
  rintro ⟨ps, ty, cs, hd, hc⟩
  obtain ⟨ps', ty', hd'⟩ := Integrate.findDef_default (BI P hn host)
  rw [hd'] at hd
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hd
  have hU : TryClausesUndef (simEnv (BI P hn host)) Integrate.defaultClauses
      [.val (tyV (Ty.botv : CValType))] :=
    IntNumeric.tryClausesUndef_skip_match (matchArgs_cons_undef
      (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub rfl))
    (IntNumeric.tryClausesUndef_skip_match (matchArgs_cons_undef
      (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub rfl))
    (IntNumeric.tryClausesUndef_skip_match (matchArgs_cons_undef
      (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub rfl))
    (IntNumeric.tryClausesUndef_skip_match (matchArgs_cons_undef (matchArg_expA_undef
      (Equiv.ExecBuiltins.matchExp_caseE_undef_of_ne (op := "REF") (op' := "BOT")
        (w := .tuple []) (by decide))))
    (IntNumeric.tryClausesUndef_skip_match (matchArgs_cons_undef (matchArg_expA_undef
      (Equiv.ExecBuiltins.matchExp_caseE_undef_of_ne (op := "REF") (op' := "BOT")
        (w := .tuple []) (by decide))))
      IntNumeric.tryClausesUndef_nil))))
  rcases hc with hc | ⟨-, hb⟩
  · exact Equiv.ExecNumeric.not_tryClauses_and_undef hc hU
  · rw [simEnv, Env.builtins_withBuiltins, call_default_none] at hb
    cases hb

/-- **`$default_(t)`, read back**: Core's default of `t`, as an option. -/
theorem default_inv (t : CValType) {u : Value}
    (h : Applies (simEnv (BI P hn host)) "default_" [.val (tyV t)] u) :
    u = .opt ((defaultVal? t).map valV) := by
  cases hd : defaultVal? t with
  | some v => exact Applies.unique h (FwdSimdAgg.applies_default_closed t hd)
  | none =>
    match t, hd with
    | .refv (.ref false hv), _ => exact Applies.unique h (applies_default_refNonNull _)
    | .botv, _ => exact absurd h not_applies_default_bot

/-! ## The rounds of the premise -/

/-- Two variable domains, evaluated. -/
theorem evalDoms_two {env : Env} {n : Nat} {ρ : VarEnv} {x₁ y₁ x₂ y₂ : IL.Id}
    {xvs : List (IL.Id × Value)}
    (h : evalDoms n env ρ [.mk x₁ (.varE y₁), .mk x₂ (.varE y₂)] = .ok xvs) :
    ∃ v₁ v₂, ρ.findVal? y₁ = some v₁ ∧ ρ.findVal? y₂ = some v₂ ∧ xvs = [(x₁, v₁), (x₂, v₂)] := by
  cases n with
  | zero => simp [evalDoms] at h
  | succ n =>
      simp only [evalDoms, List.mapM_cons, List.mapM_nil, domVar, domSrc] at h
      cases h₁ : evalExp n env ρ (.varE y₁) with
      | error e => simp [h₁] at h
      | ok v₁ =>
        cases h₂ : evalExp n env ρ (.varE y₂) with
        | error e => simp [h₁, h₂] at h
        | ok v₂ =>
          simp [h₁, h₂] at h
          exact ⟨v₁, v₂, evalExp_varE_iff.1 ⟨n, h₁⟩, evalExp_varE_iff.1 ⟨n, h₂⟩, h.symm⟩

/-- **One round of `$default_($unpack(zt)) = ?(val)`, read back.** -/
theorem default_row {ρ : VarEnv} (hρ : ValsOnly ρ) {zt : CStorageType} {V : Value}
    (fzt : ρ.findVal? "zt" = some (tyV zt)) (fval : ρ.findVal? "val" = some V)
    (h : EvalExp (simEnv (BI P hn host)) ρ (.cmpE .eqOp .boolT
      (.callE "default_" [.expA (.callE "unpack" [.expA (.varE "zt")])])
      (.optE (some (.varE "val")))) (.bool true)) :
    ∃ v, defaultVal? zt.unpack = some v ∧ V = valV v := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 h
  obtain rfl := Silmaril.SpecTec.Equiv.ExecNumeric.cmpValues_eq_true_iff.1 hc
  have e₂ := EvalExp.unique h₂ (evalExp_optE_some_iff.2 ⟨_, evalExp_var fval, rfl⟩)
  subst e₂
  obtain ⟨ws, hws⟩ := BwdStep.args_of_call h₁
  obtain ⟨U, ws', hU, hws', rfl⟩ := BwdStep.evalArgs_cons_inv hws
  obtain rfl := Equiv.Validation.evalArgs_nil_iff.1 hws'
  have eU := EvalExp.unique hU (Vec.evalExp_call (Prims.findDef_none_of_valsOnly hρ _)
    (Vec.evalArgs_var fzt Equiv.evalArgs_nil) (R4Fwd.applies_unpack_any zt))
  subst eU
  have hA := default_inv zt.unpack ((applies_iff_callDef (Prims.findDef_none_of_valsOnly hρ _)
    (Equiv.evalArgs_cons hU Equiv.evalArgs_nil)).2 (evalExp_callE_iff.1 h₁))
  cases hd : defaultVal? zt.unpack with
  | none => simp [hd] at hA
  | some v =>
    simp only [hd, Option.map_some, Value.opt.injEq, Option.some.injEq] at hA
    exact ⟨v, rfl, hA⟩

theorem findVal_row_zt {ρ : VarEnv} {a b : Value} :
    (ρ.bindVals [("val", a), ("zt", b)]).findVal? "zt" = some b := by
  simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind]

theorem findVal_row_val {ρ : VarEnv} {a b : Value} :
    (ρ.bindVals [("val", a), ("zt", b)]).findVal? "val" = some a := by
  simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind]

theorem findVal_one {ρ : VarEnv} {x : IL.Id} (hx : x ≠ "_") {a : Value} :
    (ρ.bindVals [(x, a)]).findVal? x = some a := by
  simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind, hx]

/-- `mapM` of a partial function defined on every element. -/
theorem mapM_some_of {α β : Type} (g : α → Option β) :
    ∀ (l : List α), (∀ a ∈ l, (g a).isSome) →
      ∃ vs, l.mapM g = some vs ∧ vs.length = l.length ∧
        ∀ j (h₁ : j < l.length) (h₂ : j < vs.length), g l[j] = some vs[j]
  | [], _ => ⟨[], rfl, rfl, fun j h₁ => absurd h₁ (Nat.not_lt_zero _)⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h a List.mem_cons_self)
    obtain ⟨vs, hvs, hlen, hget⟩ := mapM_some_of g l fun a ha => h a (List.mem_cons_of_mem _ ha)
    refine ⟨b :: vs, by simp [List.mapM_cons, hb, hvs], by simp [hlen], fun j h₁ h₂ => ?_⟩
    cases j with
    | zero => simpa using hb
    | succ j => simpa using hget j (by simpa using h₁) (by simpa using h₂)

theorem head_structNewDefault {a : Admin} (h : Typing.adminHead a = "STRUCT.NEW_DEFAULT") :
    ∃ x, a = .plain (.structNewDefault x) := by
  revert h
  admin_head_inv

/-- **`Step_read` 69 (`struct.new_default`), backward.** -/
theorem bwd_structNewDefault : ∀ (c : Config H) (w : Value),
    Fires (simEnv (BI P hn host)) "Step_read" 69 (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩ := by
  rintro ⟨s, f, is⟩ w hf
  have RR := State.hasReadRules_simEnv (BI P hn host)
  obtain ⟨σ, hq, he, hp⟩ := ruleBody_scope (fires_body RR.structNewDefault hf)
  have hρ := valsOnly_bindVals σ
  obtain ⟨hz, hcode⟩ := RefsGC.cfgz_inv (z := stateV hn s f) (l := adminsToV is)
    (RefsGC.lhs_of_concl he)
  have fz := evalExp_varE_iff.1 hz
  obtain ⟨a, is', rfl, h₁, hrest⟩ := BwdPureStep.evalExps_admins_cons (RefsGC.elems_of_list hcode)
  obtain rfl := BwdPureStep.evalExps_admins_nil hrest
  obtain ⟨x, rfl⟩ := head_structNewDefault (BwdPureStep.head_of_caseE h₁)
  have fx : (VarEnv.empty.bindVals σ).findVal? "x" = some (Encode.toValue x) :=
    BwdPureStep.idx_of_var' h₁ rfl
  -- the premise `$type(z, x) ~~ STRUCT (%% mut? zt)*`
  obtain ⟨we, hwe, hD⟩ := RefsGC.premW_rule (hp _ List.mem_cons_self)
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hwe
  obtain ⟨v₁, vs', h₁', hvs', rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨d, hd, rfl⟩ := BwdStep.type_inv hρ fz fx h₁'
  obtain ⟨v₂, vs'', h₂', hvs'', rfl⟩ := evalExps_cons_iff.1 hvs'
  obtain rfl := evalExps_nil_iff.1 hvs''
  obtain ⟨ct, hct, rfl⟩ := R4Fwd.expandInv_builtins hn host _ d _ hD
  obtain ⟨fs, rfl⟩ := BwdStep.struct_of_tyV h₂'
  obtain ⟨l, fzt, rfl⟩ := BwdStep.ztStar_of_expand h₂'
  -- the iterated premise
  obtain ⟨xvs, dls, k, ⟨n, hdoms⟩, hdl, hlen, hrows⟩ : ∃ xvs dls k,
      EvalDoms (simEnv (BI P hn host)) (VarEnv.empty.bindVals σ)
        [.mk "val" (.varE "val*"), .mk "zt" (.varE "zt*")] xvs ∧ domLists xvs = some dls ∧
      (∀ d ∈ dls, d.2.length = k) ∧ ∀ r ∈ iterRows dls none k,
        EvalExp (simEnv (BI P hn host)) ((VarEnv.empty.bindVals σ).bindVals r) (.cmpE .eqOp .boolT
          (.callE "default_" [.expA (.callE "unpack" [.expA (.varE "zt")])])
          (.optE (some (.varE "val")))) (.bool true) := by
    cases hp _ (List.mem_cons_of_mem _ List.mem_cons_self) with
    | iterList _ hdoms _ hdl hlen hrows =>
      exact ⟨_, _, _, hdoms, hdl, hlen, fun r hr => ifPrem (hrows r hr)⟩
  obtain ⟨V, ZT, fval, fzt', rfl⟩ := evalDoms_two hdoms
  rw [fzt, Option.some.injEq] at fzt'
  subst fzt'
  have hV : ∃ lv, V = .list lv := by
    cases V with
    | list lv => exact ⟨lv, rfl⟩
    | _ => simp [domLists, Value.asList?] at hdl
  obtain ⟨lv, rfl⟩ := hV
  have edl : dls = [("val", lv), ("zt", fs.toList.map (tyV ∘ fieldStorage))] := by
    simpa [domLists, Value.asList?] using hdl.symm
  subst edl
  have hk₁ : lv.length = k := hlen _ List.mem_cons_self
  have hk₂ : (fs.toList.map (tyV ∘ fieldStorage)).length = k :=
    hlen _ (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [List.length_map] at hk₂
  -- each round gives a default
  have hrow : ∀ j (hj₁ : j < lv.length) (hj₂ : j < fs.toList.length),
      ∃ v, defaultVal? (fieldStorage fs.toList[j]).unpack = some v ∧ lv[j] = valV v := by
    intro j hj₁ hj₂
    have hr := hrows _ (List.mem_map.2 ⟨j, List.mem_range.2 (by omega), rfl⟩)
    have erow : iterRow [("val", lv), ("zt", fs.toList.map (tyV ∘ fieldStorage))] none j =
        [("val", lv[j]), ("zt", tyV (fieldStorage fs.toList[j]))] := by
      simp [iterRow, List.getElem?_eq_getElem hj₁, List.getElem?_eq_getElem hj₂]
    rw [erow] at hr
    exact default_row (ρ := (VarEnv.empty.bindVals σ).bindVals
      [("val", lv[j]), ("zt", tyV (fieldStorage fs.toList[j]))]) ⟨hρ.1, hρ.2.1, hρ.2.2⟩
      findVal_row_zt findVal_row_val hr
  obtain ⟨vs, hvs, hvl, hget⟩ := mapM_some_of (fun ft => defaultVal? (fieldStorage ft).unpack)
    fs.toList fun a ha => by
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      obtain ⟨v, hv, -⟩ := hrow j (by omega) hj
      simp [hv]
  have elv : lv = vs.map valV := by
    refine List.ext_getElem (by simp [hvl]; omega) fun j h₁ h₂ => ?_
    have hj₂ : j < fs.toList.length := by omega
    obtain ⟨v, hv, e⟩ := hrow j h₁ hj₂
    have hv' := hget j hj₂ (by omega)
    rw [hv] at hv'
    rw [e, List.getElem_map, Option.some.inj hv']
  subst elv
  -- the right-hand side
  have hw := EvalExp.unique (RefsGC.rhs_of_concl he) (evalExp_cat
    (Sim.evalExp_iterMap (g := fun w => w) fval (fun w _ => RefsGC.evalExp_sub_of (evalExp_var
      (findVal_one (by decide)))))
    (evalExp_list1 (evalExp_case (evalExp_var fx))))
  refine ⟨vals vs ++ [.plain (.structNew x)], ?_, .aggregate (.structNewDefault hd hct hvs)⟩
  rw [hw, adminsToV_append, adminsToV_vals, List.map_id']
  rfl

end Silmaril.Wasm.SpecTec.Sim.Round5.Read2
