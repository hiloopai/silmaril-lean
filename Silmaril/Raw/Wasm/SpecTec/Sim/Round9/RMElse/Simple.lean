module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.RMElse.NcTyp
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.RMElse.Fires
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.RMElse.CheckTyp
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.RMElse.CheckPairs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.RMElse.CheckChain
public import Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.Thms

/-!
# Round 9, rm: the backward firing at the simple pairs, along code erasure (unrefined)

Round 9's `ElseBwd.reflect_core` (RE, `eraseV`) ported to `eraseC` and the declarative reading.

Rule `i` fired at `(a, b)` with `a = z; L` (`lhsRuleC`), so `a = (zv; lv)` where `lv` holds no
`CODE` record (`fired_cfgC`): the quantifiers `L` reads have `CODE`-free types, so their values
are fixed by `eraseC` (`ncB_of_quant`, from the typing sweep `NcTyp` and the kernel check
`goodTypsC_fixed`). The earlier rule `j` fires on the erased side at `(eraseC a, c')` in an
instance `σ'` whose state quantifier is `eraseC zv`; rebinding it to `zv` gives `σ' ++ [(z, zv)]`.
Its other quantifiers are `CODE`-free, so `eraseScope` of the new instance agrees with `σ'` on the
rule's variables, and round 8's equation `CodeErase.EraseAll.eraseAt` reads the conclusion and the
`if` premises back. The quantifier types do not mention `z` (`tyZ`), so they type the same values
in the new instance (`hasTyp_offZ`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMElse

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites (TypsNx)
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll (Hyps grC gdC xRule xPrem eraseAt)
open Silmaril.Wasm.SpecTec.Sim.Round8.FiresC (QT)
open Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd (FiredD PairReflectD cfgVar stateQ)

variable {B : Builtins}

/-! ## `CODE`-free values -/

/-- **The `goodC` types of `simEnv B` are `CODE`-free.** -/
theorem envNC_simEnv (B : Builtins) : EnvNC goodC (simEnv B) := by
  intro x td h hx
  have hm := TypAgree.mem_typs_of_findTyp (B := B) h
  have h1 := List.all_eq_true.1 goodTypsC_fixed _ hm
  simp only [hx, Bool.not_true, Bool.false_or, List.all_eq_true] at h1
  exact h1

/-- A quantifier of `CODE`-free type has a `CODE`-free value. -/
theorem ncB_of_quant {ρ : VarEnv} (hρ : ρ.typs = []) {qs : List Param}
    (hq : QuantsOk (simEnv B) ρ qs) {x : IL.Id} {t : Typ} (hx : Param.expP x t ∈ qs)
    (ht : ncT t = true) :
    ∃ w, ρ.findVal? x = some w ∧ ncB w = true ∧ HasTyp (simEnv B) ρ t w := by
  obtain ⟨w, hw, hty⟩ := hq x t hx
  have hT : TypsNx goodC ρ := fun p hp => by rw [hρ] at hp; cases hp
  exact ⟨w, hw, ncB_of_HasTyp (envNC_simEnv B) hT ht hty, hty⟩

theorem mem_ncNames {qs : List Param} {x : IL.Id} (h : x ∈ ncNames qs) :
    ∃ t, Param.expP x t ∈ qs ∧ ncT t = true := by
  simp only [ncNames, List.mem_filterMap] at h
  obtain ⟨q, hq, hx⟩ := h
  cases q with
  | expP y t =>
    by_cases ht : ncT t = true
    · simp only [ht, ↓reduceIte, Option.some.injEq] at hx
      subst hx
      exact ⟨t, hq, ht⟩
    · simp [ht] at hx
  | _ => cases hx

/-! ## Scopes that differ at one variable -/

/-- **Two term scopes without type variables that agree off `z`.** -/
def OffZ (z : IL.Id) (ρ ρ' : VarEnv) : Prop :=
  ρ.typs = [] ∧ ρ'.typs = [] ∧ ∀ s : Sets, z ∉ s.varid → VarEnv.AgreeOn s ρ ρ'

theorem localTyp_nil {ρ : VarEnv} (hρ : ρ.typs = []) (x : IL.Id) (args : List Arg) :
    localTyp? ρ x args = none := by
  cases args <;> simp [localTyp?, VarEnv.findTyp?, hρ]

/-- **`hasTyp` reads a `tyZ z` type alike in two scopes that agree off `z`.** -/
theorem hasTyp_offZ {env : Env} {z : IL.Id} {ρ ρ' : VarEnv} (h : OffZ z ρ ρ') : ∀ n,
    (∀ t v, tyZ z t = true → hasTyp n env ρ t v = hasTyp n env ρ' t v) ∧
    (∀ t vs, tyZ z t = true → hasTypList n env ρ t vs = hasTypList n env ρ' t vs)
  | 0 => ⟨fun _ _ _ => by simp [hasTyp], fun _ _ _ => by simp [hasTypList]⟩
  | n + 1 => by
    obtain ⟨ih₁, ih₂⟩ := hasTyp_offZ h n
    refine ⟨fun t v ht => ?_, fun t vs ht => ?_⟩
    · cases t with
      | boolT => simp only [hasTyp]
      | numT _ => simp only [hasTyp]
      | textT => simp only [hasTyp]
      | tupT _ => simp [tyZ] at ht
      | varT x args =>
        have ha : evalArgs n env ρ args = evalArgs n env ρ' args :=
          evalArgs_agreeOn (h.2.2 _ (by simpa [tyZ] using ht))
        simp only [hasTyp, localTyp_nil h.1, localTyp_nil h.2.1, ha]
      | iterT t it =>
        cases it with
        | opt =>
          have e₁ : ∀ w, hasTyp n env ρ t w = hasTyp n env ρ' t w := fun w => ih₁ t w ht
          simp only [hasTyp, e₁]
        | list =>
          have e₂ : ∀ ws, hasTypList n env ρ t ws = hasTypList n env ρ' t ws :=
            fun ws => ih₂ t ws ht
          simp only [hasTyp, e₂]
        | list1 =>
          have e₂ : ∀ ws, hasTypList n env ρ t ws = hasTypList n env ρ' t ws :=
            fun ws => ih₂ t ws ht
          simp only [hasTyp, e₂]
        | listN _ _ => simp [tyZ] at ht
    · cases vs with
      | nil => simp only [hasTypList]
      | cons v vs => simp only [hasTypList, ih₁ t v ht, ih₂ t vs ht]

theorem hasTyp_of_offZ {env : Env} {z : IL.Id} {ρ ρ' : VarEnv} (h : OffZ z ρ ρ') {t : Typ}
    {v : Value} (ht : tyZ z t = true) (hv : HasTyp env ρ t v) : HasTyp env ρ' t v := by
  obtain ⟨n, hn⟩ := hv
  exact ⟨n, ((hasTyp_offZ h n).1 t v ht) ▸ hn⟩

theorem offZ_snoc {σ : List (IL.Id × Value)} {z : IL.Id} (u : Value) :
    OffZ z (VarEnv.empty.bindVals σ) (VarEnv.empty.bindVals (σ ++ [(z, u)])) :=
  ⟨rfl, rfl, fun _ hs => ⟨fun y hy => (ElseBwd.findVal_snoc_ne (fun h => hs (by rw [← h]; exact hy)) u).symm,
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩⟩

/-! ## The firing of rule `i` -/

theorem bindParams_nil {ps : List Param} {ρ₀ : VarEnv}
    (h : bindParams VarEnv.empty ps [] = some ρ₀) : ps = [] ∧ ρ₀ = VarEnv.empty := by
  cases ps with
  | nil => exact ⟨rfl, (Option.some.inj h).symm⟩
  | cons p ps => cases p <;> simp [bindParams] at h

theorem xRule_of {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat}
    {r : Rule} (H : Hyps QT grC gdC (simEnv B))
    (hrel : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules)) (hr : rules[i]? = some r) :
    xRule grC gdC r = true :=
  H.rels "Step_read" _ (by decide) hrel r (List.mem_of_getElem? hr)

theorem lhsOkC_parts {qs : List Param} {e : Exp} (h : lhsOkC qs e = true) :
    ∃ z l, cfgVar e = some (z, l) ∧ stateQ qs z = true ∧
      EraseDer.varsIn (ncNames qs) (freeExp l) = true ∧ z ∉ ncNames qs := by
  unfold lhsOkC at h
  split at h
  · rename_i z l hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    have h2 : (ncNames qs).contains z = false := h.2
    exact ⟨z, l, hc, h.1.1, h.1.2, fun hm => by rw [List.contains_iff_mem.2 hm] at h2; cases h2⟩
  · cases h

/-- **The scope erasure agrees with the scope on the `CODE`-free quantifiers.** -/
theorem agree_erase_nc {qs : List Param} {σ : List (IL.Id × Value)}
    (hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ) qs) {s : Sets}
    (hs : EraseDer.varsIn (ncNames qs) s = true) :
    VarEnv.AgreeOn s (VarEnv.empty.bindVals σ) (eraseScope (VarEnv.empty.bindVals σ)) := by
  refine ⟨fun y hy => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  rw [Round8.CodeErase.Erase.find?_eraseScope]
  obtain ⟨t, ht, hnc⟩ := mem_ncNames (EraseDer.varsIn_mem hs y hy)
  obtain ⟨w, hw, hnw, -⟩ := ncB_of_quant rfl hq ht hnc
  rw [hw]
  simp [eraseC_of_ncB w hnw]

/-- **The left-hand side of a firing of rule `i`** is `(zv; lv)` with `lv` fixed by `eraseC`
and `zv` of type `state`. -/
theorem fired_cfgC (H : Hyps QT grC gdC (simEnv B)) {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {i : Nat} {ri : Rule} {a b : Value}
    (hrel : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules))
    (hri : rules[i]? = some ri) (hli : lhsRuleC ri = true)
    (hF : FiredD (simEnv B) "Step_read" [] i (.tuple [a, b])) :
    ∃ zv lv, a = .case "%;%" (.tuple [zv, lv]) ∧ eraseC lv = lv ∧
      HasTyp (simEnv B) VarEnv.empty (.varT "state" []) zv := by
  obtain ⟨ps', op', t', rules', nm, qs, e, prems, ρ₀, σ, hrel', hrule, hps, hq, hev⟩ := hF
  rw [hrel] at hrel'
  cases hrel'
  rw [hrule] at hri
  cases hri
  obtain ⟨-, rfl⟩ := bindParams_nil hps
  have hxr := xRule_of H hrel hrule
  simp only [xRule, Bool.and_eq_true] at hxr
  simp only [lhsRuleC] at hli
  obtain ⟨z, l, hc, hsq, hl, -⟩ := lhsOkC_parts hli
  obtain ⟨r, rfl⟩ := ElseBwd.cfgVar_some hc
  obtain ⟨n, hn⟩ := hev
  obtain ⟨k, zv, lv, rv, hk, hw, hz, hlv⟩ := ElseBwd.eval_cfg hn
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hw
  obtain ⟨rfl, -⟩ := hw
  have hE := ((eraseAt H n).exp _ _ (Round8.FiresC.sg_bindVals Round8.CodeErase.EraseAll.sg_empty σ) hxr.1).1
  rw [hn] at hE
  obtain ⟨k', zv', lv', rv', hk', hw', -, hlv'⟩ := ElseBwd.eval_cfg hE
  have hkk : k' = k := by omega
  subst hkk
  rw [← evalExp_agreeOn (agree_erase_nc hq hl), hlv] at hlv'
  cases hlv'
  refine ⟨zv, lv, rfl, ?_, ?_⟩
  · simp only [eraseC, eraseCs, Value.tuple.injEq, List.cons.injEq, Value.case.injEq, true_and,
      and_true] at hw'
    exact hw'.1.2
  · obtain ⟨tz, htz⟩ := ElseBwd.mem_quantNames (ElseBwd.stateQ_mem hsq)
    have htz' := ElseBwd.stateQ_type hsq htz
    subst htz'
    obtain ⟨w, hw, hty⟩ := hq z _ htz
    rw [hz] at hw
    cases hw
    exact ElseBwd.hasTyp_varT_scope rfl rfl hty

/-! ## `Expand` concludes `CODE`-free values -/

theorem pairVars_some {e : Exp} {x y : IL.Id} (h : pairVars e = some (x, y)) :
    e = .tupE [.varE x, .varE y] := by
  unfold pairVars at h
  split at h
  · cases h; rfl
  · cases h

theorem bindParams_nil_ps {avs : List ArgV} {ρ₀ : VarEnv}
    (h : bindParams VarEnv.empty [] avs = some ρ₀) : ρ₀ = VarEnv.empty := by
  cases avs with
  | nil => exact (Option.some.inj h).symm
  | cons _ _ => simp [bindParams] at h

/-- **A relation that passes `relNC` derives only `CODE`-free values.** -/
theorem dderives_ncB {O : ElseI} {x : IL.Id} {op : MixopS} {avs : List ArgV} {w : Value}
    (hx : relNC (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) x = true)
    (h : Sim.DDerives (simEnv B) O x op avs w) : ncB w = true := by
  cases h with
  | rule hrel hrule hps hq he _ =>
    rename_i ps t rules i nm qs e prems ρ₀ σ
    unfold relNC at hx
    rw [← Round8.FiresC.findRel?_simEnv (B := B), hrel] at hx
    simp only [Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff] at hx
    obtain ⟨rfl, hall⟩ := hx
    obtain rfl := bindParams_nil_ps hps
    have hc := hall _ (List.mem_of_getElem? hrule)
    simp only [concl2C] at hc
    split at hc
    · rename_i y₁ y₂ hpv
      obtain rfl := pairVars_some hpv
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hc
      obtain ⟨n, hn⟩ := he
      obtain ⟨k, u₁, u₂, -, h₁, h₂, rfl⟩ := Round8.NxElse.evalExp_pair hn
      obtain ⟨t₁, ht₁, hn₁⟩ := mem_ncNames hc.1
      obtain ⟨t₂, ht₂, hn₂⟩ := mem_ncNames hc.2
      obtain ⟨w₁, hw₁, hc₁, -⟩ := ncB_of_quant rfl hq ht₁ hn₁
      obtain ⟨w₂, hw₂, hc₂, -⟩ := ncB_of_quant rfl hq ht₂ hn₂
      rw [ElseBwd.evalExp_varE h₁] at hw₁
      rw [ElseBwd.evalExp_varE h₂] at hw₂
      cases hw₁
      cases hw₂
      simp [ncB, ncBs, hc₁, hc₂]
    · cases hc

/-! ## The earlier rule, backward -/

/-- The parts of `simpleRuleCE`. -/
theorem simpleRuleCE_parts {nm : IL.Id} {qs : List Param} {op : MixopS} {e : Exp}
    {prems : List Prem} (h : simpleRuleCE (.ruleD nm qs op e prems) = true) :
    ∃ z l, cfgVar e = some (z, l) ∧ lhsOkC qs e = true ∧ quantsNC qs z = true ∧ z ≠ "_" ∧
      EraseDer.varsIn (Determ.quantNames qs) (freeExp e) = true ∧
      ∀ pr ∈ prems, (∃ c, pr = .ifPr c ∧ EraseDer.varsIn (Determ.quantNames qs) (freeExp c) = true)
        ∨ pr = .elsePr ∨ (∃ o c, pr = .rulePr "Expand" [] o c ∧
          EraseDer.varsIn (Determ.quantNames qs) (freeExp c) = true) := by
  simp only [simpleRuleCE, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hsc, hfe⟩, hsp⟩ := h
  split at hsc
  · rename_i z l hc
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hsc
    refine ⟨z, l, hc, hsc.1.1, hsc.1.2, hsc.2, hfe, fun pr hpr => ?_⟩
    have h' := hsp pr hpr
    cases pr with
    | ifPr c => exact .inl ⟨c, rfl, h'⟩
    | elsePr => exact .inr (.inl rfl)
    | rulePr x args o c =>
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h'
      obtain ⟨⟨rfl, rfl⟩, hc⟩ := h'
      exact .inr (.inr ⟨o, c, rfl, hc⟩)
    | _ => cases h'
  · cases hsc

theorem quantsNC_at {qs : List Param} {z : IL.Id} (h : quantsNC qs z = true) {y : IL.Id}
    {t : Typ} (hy : Param.expP y t ∈ qs) (hyz : y ≠ z) : ncT t = true ∧ tyZ z t = true := by
  simp only [quantsNC, List.all_eq_true] at h
  have := h _ hy
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at this
  exact this.resolve_left hyz

/-- **The backward firing at a rule `j` that passes `simpleRuleCE`**, given that its `otherwise`
premise, if it has one, goes back from the erased left-hand side (`hEl`). -/
theorem reflect_coreC (H : Hyps QT grC gdC (simEnv B)) {ps : List Param} {op : MixopS} {t : Typ}
    {rules : List Rule} {i j : Nat} {ri : Rule} {nm : IL.Id} {qs : List Param} {opj : MixopS}
    {e : Exp} {prems : List Prem} {a b c' : Value}
    (hrel : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules))
    (hri : rules[i]? = some ri) (hr : rules[j]? = some (.ruleD nm qs opj e prems))
    (hli : lhsRuleC ri = true) (hsj : simpleRuleCE (.ruleD nm qs opj e prems) = true)
    (hFi : FiredD (simEnv B) "Step_read" [] i (.tuple [a, b]))
    (hEl : Prem.elsePr ∈ prems → ∀ c,
      Sim.otherwiseAt (simEnv B) "Step_read" [] j (.tuple [eraseC a, c']) →
      Sim.otherwiseAt (simEnv B) "Step_read" [] j (.tuple [a, c]))
    (hbody : Sim.RuleBody (simEnv B) (Sim.DDerives (simEnv B) Sim.noElse)
      (Sim.otherwiseAt (simEnv B) "Step_read" [] j (.tuple [eraseC a, c'])) ps [] op
      (.ruleD nm qs opj e prems) (.tuple [eraseC a, c'])) :
    ∃ c, Sim.RuleBody (simEnv B) (Sim.DDerives (simEnv B) Sim.noElse)
      (Sim.otherwiseAt (simEnv B) "Step_read" [] j (.tuple [a, c])) ps [] op
      (.ruleD nm qs opj e prems) (.tuple [a, c]) := by
  obtain ⟨zv, lv, rfl, hlv, hzt⟩ := fired_cfgC H hrel hri hli hFi
  obtain ⟨hop, ρ₀, σ', hps, hq', hev', hpr'⟩ := hbody
  obtain ⟨rfl, rfl⟩ := bindParams_nil hps
  have hxr := xRule_of H hrel hr
  simp only [xRule, Bool.and_eq_true] at hxr
  obtain ⟨z, l, hcfg, hok, hqn, hzw, hfe, hsp⟩ := simpleRuleCE_parts hsj
  obtain ⟨z', l', hcfg', hsq, hl, hzn⟩ := lhsOkC_parts hok
  rw [hcfg] at hcfg'
  cases hcfg'
  obtain ⟨r0, rfl⟩ := ElseBwd.cfgVar_some hcfg
  obtain ⟨n, hn⟩ := hev'
  obtain ⟨k, zv', lv', rv', hk, hw, hz', hl'⟩ := ElseBwd.eval_cfg hn
  simp only [eraseC, eraseCs, Value.tuple.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true, hlv] at hw
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hw
  -- the new instance
  let σj := σ' ++ [(z, zv)]
  have hfz : (VarEnv.empty.bindVals σj).findVal? z = some zv := ElseBwd.findVal_snoc_self hzw zv
  have hfo : ∀ y, y ≠ z → (VarEnv.empty.bindVals σj).findVal? y =
      (VarEnv.empty.bindVals σ').findVal? y := fun y hy => ElseBwd.findVal_snoc_ne hy zv
  have hoff : OffZ z (VarEnv.empty.bindVals σ') (VarEnv.empty.bindVals σj) := offZ_snoc zv
  have hval : ∀ y ty, Param.expP y ty ∈ qs → y ≠ z → ∃ w,
      (VarEnv.empty.bindVals σ').findVal? y = some w ∧ ncB w = true ∧
        HasTyp (simEnv B) (VarEnv.empty.bindVals σ') ty w := fun y ty hy hyz =>
    ncB_of_quant rfl hq' hy (quantsNC_at hqn hy hyz).1
  have hqj : QuantsOk (simEnv B) (VarEnv.empty.bindVals σj) qs := by
    intro y ty hy
    by_cases hyz : y = z
    · subst hyz
      have := ElseBwd.stateQ_type hsq hy
      subst this
      exact ⟨zv, hfz, ElseBwd.hasTyp_varT_scope rfl rfl hzt⟩
    · obtain ⟨w, hw, -, hty⟩ := hval y ty hy hyz
      exact ⟨w, (hfo y hyz).trans hw, hasTyp_of_offZ hoff (quantsNC_at hqn hy hyz).2 hty⟩
  -- the erased new instance agrees with `σ'` on the quantifiers
  have hag : ∀ s, EraseDer.varsIn (Determ.quantNames qs) s = true →
      VarEnv.AgreeOn s (eraseScope (VarEnv.empty.bindVals σj)) (VarEnv.empty.bindVals σ') := by
    intro s hs
    refine ⟨fun y hy => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    rw [Round8.CodeErase.Erase.find?_eraseScope]
    by_cases hyz : y = z
    · subst hyz; rw [hfz, hz']; rfl
    · obtain ⟨ty, hty⟩ := ElseBwd.mem_quantNames (EraseDer.varsIn_mem hs y hy)
      obtain ⟨w, hw, hnw, -⟩ := hval y ty hty hyz
      rw [hfo y hyz, hw]
      simp [eraseC_of_ncB w hnw]
  have hsg := Round8.FiresC.sg_bindVals Round8.CodeErase.EraseAll.sg_empty σj
  -- the conclusion on the original side
  have hE := ((eraseAt H n).exp _ _ hsg hxr.1).1
  rw [evalExp_agreeOn (hag _ hfe), hn] at hE
  obtain ⟨u, hu, hue⟩ := ElseBwd.map_eq_ok hE.symm
  obtain ⟨k₂, zv₂, lv₂, rv₂, hk₂, rfl, hz₂, hl₂⟩ := ElseBwd.eval_cfg hu
  have hkk : k₂ = k := by omega
  subst hkk
  rw [hfz] at hz₂
  cases hz₂
  have hagl : VarEnv.AgreeOn (freeExp l) (VarEnv.empty.bindVals σ') (VarEnv.empty.bindVals σj) :=
    hoff.2.2 _ (fun hzl => hzn (EraseDer.varsIn_mem hl z hzl))
  rw [← evalExp_agreeOn hagl, hl'] at hl₂
  cases hl₂
  refine ⟨rv₂, hop, VarEnv.empty, σj, rfl, hqj, ⟨n, hu⟩, fun pr hpr => ?_⟩
  -- the premises on the original side
  rcases hsp pr hpr with ⟨c₀, rfl, hfc⟩ | rfl | hex
  · have hxc : xPrem grC gdC (.ifPr c₀) = true :=
      Round8.CodeErase.EraseAll.xPrems_mem hxr.2 _ hpr
    cases hpr' _ hpr with
    | ifPr h =>
      obtain ⟨n₀, hn₀⟩ := h
      have hE₀ := ((eraseAt H n₀).exp _ c₀ hsg hxc).1
      rw [evalExp_agreeOn (hag _ hfc), hn₀] at hE₀
      obtain ⟨u₀, hu₀, hue₀⟩ := ElseBwd.map_eq_ok hE₀.symm
      exact .ifPr ⟨n₀, by rw [hu₀, Round8.CodeErase.EraseAll.eraseC_eq_bool.1 hue₀]⟩
  · cases hpr' _ hpr with
    | elsePr h => exact .elsePr (hEl hpr _ h)
  · obtain ⟨o, c₀, rfl, hfc⟩ := hex
    have hxc : xPrem grC gdC (.rulePr "Expand" [] o c₀) = true :=
      Round8.CodeErase.EraseAll.xPrems_mem hxr.2 _ hpr
    simp only [xPrem, Bool.and_eq_true] at hxc
    cases hpr' _ hpr with
    | rulePr ha he hd =>
      obtain ⟨n₀, hn₀⟩ := he
      have hE₀ := ((eraseAt H n₀).exp _ c₀ hsg hxc.2).1
      rw [evalExp_agreeOn (hag _ hfc), hn₀] at hE₀
      obtain ⟨u₀, hu₀, hue₀⟩ := ElseBwd.map_eq_ok hE₀.symm
      have hnc : ncB u₀ = true := by
        rw [← Round8.CodeErase.EraseAll.ncB_eraseC, hue₀]; exact dderives_ncB expandNC hd
      rw [eraseC_of_ncB u₀ hnc] at hue₀
      subst hue₀
      obtain ⟨m, hm⟩ := ha
      exact .rulePr ⟨m, by rw [← hm]; exact evalArgs_agreeOn (VarEnv.AgreeOn.empty _ _)⟩
        ⟨n₀, hu₀⟩ hd

/-! ## The simple pairs -/

theorem pairsOk_at {f : Rule → Bool} {rules : List Rule} {l : List (Nat × Nat)}
    (h : pairsOk f rules l = true) {i j : Nat} (hij : (i, j) ∈ l) :
    ∃ ri rj, rules[i]? = some ri ∧ rules[j]? = some rj ∧ lhsRuleC ri = true ∧
      f rj = true := by
  have h' := List.all_eq_true.1 h _ hij
  simp only at h'
  split at h'
  · rename_i ri rj hri hrj
    simp only [Bool.and_eq_true] at h'
    exact ⟨ri, rj, hri, hrj, h'.1, h'.2⟩
  · cases h'

theorem noElse_of_hasElse {nm : IL.Id} {qs : List Param} {op : MixopS} {e : Exp}
    {prems : List Prem} (h : ElseBwd.hasElse (.ruleD nm qs op e prems) = false) :
    Prem.elsePr ∉ prems := fun hel => by
  have : ElseBwd.hasElse (.ruleD nm qs op e prems) = true := by
    simp only [ElseBwd.hasElse, List.any_eq_true]
    exact ⟨_, hel, rfl⟩
  rw [h] at this
  cases this

/-- **The backward firing at a simple pair (RM).** -/
theorem pairReflectD_simple (H : Hyps QT grC gdC (simEnv B)) {i j : Nat}
    (hij : (i, j) ∈ simplePairsC) :
    PairReflectD (simEnv B) eraseC "Step_read" [] [] i j := by
  intro ps op t rules r hrel hr a b c' hFi hbody
  obtain ⟨ri, rj, hri, hrj, hli, hsj⟩ := pairsOk_at simplePairsC_fixed hij
  rw [Round8.FiresC.rulesOf_eq hrel] at hri hrj
  rw [hr] at hrj
  cases hrj
  obtain ⟨nm, qs, opj, e, prems⟩ := r
  simp only [simpleRuleC, Bool.and_eq_true, Bool.not_eq_true'] at hsj
  exact reflect_coreC H hrel hri hr hli hsj.1 hFi
    (fun hel => absurd hel (noElse_of_hasElse hsj.2)) hbody

end Silmaril.Wasm.SpecTec.Sim.Round9.RMElse
