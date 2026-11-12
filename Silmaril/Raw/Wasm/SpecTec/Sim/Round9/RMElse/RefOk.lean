module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.RMElse.Chain
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.RMElse.CheckRef

/-!
# Round 9, rm: the pairs with `Ref_ok`, along code erasure (unrefined)

The four pairs left by `Chain` (`leftPairsC`) have an earlier rule with a `Ref_ok` premise
`s ⊢ ref : rt`, and both rules read the state as `(s; f)`. The argument is `reflect_coreC`'s with
the store quantifier `s` rebound instead of the state, and without decomposing the left-hand side:

* **Rebinding.** On the erased side the store quantifier holds `eraseC sv`, the other quantifiers
  hold `CODE`-free values. Rebinding it to `sv` gives an instance whose scope erasure agrees with
  the erased one on every quantifier (`rebind_agree`) and which is typed (`rebind_quants`). Round
  8's equation `eraseAt` then gives every expression's value on the original side up to `eraseC`
  (`eval_back`), and injectivity of `eraseC` fixes it.
* **`Ref_ok` backward** (`refOk_bwd`, by mutual recursion with `dprem_bwd`): every rule of `Ref_ok`
  concludes `(s, e₂, e₃)` with `s` a store quantifier (kernel check `refOkOk_fixed`); its `if`
  premises go back by `eval_back`, its `Ref_ok` premises by recursion (they conclude `(s, …)`), and
  its other premises (`Reftype_ok`, `Reftype_sub`) do not mention `s`, so they hold verbatim.
* `pairReflectD_sf`: `PairReflectD` along `eraseC` at the 4 pairs (kernel check `sfPairsOk_fixed`).
* `elseBwdDLeftC_sim`: so `ElseBwdDLeftC`, and with `Chain`, `ElseBwd.ElseBwdDRest` hold.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMElse

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll (Hyps grC gdC xRule xPrem eraseAt)
open Silmaril.Wasm.SpecTec.Sim.Round8.FiresC (QT)
open Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd (FiredD PairReflectD)

variable {B : Builtins}

/-! ## Small facts -/

theorem storeQ_type {qs : List Param} {z : IL.Id} (h : storeQ qs z = true) {t : Typ}
    (ht : Param.expP z t ∈ qs) : t = .varT "store" [] := by
  simp only [storeQ, Bool.and_eq_true, List.all_eq_true] at h
  have h' := h.2 _ ht
  simp only [bne_self_eq_false, Bool.false_or] at h'
  unfold isStoreT at h'
  split at h'
  · rename_i x; simp only [beq_iff_eq] at h'; rw [h']
  · cases h'

theorem storeQ_mem {qs : List Param} {z : IL.Id} (h : storeQ qs z = true) :
    z ∈ Determ.quantNames qs := by
  simp only [storeQ, Bool.and_eq_true, List.contains_iff_mem] at h
  exact h.1

/-- A triple expression evaluates componentwise. -/
theorem evalExp_triple {n : Nat} {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {w : Value}
    (h : evalExp n env ρ (.tupE [e₁, e₂, e₃]) = .ok w) :
    ∃ k a₁ a₂ a₃, evalExp k env ρ e₁ = .ok a₁ ∧ w = .tuple [a₁, a₂, a₃] := by
  rcases n with _ | _ | k
  · simp [evalExp] at h
  · simp [evalExp, evalExps] at h
  · simp only [evalExp, evalExps, List.mapM_cons, List.mapM_nil] at h
    cases h₁ : evalExp k env ρ e₁ with
    | error s => simp [h₁] at h
    | ok a₁ =>
      cases h₂ : evalExp k env ρ e₂ with
      | error s => simp [h₁, h₂] at h
      | ok a₂ =>
        cases h₃ : evalExp k env ρ e₃ with
        | error s => simp [h₁, h₂, h₃] at h
        | ok a₃ =>
          simp [h₁, h₂, h₃] at h
          exact ⟨k, a₁, a₂, a₃, h₁, by subst h; rfl⟩

theorem concl3_some {e : Exp} {x : IL.Id} {a b : Exp} (h : concl3 e = some (x, a, b)) :
    e = .tupE [.varE x, a, b] := by
  unfold concl3 at h
  split at h
  · cases h; rfl
  · cases h

theorem cfgSF_some {e : Exp} {s f : IL.Id} (h : cfgSF e = some (s, f)) :
    ∃ l r, e = .tupE [.caseE "%;%" (.tupE [.caseE "%;%" (.tupE [.varE s, .varE f]), l]), r] := by
  unfold cfgSF at h
  split at h
  · rename_i op op' s' f' l r
    split at h
    · rename_i hop
      cases h
      obtain ⟨rfl, rfl⟩ := hop
      exact ⟨l, r, rfl⟩
    · cases h
  · cases h

/-- **A conclusion `((s; f); L, R)` evaluates to `((sv; fv); lv, rv)`** with `sv` the value of
`s`. -/
theorem eval_sf {n : Nat} {env : Env} {ρ : VarEnv} {s f : IL.Id} {l r : Exp} {w : Value}
    (h : evalExp n env ρ
      (.tupE [.caseE "%;%" (.tupE [.caseE "%;%" (.tupE [.varE s, .varE f]), l]), r]) = .ok w) :
    ∃ sv fv lv rv, w = .tuple [.case "%;%" (.tuple [.case "%;%" (.tuple [sv, fv]), lv]), rv] ∧
      ρ.findVal? s = some sv := by
  obtain ⟨k₁, a, rv, -, ha, -, rfl⟩ := Round8.NxElse.evalExp_pair h
  obtain ⟨k₂, a₀, -, ha₀, rfl⟩ := ElseBwd.evalExp_caseE ha
  obtain ⟨k₃, c, lv, -, hc, -, rfl⟩ := Round8.NxElse.evalExp_pair ha₀
  obtain ⟨k₄, c₀, -, hc₀, rfl⟩ := ElseBwd.evalExp_caseE hc
  obtain ⟨k₅, sv, fv, -, hs, -, rfl⟩ := Round8.NxElse.evalExp_pair hc₀
  exact ⟨sv, fv, lv, rv, rfl, ElseBwd.evalExp_varE hs⟩

/-! ## Rebinding one quantifier -/

section Rebind

variable {qs : List Param} {σ' : List (IL.Id × Value)} {z : IL.Id} {zv : Value}

/-- **The scope erasure of the rebound instance agrees with the erased instance** on the
quantifiers. -/
theorem rebind_agree (hq' : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ') qs)
    (hz' : (VarEnv.empty.bindVals σ').findVal? z = some (eraseC zv))
    (hqn : quantsNC qs z = true) (hzw : z ≠ "_") :
    ∀ s, EraseDer.varsIn (Determ.quantNames qs) s = true →
      VarEnv.AgreeOn s (eraseScope (VarEnv.empty.bindVals (σ' ++ [(z, zv)])))
        (VarEnv.empty.bindVals σ') := by
  intro s hs
  refine ⟨fun y hy => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  rw [Round8.CodeErase.Erase.find?_eraseScope]
  by_cases hyz : y = z
  · subst hyz; rw [ElseBwd.findVal_snoc_self hzw zv, hz']; rfl
  · obtain ⟨ty, hty⟩ := ElseBwd.mem_quantNames (EraseDer.varsIn_mem hs y hy)
    obtain ⟨w, hw, hnw, -⟩ := ncB_of_quant rfl hq' hty (quantsNC_at hqn hty hyz).1
    rw [ElseBwd.findVal_snoc_ne hyz zv, hw]
    simp [eraseC_of_ncB w hnw]

/-- **The rebound instance is typed**, given the type of the new value. -/
theorem rebind_quants {tz : String} (hq' : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ') qs)
    (hqn : quantsNC qs z = true) (hzw : z ≠ "_")
    (hzT : ∀ t, Param.expP z t ∈ qs → t = .varT tz [])
    (hzt : HasTyp (simEnv B) VarEnv.empty (.varT tz []) zv) :
    QuantsOk (simEnv B) (VarEnv.empty.bindVals (σ' ++ [(z, zv)])) qs := by
  intro y ty hy
  by_cases hyz : y = z
  · subst hyz
    obtain rfl := hzT ty hy
    exact ⟨zv, ElseBwd.findVal_snoc_self hzw zv, ElseBwd.hasTyp_varT_scope rfl rfl hzt⟩
  · obtain ⟨w, hw, hty⟩ := hq' y ty hy
    exact ⟨w, (ElseBwd.findVal_snoc_ne hyz zv).trans hw,
      hasTyp_of_offZ (offZ_snoc zv) (quantsNC_at hqn hy hyz).2 hty⟩

/-- **An expression reading only quantifiers has, on the rebound instance, a value whose erasure
is its value on the erased instance.** -/
theorem eval_back (H : Hyps QT grC gdC (simEnv B))
    (hag : ∀ s, EraseDer.varsIn (Determ.quantNames qs) s = true →
      VarEnv.AgreeOn s (eraseScope (VarEnv.empty.bindVals (σ' ++ [(z, zv)])))
        (VarEnv.empty.bindVals σ'))
    {e : Exp} (hx : Round8.CodeErase.EraseAll.xExp grC gdC e = true)
    (hv : EraseDer.varsIn (Determ.quantNames qs) (freeExp e) = true) {w' : Value}
    (h : EvalExp (simEnv B) (VarEnv.empty.bindVals σ') e w') :
    ∃ n u, evalExp n (simEnv B) (VarEnv.empty.bindVals (σ' ++ [(z, zv)])) e = .ok u ∧
      eraseC u = w' := by
  obtain ⟨n, hn⟩ := h
  have hE := ((eraseAt H n).exp _ e
    (Round8.FiresC.sg_bindVals Round8.CodeErase.EraseAll.sg_empty (σ' ++ [(z, zv)])) hx).1
  rw [evalExp_agreeOn (hag _ hv), hn] at hE
  obtain ⟨u, hu, hue⟩ := ElseBwd.map_eq_ok hE.symm
  exact ⟨n, u, hu, hue⟩

end Rebind

/-! ## `Ref_ok` backward -/

/-- A tuple whose first component is a typed store. -/
def StoreT (u : Value) : Prop :=
  ∃ sv l, u = .tuple (sv :: l) ∧ HasTyp (simEnv B) VarEnv.empty (.varT "store" []) sv

theorem refOkRule_parts {nm : IL.Id} {qs : List Param} {op : MixopS} {e : Exp}
    {prems : List Prem} (h : refOkRule (.ruleD nm qs op e prems) = true) :
    ∃ z e₂ e₃, e = .tupE [.varE z, e₂, e₃] ∧ storeQ qs z = true ∧ quantsNC qs z = true ∧
      z ≠ "_" ∧ EraseDer.varsIn (Determ.quantNames qs) (freeExp e) = true ∧
      ∀ pr ∈ prems, refPremOk qs z pr = true := by
  simp only [refOkRule] at h
  split at h
  · rename_i z e₂ e₃ hc
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at h
    exact ⟨z, e₂, e₃, concl3_some hc, h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
  · cases h

theorem refOk_facts {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    (hrel : (simEnv B).findRel? "Ref_ok" = some (ps, op, t, rules)) :
    ps = [] ∧ ∀ r ∈ rules, refOkRule r = true := by
  have hk := refOkOk_fixed
  unfold refOkOk at hk
  rw [← Round8.FiresC.findRel?_simEnv (B := B), hrel] at hk
  simp only [Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff] at hk
  exact hk

theorem args_nil_same {ρ ρ' : VarEnv} {avs : List ArgV} (h : EvalArgs (simEnv B) ρ [] avs) :
    EvalArgs (simEnv B) ρ' [] avs := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, by rw [← hm]; exact evalArgs_agreeOn (VarEnv.AgreeOn.empty _ _)⟩

/-- The first component of a `Ref_ok` premise's conclusion on the rebound instance is the new
store. -/
theorem storeT_of_eval {σ' : List (IL.Id × Value)} {z : IL.Id} {zv : Value} (hzw : z ≠ "_")
    (hzt : HasTyp (simEnv B) VarEnv.empty (.varT "store" []) zv) {e₂ e₃ : Exp} {n : Nat}
    {u : Value}
    (h : evalExp n (simEnv B) (VarEnv.empty.bindVals (σ' ++ [(z, zv)]))
      (.tupE [.varE z, e₂, e₃]) = .ok u) : StoreT (B := B) u := by
  obtain ⟨k, a₁, a₂, a₃, h₁, rfl⟩ := evalExp_triple h
  have := ElseBwd.evalExp_varE h₁
  rw [ElseBwd.findVal_snoc_self hzw zv] at this
  cases this
  exact ⟨zv, [a₂, a₃], rfl, hzt⟩

section RefOk

variable (H : Hyps QT grC gdC (simEnv B))
include H

mutual
/-- **A `Ref_ok` derivation at an erased store goes back to the original store.** -/
theorem refOk_bwd {O : ElseI} : ∀ {x : IL.Id} {op : MixopS} {avs : List ArgV} {w' : Value},
    Sim.DDerives (simEnv B) O x op avs w' → x = "Ref_ok" → ∀ u, eraseC u = w' →
    StoreT (B := B) u → Sim.DDerives (simEnv B) O x op avs u
  | x, op, avs, w', .rule (ps := ps) (rules := rules) (i := i) (nm := nm) (qs := qs) (e := e)
      (prems := prems) (ρ₀ := ρ₀) (σ := σ) hrel hrule hps hq he hp, hx, u, hu, hst =>
    have ih := fun pr hpr => dprem_bwd (hp pr hpr)
    by
    subst hx
    obtain ⟨rfl, hall⟩ := refOk_facts hrel
    obtain rfl := bindParams_nil_ps hps
    obtain ⟨z, e₂, e₃, rfl, hsq, hqn, hzw, hfe, hpr⟩ := refOkRule_parts
      (hall _ (List.mem_of_getElem? hrule))
    obtain ⟨sv, l, rfl, hsvt⟩ := hst
    have hxr : xRule grC gdC (.ruleD nm qs op (.tupE [.varE z, e₂, e₃]) prems) = true :=
      H.rels "Ref_ok" _ (by decide) hrel _ (List.mem_of_getElem? hrule)
    simp only [xRule, Bool.and_eq_true] at hxr
    obtain ⟨n, hn⟩ := he
    obtain ⟨k, a₁, a₂, a₃, h₁, hw⟩ := evalExp_triple hn
    rw [← hu] at hw
    have hz' : (VarEnv.empty.bindVals σ).findVal? z = some (eraseC sv) := by
      rw [ElseBwd.evalExp_varE h₁]
      cases l with
      | nil => simp [eraseC, eraseCs] at hw
      | cons _ _ =>
        simp only [eraseC, eraseCs, Value.tuple.injEq, List.cons.injEq] at hw
        rw [hw.1]
    have hag := rebind_agree (zv := sv) hq hz' hqn hzw
    have hqj := rebind_quants hq hqn hzw (fun t ht => storeQ_type hsq ht) hsvt
    obtain ⟨m, u', hu', hue'⟩ := eval_back H hag hxr.1 hfe ⟨n, hn⟩
    have heq : u' = .tuple (sv :: l) := eraseC_injective (hue'.trans hu.symm)
    subst heq
    refine Sim.DDerives.rule hrel hrule hps hqj ⟨m, hu'⟩ fun pr hpr' => ?_
    exact ih pr hpr' _ qs z sv σ rfl (hpr pr hpr')
      (Round8.CodeErase.EraseAll.xPrems_mem hxr.2 pr hpr') hag hzw hsvt

/-- **A premise of a `Ref_ok` rule goes back to the rebound instance.** -/
theorem dprem_bwd {O : ElseI} : ∀ {els : Prop} {ρ' : VarEnv} {pr : Prem},
    Sim.DPrem (simEnv B) O els ρ' pr →
    ∀ (els' : Prop) (qs : List Param) (z : IL.Id) (zv : Value) (σ' : List (IL.Id × Value)),
    ρ' = VarEnv.empty.bindVals σ' → refPremOk qs z pr = true → xPrem grC gdC pr = true →
    (∀ s, EraseDer.varsIn (Determ.quantNames qs) s = true →
      VarEnv.AgreeOn s (eraseScope (VarEnv.empty.bindVals (σ' ++ [(z, zv)])))
        (VarEnv.empty.bindVals σ')) → z ≠ "_" →
    HasTyp (simEnv B) VarEnv.empty (.varT "store" []) zv →
    Sim.DPrem (simEnv B) O els' (VarEnv.empty.bindVals (σ' ++ [(z, zv)])) pr
  | _, _, _, .ifPr he, _, _, _, _, _, hρ, hok, hx, hag, _, _ => by
    subst hρ
    obtain ⟨n, u, hu, hue⟩ := eval_back H hag (by simpa [xPrem] using hx)
      (by simpa [refPremOk] using hok) he
    exact .ifPr ⟨n, by rw [hu, Round8.CodeErase.EraseAll.eraseC_eq_bool.1 hue]⟩
  | _, _, .rulePr x args op c, .rulePr hargs he hd, _, qs, z, zv, σ', hρ, hok, hx, hag, hzw, hzt =>
    have ih := fun hxe u hu hst => refOk_bwd (O := O) hd hxe u hu hst
    by
    subst hρ
    simp only [xPrem, Bool.and_eq_true] at hx
    unfold refPremOk at hok
    by_cases hxr : x = "Ref_ok"
    · subst hxr
      simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, List.isEmpty_iff] at hok
      obtain ⟨⟨rfl, hc⟩, hv⟩ := hok
      split at hc
      · rename_i y c₂ c₃ hcc
        simp only [beq_iff_eq] at hc
        subst hc
        obtain rfl := concl3_some hcc
        obtain ⟨n, u, hu, hue⟩ := eval_back H hag hx.2 hv he
        exact .rulePr (args_nil_same hargs) ⟨n, hu⟩
          (ih rfl u hue (storeT_of_eval hzw hzt hu))
      · cases hc
    · have hne : (x == "Ref_ok") = false := by simpa using hxr
      simp only [hne, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨m, hm⟩ := hargs
      obtain ⟨n, hn⟩ := he
      have hoff := offZ_snoc (σ := σ') (z := z) zv
      exact .rulePr ⟨m, by rw [← hm]; exact (evalArgs_agreeOn (hoff.2.2 _ hok.1)).symm⟩
        ⟨n, by rw [← hn]; exact (evalExp_agreeOn (hoff.2.2 _ hok.2)).symm⟩ hd
  | _, _, _, .elsePr _, _, _, _, _, _, _, hok, _, _, _, _ => by simp [refPremOk] at hok
  | _, _, _, .letPr _ _, _, _, _, _, _, _, hok, _, _, _, _ => by simp [refPremOk] at hok
  | _, _, _, .iterOptNone _ _ _, _, _, _, _, _, _, hok, _, _, _, _ => by simp [refPremOk] at hok
  | _, _, _, .iterOptSome _ _ _ _, _, _, _, _, _, _, hok, _, _, _, _ => by simp [refPremOk] at hok
  | _, _, _, .iterList _ _ _ _ _ _, _, _, _, _, _, _, hok, _, _, _, _ => by simp [refPremOk] at hok
  | _, _, _, .iterListN _ _ _ _ _ _, _, _, _, _, _, _, hok, _, _, _, _ => by simp [refPremOk] at hok
end

end RefOk

/-! ## The four pairs -/

theorem sfRule_parts {nm : IL.Id} {qs : List Param} {op : MixopS} {e : Exp}
    {prems : List Prem} (h : sfRule (.ruleD nm qs op e prems) = true) :
    ∃ z f, cfgSF e = some (z, f) ∧ storeQ qs z = true ∧ quantsNC qs z = true ∧ z ≠ "_" ∧
      EraseDer.varsIn (Determ.quantNames qs) (freeExp e) = true ∧
      ∀ pr ∈ prems, refPremOk qs z pr = true := by
  simp only [sfRule] at h
  split at h
  · rename_i z f hc
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at h
    exact ⟨z, f, hc, h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
  · cases h

theorem sfPairs_at {rules : List Rule} {i j : Nat} (h : sfPairsOk rules leftPairsC = true)
    (hij : (i, j) ∈ leftPairsC) :
    ∃ ri rj, rules[i]? = some ri ∧ rules[j]? = some rj ∧ lhsSF ri = true ∧ sfRule rj = true := by
  have h' := List.all_eq_true.1 h _ hij
  simp only at h'
  split at h'
  · rename_i ri rj hri hrj
    simp only [Bool.and_eq_true] at h'
    exact ⟨ri, rj, hri, hrj, h'.1, h'.2⟩
  · cases h'

/-- **The left-hand side of a firing of a `lhsSF` rule** is `((sv; fv); lv)` with `sv` a typed
store. -/
theorem fired_sf {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat}
    {ri : Rule} {a b : Value} (hrel : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules))
    (hri : rules[i]? = some ri) (hli : lhsSF ri = true)
    (hF : FiredD (simEnv B) "Step_read" [] i (.tuple [a, b])) :
    ∃ sv fv lv, a = .case "%;%" (.tuple [.case "%;%" (.tuple [sv, fv]), lv]) ∧
      HasTyp (simEnv B) VarEnv.empty (.varT "store" []) sv := by
  obtain ⟨ps', op', t', rules', nm, qs, e, prems, ρ₀, σ, hrel', hrule, hps, hq, hev⟩ := hF
  rw [hrel] at hrel'
  cases hrel'
  rw [hrule] at hri
  cases hri
  obtain ⟨-, rfl⟩ := bindParams_nil hps
  simp only [lhsSF] at hli
  split at hli
  · rename_i s f hc
    obtain ⟨l, r, rfl⟩ := cfgSF_some hc
    obtain ⟨n, hn⟩ := hev
    obtain ⟨sv, fv, lv, rv, hw, hs⟩ := eval_sf hn
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hw
    obtain ⟨rfl, -⟩ := hw
    obtain ⟨ts, hts⟩ := ElseBwd.mem_quantNames (storeQ_mem hli)
    obtain rfl := storeQ_type hli hts
    obtain ⟨w, hw, hty⟩ := hq s _ hts
    rw [hs] at hw
    cases hw
    exact ⟨sv, fv, lv, rfl, ElseBwd.hasTyp_varT_scope rfl rfl hty⟩
  · cases hli

/-- **A premise of an `sfRule` goes back to the rebound instance**, read by `DDerives noElse`. -/
theorem premW_bwd (H : Hyps QT grC gdC (simEnv B)) {els els' : Prop} {qs : List Param} {z : IL.Id}
    {zv : Value} {σ' : List (IL.Id × Value)} {pr : Prem}
    (h : PremW (simEnv B) (Sim.DDerives (simEnv B) Sim.noElse) els (VarEnv.empty.bindVals σ') pr)
    (hok : refPremOk qs z pr = true) (hx : xPrem grC gdC pr = true)
    (hag : ∀ s, EraseDer.varsIn (Determ.quantNames qs) s = true →
      VarEnv.AgreeOn s (eraseScope (VarEnv.empty.bindVals (σ' ++ [(z, zv)])))
        (VarEnv.empty.bindVals σ')) (hzw : z ≠ "_")
    (hzt : HasTyp (simEnv B) VarEnv.empty (.varT "store" []) zv) :
    PremW (simEnv B) (Sim.DDerives (simEnv B) Sim.noElse) els'
      (VarEnv.empty.bindVals (σ' ++ [(z, zv)])) pr := by
  cases h with
  | ifPr he =>
    obtain ⟨n, u, hu, hue⟩ := eval_back H hag (by simpa [xPrem] using hx)
      (by simpa [refPremOk] using hok) he
    exact .ifPr ⟨n, by rw [hu, Round8.CodeErase.EraseAll.eraseC_eq_bool.1 hue]⟩
  | rulePr hargs he hd =>
    rename_i x args op c avs w
    simp only [xPrem, Bool.and_eq_true] at hx
    unfold refPremOk at hok
    by_cases hxr : x = "Ref_ok"
    · subst hxr
      simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, List.isEmpty_iff] at hok
      obtain ⟨⟨rfl, hc⟩, hv⟩ := hok
      split at hc
      · rename_i y c₂ c₃ hcc
        simp only [beq_iff_eq] at hc
        subst hc
        obtain rfl := concl3_some hcc
        obtain ⟨n, u, hu, hue⟩ := eval_back H hag hx.2 hv he
        exact .rulePr (args_nil_same hargs) ⟨n, hu⟩
          (refOk_bwd H hd rfl u hue (storeT_of_eval hzw hzt hu))
      · cases hc
    · have hne : (x == "Ref_ok") = false := by simpa using hxr
      simp only [hne, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨m, hm⟩ := hargs
      obtain ⟨n, hn⟩ := he
      have hoff := offZ_snoc (σ := σ') (z := z) zv
      exact .rulePr ⟨m, by rw [← hm]; exact (evalArgs_agreeOn (hoff.2.2 _ hok.1)).symm⟩
        ⟨n, by rw [← hn]; exact (evalExp_agreeOn (hoff.2.2 _ hok.2)).symm⟩ hd
  | elsePr _ => simp [refPremOk] at hok
  | letPr _ _ => simp [refPremOk] at hok
  | iterOptNone _ _ _ => simp [refPremOk] at hok
  | iterOptSome _ _ _ _ => simp [refPremOk] at hok
  | iterList _ _ _ _ _ _ => simp [refPremOk] at hok
  | iterListN _ _ _ _ _ _ => simp [refPremOk] at hok

/-- **The backward firing at the 4 pairs with `Ref_ok` (RM).** -/
theorem pairReflectD_sf (H : Hyps QT grC gdC (simEnv B)) {i j : Nat} (hij : (i, j) ∈ leftPairsC) :
    PairReflectD (simEnv B) eraseC "Step_read" [] [] i j := by
  intro ps op t rules r hrel hr a b c' hFi hbody
  obtain ⟨ri, rj, hri, hrj, hli, hsj⟩ := sfPairs_at sfPairsOk_fixed hij
  rw [Round8.FiresC.rulesOf_eq hrel] at hri hrj
  rw [hr] at hrj
  cases hrj
  obtain ⟨nm, qs, opj, e, prems⟩ := r
  obtain ⟨sv, fv, lv, rfl, hsvt⟩ := fired_sf hrel hri hli hFi
  obtain ⟨hop, ρ₀, σ', hps, hq', hev', hpr'⟩ := hbody
  obtain ⟨rfl, rfl⟩ := bindParams_nil hps
  have hxr := xRule_of H hrel hr
  simp only [xRule, Bool.and_eq_true] at hxr
  obtain ⟨z, f, hcfg, hsq, hqn, hzw, hfe, hpr⟩ := sfRule_parts hsj
  obtain ⟨l, r, rfl⟩ := cfgSF_some hcfg
  obtain ⟨n, hn⟩ := hev'
  obtain ⟨sv', fv', lv', rv', hw, hs'⟩ := eval_sf hn
  simp only [eraseC, eraseCs, Value.tuple.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hw
  have hz' : (VarEnv.empty.bindVals σ').findVal? z = some (eraseC sv) := by
    rw [hs', hw.1.1.1]
  have hag := rebind_agree (zv := sv) hq' hz' hqn hzw
  have hqj := rebind_quants hq' hqn hzw (fun t ht => storeQ_type hsq ht) hsvt
  obtain ⟨m, u, hu, hue⟩ := eval_back H hag hxr.1 hfe ⟨n, hn⟩
  obtain ⟨a₀, c₀, rfl, ha₀⟩ := ElseBwd.eraseC_pair hue
  have ha : a₀ = .case "%;%" (.tuple [.case "%;%" (.tuple [sv, fv]), lv]) := by
    refine eraseC_injective ?_
    simp only [eraseC, eraseCs, Value.tuple.injEq, List.cons.injEq] at hue ⊢
    exact hue.1
  subst ha
  refine ⟨c₀, hop, VarEnv.empty, σ' ++ [(z, sv)], rfl, hqj, ⟨m, hu⟩, fun pr hpr₀ => ?_⟩
  exact premW_bwd H (hpr' pr hpr₀) (hpr pr hpr₀)
    (Round8.CodeErase.EraseAll.xPrems_mem hxr.2 pr hpr₀) hag hzw hsvt

/-- **`ElseBwdDLeftC` holds.** -/
theorem elseBwdDLeftC_sim (H : Hyps QT grC gdC (simEnv B)) : ElseBwdDLeftC (simEnv B) := by
  intro p hp
  obtain ⟨i, j⟩ := p
  exact pairReflectD_sf H hp

/-- **`ElseBwd.ElseBwdDRest` holds**: the backward firing along code erasure at all 68 pairs. -/
theorem elseBwdDRest_sim (H : Hyps QT grC gdC (simEnv B)) : ElseBwd.ElseBwdDRest (simEnv B) :=
  elseBwdDRest_of_left H (elseBwdDLeftC_sim H)

end Silmaril.Wasm.SpecTec.Sim.Round9.RMElse
