module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.ElseBwd.Fwd
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.ElseBwd.CheckAdj

/-!
# Round 9, `otherwise` rules: the pairs with `throw_ref-instrs` (unrefined)

At the 26 pairs of `adjPairs` the earlier rule is `throw_ref-instrs`, whose instructions contain
`REF.EXN_ADDR a` immediately followed by `THROW_REF`. The `otherwise` rule's instructions are a list
literal whose heads (`cfgHeads`) cannot line up with that pair (`noAdj`), and both erasures keep
constructor heads elementwise. So the earlier rule cannot fire at the image of a left-hand side of
the `otherwise` rule, and the backward firing holds vacuously, for RE (`pairReflectB_adj`, along
`eraseV`) and for RM (`pairReflectD_adj`, along `eraseC`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseVs)
open Round8.CodeErase.Swap (eraseC eraseCs)
open Round6.Reading (DDerivesB RuleBodyB conclAlts otherwiseAtB)

/-! ## Evaluation -/

theorem mapM_get {α β : Type} {f : α → Res β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys →
      ys.length = xs.length ∧ ∀ (p : Nat) (x : α), xs[p]? = some x →
        ∃ y, ys[p]? = some y ∧ f x = .ok y
  | [], ys, h => by
    simp only [List.mapM_nil] at h
    cases h
    exact ⟨rfl, fun p x hx => by simp at hx⟩
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, Res.bind_eq_ok] at h
    obtain ⟨y₀, h₀, ys', h', hys⟩ := h
    cases hys
    obtain ⟨hl, hp⟩ := mapM_get h'
    refine ⟨by simp [hl], fun p x' hx' => ?_⟩
    cases p with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx'
      subst hx'
      exact ⟨y₀, rfl, h₀⟩
    | succ p =>
      simp only [List.getElem?_cons_succ] at hx' ⊢
      exact hp p x' hx'

theorem evalExp_listE {n : Nat} {env : Env} {ρ : VarEnv} {es : List Exp} {v : Value}
    (h : evalExp n env ρ (.listE es) = .ok v) :
    ∃ k vs, v = .list vs ∧ es.mapM (evalExp k env ρ) = .ok vs := by
  rcases n with _ | _ | k
  · simp [evalExp] at h
  · simp [evalExp, evalExps, Functor.map, Except.map] at h
  · simp only [evalExp, evalExps, Functor.map, Except.map] at h
    split at h
    · cases h
    · rename_i vs hvs
      cases h
      exact ⟨k, vs, rfl, hvs⟩

theorem evalExp_catE {n : Nat} {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v : Value}
    (h : evalExp n env ρ (.catE e₁ e₂) = .ok v) :
    ∃ k v₁ v₂, evalExp k env ρ e₁ = .ok v₁ ∧ evalExp k env ρ e₂ = .ok v₂ ∧
      Value.cat? v₁ v₂ = some v := by
  rcases n with _ | k
  · simp [evalExp] at h
  · simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
    obtain ⟨v₁, h₁, v₂, h₂, hc⟩ := h
    exact ⟨k, v₁, v₂, h₁, h₂, hc⟩

theorem cat_list_right {v₁ v : Value} {l₂ : List Value} (h : Value.cat? v₁ (.list l₂) = some v) :
    ∃ l₁, v₁ = .list l₁ ∧ v = .list (l₁ ++ l₂) := by
  cases v₁ with
  | list l₁ => simp only [Value.cat?, Option.some.injEq] at h; exact ⟨l₁, rfl, h.symm⟩
  | opt o => cases o <;> simp [Value.cat?] at h
  | _ => simp [Value.cat?] at h

theorem cat_list_left {v₂ v : Value} {l₁ : List Value} (h : Value.cat? (.list l₁) v₂ = some v) :
    ∃ l₂, v₂ = .list l₂ ∧ v = .list (l₁ ++ l₂) := by
  cases v₂ with
  | list l₂ => simp only [Value.cat?, Option.some.injEq] at h; exact ⟨l₂, rfl, h.symm⟩
  | opt o => cases o <;> simp [Value.cat?] at h
  | _ => simp [Value.cat?] at h

theorem evalExp_single {n : Nat} {env : Env} {ρ : VarEnv} {o : MixopS} {e : Exp} {v : Value}
    (h : evalExp n env ρ (.listE [.caseE o e]) = .ok v) : ∃ u, v = .list [.case o u] := by
  obtain ⟨k, vs, rfl, hvs⟩ := evalExp_listE h
  simp only [List.mapM_cons, List.mapM_nil, Res.bind_eq_ok] at hvs
  obtain ⟨y, hy, _, ⟨⟩, hys⟩ := hvs
  cases hys
  obtain ⟨k', a₀, -, -, rfl⟩ := evalExp_caseE hy
  exact ⟨a₀, rfl⟩

/-- **A configuration with list-literal instructions evaluates to instructions with those
heads.** -/
theorem eval_heads {n : Nat} {env : Env} {ρ : VarEnv} {e : Exp} {w : Value}
    {hs : List (Option MixopS)} (hh : cfgHeads e = some hs) (h : evalExp n env ρ e = .ok w) :
    ∃ zv vs rv, w = .tuple [.case "%;%" (.tuple [zv, .list vs]), rv] ∧ vs.length = hs.length ∧
      ∀ (p : Nat) (o : MixopS), hs[p]? = some (some o) → ∃ u, vs[p]? = some (Value.case o u) := by
  unfold cfgHeads at hh
  split at hh
  case h_2 => cases hh
  rename_i op z es r
  split at hh
  case isFalse => cases hh
  rename_i hop
  cases hh
  rw [hop] at h
  obtain ⟨k, a, rv, -, ha, -, rfl⟩ := Round8.NxElse.evalExp_pair h
  obtain ⟨k', a₀, -, ha₀, rfl⟩ := evalExp_caseE ha
  obtain ⟨k'', zv, lv, -, -, hl, rfl⟩ := Round8.NxElse.evalExp_pair ha₀
  obtain ⟨m, vs, rfl, hvs⟩ := evalExp_listE hl
  obtain ⟨hlen, hget⟩ := mapM_get hvs
  refine ⟨zv, vs, rv, rfl, by simp [hlen], fun p o hp => ?_⟩
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hp
  obtain ⟨e₀, he₀, hh₀⟩ := hp
  obtain ⟨y, hy, hfy⟩ := hget p e₀ he₀
  cases e₀ with
  | caseE o' e₁ =>
    simp only [instrHead, Option.some.injEq] at hh₀
    subst hh₀
    obtain ⟨-, u, -, -, rfl⟩ := evalExp_caseE hfy
    exact ⟨u, hy⟩
  | _ => simp [instrHead] at hh₀

/-- **A configuration with two adjacent constructors evaluates to instructions with them.** -/
theorem eval_adj {n : Nat} {env : Env} {ρ : VarEnv} {e : Exp} {w : Value} {o₁ o₂ : MixopS}
    (ha : cfgAdj e = some (o₁, o₂)) (h : evalExp n env ρ e = .ok w) :
    ∃ zv ws rv, w = .tuple [.case "%;%" (.tuple [zv, .list ws]), rv] ∧
      ∃ pre u₁ u₂ suf, ws = pre ++ .case o₁ u₁ :: .case o₂ u₂ :: suf := by
  unfold cfgAdj at ha
  split at ha
  case h_2 => cases ha
  rename_i op z e₁ o₁' e₂ o₂' e₃ e₄ r
  split at ha
  case isFalse => cases ha
  rename_i hop
  cases ha
  rw [hop] at h
  obtain ⟨k, a, rv, -, ha, -, rfl⟩ := Round8.NxElse.evalExp_pair h
  obtain ⟨k', a₀, -, ha₀, rfl⟩ := evalExp_caseE ha
  obtain ⟨k'', zv, lv, -, -, hl, rfl⟩ := Round8.NxElse.evalExp_pair ha₀
  obtain ⟨m₁, v₁, v₂, _, h₂, hc⟩ := evalExp_catE hl
  obtain ⟨m₂, v₃, v₄, h₃, h₄, hc₂⟩ := evalExp_catE h₂
  obtain ⟨u₁, rfl⟩ := evalExp_single h₃
  obtain ⟨m₃, v₅, v₆, h₅, _, hc₃⟩ := evalExp_catE h₄
  obtain ⟨u₂, rfl⟩ := evalExp_single h₅
  obtain ⟨suf, _, rfl⟩ := cat_list_left hc₃
  simp only [Value.cat?, Option.some.injEq] at hc₂
  subst hc₂
  obtain ⟨pre, _, rfl⟩ := cat_list_right hc
  exact ⟨zv, _, rv, rfl, pre, u₁, u₂, suf, by simp⟩

/-! ## The clash -/

theorem noAdj_spec {o₁ o₂ : MixopS} :
    ∀ {hs : List (Option MixopS)}, noAdj o₁ o₂ hs = true → ∀ p h₁ h₂, hs[p]? = some h₁ →
      hs[p + 1]? = some h₂ → compat h₁ o₁ = true → compat h₂ o₂ = true → False
  | [], _, p, _, _, h, _, _, _ => by simp at h
  | [_], _, p, _, _, _, h, _, _ => by simp at h
  | a :: b :: t, hn, p, h₁, h₂, hp, hp', hc₁, hc₂ => by
    simp only [noAdj, Bool.and_eq_true, Bool.not_eq_true'] at hn
    cases p with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, zero_add,
        List.getElem?_cons_succ] at hp hp'
      subst hp hp'
      simp [hc₁, hc₂] at hn
    | succ p =>
      simp only [List.getElem?_cons_succ] at hp hp'
      exact noAdj_spec hn.2 p h₁ h₂ hp hp' hc₁ hc₂

/-- **Instructions with heads `hs` whose image under a head-keeping `ε` has `o₁ o₂` adjacent
contradict `noAdj`.** -/
theorem adj_clash {ε : Value → Value} (hε : ∀ v o u, ε v = .case o u → ∃ u', v = .case o u')
    {hs : List (Option MixopS)} {vs : List Value} {o₁ o₂ : MixopS}
    (hlen : vs.length = hs.length)
    (hget : ∀ (p : Nat) (o : MixopS), hs[p]? = some (some o) → ∃ u, vs[p]? = some (Value.case o u))
    (hn : noAdj o₁ o₂ hs = true) {pre suf : List Value} {u₁ u₂ : Value}
    (hws : vs.map ε = pre ++ .case o₁ u₁ :: .case o₂ u₂ :: suf) : False := by
  have hp₁ : (vs.map ε)[pre.length]? = some (.case o₁ u₁) := by rw [hws]; simp
  have hp₂ : (vs.map ε)[pre.length + 1]? = some (.case o₂ u₂) := by
    rw [hws, List.getElem?_append_right (by omega)]; simp
  rw [List.getElem?_map] at hp₁ hp₂
  obtain ⟨v₁, hv₁, he₁⟩ := Option.map_eq_some_iff.1 hp₁
  obtain ⟨v₂, hv₂, he₂⟩ := Option.map_eq_some_iff.1 hp₂
  obtain ⟨w₁, rfl⟩ := hε _ _ _ he₁
  obtain ⟨w₂, rfl⟩ := hε _ _ _ he₂
  have hl₁ : pre.length < hs.length := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hv₁).1
  have hl₂ : pre.length + 1 < hs.length := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hv₂).1
  have hc : ∀ (q : Nat) (o' : MixopS) (w : Value) (hq : q < hs.length),
      vs[q]? = some (Value.case o' w) → compat hs[q] o' = true := by
    intro q o' w hq hvq
    cases hhq : hs[q] with
    | none => rfl
    | some o =>
      obtain ⟨u, hu⟩ := hget q o (by rw [List.getElem?_eq_getElem hq, hhq])
      rw [hvq] at hu
      simp only [Option.some.injEq, Value.case.injEq] at hu
      simp [compat, hu.1]
  exact noAdj_spec hn pre.length _ _ (List.getElem?_eq_getElem hl₁)
    (List.getElem?_eq_getElem hl₂) (hc _ _ _ hl₁ hv₁) (hc _ _ _ hl₂ hv₂)

theorem eraseV_case {v : Value} {o : MixopS} {u : Value} (h : eraseV v = .case o u) :
    ∃ u', v = .case o u' := by
  cases v with
  | case o' w => simp only [eraseV, Value.case.injEq] at h; exact ⟨w, by rw [h.1]⟩
  | opt x => cases x <;> simp [eraseV] at h
  | _ => simp [eraseV] at h

theorem eraseC_case {v : Value} {o : MixopS} {u : Value} (h : eraseC v = .case o u) :
    ∃ u', v = .case o u' := by
  cases v with
  | case o' w => simp only [eraseC, Value.case.injEq] at h; exact ⟨w, by rw [h.1]⟩
  | opt x => cases x <;> simp [eraseC] at h
  | _ => simp [eraseC] at h

/-- **The two firings clash**: a conclusion with heads `hs` evaluates to `(a, b)`, one with
adjacent `o₁ o₂` to `(ε a, c')`, and `noAdj o₁ o₂ hs`. -/
theorem fire_clash {ε : Value → Value} (hε : ∀ v o u, ε v = .case o u → ∃ u', v = .case o u')
    (hcfg : ∀ zv vs, ε (.case "%;%" (.tuple [zv, .list vs])) =
      .case "%;%" (.tuple [ε zv, .list (vs.map ε)]))
    {env : Env} {ρ₁ ρ₂ : VarEnv} {e₁ e₂ : Exp} {a b c' : Value} {hs : List (Option MixopS)}
    {o₁ o₂ : MixopS} (hh : cfgHeads e₁ = some hs) (ha : cfgAdj e₂ = some (o₁, o₂))
    (hn : noAdj o₁ o₂ hs = true) (h₁ : EvalExp env ρ₁ e₁ (.tuple [a, b]))
    (h₂ : EvalExp env ρ₂ e₂ (.tuple [ε a, c'])) : False := by
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  obtain ⟨zv, vs, rv, hw, hlen, hget⟩ := eval_heads hh hn₁
  obtain ⟨zv', ws, rv', hw', pre, u₁, u₂, suf, hws⟩ := eval_adj ha hn₂
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hw hw'
  rw [hw.1, hcfg] at hw'
  simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.list.injEq, true_and,
    and_true] at hw'
  rw [← hw'.1.2] at hws
  exact adj_clash hε hlen hget hn hws

/-! ## The pairs -/

variable {B : Builtins}

theorem adjPairs_at {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i j : Nat}
    (hrel : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules))
    (hij : (i, j) ∈ adjPairs) :
    ∃ ri rj, rules[i]? = some ri ∧ rules[j]? = some rj ∧ adjDiffer ri rj = true := by
  have hm : adjPairsOf rules elsePairs = adjPairs := by
    have h := List.all_eq_true.1 adjPairs_fixed _ (EraseAll.mem_rels_of_findRel' hrel)
    simpa using h
  rw [← hm] at hij
  simp only [adjPairsOf, List.mem_filter] at hij
  obtain ⟨-, hij⟩ := hij
  split at hij
  · rename_i ri rj hri hrj
    exact ⟨ri, rj, hri, hrj, hij⟩
  · cases hij

theorem adjDiffer_alt {nm₁ nm₂ : IL.Id} {qs₁ qs₂ : List Param} {op₁ op₂ : MixopS}
    {e₁ e₂ : Exp} {ps₁ ps₂ : List Prem}
    (h : adjDiffer (.ruleD nm₁ qs₁ op₁ e₁ ps₁) (.ruleD nm₂ qs₂ op₂ e₂ ps₂) = true)
    {a b : Exp} (ha : a ∈ conclAlts e₁) (hb : b ∈ conclAlts e₂) :
    ∃ hs o₁ o₂, cfgHeads a = some hs ∧ cfgAdj b = some (o₁, o₂) ∧ noAdj o₁ o₂ hs = true := by
  simp only [adjDiffer, List.all_eq_true] at h
  have h' := h a ha b hb
  split at h'
  · rename_i hs o₁ o₂ hh ha'
    exact ⟨hs, o₁, o₂, hh, ha', h'⟩
  · cases h'

/-- **The backward firing at the pairs with `throw_ref-instrs`, for RE** (vacuous: the earlier
rule cannot fire). -/
theorem pairReflectB_adj {i j : Nat} (hij : (i, j) ∈ adjPairs) :
    PairReflectB (utf8Env B) eraseV "Step_read" [] [] i j := by
  intro ps op t rules r hrel hr a b c' hFi hbody
  exfalso
  obtain ⟨ri, rj, hri, hrj, hd⟩ := adjPairs_at (by rw [← findRel?_utf8Env]; exact hrel) hij
  rw [hr] at hrj
  cases hrj
  obtain ⟨ps', op', t', rules', nmi, qsi, ei, premsi, ei', ρ₀i, σi, hrel', hrulei, -, halti, -,
    -, hevi⟩ := hFi
  rw [hrel] at hrel'
  cases hrel'
  rw [hrulei] at hri
  cases hri
  obtain ⟨nm, qs, opj, e, prems⟩ := r
  obtain ⟨e'', halt'', _, ρ₀, σ, _, _, hev', _⟩ := hbody
  obtain ⟨hs, o₁, o₂, hh, ha, hn⟩ := adjDiffer_alt hd halti halt''
  exact fire_clash (fun _ _ _ => eraseV_case)
    (fun zv vs => by simp [eraseV, eraseVs, Swap.eraseVs_eq_map]) hh ha hn hevi hev'

/-- **The backward firing at the pairs with `throw_ref-instrs`, for RM** (vacuous). -/
theorem pairReflectD_adj {i j : Nat} (hij : (i, j) ∈ adjPairs) :
    PairReflectD (simEnv B) eraseC "Step_read" [] [] i j := by
  intro ps op t rules r hrel hr a b c' hFi hbody
  exfalso
  obtain ⟨ri, rj, hri, hrj, hd⟩ := adjPairs_at hrel hij
  rw [hr] at hrj
  cases hrj
  obtain ⟨ps', op', t', rules', nmi, qsi, ei, premsi, ρ₀i, σi, hrel', hrulei, -, -, hevi⟩ := hFi
  rw [hrel] at hrel'
  cases hrel'
  rw [hrulei] at hri
  cases hri
  obtain ⟨nm, qs, opj, e, prems⟩ := r
  obtain ⟨_, ρ₀, σ, _, _, hev', _⟩ := hbody
  obtain ⟨hs, o₁, o₂, hh, ha, hn⟩ := adjDiffer_alt hd List.mem_cons_self List.mem_cons_self
  exact fire_clash (fun _ _ _ => eraseC_case)
    (fun zv vs => by simp [eraseC, eraseCs, eraseCs_map]) hh ha hn hevi hev'

theorem mem_leftPairs {p : Nat × Nat} (he : p ∈ elsePairs) (hs : p ∉ simplePairs)
    (ha : p ∉ adjPairs) : p ∈ leftPairs := by
  revert he hs ha
  revert p
  decide

/-- **`ElseBwdBRest` from the 23 pairs left** (RE). -/
theorem elseBwdBRest_of_left (hL : ElseBwdBLeft (utf8Env B)) : ElseBwdBRest (utf8Env B) := by
  intro p hp hs
  by_cases ha : p ∈ adjPairs
  · exact pairReflectB_adj ha
  · exact hL p (mem_leftPairs hp hs ha)

/-- **`ElseBwdD` from the pairs outside `adjPairs`** (RM). -/
theorem elseBwdD_of_rest (hR : ElseBwdDRest (simEnv B)) : ElseBwdD (simEnv B) := by
  intro p hp
  by_cases ha : p ∈ adjPairs
  · exact pairReflectD_adj ha
  · exact hR p hp ha

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
