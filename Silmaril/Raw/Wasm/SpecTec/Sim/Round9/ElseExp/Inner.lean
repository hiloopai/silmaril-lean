module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.ElseExp.Check

/-!
# Round 9, RE and RM: `(21, 9)`, vacuously (unrefined)

`throw_ref-handler-next` (21) fires at `z; HANDLER_ n {catch catch'*} (REF.EXN_ADDR a THROW_REF)`;
`return_call_ref-handler` (9) needs `z; HANDLER_ k {catch*} (val* RETURN_CALL_REF yy instr*)`.
Pass 1 left the pair open because rule 9 quantifies over `instr*`, which is not export-free, so
rebinding the state alone does not read it backward. It is vacuous instead: both erasures keep
constructor heads elementwise, so the image of rule 21's handler body is still a list with heads
`REF.EXN_ADDR`, `THROW_REF`, and rule 9's body holds a `RETURN_CALL_REF`. The kernel check
`innerPairs_fixed` reads the shapes off the script (`innerDiffer`).

* `eval_inner`, `eval_litHeads`, `eval_mid`: what the three shapes evaluate to.
* `inner_clash`: the two firings clash, for any head-keeping map with the nested shape equation.
* `pairReflectB_inner` (RE, `eraseV`), `pairReflectD_inner` (RM, `eraseC`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseVs)
open Round8.CodeErase.Swap (eraseC eraseCs)
open Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
open Round6.Reading (DDerivesB RuleBodyB conclAlts otherwiseAtB)

/-! ## Evaluation -/

theorem evalExp_triple {n : Nat} {env : Env} {ρ : VarEnv} {a b c : Exp} {w : Value}
    (h : evalExp n env ρ (.tupE [a, b, c]) = .ok w) :
    ∃ k va vb vc, evalExp k env ρ c = .ok vc ∧ w = .tuple [va, vb, vc] := by
  rcases n with _ | _ | k
  · simp [evalExp] at h
  · simp [evalExp, evalExps] at h
  · simp only [evalExp, evalExps, List.mapM_cons, List.mapM_nil] at h
    cases ha : evalExp k env ρ a with
    | error s => simp [ha] at h
    | ok va =>
      cases hb : evalExp k env ρ b with
      | error s => simp [ha, hb] at h
      | ok vb =>
        cases hc : evalExp k env ρ c with
        | error s => simp [ha, hb, hc] at h
        | ok vc =>
          simp [ha, hb, hc] at h
          exact ⟨k, va, vb, vc, hc, by subst h; rfl⟩

/-- **A conclusion `(z; [o (n, cs, body)], rhs)` evaluates to that shape**, with the body's
value. -/
theorem eval_inner {n : Nat} {env : Env} {ρ : VarEnv} {e body : Exp} {o : MixopS} {w : Value}
    (hi : cfgInner e = some (o, body)) (h : evalExp n env ρ e = .ok w) :
    ∃ k zv nv cv bv rv, evalExp k env ρ body = .ok bv ∧
      w = .tuple [.case "%;%" (.tuple [zv, .list [.case o (.tuple [nv, cv, bv])]]), rv] := by
  unfold cfgInner at hi
  split at hi
  case h_2 => cases hi
  rename_i op z o' nn cs body' r
  split at hi
  case isFalse => cases hi
  rename_i hop
  cases hi
  rw [hop] at h
  obtain ⟨k, a, rv, -, ha, -, rfl⟩ := Round8.NxElse.evalExp_pair h
  obtain ⟨k', a₀, -, ha₀, rfl⟩ := evalExp_caseE ha
  obtain ⟨k'', zv, lv, -, -, hl, rfl⟩ := Round8.NxElse.evalExp_pair ha₀
  obtain ⟨m, vs, rfl, hvs⟩ := evalExp_listE hl
  simp only [List.mapM_cons, List.mapM_nil, Res.bind_eq_ok] at hvs
  obtain ⟨y, hy, _, ⟨⟩, hys⟩ := hvs
  cases hys
  obtain ⟨m', y₀, -, hy₀, rfl⟩ := evalExp_caseE hy
  obtain ⟨m'', nv, cv, bv, hb, rfl⟩ := evalExp_triple hy₀
  exact ⟨m'', zv, nv, cv, bv, rv, hb, rfl⟩

theorem mapM_heads {k : Nat} {env : Env} {ρ : VarEnv} :
    ∀ {es : List Exp} {hs : List MixopS} {vs : List Value}, es.mapM instrHead = some hs →
      es.mapM (evalExp k env ρ) = .ok vs → ∀ v ∈ vs, ∃ o ∈ hs, ∃ u, v = .case o u
  | [], hs, vs, _, h, v, hv => by
    simp only [List.mapM_nil] at h
    cases h
    simp at hv
  | e :: es, hs, vs, hh, h, v, hv => by
    simp only [List.mapM_cons, Res.bind_eq_ok] at h
    obtain ⟨y, hy, ys, hys, hv'⟩ := h
    cases hv'
    rw [List.mapM_cons] at hh
    cases ho : instrHead e with
    | none => rw [ho] at hh; cases hh
    | some o =>
    cases hhs' : es.mapM instrHead with
    | none => rw [ho, hhs'] at hh; cases hh
    | some hs' =>
    have hh' : hs = o :: hs' := by
      rw [ho, hhs'] at hh
      exact (Option.some.inj hh).symm
    subst hh'
    rcases List.mem_cons.1 hv with rfl | hv
    · cases e with
      | caseE o' e₁ =>
        simp only [instrHead, Option.some.injEq] at ho
        subst ho
        obtain ⟨-, u, -, -, rfl⟩ := evalExp_caseE hy
        exact ⟨o', List.mem_cons_self, u, rfl⟩
      | _ => simp [instrHead] at ho
    · obtain ⟨o'', ho'', u, rfl⟩ := mapM_heads hhs' hys v hv
      exact ⟨o'', List.mem_cons_of_mem _ ho'', u, rfl⟩

/-- **A list literal of constructors evaluates to a list with those heads.** -/
theorem eval_litHeads {n : Nat} {env : Env} {ρ : VarEnv} {e : Exp} {hs : List MixopS}
    {w : Value} (hh : litHeads e = some hs) (h : evalExp n env ρ e = .ok w) :
    ∃ vs, w = .list vs ∧ ∀ v ∈ vs, ∃ o ∈ hs, ∃ u, v = .case o u := by
  cases e with
  | listE es =>
    simp only [litHeads] at hh
    obtain ⟨k, vs, rfl, hvs⟩ := evalExp_listE h
    exact ⟨vs, rfl, mapM_heads hh hvs⟩
  | _ => simp [litHeads] at hh

/-- **`pre ++ [o …] ++ suf` evaluates to a list holding an `o`.** -/
theorem eval_mid {n : Nat} {env : Env} {ρ : VarEnv} {e : Exp} {o : MixopS} {w : Value}
    (hm : midHead e = some o) (h : evalExp n env ρ e = .ok w) :
    ∃ pre u suf, w = .list (pre ++ .case o u :: suf) := by
  unfold midHead at hm
  split at hm
  case h_2 => cases hm
  rename_i e₁ o' e₂ e₃
  cases hm
  obtain ⟨m₁, v₁, v₂, h₁, _, hc⟩ := evalExp_catE h
  obtain ⟨m₂, v₃, v₄, _, h₄, hc₂⟩ := evalExp_catE h₁
  obtain ⟨u, rfl⟩ := evalExp_single h₄
  obtain ⟨pre, _, rfl⟩ := cat_list_right hc₂
  obtain ⟨suf, _, rfl⟩ := cat_list_left hc
  exact ⟨pre, u, suf, by simp⟩

/-! ## The clash -/

/-- **The two firings clash**, for a map `ε` that keeps heads and maps the nested shape
componentwise. -/
theorem inner_clash {ε : Value → Value} (hε : ∀ v o u, ε v = .case o u → ∃ u', v = .case o u')
    (hmap : ∀ zv o nv cv vs, ε (.case "%;%" (.tuple [zv, .list [.case o (.tuple [nv, cv, .list vs])]])) =
      .case "%;%" (.tuple [ε zv, .list [.case o (.tuple [ε nv, ε cv, .list (vs.map ε)])]]))
    {env : Env} {ρ₁ ρ₂ : VarEnv} {e₁ e₂ b₁ b₂ : Exp} {a b c' : Value} {o₁ o₂ o : MixopS}
    {hs : List MixopS} (hi₁ : cfgInner e₁ = some (o₁, b₁)) (hi₂ : cfgInner e₂ = some (o₂, b₂))
    (hl : litHeads b₁ = some hs) (hm : midHead b₂ = some o) (hn : hs.contains o = false)
    (h₁ : EvalExp env ρ₁ e₁ (.tuple [a, b])) (h₂ : EvalExp env ρ₂ e₂ (.tuple [ε a, c'])) :
    False := by
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  obtain ⟨k₁, zv, nv, cv, bv, rv, hb₁, hw₁⟩ := eval_inner hi₁ hn₁
  obtain ⟨k₂, zv', nv', cv', bv', rv', hb₂, hw₂⟩ := eval_inner hi₂ hn₂
  obtain ⟨vs, rfl, hvs⟩ := eval_litHeads hl hb₁
  obtain ⟨pre, u, suf, rfl⟩ := eval_mid hm hb₂
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hw₁ hw₂
  rw [hw₁.1, hmap] at hw₂
  simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.list.injEq, true_and,
    and_true] at hw₂
  have hmem : Value.case o u ∈ vs.map ε := by rw [hw₂.1.2.2.2.2]; simp
  obtain ⟨v, hv, hev⟩ := List.mem_map.1 hmem
  obtain ⟨u', rfl⟩ := hε _ _ _ hev
  obtain ⟨o', ho', u'', hu''⟩ := hvs _ hv
  simp only [Value.case.injEq] at hu''
  rw [hu''.1] at hn
  simp at hn
  exact hn ho'

/-! ## The pair -/

variable {B : Builtins}

theorem innerPairs_at {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {i j : Nat}
    (hrel : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules))
    (hij : (i, j) ∈ innerPairs) :
    ∃ ri rj, rules[i]? = some ri ∧ rules[j]? = some rj ∧ innerDiffer ri rj = true := by
  have h := List.all_eq_true.1 innerPairs_fixed _ (EraseAll.mem_rels_of_findRel' hrel)
  simp only [bne_self_eq_false, Bool.false_or, List.all_eq_true] at h
  have h' := h _ hij
  split at h'
  · rename_i ri rj hri hrj
    exact ⟨ri, rj, hri, hrj, h'⟩
  · cases h'

theorem innerDiffer_alt {nm₁ nm₂ : IL.Id} {qs₁ qs₂ : List Param} {op₁ op₂ : MixopS}
    {e₁ e₂ : Exp} {ps₁ ps₂ : List Prem}
    (h : innerDiffer (.ruleD nm₁ qs₁ op₁ e₁ ps₁) (.ruleD nm₂ qs₂ op₂ e₂ ps₂) = true)
    {a b : Exp} (ha : a ∈ conclAlts e₁) (hb : b ∈ conclAlts e₂) :
    ∃ o₁ o₂ b₁ b₂ hs o, cfgInner a = some (o₁, b₁) ∧ cfgInner b = some (o₂, b₂) ∧
      litHeads b₁ = some hs ∧ midHead b₂ = some o ∧ hs.contains o = false := by
  simp only [innerDiffer, List.all_eq_true] at h
  have h' := h a ha b hb
  split at h'
  · rename_i o₁ b₁ o₂ b₂ hi₁ hi₂
    split at h'
    · rename_i hs o hl hm
      simp only [Bool.not_eq_true'] at h'
      exact ⟨o₁, o₂, b₁, b₂, hs, o, hi₁, hi₂, hl, hm, h'⟩
    · cases h'
  · cases h'

/-- **The backward firing at `(21, 9)`, for RE** (vacuous: rule 9 cannot fire). -/
theorem pairReflectB_inner {i j : Nat} (hij : (i, j) ∈ innerPairs) :
    PairReflectB (utf8Env B) eraseV "Step_read" [] [] i j := by
  intro ps op t rules r hrel hr a b c' hFi hbody
  exfalso
  obtain ⟨ri, rj, hri, hrj, hd⟩ := innerPairs_at (by rw [← findRel?_utf8Env]; exact hrel) hij
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
  obtain ⟨o₁, o₂, b₁, b₂, hs, o, hi₁, hi₂, hl, hm, hn⟩ := innerDiffer_alt hd halti halt''
  exact inner_clash (fun _ _ _ => eraseV_case)
    (fun zv o vs nv cv => by simp [eraseV, eraseVs, Swap.eraseVs_eq_map]) hi₁ hi₂ hl hm hn
    hevi hev'

/-- **The backward firing at `(21, 9)`, for RM** (vacuous). -/
theorem pairReflectD_inner {i j : Nat} (hij : (i, j) ∈ innerPairs) :
    PairReflectD (simEnv B) eraseC "Step_read" [] [] i j := by
  intro ps op t rules r hrel hr a b c' hFi hbody
  exfalso
  obtain ⟨ri, rj, hri, hrj, hd⟩ := innerPairs_at hrel hij
  rw [hr] at hrj
  cases hrj
  obtain ⟨ps', op', t', rules', nmi, qsi, ei, premsi, ρ₀i, σi, hrel', hrulei, -, -, hevi⟩ := hFi
  rw [hrel] at hrel'
  cases hrel'
  rw [hrulei] at hri
  cases hri
  obtain ⟨nm, qs, opj, e, prems⟩ := r
  obtain ⟨_, ρ₀, σ, _, _, hev', _⟩ := hbody
  obtain ⟨o₁, o₂, b₁, b₂, hs, o, hi₁, hi₂, hl, hm, hn⟩ :=
    innerDiffer_alt hd List.mem_cons_self List.mem_cons_self
  exact inner_clash (fun _ _ _ => eraseC_case)
    (fun zv o vs nv cv => by simp [eraseC, eraseCs, eraseCs_map]) hi₁ hi₂ hl hm hn hevi hev'

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp
