module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.Basic

/-!
# Round 7, the whole-evaluator erasure: the expression members, one step (unrefined)

From `EraseAt Q gr gd env n` and the hypotheses `Hyps Q gr gd env`, each member of the
expression side of the evaluator (`evalExp`, `evalExps`, `evalExpFields`, `evalArg`, `evalArgs`,
`evalDoms`, `evalIterE`, `evalIterList`, `evalRounds`, `pathGet`, `pathSet`, `patLen`) commutes
with erasure at fuel `n + 1`. Every recursive call of the evaluator is at fuel `n`, so each member
is a separate theorem.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope ScopeIn find?_eraseScope)

variable {Q : Value → Prop} {gr gd : String → Bool} {env : Env} {n : Nat}

theorem ER.of_bool_num {r : Res Value}
    (h : ∀ v, r = .ok v → (∃ b, v = .bool b) ∨ ∃ m, v = .num m) : ER eraseV (AllIn Q) r r := by
  refine ⟨(eraseV_res_bool_num h).symm, fun v hv => ?_⟩
  rcases h v hv with ⟨b, rfl⟩ | ⟨m, rfl⟩ <;> trivial

theorem ER.eq_ok {α : Type} {f : α → α} {P : α → Prop} {r r' : Res α} {a : α} (h : ER f P r r')
    (hr : r = .ok a) : r' = .ok (f a) := by
  rw [h.1, hr]; rfl

theorem ER.eq_error {α : Type} {f : α → α} {P : α → Prop} {r r' : Res α} {e : Stuck}
    (h : ER f P r r') (hr : r = .error e) : r' = .error e := by
  rw [h.1, hr]; rfl

/-- **`evalExp`, one step.** -/
theorem step_exp (H : Hyps Q gr gd env) (ih : EraseAt Q gr gd env n) :
    ∀ ρ e, SG Q gd ρ → xExp gr gd e = true →
      ER eraseV (AllIn Q) (evalExp (n + 1) env ρ e) (evalExp (n + 1) env (eraseScope ρ) e) := by
  have hQ := H.inj
  intro ρ e hρ hx
  cases e with
  | varE x =>
    simp only [evalExp]
    exact ER.ofOption (find?_eraseScope ρ x) fun v hv => hρ.find? hv
  | boolE b => simp only [evalExp]; exact ER.ok (a := Value.bool b) trivial
  | numE m => simp only [evalExp]; exact ER.ok (a := Value.num m) trivial
  | textE t => simp only [evalExp]; exact ER.ok (a := Value.text t) trivial
  | unE op t e =>
    simp only [xExp] at hx
    simp only [evalExp]
    refine ER.bind (ih.exp ρ e hρ hx) fun v _ _ => ?_
    rw [unValue_eraseV]
    exact ER.of_bool_num (Erase.unValue_bn _ v)
  | binE op t e₁ e₂ =>
    simp only [xExp, Bool.and_eq_true] at hx
    simp only [evalExp]
    refine ER.bind (ih.exp ρ e₁ hρ hx.1) fun v _ _ => ?_
    rw [boolShort_eraseV]
    cases hb : boolShort op v with
    | some u =>
      obtain ⟨b, rfl⟩ := Erase.boolShort_bool hb
      exact ER.ok (a := Value.bool b) trivial
    | none =>
      refine ER.bind (ih.exp ρ e₂ hρ hx.2) fun w _ _ => ?_
      rw [binValues_eraseV]
      exact ER.of_bool_num (Erase.binValues_bn _ v w)
  | cmpE op t e₁ e₂ =>
    simp only [xExp, Bool.and_eq_true] at hx
    simp only [evalExp]
    refine ER.bind (ih.exp ρ e₁ hρ hx.1) fun v _ hv => ER.bind (ih.exp ρ e₂ hρ hx.2) fun w _ hw => ?_
    rw [cmpValues_eraseV hQ hv hw]
    exact ER.of_bool_num fun u hu => .inl (Erase.cmpValues_bn _ v w u hu)
  | tupE es =>
    simp only [xExp] at hx
    simp only [evalExp]
    exact ER.map Value.tuple (fun vs _ => (eraseV_tuple' vs).symm) (fun vs h => allIn_tuple_of h)
      (ih.exps ρ es hρ hx)
  | projE e i =>
    simp only [xExp] at hx
    simp only [evalExp]
    refine ER.bind (ih.exp ρ e hρ hx) fun v _ hv => ?_
    rw [asTuple?_eraseV]
    cases ht : v.asTuple? with
    | none => exact ER.error _
    | some vs =>
      refine ER.ofOption ?_ ?_
      · split <;> simp [List.getElem?_map]
      · intro u hu
        split at hu
        · exact Erase.allIn_asTuple hv ht u (List.mem_of_getElem? hu)
        · cases hu
  | caseE op e =>
    simp only [xExp] at hx
    simp only [evalExp]
    exact ER.map (Value.case op) (fun _ _ => rfl) (fun _ h => h) (ih.exp ρ e hρ hx)
  | uncaseE e op =>
    simp only [xExp] at hx
    simp only [evalExp]
    refine ER.bind (ih.exp ρ e hρ hx) fun v _ hv => ?_
    rw [asCase?_eraseV]
    cases ht : v.asCase? with
    | none => exact ER.error _
    | some p =>
      obtain ⟨op', w⟩ := p
      simp only [Option.map_some, Res.ofOption_some]
      show ER eraseV (AllIn Q) (Res.assert (op' = op) (.ok w))
        (Res.assert (op' = op) (.ok (eraseV w)))
      exact ER.assert Iff.rfl fun _ => ER.ok (Erase.allIn_asCase hv ht)
  | optE eo =>
    cases eo with
    | none => simp only [evalExp]; exact ER.ok (a := Value.opt none) trivial
    | some e =>
      simp only [xExp, xOExp] at hx
      simp only [evalExp]
      exact ER.map (fun v => Value.opt (some v)) (fun _ _ => rfl) (fun _ h => h) (ih.exp ρ e hρ hx)
  | theE e =>
    simp only [xExp] at hx
    simp only [evalExp]
    refine ER.bind (ih.exp ρ e hρ hx) fun v _ hv => ?_
    rw [asOpt?_eraseV]
    cases ht : v.asOpt? with
    | none => exact ER.error _
    | some o =>
      simp only [Option.map_some, Res.ofOption_some]
      show ER eraseV (AllIn Q) (Res.ofOption o) (Res.ofOption (o.map eraseV))
      exact ER.ofOption rfl (Erase.allIn_asOpt hv ht)
  | strE fs =>
    simp only [xExp] at hx
    simp only [evalExp]
    refine ER.map Value.struct (fun gs hg => ?_) (fun gs hg => ?_) (ih.expFields ρ fs hρ hx)
    · exact (eraseV_struct_of_noExp fun p hp => (hg p hp).2).symm
    · exact allIn_struct_of_noExp (fun p hp => (hg p hp).2) fun p hp => (hg p hp).1
  | dotE e a =>
    simp only [xExp, Bool.and_eq_true, bne_iff_ne, ne_eq] at hx
    simp only [evalExp]
    refine ER.bind (ih.exp ρ e hρ hx.2) fun v _ hv => ?_
    exact ER.ofOption (field?_eraseV hx.1 v) fun u hu => hv.field? hu
  | compE e₁ e₂ =>
    simp only [xExp, Bool.and_eq_true] at hx
    simp only [evalExp]
    refine ER.bind (ih.exp ρ e₁ hρ hx.1.2) fun v _ hv => ER.bind (ih.exp ρ e₂ hρ hx.2) fun w _ hw => ?_
    obtain ⟨gs, rfl, hgs⟩ := nilLit_eval hx.1.1 hx.1.2 ‹_›
    have hg : ∀ p ∈ gs, p.1 ≠ "EXPORTS" ∧ NilV p.2 ∧ AllIn Q p.2 := fun p hp =>
      ⟨(hgs p hp).1, (hgs p hp).2, allIn_struct_fields hv p hp⟩
    obtain ⟨hc, hcA⟩ := comp?_nilLit hg hw
    exact ER.ofOption hc hcA
  | listE es =>
    simp only [xExp] at hx
    simp only [evalExp]
    exact ER.map Value.list (fun vs _ => (eraseV_list' vs).symm) (fun vs h => allIn_list_of h)
      (ih.exps ρ es hρ hx)
  | liftE e =>
    simp only [xExp] at hx
    simp only [evalExp]
    refine ER.bind (ih.exp ρ e hρ hx) fun v _ hv => ?_
    rw [asOpt?_eraseV]
    cases ht : v.asOpt? with
    | none => exact ER.error _
    | some o =>
      simp only [Option.map_some, Res.ofOption_some]
      show ER eraseV (AllIn Q) (.ok (.list o.toList) >>= pure) (.ok (.list (o.map eraseV).toList) >>= pure)
      have := ER.ok (f := eraseV) (P := AllIn Q) (a := .list o.toList)
        (allIn_list_of fun w hw => Erase.allIn_asOpt hv ht w (Option.mem_toList.1 hw))
      cases o <;> simpa [eraseVs_eq_map] using this
  | memE e₁ e₂ =>
    simp only [xExp, Bool.and_eq_true] at hx
    simp only [evalExp]
    refine ER.bind (ih.exp ρ e₁ hρ hx.1) fun v _ hv => ER.bind (ih.exp ρ e₂ hρ hx.2) fun w _ hw => ?_
    rw [memValue_eraseV hQ hv hw]
    exact ER.of_bool_num fun u hu => .inl (Erase.memValue_bn v w u hu)
  | lenE e =>
    simp only [xExp] at hx
    simp only [evalExp]
    refine ER.bind (ih.exp ρ e hρ hx) fun v _ _ => ?_
    rw [len?_eraseV]
    exact ER.of_bool_num fun u hu => by
      simp only [Res.ofOption_eq_ok, Option.map_eq_some_iff] at hu
      obtain ⟨k, -, rfl⟩ := hu
      exact .inr ⟨_, rfl⟩
  | catE e₁ e₂ =>
    simp only [xExp, Bool.and_eq_true] at hx
    simp only [evalExp]
    refine ER.bind (ih.exp ρ e₁ hρ hx.1) fun v _ hv => ER.bind (ih.exp ρ e₂ hρ hx.2) fun w _ hw => ?_
    exact ER.ofOption (cat?_eraseV v w) fun u hu => AllIn.cat? hv hw hu
  | idxE e₁ e₂ =>
    simp only [xExp, Bool.and_eq_true] at hx
    simp only [evalExp]
    refine ER.bind (ih.exp ρ e₁ hρ hx.1) fun v _ hv => ER.bind (ih.exp ρ e₂ hρ hx.2) fun w _ _ => ?_
    rw [asNat?_eraseV]
    cases w.asNat? with
    | none => exact ER.error _
    | some i =>
      simp only [Res.ofOption_some]
      show ER eraseV (AllIn Q) (Res.ofOption (v.idx? i)) (Res.ofOption ((eraseV v).idx? i))
      exact ER.ofOption (idx?_eraseV v i) fun u hu => hv.idx? hu
  | sliceE e₁ e₂ e₃ =>
    simp only [xExp, Bool.and_eq_true] at hx
    simp only [evalExp]
    refine ER.bind (ih.exp ρ e₁ hρ hx.1.1) fun v _ hv => ER.bind (ih.exp ρ e₂ hρ hx.1.2) fun w _ _ =>
      ER.bind (ih.exp ρ e₃ hρ hx.2) fun x _ _ => ?_
    rw [asNat?_eraseV, asNat?_eraseV]
    cases w.asNat? with
    | none => exact ER.error _
    | some i =>
      cases x.asNat? with
      | none => exact ER.error _
      | some k =>
        simp only [Res.ofOption_some]
        show ER eraseV (AllIn Q) (Res.ofOption (v.slice? i k)) (Res.ofOption ((eraseV v).slice? i k))
        exact ER.ofOption (slice?_eraseV v i k) fun u hu => hv.slice? hu
  | updE e₁ p e₂ =>
    simp only [xExp, Bool.and_eq_true] at hx
    simp only [evalExp]
    refine ER.bind (ih.exp ρ e₁ hρ hx.1.1.2) fun v₁ _ hv₁ =>
      ER.bind (ih.exp ρ e₂ hρ hx.2) fun v₂ _ hv₂ => ?_
    exact ⟨ih.pathSet ρ v₁ p v₂ hρ hx.1.2 hv₁, fun u hu =>
      H.upd n ρ v₁ p v₂ u (xPath_dotsOk hx.1.2) hx.1.1.1 hv₁ hv₂ hu⟩
  | extE e₁ p e₂ =>
    simp only [xExp, Bool.and_eq_true] at hx
    simp only [evalExp]
    refine ER.bind (ih.exp ρ e₁ hρ hx.1.1.2) fun v₁ _ hv₁ =>
      ER.bind (ih.exp ρ e₂ hρ hx.2) fun v₂ _ hv₂ =>
        ER.bind (ih.pathGet ρ v₁ p hρ hx.1.2 hv₁) fun u _ hu => ?_
    rw [cat?_eraseV]
    cases hc : Value.cat? u v₂ with
    | none => exact ER.error _
    | some u' =>
      have hu' : AllIn Q u' := AllIn.cat? hu hv₂ hc
      show ER eraseV (AllIn Q) (pathSet n env ρ v₁ p u')
        (pathSet n env (eraseScope ρ) (eraseV v₁) p (eraseV u'))
      exact ⟨ih.pathSet ρ v₁ p u' hρ hx.1.2 hv₁, fun w hw =>
        H.upd n ρ v₁ p u' w (xPath_dotsOk hx.1.2) hx.1.1.1 hv₁ hu' hw⟩
  | callE x args =>
    simp only [xExp, Bool.and_eq_true] at hx
    simp only [evalExp]
    exact ih.callDef ρ x args hρ hx.1 hx.2
  | iterE e it =>
    obtain ⟨it, ds⟩ := it
    simp only [xExp, Bool.and_eq_true] at hx
    simp only [evalExp]
    exact ih.iterE ρ e it ds hρ hx.1.1 hx.1.2 hx.2
  | cvtE e t₁ t₂ =>
    simp only [xExp] at hx
    simp only [evalExp]
    refine ER.bind (ih.exp ρ e hρ hx) fun v _ _ => ?_
    rw [asNum?_eraseV]
    cases v.asNum? with
    | none => exact ER.error _
    | some m =>
      exact ER.of_bool_num fun u hu => by
        simp only [Res.ofOption_some, bind, Except.bind, Res.ofOption_eq_ok,
          Option.map_eq_some_iff] at hu
        obtain ⟨k, -, rfl⟩ := hu
        exact .inr ⟨_, rfl⟩
  | subE e t₁ t₂ =>
    simp only [xExp] at hx
    simp only [evalExp]
    exact ih.exp ρ e hρ hx

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
