module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxErase.Basic

/-!
# Round 7, REH route 2: the erasure copy without `QInj`, `evalExp` in one step (unrefined)

The proof follows round 3's `EraseAll.step_exp` case by case, with every value in the swap set
(`QT`). The two cases that used `QInj` there, equality and membership tests, use the site check
instead: `NxSites.badE … = 0` makes one operand `nxE`, `NxFlow.expAt` makes its value
export-free, and then the test reads alike before and after erasure.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxErase

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope ScopeIn find?_eraseScope)

variable {gr gd : String → Bool} {env : Env} {n : Nat}

/-- A comparison site that passes `NxSites.siteOk`, evaluated in a conforming scope, has an
export-free operand. -/
theorem nx_of_site {S : Sig} {T : TSig} {Γ : List (String × AT)} {tps : AuxCtx} {ρ : VarEnv}
    {e₁ e₂ : Exp} {v w : Value} (hρ : ScopeVT S Γ ρ) (hc : CallH S T tps env ρ n)
    (hs : siteOk S Γ e₁ e₂ = true) (ht₁ : tyOk S T Γ e₁ = true) (ht₂ : tyOk S T Γ e₂ = true)
    (ha₁ : auxE tps e₁ = true) (ha₂ : auxE tps e₂ = true) (hv : evalExp n env ρ e₁ = .ok v)
    (hw : evalExp n env ρ e₂ = .ok w) : nxB v = true ∨ nxB w = true := by
  simp only [siteOk, Bool.or_eq_true] at hs
  rcases hs with hs | hs
  · exact .inl (((expAt env n).exp S T Γ tps ρ e₁ v hρ hc ht₁ ha₁ hv).nx (nxD_of_nxE _ hs))
  · exact .inr (((expAt env n).exp S T Γ tps ρ e₂ w hρ hc ht₂ ha₂ hw).nx (nxD_of_nxE _ hs))

set_option maxHeartbeats 1000000 in
/-- **`evalExp`, one step.** -/
theorem step_exp (ih : NAt gr gd env n) : ∀ (S : Sig) (T : TSig) (Γ : List (String × AT))
    (tps : AuxCtx) (ρ : VarEnv) (e : Exp), ScopeVT S Γ ρ → NCalls gd S T tps env ρ (n + 1) →
    tyOk S T Γ e = true → auxE tps e = true → auxX tps e = true → badE S Γ e = 0 →
    xExp gr gd e = true →
    ER eraseV (AllIn QT) (evalExp (n + 1) env ρ e) (evalExp (n + 1) env (eraseScope ρ) e) := by
  intro S T Γ tps ρ e hρ hc ht ha hX hb hx
  have hc' := hc.mono (Nat.le_succ n)
  have E := fun e => ih.exp S T Γ tps ρ e hρ hc'
  cases e with
  | varE x =>
    simp only [evalExp]
    exact ER.ofOption (find?_eraseScope ρ x) fun v _ => allIn_top v
  | boolE b => simp only [evalExp]; exact ER.ok (a := Value.bool b) trivial
  | numE m => simp only [evalExp]; exact ER.ok (a := Value.num m) trivial
  | textE t => simp only [evalExp]; exact ER.ok (a := Value.text t) trivial
  | unE op t e =>
    simp only [tyOk, auxE, auxX, badE, xExp] at ht ha hX hb hx
    simp only [evalExp]
    refine ER.bind (E e ht ha hX hb hx) fun v _ _ => ?_
    rw [unValue_eraseV]
    exact ER.of_bool_num (Erase.unValue_bn _ v)
  | binE op t e₁ e₂ =>
    simp only [tyOk, auxE, auxX, badE, xExp, Bool.and_eq_true, Nat.add_eq_zero_iff] at ht ha hX hb hx
    simp only [evalExp]
    refine ER.bind (E e₁ ht.1 ha.1 hX.1 hb.1 hx.1) fun v _ _ => ?_
    rw [boolShort_eraseV]
    cases hbs : boolShort op v with
    | some u =>
      obtain ⟨b, rfl⟩ := Erase.boolShort_bool hbs
      exact ER.ok (a := Value.bool b) trivial
    | none =>
      refine ER.bind (E e₂ ht.2 ha.2 hX.2 hb.2 hx.2) fun w _ _ => ?_
      rw [binValues_eraseV]
      exact ER.of_bool_num (Erase.binValues_bn _ v w)
  | cmpE op t e₁ e₂ =>
    simp only [tyOk, auxE, auxX, badE, xExp, Bool.and_eq_true, Nat.add_eq_zero_iff] at ht ha hX hb hx
    simp only [evalExp]
    refine ER.bind (E e₁ ht.1 ha.1 hX.1 hb.1.2 hx.1) fun v hv _ =>
      ER.bind (E e₂ ht.2 ha.2 hX.2 hb.2 hx.2) fun w hw _ => ?_
    have hcmp : cmpValues op (eraseV v) (eraseV w) = cmpValues op v w := by
      by_cases h1 : op = .eqOp ∨ op = .neOp
      · have hs : siteOk S Γ e₁ e₂ = true := by
          have hr := hb.1.1
          rcases h1 with rfl | rfl <;>
            · simp only [rootBad] at hr
              split at hr
              · assumption
              · omega
        exact cmpValues_eraseV_nx (nx_of_site hρ hc'.callH hs ht.1 ht.2 ha.1 ha.2 hv hw) op
      · simp only [not_or] at h1
        exact cmpValues_eraseV_ord h1.1 h1.2 v w
    rw [hcmp]
    exact ER.of_bool_num fun u hu => .inl (Erase.cmpValues_bn _ v w u hu)
  | tupE es =>
    simp only [tyOk, auxE, auxX, badE, xExp] at ht ha hX hb hx
    simp only [evalExp]
    exact ER.map Value.tuple (fun vs _ => (eraseV_tuple' vs).symm)
      (fun vs _ => allIn_top _) (ih.exps S T Γ tps ρ es hρ hc' ht ha hX hb hx)
  | projE e i =>
    simp only [tyOk, auxE, auxX, badE, xExp] at ht ha hX hb hx
    simp only [evalExp]
    refine ER.bind (E e ht ha hX hb hx) fun v _ _ => ?_
    rw [asTuple?_eraseV]
    cases v.asTuple? with
    | none => exact ER.error _
    | some vs =>
      refine ER.ofOption ?_ fun u _ => allIn_top u
      split <;> simp [List.getElem?_map]
  | caseE op e =>
    simp only [tyOk, auxE, auxX, badE, xExp] at ht ha hX hb hx
    simp only [evalExp]
    exact ER.map (Value.case op) (fun _ _ => rfl) (fun _ h => h) (E e ht ha hX hb hx)
  | uncaseE e op =>
    simp only [tyOk, auxE, auxX, badE, xExp] at ht ha hX hb hx
    simp only [evalExp]
    refine ER.bind (E e ht ha hX hb hx) fun v _ _ => ?_
    rw [asCase?_eraseV]
    cases v.asCase? with
    | none => exact ER.error _
    | some p =>
      obtain ⟨op', w⟩ := p
      simp only [Option.map_some, Res.ofOption_some]
      show ER eraseV (AllIn QT) (Res.assert (op' = op) (.ok w))
        (Res.assert (op' = op) (.ok (eraseV w)))
      exact ER.assert Iff.rfl fun _ => ER.ok (allIn_top w)
  | optE eo =>
    cases eo with
    | none => simp only [evalExp]; exact ER.ok (a := Value.opt none) trivial
    | some e =>
      simp only [tyOk, auxE, auxX, badE, badO, xExp, xOExp] at ht ha hX hb hx
      simp only [evalExp]
      exact ER.map (fun v => Value.opt (some v)) (fun _ _ => rfl) (fun _ h => h)
        (E e ht ha hX hb hx)
  | theE e =>
    simp only [tyOk, auxE, auxX, badE, xExp] at ht ha hX hb hx
    simp only [evalExp]
    refine ER.bind (E e ht ha hX hb hx) fun v _ _ => ?_
    rw [asOpt?_eraseV]
    cases v.asOpt? with
    | none => exact ER.error _
    | some o =>
      simp only [Option.map_some, Res.ofOption_some]
      show ER eraseV (AllIn QT) (Res.ofOption o) (Res.ofOption (o.map eraseV))
      exact ER.ofOption rfl fun u _ => allIn_top u
  | strE fs =>
    simp only [tyOk, auxE, auxX, badE, xExp] at ht ha hX hb hx
    simp only [evalExp]
    refine ER.map Value.struct (fun gs hg => ?_) (fun gs _ => allIn_top _)
      (ih.fields S T Γ tps ρ fs hρ hc' ht ha hX hb hx)
    exact (eraseV_struct_of_noExp fun p hp => (hg p hp).2).symm
  | dotE e a =>
    simp only [tyOk, auxE, auxX, badE, xExp, Bool.and_eq_true, bne_iff_ne, ne_eq] at ht ha hX hb hx
    simp only [evalExp]
    refine ER.bind (E e ht ha hX hb hx.2) fun v _ _ => ?_
    exact ER.ofOption (field?_eraseV hx.1 v) fun u _ => allIn_top u
  | compE e₁ e₂ =>
    simp only [tyOk, auxE, auxX, badE, xExp, Bool.and_eq_true, Nat.add_eq_zero_iff] at ht ha hX hb hx
    simp only [evalExp]
    refine ER.bind (E e₁ ht.1 ha.1 hX.1 hb.1 hx.1.2) fun v hv _ =>
      ER.bind (E e₂ ht.2 ha.2 hX.2 hb.2 hx.2) fun w _ _ => ?_
    obtain ⟨gs, rfl, hgs⟩ := nilLit_eval hx.1.1 hx.1.2 hv
    have hg : ∀ p ∈ gs, p.1 ≠ "EXPORTS" ∧ NilV p.2 ∧ AllIn QT p.2 := fun p hp =>
      ⟨(hgs p hp).1, (hgs p hp).2, allIn_top _⟩
    obtain ⟨hcp, hcA⟩ := comp?_nilLit hg (allIn_top w)
    exact ER.ofOption hcp hcA
  | listE es =>
    simp only [tyOk, auxE, auxX, badE, xExp, Bool.and_eq_true] at ht ha hX hb hx
    simp only [evalExp]
    exact ER.map Value.list (fun vs _ => (eraseV_list' vs).symm) (fun vs _ => allIn_top _)
      (ih.exps S T Γ tps ρ es hρ hc' ht.1 ha hX hb hx)
  | liftE e =>
    simp only [tyOk, auxE, auxX, badE, xExp] at ht ha hX hb hx
    simp only [evalExp]
    refine ER.bind (E e ht ha hX hb hx) fun v _ _ => ?_
    rw [asOpt?_eraseV]
    cases v.asOpt? with
    | none => exact ER.error _
    | some o =>
      simp only [Option.map_some, Res.ofOption_some]
      show ER eraseV (AllIn QT) (.ok (.list o.toList) >>= pure)
        (.ok (.list (o.map eraseV).toList) >>= pure)
      have := ER.ok (f := eraseV) (P := AllIn QT) (a := .list o.toList) (allIn_top _)
      cases o <;> simpa [eraseVs_eq_map] using this
  | memE e₁ e₂ =>
    simp only [tyOk, auxE, auxX, badE, xExp, Bool.and_eq_true, Nat.add_eq_zero_iff] at ht ha hX hb hx
    simp only [evalExp]
    refine ER.bind (E e₁ ht.1 ha.1 hX.1 hb.1.2 hx.1) fun v hv _ =>
      ER.bind (E e₂ ht.2 ha.2 hX.2 hb.2 hx.2) fun w hw _ => ?_
    have hs : siteOk S Γ e₁ e₂ = true := by
      have hr := hb.1.1
      simp only [rootBad] at hr
      split at hr
      · assumption
      · omega
    rw [memValue_eraseV_nx (nx_of_site hρ hc'.callH hs ht.1 ht.2 ha.1 ha.2 hv hw)]
    exact ER.of_bool_num fun u hu => .inl (Erase.memValue_bn v w u hu)
  | lenE e =>
    simp only [tyOk, auxE, auxX, badE, xExp] at ht ha hX hb hx
    simp only [evalExp]
    refine ER.bind (E e ht ha hX hb hx) fun v _ _ => ?_
    rw [len?_eraseV]
    exact ER.of_bool_num fun u hu => by
      simp only [Res.ofOption_eq_ok, Option.map_eq_some_iff] at hu
      obtain ⟨k, -, rfl⟩ := hu
      exact .inr ⟨_, rfl⟩
  | catE e₁ e₂ =>
    simp only [tyOk, auxE, auxX, badE, xExp, Bool.and_eq_true, Nat.add_eq_zero_iff] at ht ha hX hb hx
    simp only [evalExp]
    refine ER.bind (E e₁ ht.1.1 ha.1 hX.1 hb.1 hx.1) fun v _ _ =>
      ER.bind (E e₂ ht.1.2 ha.2 hX.2 hb.2 hx.2) fun w _ _ => ?_
    exact ER.ofOption (cat?_eraseV v w) fun u _ => allIn_top u
  | idxE e₁ e₂ =>
    simp only [tyOk, auxE, auxX, badE, xExp, Bool.and_eq_true, Nat.add_eq_zero_iff] at ht ha hX hb hx
    simp only [evalExp]
    refine ER.bind (E e₁ ht.1 ha.1 hX.1 hb.1 hx.1) fun v _ _ =>
      ER.bind (E e₂ ht.2 ha.2 hX.2 hb.2 hx.2) fun w _ _ => ?_
    rw [asNat?_eraseV]
    cases w.asNat? with
    | none => exact ER.error _
    | some i =>
      simp only [Res.ofOption_some]
      show ER eraseV (AllIn QT) (Res.ofOption (v.idx? i)) (Res.ofOption ((eraseV v).idx? i))
      exact ER.ofOption (idx?_eraseV v i) fun u _ => allIn_top u
  | sliceE e₁ e₂ e₃ =>
    simp only [tyOk, auxE, auxX, badE, xExp, Bool.and_eq_true, Nat.add_eq_zero_iff] at ht ha hX hb hx
    simp only [evalExp]
    refine ER.bind (E e₁ ht.1.1 ha.1.1 hX.1.1 hb.1.1 hx.1.1) fun v _ _ =>
      ER.bind (E e₂ ht.1.2 ha.1.2 hX.1.2 hb.1.2 hx.1.2) fun w _ _ =>
        ER.bind (E e₃ ht.2 ha.2 hX.2 hb.2 hx.2) fun x _ _ => ?_
    rw [asNat?_eraseV, asNat?_eraseV]
    cases w.asNat? with
    | none => exact ER.error _
    | some i =>
      cases x.asNat? with
      | none => exact ER.error _
      | some k =>
        simp only [Res.ofOption_some]
        show ER eraseV (AllIn QT) (Res.ofOption (v.slice? i k))
          (Res.ofOption ((eraseV v).slice? i k))
        exact ER.ofOption (slice?_eraseV v i k) fun u _ => allIn_top u
  | updE e₁ p e₂ =>
    simp only [tyOk, auxE, auxX, badE, xExp, Bool.and_eq_true, Nat.add_eq_zero_iff] at ht ha hX hb hx
    simp only [evalExp]
    refine ER.bind (E e₁ ht.1.1 ha.1 hX.1.1 hb.1.1 hx.1.1.2) fun v₁ _ _ =>
      ER.bind (E e₂ ht.2 ha.2 hX.2 hb.2 hx.2) fun v₂ _ _ => ?_
    exact ⟨ih.pathSet S T Γ tps ρ v₁ p v₂ hρ hc' ht.1.2 hX.1.2 hb.1.2 hx.1.2,
      fun u _ => allIn_top u⟩
  | extE e₁ p e₂ =>
    simp only [tyOk, auxE, auxX, badE, xExp, Bool.and_eq_true, Nat.add_eq_zero_iff] at ht ha hX hb hx
    simp only [evalExp]
    refine ER.bind (E e₁ ht.1.1 ha.1 hX.1.1 hb.1.1 hx.1.1.2) fun v₁ _ _ =>
      ER.bind (E e₂ ht.2 ha.2 hX.2 hb.2 hx.2) fun v₂ _ _ =>
        ER.bind (ih.pathGet S T Γ tps ρ v₁ p hρ hc' ht.1.2 hX.1.2 hb.1.2 hx.1.2) fun u _ _ => ?_
    rw [cat?_eraseV]
    cases Value.cat? u v₂ with
    | none => exact ER.error _
    | some u' =>
      show ER eraseV (AllIn QT) (pathSet n env ρ v₁ p u')
        (pathSet n env (eraseScope ρ) (eraseV v₁) p (eraseV u'))
      exact ⟨ih.pathSet S T Γ tps ρ v₁ p u' hρ hc' ht.1.2 hX.1.2 hb.1.2 hx.1.2,
        fun w _ => allIn_top w⟩
  | callE f args =>
    simp only [evalExp]
    exact ih.call S T Γ tps ρ f args hρ hc' ht ha hX hb hx
  | iterE e it =>
    obtain ⟨it, ds⟩ := it
    simp only [tyOk, auxE, auxX, badE, xExp, Bool.and_eq_true, Nat.add_eq_zero_iff] at ht ha hX hb hx
    simp only [evalExp]
    exact ih.iter S T Γ tps ρ e it ds hρ hc' ht.1.1 ht.1.2 ht.2 ha.1.1.1 ha.1.1.2 ha.1.2 ha.2
      hX.1.1 hX.1.2 hX.2 hb.1.1 hb.1.2 hb.2 hx.1.1 hx.1.2 hx.2
  | cvtE e t₁ t₂ =>
    simp only [tyOk, auxE, auxX, badE, xExp] at ht ha hX hb hx
    simp only [evalExp]
    refine ER.bind (E e ht ha hX hb hx) fun v _ _ => ?_
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
    simp only [tyOk, auxE, auxX, badE, xExp, Bool.and_eq_true] at ht ha hX hb hx
    simp only [evalExp]
    exact E e ht.1 ha hX hb hx

end Silmaril.Wasm.SpecTec.Sim.Round7.NxErase
