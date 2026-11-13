module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.XSwap.Prem

/-!
# derivations across the re-encoding (unrefined)

Under the declarative reading with optional conclusions (`Round6.Reading.DDerivesB`), in
`utf8Env20T B`:

* `dderivesB_swap`: a derivation of `Step`, `Step_read` or `Step_pure` (`gr20`) at `w` gives one
  at `swapX w`, whenever the reading `O` of `otherwise` moves to `O'` along `swapX`. By mutual
  structural recursion on the derivation: quantifiers by `hasTyp_erase` (with the fuel shift
  `K`), conclusions and side conditions by the evaluator-level re-encoding, relation premises by
  recursion (the check `xPrem` keeps them in `gr20`).
* `ruleBodyB_swap`: a rule body under `DDerivesB env noElse` moves the same way; this is what an
  `otherwise` premise quantifies over.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.concreteInstances false

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.Typ

variable [XTau]

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.XSwap.Swap
open Silmaril.Wasm.SpecTec.Sim20.XSwap.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll (Hyps SG ArgIn gr20 gd20 xRule xPrem xIter eraseP
  xExp)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (utf8Env20T)
open Silmaril.Wasm.SpecTec.Sim (QuantsOk ElseI Interp PremW RuleBody noElse domSomes domLists)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (DDerivesB DPremB RuleBodyB conclAlts hasOptNil
  optAlts)

variable {B : Builtins}

theorem mem_rels_of_findRel {x : IL.Id} {d : RelDef} (h : (utf8Env20T B).findRel? x = some d) :
    (x, d) ∈ relsOfDefs Silmaril.Wasm.SpecTec.Sim20.StoreFix.fixedT20 := by
  rw [Utf8Mono.findRel?_utf8Env20T] at h
  exact EraseAll.mem_rels_of_findRel20 h

/-- What the kernel checks say about a relation of `gr20`. -/
theorem relFacts {x : IL.Id} {d : RelDef} (h : (utf8Env20T B).findRel? x = some d)
    (hx : gr20 x = true) :
    d.1 = [] ∧ (∀ r ∈ d.2.2.2, xRule gr20 gd20 r = true) ∧
      (∀ r ∈ d.2.2.2, match r with
        | .ruleD _ qs _ e _ => (∀ y t, Param.expP y t ∈ qs → xTy tyC20 t = true) ∧
            (∀ e' ∈ conclAlts e, xExp gr20 gd20 e' = true)) := by
  have hm := mem_rels_of_findRel h
  have h₁ := List.all_eq_true.1 relsNoParams20 _ hm
  simp only [hx, Bool.not_true, Bool.false_or, List.isEmpty_iff] at h₁
  have h₂ := List.all_eq_true.1 EraseAll.xRelsOk20 _ hm
  simp only [hx, Bool.not_true, Bool.false_or, List.all_eq_true] at h₂
  have h₃ := List.all_eq_true.1 xRelQuants20 _ hm
  simp only [hx, Bool.not_true, Bool.false_or, List.all_eq_true] at h₃
  have h₄ := List.all_eq_true.1 EraseAll.xAltsOk20 _ hm
  simp only [hx, Bool.not_true, Bool.false_or, List.all_eq_true] at h₄
  refine ⟨h₁, h₂, fun r hr => ?_⟩
  obtain ⟨nm, qs, op, e, prems⟩ := r
  refine ⟨fun y t hq => ?_, fun e' he' => ?_⟩
  · have h₃' := h₃ _ hr
    simp only [List.all_eq_true] at h₃'
    simpa using h₃' _ hq
  rcases List.mem_cons.1 he' with rfl | he'
  · have := h₂ _ hr
    simp only [xRule, Bool.and_eq_true] at this
    exact this.1
  · have h₅ := h₄ _ hr
    simp only at h₅
    split at he'
    · rename_i hn
      simp only [hn, ite_true, List.all_eq_true] at h₅
      exact h₅ e' he'
    · cases he'

section
variable (H : Hyps QT gr20 gd20 (utf8Env20T B)) {K : Nat} (hK : ExpK B K)
include H hK

/-- **Quantifiers stay typed on the re-encoded scope.** -/
theorem quantsOk_erase {ρ : VarEnv} {qs : List Param} (hρ : SG QT gd20 ρ) (hX : XT ρ)
    (hq : ∀ x t, Param.expP x t ∈ qs → xTy tyC20 t = true) (h : QuantsOk (utf8Env20T B) ρ qs) :
    QuantsOk (utf8Env20T B) (eraseScope ρ) qs := by
  intro x t hm
  obtain ⟨w, hw, ht⟩ := h x t hm
  refine ⟨swapX w, ?_, hasTyp_erase H hK hρ hX (hq x t hm) ht⟩
  rw [Erase.find?_eraseScope, hw]
  rfl

omit H hK in
theorem eraseScope_inst (σ : List (IL.Id × Value)) :
    eraseScope (VarEnv.empty.bindVals σ) = VarEnv.empty.bindVals (σ.map eraseP) := by
  rw [EraseAll.eraseScope_bindVals, EraseAll.eraseScope_empty]

set_option maxRecDepth 20000 in
mutual

/-- **A derivation of a `gr20` relation moves across the re-encoding.** -/
theorem dderivesB_swap {O O' : ElseI}
    (hO : ∀ x i v, gr20 x = true → O x [] i v → O' x [] i (swapX v)) :
    ∀ {x : IL.Id} {op : MixopS} {avs : List ArgV} {w : Value},
    DDerivesB (utf8Env20T B) O x op avs w → gr20 x = true →
    DDerivesB (utf8Env20T B) O' x op (avs.map eraseA) (swapX w)
  | x, op, avs, w, .rule (ps := ps) (rules := rules) (i := i) (nm := nm) (qs := qs) (e := e)
      (e' := e') (prems := prems) (ρ₀ := ρ₀) (σ := σ) hrel hrule halt hps hq he hp, hG =>
    have ih : ∀ pr ∈ prems, ∀ {els' : Prop}, SG QT gd20 (ρ₀.bindVals σ) →
        xPrem gr20 gd20 pr = true → (O x avs i w → els') →
        DPremB (utf8Env20T B) O' els' (eraseScope (ρ₀.bindVals σ)) pr :=
      fun pr hpr => dpremB_swap hO (hp pr hpr)
    by
    obtain ⟨hps0, hrules, hqa⟩ := relFacts hrel hG
    simp only at hps0
    subst hps0
    have hargs : avs = [] ∧ ρ₀ = VarEnv.empty := by
      cases avs with
      | nil => simp only [Sem.bindParams, Option.some.injEq] at hps; exact ⟨rfl, hps.symm⟩
      | cons _ _ => simp [Sem.bindParams] at hps
    obtain ⟨rfl, rfl⟩ := hargs
    have hmem := List.mem_of_getElem? hrule
    have hx := hrules _ hmem
    simp only [xRule, Bool.and_eq_true] at hx
    have hqa' := hqa _ hmem
    simp only at hqa'
    have hρ : SG QT gd20 (VarEnv.empty.bindVals σ) := sg_bindVals EraseAll.sg_empty σ
    have hX : XT (VarEnv.empty.bindVals σ) := xt_of_typs xt_empty rfl
    refine DDerivesB.rule (σ := σ.map eraseP) hrel hrule halt rfl ?_ ?_ ?_
    · rw [← eraseScope_inst]
      exact quantsOk_erase H hK hρ hX hqa'.1 hq
    · rw [← eraseScope_inst]
      exact evalExp_erase H hρ (hqa'.2 e' halt) he
    · intro pr hpr
      rw [← eraseScope_inst]
      exact ih pr hpr hρ (EraseAll.xPrems_mem hx.2 pr hpr) (hO x i w hG)

/-- **A premise moves across the re-encoding.** -/
theorem dpremB_swap {O O' : ElseI}
    (hO : ∀ x i v, gr20 x = true → O x [] i v → O' x [] i (swapX v)) :
    ∀ {els els' : Prop} {ρ : VarEnv} {pr : Prem},
    DPremB (utf8Env20T B) O els ρ pr → SG QT gd20 ρ → xPrem gr20 gd20 pr = true →
    (els → els') → DPremB (utf8Env20T B) O' els' (eraseScope ρ) pr
  | _, _, ρ, _, .ifPr he, hρ, hx, _ =>
    .ifPr (by simpa using evalExp_erase H hρ (by simpa [xPrem] using hx) he)
  | _, _, _, _, .elsePr h, _, _, hE => .elsePr (hE h)
  | _, _, ρ, _, .letPr he₂ he₁, hρ, hx, _ => by
    simp only [xPrem, Bool.and_eq_true] at hx
    exact .letPr (evalExp_erase H hρ hx.2 he₂) (evalExp_erase H hρ hx.1 he₁)
  | _, _, ρ, .rulePr x _ _ _, .rulePr hargs he hd, hρ, hx, _ =>
    have hx' : gr20 x = true ∧ _ := by
      simp only [xPrem, Bool.and_eq_true] at hx
      exact ⟨hx.1.1, hx⟩
    have ih := dderivesB_swap hO hd hx'.1
    by
    have hx := hx'.2
    exact .rulePr (evalArgs_erase H hρ hx.1.2 hargs) (evalExp_erase H hρ hx.2 he) ih
  | _, _, ρ, _, .iterOptNone (xvs := xvs) hdoms hne hall, hρ, hx, _ => by
    simp only [xPrem, Bool.and_eq_true] at hx
    refine .iterOptNone (evalDoms_erase H hρ hx.2 hdoms) hne ?_
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    simp [eraseP, hall q hq]
  | _, _, ρ, _, .iterOptSome (row := row) hdoms hne hsome hpr, hρ, hx, hE =>
    have ih := fun h => dpremB_swap hO hpr (sg_bindVals hρ row) h hE
    by
    simp only [xPrem, Bool.and_eq_true] at hx
    refine .iterOptSome (row := row.map eraseP) (evalDoms_erase H hρ hx.2 hdoms) hne
      (by rw [domSomes_erase, hsome]; rfl) ?_
    rw [← EraseAll.eraseScope_bindVals]
    exact ih hx.1.1
  | _, _, ρ, _, .iterList (dls := dls) (k := k) hit hdoms hne hdl hlen hrows, hρ, hx, hE =>
    have ih := fun r₀ hr₀ h => dpremB_swap hO (hrows r₀ hr₀) (sg_bindVals hρ r₀) h hE
    by
    simp only [xPrem, Bool.and_eq_true] at hx
    refine .iterList (dls := dls.map fun p => (p.1, p.2.map swapX)) (k := k) hit
      (evalDoms_erase H hρ hx.2 hdoms) hne (by rw [domLists_erase, hdl]; rfl) ?_ ?_
    · intro d hd
      obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.1 hd
      simpa using hlen d₀ hd₀
    · intro r hr
      rw [EraseAll.iterRows_erase] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := mem_map_eraseP_rows hr
      rw [← EraseAll.eraseScope_bindVals]
      exact ih r₀ hr₀ hx.1.1
  | _, _, ρ, _, .iterListN (eₙ := eₙ) (dls := dls) (kv := kv) (k := k) hdoms hn hk hdl hlen hrows,
      hρ, hx, hE =>
    have ih := fun r₀ hr₀ h => dpremB_swap hO (hrows r₀ hr₀) (sg_bindVals hρ r₀) h hE
    by
    simp only [xPrem, Bool.and_eq_true] at hx
    have hxn : xExp gr20 gd20 eₙ = true := by simpa [xIter] using hx.1.2
    refine .iterListN (dls := dls.map fun p => (p.1, p.2.map swapX)) (kv := swapX kv) (k := k)
      (evalDoms_erase H hρ hx.2 hdoms) (evalExp_erase H hρ hxn hn)
      (by rw [asNat?_eraseC]; exact hk) (by rw [domLists_erase, hdl]; rfl) ?_ ?_
    · intro d hd
      obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.1 hd
      simpa using hlen d₀ hd₀
    · intro r hr
      rw [EraseAll.iterRows_erase] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := mem_map_eraseP_rows hr
      rw [← EraseAll.eraseScope_bindVals]
      exact ih r₀ hr₀ hx.1.1

end

/-- **A rule body of a `gr20` relation, read by `DDerivesB env noElse`, moves across the
re-encoding**, whenever its `otherwise` premise does. -/
theorem ruleBodyB_swap {x : IL.Id} {d : RelDef} (hrel : (utf8Env20T B).findRel? x = some d)
    (hG : gr20 x = true) {r : Rule} (hr : r ∈ d.2.2.2) {els els' : Prop} {op : MixopS}
    {v : Value} (hE : els → els')
    (h : RuleBodyB (utf8Env20T B) (DDerivesB (utf8Env20T B) noElse) els d.1 [] op r v) :
    RuleBodyB (utf8Env20T B) (DDerivesB (utf8Env20T B) noElse) els' d.1 [] op r (swapX v) := by
  obtain ⟨hps0, hrules, hqa⟩ := relFacts hrel hG
  rw [hps0] at h ⊢
  obtain ⟨nm, qs, op', e, prems⟩ := r
  have hx := hrules _ hr
  simp only [xRule, Bool.and_eq_true] at hx
  have hqa' := hqa _ hr
  simp only at hqa'
  obtain ⟨e', halt, hop, ρ₀, σ, hb, hqs, he, hps⟩ := h
  simp only [Sem.bindParams, Option.some.injEq] at hb
  subst hb
  have hρ : SG QT gd20 (VarEnv.empty.bindVals σ) := sg_bindVals EraseAll.sg_empty σ
  have hX : XT (VarEnv.empty.bindVals σ) := xt_of_typs xt_empty rfl
  refine ⟨e', halt, hop, VarEnv.empty, σ.map eraseP, rfl, ?_, ?_, ?_⟩
  · rw [← eraseScope_inst]; exact quantsOk_erase H hK hρ hX hqa'.1 hqs
  · rw [← eraseScope_inst]; exact evalExp_erase H hρ (hqa'.2 e' halt) he
  · intro pr hpr
    rw [← eraseScope_inst]
    refine premW_erase H (hps pr hpr) hρ (EraseAll.xPrems_mem hx.2 pr hpr) ?_ hE
    intro y op avs w hy hd
    exact dderivesB_swap H hK (O := noElse) (O' := noElse) (fun _ _ _ _ h => h) hd hy

end

end Silmaril.Wasm.SpecTec.Sim20.XSwap.Typ
