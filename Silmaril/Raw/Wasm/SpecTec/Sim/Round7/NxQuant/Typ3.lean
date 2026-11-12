module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxQuant.Typ2

/-!
# Round 7, REH route 2: the induction on `hasTyp`'s fuel, one step (unrefined)
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)

variable {env : Env} {m : Nat}

theorem vtB_of_nxB' {a : AT} {v : Value} (h : nxB v = true) : vtB sigX a v = true :=
  vtB_of_nxB sigX a v h

theorem fieldAtoms_cons (a : AtomS) (t : Typ) (q : List Param) (p : List Prem)
    (fs : List TypField) : fieldAtoms (.mk a t q p :: fs) = a :: fieldAtoms fs := rfl

theorem fieldOf_mem : ∀ {fs : List TypField} {k : String} {t : Typ}, fieldOf k fs = some t →
    k ∈ fieldAtoms fs
  | [], _, _, h => by simp [fieldOf] at h
  | .mk a t' _ _ :: fs, k, t, h => by
    simp only [fieldOf] at h
    simp only [fieldAtoms, List.map_cons, List.mem_cons]
    split at h
    · rename_i hk; exact .inl (beq_iff_eq.1 hk).symm
    · exact .inr (fieldOf_mem h)

theorem noAlias_of {x : String} {dt : DefTyp} (hx : XF x dt) (hdt : ∀ t, dt ≠ .aliasT t) :
    sigX.aliases.lookup x = none := by
  cases hl : sigX.aliases.lookup x with
  | none => rfl
  | some a =>
    obtain ⟨p, hp, h1, _⟩ := lookup_entry hl
    obtain ⟨t, ht, _⟩ := hx.ali p hp h1
    exact absurd ht (hdt t)

theorem noFields_of {x : String} {dt : DefTyp} (hx : XF x dt) (hdt : ∀ fs, dt ≠ .structT fs) :
    ∀ p ∈ sigX.fields, p.1 ≠ x := by
  intro p hp h1
  obtain ⟨fs, hfs, _⟩ := hx.field p hp h1
  exact hdt fs hfs

theorem noCases_of {x : String} {dt : DefTyp} (hx : XF x dt) (hdt : ∀ cs, dt ≠ .variantT cs) :
    ∀ p ∈ sigX.cases, p.1 ≠ x := by
  intro p hp h1
  obtain ⟨cs, hcs, _⟩ := hx.case p hp h1
  exact hdt cs hcs

/-- At a name with neither alias, fields nor cases, every value conforms (off export-free). -/
theorem vtB_name_plain {x : String} {A : List AT} (hn : nxAT sigX.good (.name x A) = false)
    (ha : sigX.aliases.lookup x = none) (hf : ∀ p ∈ sigX.fields, p.1 ≠ x)
    (hc : ∀ p ∈ sigX.cases, p.1 ≠ x) (v : Value) : vtB sigX (.name x A) v = true := by
  rw [vtB_name hn (unf_name_none ha)]
  cases v with
  | struct gs => exact vtF_noFields hf gs
  | case op w =>
    show vtB sigX (caseAT sigX x op) w = true
    rw [caseAT_noCases hc]; exact vtB_unk _ _
  | _ => rfl

theorem nx_name_good {x : String} {A : List AT} (h : nxAT sigX.good (.name x A) = true) :
    sigX.good.contains x = true := by
  simp only [nxAT, Bool.and_eq_true] at h; exact h.1

set_option maxHeartbeats 800000 in
theorem vt_defT_succ (hE : EnvNx sigX.good env) (ih : VtTyp env m) (x : String) (ρ : VarEnv)
    (dt : DefTyp) (v : Value) (A : List AT) (hx : XF x dt) (hρ : ρ.typs = [])
    (h : hasTypDef (m + 1) env ρ dt v = .ok true) : vtB sigX (.name x A) v = true := by
  cases dt with
  | aliasT t =>
    simp only [hasTypDef] at h
    have hv := ih.typ ρ t v (typsNx_nil hρ) h
    cases hn : nxAT sigX.good (.name x A)
    · cases hl : sigX.aliases.lookup x with
      | some a =>
        obtain ⟨p, hp, h1, h2⟩ := lookup_entry hl
        obtain ⟨t', ht', ha'⟩ := hx.ali p hp h1
        cases ht'
        rw [h2] at ha'
        rw [ha'] at hv
        cases hna : nxAT sigX.good a
        · rw [vtB_congr (hn.trans hna.symm) (unf_name_some hl)]; exact hv
        · exact vtB_of_nxB' (nxB_of_vtB hna hv)
      | none =>
        exact vtB_name_plain hn hl (noFields_of hx (by intro fs h; cases h))
          (noCases_of hx (by intro cs h; cases h)) v
    · have hg := hx.good (nx_name_good hn)
      simp only [goodDT, goodTyp_eq] at hg
      exact vtB_of_nxB' (nxB_of_vtB hg hv)
  | structT fs =>
    cases v <;> simp only [hasTypDef, Value.asStruct?, Except.ok.injEq, Bool.false_eq_true] at h
    rename_i gs
    cases hn : nxAT sigX.good (.name x A)
    · have hl := noAlias_of hx (by intro t h; cases h)
      rw [vtB_struct_name hn (unf_name_none hl)]
      refine ih.fields x ρ fs gs ⟨fun p hp h1 t ht => ?_, hx.nodup fs rfl⟩ hρ h
      obtain ⟨fs', hfs', hm⟩ := hx.field p hp h1
      cases hfs'
      rw [ht] at hm
      simpa using hm
    · have hg := hx.good (nx_name_good hn)
      have hfx : FieldsNx sigX.good fs := hg
      have := (nxTyp hE m).fields ρ fs gs (typsNx_nil hρ) hfx h
      exact vtB_of_nxB' (by simpa [nxB] using this)
  | variantT cs =>
    cases v <;> simp only [hasTypDef, Value.asCase?, Except.ok.injEq, Bool.false_eq_true] at h
    rename_i op w
    cases hn : nxAT sigX.good (.name x A)
    · have hl := noAlias_of hx (by intro t h; cases h)
      rw [vtB_case_name hn (unf_name_none hl)]
      refine ih.case x ρ cs op w (fun p hp h1 h2 t ht => ?_) hρ h
      obtain ⟨cs', hcs', hm⟩ := hx.case p hp h1
      cases hcs'
      rw [h2, ht] at hm
      simpa using hm
    · have hg := hx.good (nx_name_good hn)
      have hcx : CasesNx sigX.good cs := hg
      have := (nxTyp hE m).case ρ cs op w (typsNx_nil hρ) hcx h
      exact vtB_of_nxB' (by simpa [nxB] using this)

theorem vt_fields_succ (ih : VtTyp env m) (x : String) (ρ : VarEnv) (hρ : ρ.typs = []) :
    ∀ (fs : List TypField) (gs : List (AtomS × Value)), FF x fs →
      hasTypFields (m + 1) env ρ fs gs = .ok true → vtF sigX x gs = true
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [hasTypFields] at h
  | _ :: _, [], _, h => by simp [hasTypFields] at h
  | .mk a t q prems :: fs, (a', w) :: gs, hF, h => by
    simp only [hasTypFields] at h
    split at h
    · rename_i haa
      subst haa
      simp only [Res.bind_eq_ok] at h
      obtain ⟨b, hb, h⟩ := h
      cases b
      · simp at h
      simp only [↓reduceIte, Res.bind_eq_ok] at h
      obtain ⟨hp, _, h⟩ := h
      cases hp
      · simp at h
      simp only [↓reduceIte] at h
      have hnd := hF.2
      rw [fieldAtoms_cons] at hnd
      simp only [nodupS, Bool.and_eq_true, Bool.not_eq_true'] at hnd
      simp only [vtF, Bool.and_eq_true]
      refine ⟨?_, ih.fields x ρ fs gs ⟨fun p hp h1 t' ht' => ?_, hnd.2⟩ hρ h⟩
      · rcases fieldAT_cases x a with he | ⟨p, hp, h1, h2, he⟩
        · rw [he]; exact vtB_unk _ _
        · rw [he]
          have := hF.1 p hp h1 t (by simp [fieldOf, h2])
          rw [← this]
          exact ih.typ ρ t w (typsNx_nil hρ) hb
      · have hne : p.2.1 ≠ a := by
          intro he
          have := fieldOf_mem ht'
          rw [he] at this
          have hc : (fieldAtoms fs).contains a = true := List.contains_iff_mem.2 this
          rw [hc] at hnd
          cases hnd.1
        exact hF.1 p hp h1 t' (by simp [fieldOf, Ne.symm hne, ht'])
    · cases h

theorem vt_case_succ (ih : VtTyp env m) (x : String) (ρ : VarEnv) (hρ : ρ.typs = []) :
    ∀ (cs : List TypCase) (op : MixopS) (w : Value),
      (∀ p ∈ sigX.cases, p.1 = x → p.2.1 = op → ∀ t, caseOf op cs = some t → toAT t = p.2.2) →
      hasTypCase (m + 1) env ρ cs op w = .ok true → vtB sigX (caseAT sigX x op) w = true
  | [], _, _, _, h => by simp [hasTypCase] at h
  | .mk op t qs prems :: cs, op', w, hC, h => by
    simp only [hasTypCase] at h
    split at h
    · rename_i ho
      subst ho
      simp only [Res.bind_eq_ok] at h
      obtain ⟨b, hb, h⟩ := h
      cases b
      · simp at h
      rcases caseAT_cases x op with he | ⟨p, hp, h1, h2, he⟩
      · rw [he]; exact vtB_unk _ _
      · rw [he, ← hC p hp h1 h2 t (by simp [caseOf])]
        exact ih.typ ρ t w (typsNx_nil hρ) hb
    · rename_i ho
      exact ih.case x ρ cs op' w (fun p hp h1 h2 t ht => hC p hp h1 h2 t
        (by simp [caseOf, ho, ht])) hρ h

theorem vt_insts_succ (ih : VtTyp env m) (x : String) :
    ∀ (insts : List Inst) (ws : List ArgV) (v : Value) (A : List AT), IF x insts →
      hasTypInsts (m + 1) env insts ws v = .ok true → vtB sigX (.name x A) v = true
  | [], _, _, _, _, h => by simp [hasTypInsts] at h
  | .instD q pats dt :: insts, ws, v, A, hI, h => by
    simp only [hasTypInsts] at h
    have h0 := hI _ (List.mem_cons_self ..)
    rcases elimUndef_eq_ok' h with ⟨ρ', hm, h⟩ | ⟨_, h⟩
    · have hρ : ρ'.typs = [] := by
        rw [matchArgs_typs m VarEnv.empty ρ' pats ws h0.1 hm]; rfl
      exact ih.defT x ρ' dt v A h0.2 hρ h
    · exact ih.insts x insts ws v A (fun i hi => hI i (List.mem_cons_of_mem _ hi)) h
where
  elimUndef_eq_ok' {α β : Type} {r : Res α} {f : α → Res β} {g : Unit → Res β} {b : β}
      (h : Res.elimUndef r f g = .ok b) :
      (∃ a, r = .ok a ∧ f a = .ok b) ∨ (r = .error .undef ∧ g () = .ok b) := by
    cases r with
    | ok a => exact .inl ⟨a, rfl, h⟩
    | error e =>
      cases e with
      | undef => exact .inr ⟨rfl, h⟩
      | outOfFuel => cases h

theorem vt_tup_succ (ih : VtTyp env m) : ∀ (ρ : VarEnv) (bs : List TypBind) (vs : List Value),
    TypsNx sigX.good ρ → hasTypTup (m + 1) env ρ bs vs = .ok true →
    vtT sigX (toATBinds bs) vs = true
  | _, [], [], _, _ => rfl
  | _, [], _ :: _, _, h => by simp [hasTypTup] at h
  | _, _ :: _, [], _, _ => rfl
  | ρ, .mk x t :: bs, v :: vs, hρ, h => by
    simp only [hasTypTup, Res.bind_eq_ok] at h
    obtain ⟨b, hb, h⟩ := h
    cases b
    · simp at h
    simp only [↓reduceIte] at h
    simp only [toATBinds, vtT, List.headD_cons, List.tail_cons, Bool.and_eq_true]
    exact ⟨ih.typ ρ t v hρ hb, ih.tup (ρ.bindVal x v) bs vs (typsNx_bindVal hρ x v) h⟩

theorem vt_list_succ (ih : VtTyp env m) (ρ : VarEnv) (t : Typ) : ∀ (vs : List Value),
    TypsNx sigX.good ρ → hasTypList (m + 1) env ρ t vs = .ok true →
    ∀ w ∈ vs, vtB sigX (toAT t) w = true
  | [], _, _, w, hw => by simp at hw
  | v :: vs, hρ, h, w, hw => by
    simp only [hasTypList, Res.bind_eq_ok] at h
    obtain ⟨b, hb, h⟩ := h
    cases b
    · simp at h
    simp only [↓reduceIte] at h
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ih.typ ρ t _ hρ hb
    · exact ih.list ρ t vs hρ h w hw

end Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant
