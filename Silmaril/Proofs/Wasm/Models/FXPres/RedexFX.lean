module

public import Silmaril.Proofs.Wasm.Models.FXPres.Control

/-!
# Preservation at the stack-switching redexes

`cont.new`, `cont.bind`, `resume`, `resume_throw` and `suspend` (each with its typed arity),
calls of FX functions, and `switch` (not typed, so no typed configuration reaches it).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXPres

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXResume
open Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {E : TyEnv H} {P : Profile} {host : HostSemantics H}
  {fx : H → Option FuncFX} {s : Store H} {Γ : List TypeIdx} {K : List (Option ContFX)}
  {f : Frame} {Ls : List (List FTy)} {R : Option (List FTy)} {i o : List FTy}

/-! ## Lookups -/

theorem tag?_eq (hf : f.module = E.m₀) {x : TagIdx} {ta : Nat} {ti : TagInst}
    (h : s.tag? f x = some (ta, ti)) : E.m₀.tags[x.toNat]? = some ta ∧ s.tags[ta]? = some ti := by
  simp only [Store.tag?, hf] at h
  cases ha : E.m₀.tags[x.toNat]? with
  | none => simp [ha] at h
  | some a =>
    cases ht : s.tags[a]? with
    | none => simp [ha, ht] at h
    | some t =>
      simp [ha, ht] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, ht⟩

theorem resolve_ok (hf : f.module = E.m₀) {ts : List FTy} {c : OnClause} {c' : HClause}
    (hr : resolve s f c = some c') (h : OnClauseOk E s Ls ts c) : HClauseOk E s Ls ts c' := by
  cases c with
  | onLabel x l =>
    obtain ⟨ta, hx, hc⟩ := h
    cases ht : s.tag? f x with
    | none => simp [resolve, ht] at hr
    | some p =>
      obtain ⟨ta', ti⟩ := p
      have hta : ta' = ta := by
        have := (tag?_eq hf ht).1
        rw [hx] at this
        exact (Option.some.inj this).symm
      simp only [resolve, ht, Option.map_some, Option.some.injEq] at hr
      subst hr hta
      exact hc
  | onSwitch => exact h.elim

theorem mapM_resolve_ok (hf : f.module = E.m₀) {ts : List FTy} :
    ∀ {hs : List OnClause} {hs' : List HClause}, hs.mapM (resolve s f) = some hs' →
      (∀ c ∈ hs, OnClauseOk E s Ls ts c) → ∀ c ∈ hs', HClauseOk E s Ls ts c
  | [], hs', hr, _ => by
    simp at hr
    subst hr
    simp
  | c :: cs, hs', hr, hh => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hr
    obtain ⟨c', hc', cs', hcs', rfl⟩ := hr
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact resolve_ok hf hc' (hh c (List.mem_cons_self ..))
    · exact mapM_resolve_ok hf hcs' (fun e he => hh e (List.mem_cons_of_mem _ he)) d hd

/-- A live slot of a typed store holds a continuation at the slot's type. -/
theorem KOk.live (hK : KOk E s Γ K) {k : Nat} {ct : TypeIdx} {C : ContFX}
    (hΓ : Γ[k]? = some ct) (hk : K[k]? = some (some C)) : ContTy E s Γ C ct := by
  rcases hK.2 k ct hΓ with h | ⟨C', hC', hty⟩
  · rw [hk] at h
    cases h
  · rw [hk] at hC'
    cases hC'
    exact hty

theorem contParams_eq {m : ModuleInst} {ct : TypeIdx} {ps rs : List CValType}
    (h : contType? m ct = some (ps, rs)) : contParams? m ct = some ps := by
  show (contType? m ct).map Prod.fst = some ps
  rw [h]
  rfl

/-! ## `cont.new` -/

theorem pres_contNew (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K)
    {a : Nat} {fi : FuncInst H} {ct : TypeIdx} (hfa : s.funcs[a]? = some fi)
    (h : TL E s Γ Ls R [.core (.ref (.func a)), .fx (.contNew ct)] i o) :
    PresC E s Γ Ls R i o s
      (K ++ [some ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType fi.type)]⟩]) f
      [.contRef K.length] := by
  have hn : ¬ IsCtl (Admin.ref (.func a)) := by simp [IsCtl]
  obtain ⟨pre, i₀, o₀, hc, rfl, hr⟩ := TL.core_inv hn h
  obtain ⟨rfl, x, rfl⟩ := hyp.val (v := .ref (.func a)) hc
  generalize hm : pre ++ [x] = m at hr
  cases hr with
  | @contNew _ _ _ ty _ pre' _ hct hr =>
    cases hr
    obtain ⟨rfl, hx⟩ := List.append_inj' hm rfl
    simp only [List.cons.injEq, and_true] at hx
    subst hx
    obtain ⟨ps, rs⟩ := ty
    have hC : ContTy E s (Γ ++ [ct])
        ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType fi.type)]⟩ ct :=
      ⟨ps, rs, hct, fun s' Γ' c hs _ hc' => TL.append hc' (hyp.new hfa hc hct s' Γ' hs)⟩
    have hk : (Γ ++ [ct])[K.length]? = some ct := by simp [← hK.1]
    refine ⟨Γ ++ [ct], List.prefix_append _ _, hyp.ext_refl s, hf, KOk.push hyp hK hC, ?_⟩
    simpa using TL.contRef (pre := pre) hk (.nil : TL E s (Γ ++ [ct]) Ls R [] _ _)

/-! ## Inversion at `ref.cont k; op` -/

/-- The operands of an instruction after `ref.cont k`: values `vs` at `T`, then slot `k`. -/
theorem ops_inv (hyp : CoreHyp E P host fx) {vs : List FVal} {k : Nat} {x : AdminFX}
    (h : TL E s Γ Ls R (fvals vs ++ [.contRef k, x]) i o) :
    ∃ T ct₀ m, ValsTy E s Γ vs T ∧ Γ[k]? = some ct₀ ∧ m = i ++ T ++ [.cont ct₀] ∧
      TL E s Γ Ls R [x] m o := by
  obtain ⟨m, hv, hb⟩ := TL.split h
  obtain ⟨T, hmT, hT⟩ := TL.vals_inv hyp.val hv
  cases hb with
  | contRef hΓk hr => exact ⟨T, _, _, hT, hΓk, by rw [hmT], hr⟩

/-- Two stacks ending in one type, with middles of equal length. -/
theorem stack_last {i T pre X : List FTy} {a b : FTy} (h : i ++ T ++ [a] = pre ++ X ++ [b])
    (hl : T.length = X.length) : i = pre ∧ T = X ∧ a = b := by
  obtain ⟨h₁, h₂⟩ := List.append_inj' h rfl
  obtain ⟨h₃, h₄⟩ := List.append_inj' h₁ hl
  exact ⟨h₃, h₄, by simpa using h₂⟩

theorem resume_inv {ct : TypeIdx} {hs : List OnClause} {m : List FTy}
    (h : TL E s Γ Ls R [.fx (.resume ct hs)] m o) :
    ∃ pre ps rs, contType? E.m₀ ct = some (ps, rs) ∧
      (∀ c ∈ hs, OnClauseOk E s Ls (E.tys rs) c) ∧ m = pre ++ E.tys ps ++ [.cont ct] ∧
      o = pre ++ E.tys rs := by
  cases h with
  | resume hct hh hr =>
    cases hr
    exact ⟨_, _, _, hct, hh, rfl, rfl⟩

theorem contBind_inv {ct ct' : TypeIdx} {m : List FTy}
    (h : TL E s Γ Ls R [.fx (.contBind ct ct')] m o) :
    ∃ pre ps₁ ps₂ rs, contType? E.m₀ ct = some (ps₁ ++ ps₂, rs) ∧
      contType? E.m₀ ct' = some (ps₂, rs) ∧ m = pre ++ E.tys ps₁ ++ [.cont ct] ∧
      o = pre ++ [.cont ct'] := by
  cases h with
  | contBind hct hct' hr =>
    cases hr
    exact ⟨_, _, _, _, hct, hct', rfl, rfl⟩

theorem resumeThrow_inv {ct : TypeIdx} {x : TagIdx} {hs : List OnClause} {m : List FTy}
    (h : TL E s Γ Ls R [.fx (.resumeThrow ct x hs)] m o) :
    ∃ pre ps rs tp tr ta ti, contType? E.m₀ ct = some (ps, rs) ∧
      E.m₀.tags[x.toNat]? = some ta ∧ s.tags[ta]? = some ti ∧
      ti.type.funcType? = some (tp, tr) ∧ (∀ c ∈ hs, OnClauseOk E s Ls (E.tys rs) c) ∧
      m = pre ++ E.tys tp ++ [.cont ct] ∧ o = pre ++ E.tys rs := by
  cases h with
  | resumeThrow hct hx hti htt hh hr =>
    cases hr
    exact ⟨_, _, _, _, _, _, _, hct, hx, hti, htt, hh, rfl, rfl⟩

/-! ## Arities -/

theorem len_of_resumeArity {ct : TypeIdx} {ps rs : List CValType} {n : Nat}
    (hct : contType? E.m₀ ct = some (ps, rs)) (ha : ResumeArity E.m₀ ct n) :
    n = (E.tys ps).length := by
  obtain ⟨p, hp, hlen⟩ := ha
  rw [contParams_eq hct] at hp
  cases hp
  rw [tys_length, hlen]

theorem len_of_bindArity {ct ct' : TypeIdx} {ps₁ ps₂ rs : List CValType} {n : Nat}
    (hct : contType? E.m₀ ct = some (ps₁ ++ ps₂, rs))
    (hct' : contType? E.m₀ ct' = some (ps₂, rs)) (ha : BindArity E.m₀ ct ct' n) :
    n = (E.tys ps₁).length := by
  obtain ⟨p, p', hp, hp', hlen⟩ := ha
  rw [contParams_eq hct] at hp
  rw [contParams_eq hct'] at hp'
  cases hp
  cases hp'
  simp only [List.length_append] at hlen
  rw [tys_length]
  omega

theorem len_of_tagArity {ti : TagInst} {tp tr : List CValType} {n : Nat}
    (htt : ti.type.funcType? = some (tp, tr)) (ha : TagArity ti n) : n = (E.tys tp).length := by
  obtain ⟨tp', tr', htt', hlen⟩ := ha
  rw [htt] at htt'
  obtain ⟨htp, -⟩ := Prod.mk.inj (Option.some.inj htt')
  rw [tys_length, ← hlen, htp]

/-- Apply a typed continuation at its declared type. -/
theorem ContTy.apply {C : ContFX} {ct : TypeIdx} {ps rs : List CValType} {s' : Store H}
    {Γ' : List TypeIdx} {c : List AdminFX} (hC : ContTy E s Γ C ct)
    (hct : contType? E.m₀ ct = some (ps, rs)) (hs : E.ext s s') (hΓ : Γ <+: Γ')
    (hc : TL E s' Γ' [] none c [] (E.tys ps)) : TL E s' Γ' [] none (C.plug c) [] (E.tys rs) := by
  obtain ⟨qs, rs', hq, hC'⟩ := hC
  rw [hct] at hq
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj (Option.some.inj hq)
  subst h₁ h₂
  exact hC' s' Γ' c hs hΓ hc

/-! ## `cont.bind` -/

/-- The continuation made by `cont.bind` is typed. -/
theorem contTy_bind (hyp : CoreHyp E P host fx) {vs : List FVal} {C : ContFX}
    {ct ct' : TypeIdx} {ps₁ ps₂ rs : List CValType} (hC : ContTy E s Γ C ct)
    (hct : contType? E.m₀ ct = some (ps₁ ++ ps₂, rs)) (hct' : contType? E.m₀ ct' = some (ps₂, rs))
    (hT : ValsTy E s Γ vs (E.tys ps₁)) :
    ContTy E s (Γ ++ [ct']) ⟨fun c => C.plug (fvals vs ++ c)⟩ ct' := by
  refine ⟨ps₂, rs, hct', fun s' Γ' c hs hΓ hc => ?_⟩
  have hΓ' : Γ <+: Γ' := (List.prefix_append _ _).trans hΓ
  have hv : TL E s' Γ' [] none (fvals vs) [] (E.tys ps₁) := by
    simpa using TL.vals (Ls := []) (R := none) (ValsTy.mono (CoreHyp.le hyp hs) hΓ' hT) []
  have hc' : TL E s' Γ' [] none c (E.tys ps₁) (E.tys ps₁ ++ E.tys ps₂) := by
    simpa using TL.weaken (E.tys ps₁) hc
  have hall : TL E s' Γ' [] none (fvals vs ++ c) [] (E.tys (ps₁ ++ ps₂)) := by
    simpa [TyEnv.tys] using TL.append hv hc'
  show TL E s' Γ' [] none (C.plug (fvals vs ++ c)) [] (E.tys rs)
  exact ContTy.apply hC hct hs hΓ' hall

theorem pres_contBind (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K)
    {vs : List FVal} {k : Nat} {C : ContFX} {ct ct' : TypeIdx} (hk : K[k]? = some (some C))
    (ha : BindArity f.module ct ct' vs.length)
    (h : TL E s Γ Ls R (fvals vs ++ [.contRef k, .fx (.contBind ct ct')]) i o) :
    PresC E s Γ Ls R i o s (K.set k none ++ [some ⟨fun c => C.plug (fvals vs ++ c)⟩]) f
      [.contRef K.length] := by
  obtain ⟨T, ct₀, m, hT, hΓk, hm, hx⟩ := ops_inv hyp h
  obtain ⟨pre, ps₁, ps₂, rs, hct, hct', hm', rfl⟩ := contBind_inv hx
  have hlen : T.length = (E.tys ps₁).length := by
    rw [← hT.length_eq]; exact len_of_bindArity hct hct' (hf ▸ ha)
  obtain ⟨rfl, rfl, hab⟩ := stack_last (hm.symm.trans hm') hlen
  cases hab
  have hC' := contTy_bind hyp (KOk.live hK hΓk hk) hct hct' hT
  have hkl : (Γ ++ [ct'])[(K.set k none).length]? = some ct' := by simp [← hK.1]
  have hcode : TL E s (Γ ++ [ct']) Ls R [.contRef (K.set k none).length] i (i ++ [.cont ct']) :=
    .contRef hkl .nil
  exact ⟨Γ ++ [ct'], List.prefix_append _ _, hyp.ext_refl s, hf,
    KOk.push hyp (KOk.set hK k) hC', by simpa using hcode⟩

/-! ## `resume` -/

theorem pres_resume (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K)
    {vs : List FVal} {k : Nat} {C : ContFX} {ct : TypeIdx} {hs : List OnClause}
    {hs' : List HClause} (hk : K[k]? = some (some C)) (hres : hs.mapM (resolve s f) = some hs')
    (ha : ResumeArity f.module ct vs.length)
    (h : TL E s Γ Ls R (fvals vs ++ [.contRef k, .fx (.resume ct hs)]) i o) :
    PresC E s Γ Ls R i o s (K.set k none) f [.handler hs' (C.plug (fvals vs))] := by
  obtain ⟨T, ct₀, m, hT, hΓk, hm, hx⟩ := ops_inv hyp h
  obtain ⟨pre, ps, rs, hct, hh, hm', rfl⟩ := resume_inv hx
  have hlen : T.length = (E.tys ps).length := by
    rw [← hT.length_eq]; exact len_of_resumeArity hct (hf ▸ ha)
  obtain ⟨rfl, rfl, hab⟩ := stack_last (hm.symm.trans hm') hlen
  cases hab
  have hargs : TL E s Γ [] none (fvals vs) [] (E.tys ps) := by
    simpa using TL.vals (Ls := []) (R := none) hT []
  have hbody : TL E s Γ [] none (C.plug (fvals vs)) [] (E.tys rs) :=
    ContTy.apply (KOk.live hK hΓk hk) hct (hyp.ext_refl s) (List.prefix_refl _) hargs
  exact presC_same hyp hf (KOk.set hK k)
    (.handler (pre := i) (mapM_resolve_ok hf hres hh) hbody .nil)

/-! ## `resume_throw` -/

theorem pres_resumeThrow (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀)
    (hK : KOk E s Γ K) {vs : List Val} {k : Nat} {C : ContFX} {ct : TypeIdx} {x : TagIdx}
    {hs : List OnClause} {hs' : List HClause} {ta : Nat} {ti : TagInst}
    (hk : K[k]? = some (some C)) (ht : s.tag? f x = some (ta, ti))
    (hres : hs.mapM (resolve s f) = some hs') (ha : TagArity ti vs.length)
    (h : TL E s Γ Ls R (cvals vs ++ [.contRef k, .fx (.resumeThrow ct x hs)]) i o) :
    PresC E s Γ Ls R i o (s.addExn ⟨ta, vs⟩) (K.set k none) f
      [.handler hs' (C.plug (cthrowing s.exns.length))] := by
  have h' : TL E s Γ Ls R (fvals (liftV vs) ++ [.contRef k, .fx (.resumeThrow ct x hs)]) i o := by
    simpa using h
  obtain ⟨T, ct₀, m, hT, hΓk, hm, hx⟩ := ops_inv hyp h'
  obtain ⟨pre, ps, rs, tp, tr, ta', ti', hct, hx', hti, htt, hh, hm', rfl⟩ := resumeThrow_inv hx
  obtain ⟨hxa, htia⟩ := tag?_eq hf ht
  have hta : ta' = ta := Option.some.inj (hx'.symm.trans hxa)
  have hti' : ti' = ti := Option.some.inj (hti.symm.trans (hta ▸ htia))
  have hlen : T.length = (E.tys tp).length := by
    rw [← hT.length_eq, liftV, List.length_map]; exact len_of_tagArity (hti' ▸ htt) ha
  obtain ⟨rfl, rfl, hab⟩ := stack_last (hm.symm.trans hm') hlen
  cases hab
  obtain ⟨hext, hth⟩ := hyp.exn s ⟨ta, vs⟩ Γ [] (E.tys ps)
  have hbody : TL E (s.addExn ⟨ta, vs⟩) Γ [] none (C.plug (cthrowing s.exns.length)) []
      (E.tys rs) := ContTy.apply (KOk.live hK hΓk hk) hct hext (List.prefix_refl _) hth
  have hcl : ∀ c ∈ hs', HClauseOk E (s.addExn ⟨ta, vs⟩) Ls (E.tys rs) c :=
    fun c hc => hClauseOk_mono (CoreHyp.le hyp hext) (mapM_resolve_ok hf hres hh c hc)
  exact ⟨Γ, List.prefix_refl _, hext, hf, KOk.set (KOk.mono hyp hK hext) k,
    .handler (pre := i) hcl hbody .nil⟩

end Silmaril.Proofs.Wasm.Models.FXPres
