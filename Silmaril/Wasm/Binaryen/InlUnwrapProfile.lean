module

public import Silmaril.Wasm.Binaryen.InlUnwrapClosed
public import Silmaril.Wasm.Binaryen.InlUnwrapKernelReverseSimulation

@[expose] public section

/-! # Arbitrary-profile closed-host unwrap and folding equivalence

Both directions follow chosen executions. Reverse matching retains the original
configuration's typing and admits recursive kernel cuts; no numerical determinism
or totality assumption is used. Persistent sessions and initialization observations
are transported with the actual stores.
-/

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR

variable {H : Type} {p : Prm} {P : Profile}

/-- The function relation from the transformed store back to the original store. -/
def reverseFuncs (p : Prm) (fi gi : FuncInst H) : Prop :=
  fi = gi ∨ fi = gR p ∧ gi = gL p

theorem reverseFuncs_sound (hok : PrmOk p) (hty : p.cR.type = p.cL.type) :
    ∀ fi gi : FuncInst H, reverseFuncs p fi gi →
      FuncRel (fun x y => UIL p.R y x) fi gi := by
  rintro fi gi (rfl | ⟨rfl, rfl⟩)
  · exact FuncRel.refl _
  · exact ⟨rfl, rfl, hty, hok.locals, .base hok.body⟩

private theorem reverseFuncs_set : ∀ (fs : List (FuncInst H)) (ag : Nat),
    fs[ag]? = some (gL p) → List.Forall₂ (reverseFuncs p) (fs.set ag (gR p)) fs
  | [], _, h => by simp at h
  | f :: fs, 0, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst f
    refine .cons (.inr ⟨rfl, rfl⟩) ?_
    induction fs with
    | nil => exact .nil
    | cons f fs ih => exact .cons (.inl rfl) ih
  | f :: fs, ag + 1, h =>
    .cons (.inl rfl) (reverseFuncs_set fs ag (by simpa using h))

/-- The exact one-function replacement supplies the converse Core store relation. -/
theorem SR.reverse_storeRel {s t : Store H} (h : SR p s t) :
    StoreRel (reverseFuncs p) t s := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h.ht]; exact h.sameTypes
  · rw [h.ht]; rfl
  · rw [h.ht]; exact reverseFuncs_set s.funcs p.ag h.hg

/-- Host-free execution retains the exact function table at every profile. -/
theorem steps_funcs_profile {c c' : Config H} (h : Steps P closedHost c c') :
    c'.store.funcs = c.store.funcs := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact (SingleThreaded.Step.framesLocal hs).1.trans ih

/-- A chosen reverse run recovers the exact replacement invariant for later calls. -/
theorem SR.of_reverse_storeRel {s t s' t' : Store H} (h : SR p s t)
    (hs : s'.funcs = s.funcs) (ht : t'.funcs = t.funcs)
    (rel : StoreRel (reverseFuncs p) t' s') : SR p s' t' := by
  refine ⟨by rw [hs]; exact h.hg, ?_⟩
  calc
    t' = s'.setFuncs t'.funcs := rel.symm.eq_setFuncs
    _ = withFuncs s' (s'.funcs.set p.ag (gR p)) := by rw [ht, h.ht, hs]; rfl

/-- Both directions preserve the chosen terminal result and exact mutable store,
at the same arbitrary numerical profile. -/
theorem runs_corr_profile (hok : PrmOk p) (hty : p.cR.type = p.cL.type)
    {c c' : Config H} {ts ts' : List CValType}
    (hc : ConfigOk c ts) (_hc' : ConfigOk c' ts')
    (hMR : MR p c c') (hSR : SR p c.store c'.store) :
    (∀ x, Steps P closedHost c x → x.Terminal →
      ∃ x', Steps P closedHost c' x' ∧ x'.code = x.code ∧ SR p x.store x'.store) ∧
    (Diverges P closedHost c → Diverges P closedHost c') ∧
    (∀ x', Steps P closedHost c' x' → x'.Terminal →
      ∃ x, Steps P closedHost c x ∧ x.code = x'.code ∧ SR p x.store x'.store) ∧
    (Diverges P closedHost c' → Diverges P closedHost c) := by
  have hcl : ∀ x, Steps P closedHost c x → Classif P closedHost x :=
    fun x _ => classif_closed x
  have reverse : CfgRel (reverseFuncs p) (fun x y => KUL p.R y x) c' c :=
    ⟨hSR.reverse_storeRel, hMR.1.symm, hMR.2.to_kernel⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx ⟨r, hr⟩
    obtain ⟨x', hx', hrel, hstores⟩ := run_sim hok hx hcl hMR hSR
    exact ⟨x', hx', by rw [terminal_code hrel hr, hr], hstores⟩
  · exact fun hdiv => div_sim hok closedHost_respectsCode hdiv hcl hMR hSR
  · intro x' hx' ⟨r, hr⟩
    obtain ⟨x, hx, hcode, hstores⟩ := KUL.run_reverse
      (reverseFuncs_sound hok hty) hok.bud hok.labels reverse
      (ContextTyped.of_configOk hc) hx' hr
    exact ⟨x, hx, by rw [hcode, hr], hSR.of_reverse_storeRel
      (steps_funcs_profile hx) (steps_funcs_profile hx') hstores⟩
  · exact KUL.diverges_reverse (reverseFuncs_sound hok hty)
      hok.bud hok.labels reverse (ContextTyped.of_configOk hc)

/-- **Sessions of the right module are sessions of the left one.** -/
theorem session_corr₁_profile (hok : PrmOk p) (hty : p.cR.type = p.cL.type) {mi : ModuleInst} {t : Store H} {script : List Call}
    {bs : List (Behaviour Val)} (h : Session P closedHost mi t script bs) :
    ∀ {s : Store H}, StoreOk s → StoreOk t → SR p s t → Session P closedHost mi s script bs := by
  induction h with
  | nil => exact fun _ _ _ => .nil
  | stop h => exact fun _ _ hSR => .stop fun a ha hok' => h a ha (invokeOk_of hSR hok')
  | @done t x vs rest a c r bs ha hok' run hr tail ih =>
    intro s hs ht hSR
    have hokO := invokeOk_of' hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hokO
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hok'
    obtain ⟨-, -, R3, -⟩ := runs_corr_profile hok hty hcO hcN (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    obtain ⟨x', hx', hcode, hSR'⟩ := R3 c run ⟨r, hr⟩
    exact .done ha hokO hx' (by rw [hcode, hr]) (ih (ConfigOk.storeOk (preserves_closed hcO hx'))
      (ConfigOk.storeOk (preserves_closed hcN run)) hSR')
  | @diverge t x vs rest a ha hok' hd =>
    intro s hs ht hSR
    have hokO := invokeOk_of' hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hokO
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hok'
    obtain ⟨-, -, -, R4⟩ := runs_corr_profile hok hty hcO hcN (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    exact .diverge ha hokO (R4 hd)

/-- **Sessions of the left module are sessions of the right one.** -/
theorem session_corr₂_profile (hok : PrmOk p) (hty : p.cR.type = p.cL.type) {mi : ModuleInst} {s : Store H} {script : List Call}
    {bs : List (Behaviour Val)} (h : Session P closedHost mi s script bs) :
    ∀ {t : Store H}, StoreOk s → StoreOk t → SR p s t → Session P closedHost mi t script bs := by
  induction h with
  | nil => exact fun _ _ _ => .nil
  | stop h => exact fun _ _ hSR => .stop fun a ha hok' => h a ha (invokeOk_of' hSR hok')
  | @done s x vs rest a c r bs ha hok' run hr tail ih =>
    intro t hs ht hSR
    have hokN := invokeOk_of hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hok'
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hokN
    obtain ⟨R1, -, -, -⟩ := runs_corr_profile hok hty hcO hcN (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    obtain ⟨x', hx', hcode, hSR'⟩ := R1 c run ⟨r, hr⟩
    exact .done ha hokN hx' (by rw [hcode, hr]) (ih (ConfigOk.storeOk (preserves_closed hcO run))
      (ConfigOk.storeOk (preserves_closed hcN hx')) hSR')
  | @diverge s x vs rest a ha hok' hd =>
    intro t hs ht hSR
    have hokN := invokeOk_of hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hok'
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hokN
    obtain ⟨-, R2, -, -⟩ := runs_corr_profile hok hty hcO hcN (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    exact .diverge ha hokN (R2 hd)

/-! ## Actual admission, initialization and session observations -/

/-- A correspondence between the instantiations of the left module `M` and the right module
`M'`. -/
def InstCorrProfile (P : Profile) (host : HostSemantics H) (M M' : Module) : Prop :=
  (∀ s xas c, StoreOk s → Instantiate P host s M xas c →
    ∃ c' p, PrmOk p ∧ p.cR.type = p.cL.type ∧ Instantiate P host s M' xas c' ∧ c'.frame = c.frame ∧ c'.code = c.code ∧
      SR p c.store c'.store) ∧
  (∀ s xas c', StoreOk s → Instantiate P host s M' xas c' →
    ∃ c p, PrmOk p ∧ p.cR.type = p.cL.type ∧ Instantiate P host s M xas c ∧ c'.frame = c.frame ∧ c'.code = c.code ∧
      SR p c.store c'.store)

theorem obs_corr_profile
    {M M' : Module} {s : Store H} (hs : StoreOk s) {xas : List ExternAddr} {c c' : Config H}
    (hi : Instantiate P closedHost s M xas c) (hi' : Instantiate P closedHost s M' xas c')
    (hok : PrmOk p) (hty : p.cR.type = p.cL.type) (hfr : c'.frame = c.frame) (hcode : c'.code = c.code)
    (hSR : SR p c.store c'.store) (script : List Call) :
    (∀ bs, ((∃ c₁ bs', Steps P closedHost c' c₁ ∧ c₁.code = [] ∧
        Session P closedHost c'.frame.module c₁.store script bs' ∧ bs = .returns [] :: bs') ∨
      (∃ (c₁ : Config H) (r : Result), Steps P closedHost c' c₁ ∧ c₁.code = r.toAdmin ∧
        r ≠ .values [] ∧ bs = [r.toBehaviour]) ∨
      (Diverges P closedHost c' ∧ bs = [.diverges])) →
      ((∃ c₁ bs', Steps P closedHost c c₁ ∧ c₁.code = [] ∧
        Session P closedHost c.frame.module c₁.store script bs' ∧ bs = .returns [] :: bs') ∨
      (∃ (c₁ : Config H) (r : Result), Steps P closedHost c c₁ ∧ c₁.code = r.toAdmin ∧
        r ≠ .values [] ∧ bs = [r.toBehaviour]) ∨
      (Diverges P closedHost c ∧ bs = [.diverges]))) ∧
    (∀ bs, ((∃ c₁ bs', Steps P closedHost c c₁ ∧ c₁.code = [] ∧
        Session P closedHost c.frame.module c₁.store script bs' ∧ bs = .returns [] :: bs') ∨
      (∃ (c₁ : Config H) (r : Result), Steps P closedHost c c₁ ∧ c₁.code = r.toAdmin ∧
        r ≠ .values [] ∧ bs = [r.toBehaviour]) ∨
      (Diverges P closedHost c ∧ bs = [.diverges])) →
      ((∃ c₁ bs', Steps P closedHost c' c₁ ∧ c₁.code = [] ∧
        Session P closedHost c'.frame.module c₁.store script bs' ∧ bs = .returns [] :: bs') ∨
      (∃ (c₁ : Config H) (r : Result), Steps P closedHost c' c₁ ∧ c₁.code = r.toAdmin ∧
        r ≠ .values [] ∧ bs = [r.toBehaviour]) ∨
      (Diverges P closedHost c' ∧ bs = [.diverges]))) := by
  have hc := Instantiate.ok divHost_ok hs (instantiate_of_closed_unwrap divHost hi)
  have hc' := Instantiate.ok divHost_ok hs (instantiate_of_closed_unwrap divHost hi')
  have hMR : MR p c c' := ⟨hfr.symm, by rw [hcode]; exact UL.refl _⟩
  obtain ⟨R1, R2, R3, R4⟩ := runs_corr_profile hok hty hc hc' hMR hSR
  refine ⟨fun bs h => ?_, fun bs h => ?_⟩
  · rcases h with ⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩
    · obtain ⟨x, hx, hxc, hSR'⟩ := R3 c₁ h₁ ⟨.values [], by rw [h₂]; rfl⟩
      refine .inl ⟨x, bs', hx, by rw [hxc, h₂], ?_, rfl⟩
      rw [← hfr]
      exact session_corr₁_profile hok hty h₃ (ConfigOk.storeOk (preserves_closed hc hx))
        (ConfigOk.storeOk (preserves_closed hc' h₁)) hSR'
    · obtain ⟨x, hx, hxc, -⟩ := R3 c₁ h₁ ⟨r, h₂⟩
      exact .inr (.inl ⟨x, r, hx, by rw [hxc, h₂], h₃, rfl⟩)
    · exact .inr (.inr ⟨R4 h₁, rfl⟩)
  · rcases h with ⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩
    · obtain ⟨x, hx, hxc, hSR'⟩ := R1 c₁ h₁ ⟨.values [], by rw [h₂]; rfl⟩
      refine .inl ⟨x, bs', hx, by rw [hxc, h₂], ?_, rfl⟩
      rw [hfr]
      exact session_corr₂_profile hok hty h₃ (ConfigOk.storeOk (preserves_closed hc h₁))
        (ConfigOk.storeOk (preserves_closed hc' hx)) hSR'
    · obtain ⟨x, hx, hxc, -⟩ := R1 c₁ h₁ ⟨r, h₂⟩
      exact .inr (.inl ⟨x, r, hx, by rw [hxc, h₂], h₃, rfl⟩)
    · exact .inr (.inr ⟨R2 h₁, rfl⟩)

/-- **Export equivalence from corresponding instantiations.** -/
theorem exportEquiv_of_instCorr_profile {M M' : Module} (h : InstCorrProfile P (closedHost (H := H)) M M') :
    ExportEquiv (· = ·) P (closedHost (H := H)) M' M := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨⟨fun s xas c hs hi => ?_, fun s xas script hs bs hbs => ?_⟩,
    ⟨fun s xas c' hs hi' => ?_, fun s xas script hs bs hbs => ?_⟩⟩
  · obtain ⟨c', p, -, -, hi', -⟩ := h₁ s xas c hs hi
    exact ⟨c', hi'⟩
  · obtain ⟨c', hi', hrun⟩ := hbs
    obtain ⟨c, p, hok, hty, hi, hfr, hcode, hSR⟩ := h₂ s xas c' hs hi'
    exact ⟨bs, ⟨c, hi, (obs_corr_profile hs hi hi' hok hty hfr hcode hSR script).1 bs hrun⟩,
      SessionRel.refl (fun _ => rfl) bs⟩
  · obtain ⟨c, p, -, -, hi, -⟩ := h₂ s xas c' hs hi'
    exact ⟨c, hi⟩
  · obtain ⟨c, hi, hrun⟩ := hbs
    obtain ⟨c', p, hok, hty, hi', hfr, hcode, hSR⟩ := h₁ s xas c hs hi
    exact ⟨bs, ⟨c', hi', (obs_corr_profile hs hi hi' hok hty hfr hcode hSR script).2 bs hrun⟩,
      SessionRel.refl (R := fun b b' => (fun x1 x2 => x1 = x2) b' b) (fun _ => rfl) bs⟩

/-- **The instantiations of a module and of the module with one function's code replaced
correspond**, when the codes are related by `UIL`. -/
theorem instCorr_of_set_profile {host : HostSemantics H} {R : List Instr} {M : Module} {g : Nat}
    {cL cR : Func} (hg : M.funcs[g]? = some cL) (hty : cR.type = cL.type)
    (hval : ∀ mt, ModuleOk M mt ↔ ModuleOk { M with funcs := M.funcs.set g cR } mt)
    (hgood : ∀ mi dg ag, PrmOk ⟨R, mi, dg, ag, cL, cR⟩) :
    InstCorrProfile P host M { M with funcs := M.funcs.set g cR } := by
  refine ⟨fun s xas c _ hi => ?_, fun s xas c' _ hi' => ?_⟩
  · obtain ⟨n₀, c', hi', hfr, hcode, hst, hA⟩ :=
      InlR.instantiate_set hg hty (fun mt h => (hval mt).mp h) hi
    obtain ⟨dg, hSR⟩ := sr_of_alloc (R := R) hg hA hst
    exact ⟨c', _, hgood _ _ _, hty, hi', hfr, hcode, hSR⟩
  · have hlt := (List.getElem?_eq_some_iff.mp hg).1
    have hg' : (M.funcs.set g cR)[g]? = some cR := by simp [hlt]
    have hback : ({ ({ M with funcs := M.funcs.set g cR } : Module) with
        funcs := (M.funcs.set g cR).set g cL } : Module) = M := by
      have : (M.funcs.set g cR).set g cL = M.funcs := by
        rw [List.set_set]
        apply List.ext_getElem?
        intro j
        rw [List.getElem?_set]
        by_cases hj : g = j
        · subst hj; simp [hlt, (List.getElem?_eq_some_iff.mp hg).2]
        · simp [hj]
      cases M
      simp only at this ⊢
      rw [this]
    obtain ⟨n₀, c, hi, hfr, hcode, hst, hA'⟩ :=
      InlR.instantiate_set (M := { M with funcs := M.funcs.set g cR }) hg' hty.symm
        (fun mt h => by
          rw [hback]
          obtain ⟨mt₀, h₀⟩ : ∃ mt₀, ModuleOk M mt₀ := by
            obtain ⟨xtE, xtI, hmt, -⟩ := hi'.valid
            exact ⟨_, (hval _).mpr hmt⟩
          have h₀' := (hval mt₀).mp h₀
          rw [ModuleOk.unique h h₀']
          exact h₀) hi'
    rw [hback] at hi
    obtain ⟨hA, hst'⟩ := InlR.funcAlloc_back hg hty hA' hfr hst
    obtain ⟨dg, hSR⟩ := sr_of_alloc (R := R) hg hA hst'
    exact ⟨c, _, hgood _ _ _, hty, hi, hfr.symm, hcode.symm, hSR⟩


end Silmaril.Wasm.Binaryen.Unwrap

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation Numerics Unwrap

/-- **Unwrapping a branch-free block is an equivalence.** In any function body of any
module, `block bt region` may be replaced by `region` when `region` is inside the profile
(`any = false`), has no free branch target (`labelsList = []`) and no `return`
(`branchesOut = false`), under the closed host, for arbitrary host-state types. -/
theorem block_unwrap_exportEquiv_profile {m : BModule} {g : Nat} {K : BCtx} {bt : BlockType}
    {region : List BExpr} (hg : g < m.funcs.length)
    (hok : (m.withBody g (K.plug [.block bt region])).Ok) (hfree : BExpr.labelsList region = [])
    (hany : (effectsList region).any = false) (hret : (effectsList region).branchesOut = false)
    (P : Profile) {H : Type} :
    ExportEquiv (· = ·) P (closedHost (H := H)) (m.withBody g (K.plug region)).lower
      (m.withBody g (K.plug [.block bt region])).lower := by
  obtain ⟨fg, hfg⟩ : ∃ fg, m.funcs[g]? = some fg := ⟨_, List.getElem?_eq_getElem hg⟩
  obtain ⟨mt₀, hmt₀⟩ := hok
  have hbase : ∀ B, (m.withBody g B).base = m.base := fun _ => rfl
  have hL : (m.withBody g (K.plug [.block bt region])).lower.funcs[g]? =
      some (({ fg with body := K.plug [.block bt region] } : BFunc).mapBody BExpr.lowerList) := by
    simp only [BModule.lower, withBody_eq_set hfg, List.getElem?_map]
    rw [List.getElem?_set_self hg]
    rfl
  have hRm : (m.withBody g (K.plug region)).lower =
      { (m.withBody g (K.plug [.block bt region])).lower with
        funcs := (m.withBody g (K.plug [.block bt region])).lower.funcs.set g
          (({ fg with body := K.plug region } : BFunc).mapBody BExpr.lowerList) } := by
    simp only [BModule.lower, hbase, withBody_eq_set hfg, List.map_set, List.set_set]
  rw [hRm]
  refine Unwrap.exportEquiv_of_instCorr_profile (instCorr_of_set_profile hL rfl (fun mt => ?_)
    (fun mi dg ag => ⟨rfl, lower_plug K bt region, ⟨_, region_bud hfree hany hret⟩, hfree⟩))
  rw [← hRm]
  constructor
  · exact block_unwrap_valid_mt hfree hany hret
  · intro h'
    have h₀ := block_unwrap_valid_mt hfree hany hret hmt₀
    rw [ModuleOk.unique h' h₀]
    exact hmt₀


end Silmaril.Wasm.Binaryen
