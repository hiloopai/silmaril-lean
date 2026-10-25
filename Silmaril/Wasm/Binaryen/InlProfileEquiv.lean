module

public import Silmaril.Wasm.Binaryen.InlProfileForward
public import Silmaril.Wasm.Binaryen.InlReverseMatch
public import Silmaril.Wasm.Binaryen.InlSite
public import Silmaril.Wasm.Binaryen.InlUnwrapClosed

@[expose] public section

/-! # Chosen-run inlining equivalence at arbitrary numerical profiles

The reverse local-step obligation is explicit. Given its proof, both directions
preserve the selected result, divergence and actual final mutable store at the
same profile. Persistent sessions and module initialization observations reuse
those relations; neither numerical determinism nor an empty host-state type is
required. The host is closed, so this does not claim preservation of host calls.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Profile}

/-- Both directions retain the chosen result and actual final store, without
using unique outcomes or excluding divergence from a separate terminating run. -/
theorem runs_corr_profile (hG : Good p) (replay : ChosenReverseStep p P H)
    {c c' : Config H} {ts ts' : List CValType} (hc : ConfigOk c ts)
    (_hc' : ConfigOk c' ts') (hMR : MR p .gen c c') (hSR : SR p c.store c'.store) :
    (∀ x, Steps P closedHost c x → x.Terminal →
      ∃ x', Steps P closedHost c' x' ∧ x'.code = x.code ∧ SR p x.store x'.store) ∧
    (Diverges P closedHost c → Diverges P closedHost c') ∧
    (∀ x', Steps P closedHost c' x' → x'.Terminal →
      ∃ x, Steps P closedHost c x ∧ x.code = x'.code ∧ SR p x.store x'.store) ∧
    (Diverges P closedHost c' → Diverges P closedHost c) := by
  obtain ⟨hpok, ⟨hC⟩, hfx⟩ := hG
  have classified : ∀ x, Steps P closedHost c x → Classif P closedHost x :=
    fun x _ => Unwrap.classif_closed x
  have checkpoint := ReverseCheckpoint.of_related hMR hSR (ContextTyped.of_configOk hc)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x run ⟨r, result⟩
    obtain ⟨x', run', runtime, stores⟩ := run_sim hpok hfx hC run classified hMR hSR
    exact ⟨x', run', by rw [terminal_code runtime result, result], stores⟩
  · exact fun diverges => div_sim hpok hfx hC closedHost_respectsCode diverges classified hMR hSR
  · intro x' run' ⟨r, result⟩
    obtain ⟨x, run, code, stores⟩ := reverse_checkpoint_run replay checkpoint run' result
    exact ⟨x, run, by rw [code, result], stores⟩
  · exact reverse_checkpoint_diverges replay checkpoint

/-- **Sessions of the inlined module are sessions of the original one.** -/
theorem session_reverse_profile (hG : Good p) (replay : ChosenReverseStep p P H) {mi : ModuleInst} {t : Store H} {script : List Call}
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
    obtain ⟨-, -, R3, -⟩ := runs_corr_profile hG replay hcO hcN (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    obtain ⟨x', hx', hcode, hSR'⟩ := R3 c run ⟨r, hr⟩
    exact .done ha hokO hx' (by rw [hcode, hr]) (ih (ConfigOk.storeOk (Unwrap.preserves_closed hcO hx'))
      (ConfigOk.storeOk (Unwrap.preserves_closed hcN run)) hSR')
  | @diverge t x vs rest a ha hok' hd =>
    intro s hs ht hSR
    have hokO := invokeOk_of' hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hokO
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hok'
    obtain ⟨-, -, -, R4⟩ := runs_corr_profile hG replay hcO hcN (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    exact .diverge ha hokO (R4 hd)

/-- **Sessions of the original module are sessions of the inlined one.** -/
theorem session_forward_closed_profile (hG : Good p) (replay : ChosenReverseStep p P H) {mi : ModuleInst} {s : Store H} {script : List Call}
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
    obtain ⟨R1, -, -, -⟩ := runs_corr_profile hG replay hcO hcN (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    obtain ⟨x', hx', hcode, hSR'⟩ := R1 c run ⟨r, hr⟩
    exact .done ha hokN hx' (by rw [hcode, hr]) (ih (ConfigOk.storeOk (Unwrap.preserves_closed hcO run))
      (ConfigOk.storeOk (Unwrap.preserves_closed hcN hx')) hSR')
  | @diverge s x vs rest a ha hok' hd =>
    intro t hs ht hSR
    have hokN := invokeOk_of hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hok'
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hokN
    obtain ⟨-, R2, -, -⟩ := runs_corr_profile hG replay hcO hcN (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    exact .diverge ha hokN (R2 hd)

/-! ## Module observations -/

/-- A correspondence between the instantiations of the original module `M` and the inlined
module `M'`. -/
def InstCorrProfile (P : Numerics.Profile) (host : HostSemantics H) (M M' : Module) : Prop :=
  (∀ s xas c, StoreOk s → Instantiate P host s M xas c →
    ∃ c' p, Good p ∧ Instantiate P host s M' xas c' ∧ c'.frame = c.frame ∧ c'.code = c.code ∧
      SR p c.store c'.store) ∧
  (∀ s xas c', StoreOk s → Instantiate P host s M' xas c' →
    ∃ c p, Good p ∧ Instantiate P host s M xas c ∧ c'.frame = c.frame ∧ c'.code = c.code ∧
      SR p c.store c'.store)

theorem obs_corr_profile
    {M M' : Module} {s : Store H} (hs : StoreOk s) {xas : List ExternAddr} {c c' : Config H}
    (hi : Instantiate P closedHost s M xas c) (hi' : Instantiate P closedHost s M' xas c')
    (hG : Good p) (replay : ChosenReverseStep p P H) (hfr : c'.frame = c.frame) (hcode : c'.code = c.code)
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
  have hc := Instantiate.ok divHost_ok hs (Unwrap.instantiate_of_closed_unwrap divHost hi)
  have hc' := Instantiate.ok divHost_ok hs (Unwrap.instantiate_of_closed_unwrap divHost hi')
  have hMR : MR p .gen c c' := ⟨hfr, by rw [hcode]; exact LN.refl p _⟩
  obtain ⟨R1, R2, R3, R4⟩ := runs_corr_profile hG replay hc hc' hMR hSR
  refine ⟨fun bs h => ?_, fun bs h => ?_⟩
  · rcases h with ⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩
    · obtain ⟨x, hx, hxc, hSR'⟩ := R3 c₁ h₁ ⟨.values [], by rw [h₂]; rfl⟩
      refine .inl ⟨x, bs', hx, by rw [hxc, h₂], ?_, rfl⟩
      rw [← hfr]
      exact session_reverse_profile hG replay h₃ (ConfigOk.storeOk (Unwrap.preserves_closed hc hx))
        (ConfigOk.storeOk (Unwrap.preserves_closed hc' h₁)) hSR'
    · obtain ⟨x, hx, hxc, -⟩ := R3 c₁ h₁ ⟨r, h₂⟩
      exact .inr (.inl ⟨x, r, hx, by rw [hxc, h₂], h₃, rfl⟩)
    · exact .inr (.inr ⟨R4 h₁, rfl⟩)
  · rcases h with ⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩
    · obtain ⟨x, hx, hxc, hSR'⟩ := R1 c₁ h₁ ⟨.values [], by rw [h₂]; rfl⟩
      refine .inl ⟨x, bs', hx, by rw [hxc, h₂], ?_, rfl⟩
      rw [hfr]
      exact session_forward_closed_profile hG replay h₃ (ConfigOk.storeOk (Unwrap.preserves_closed hc h₁))
        (ConfigOk.storeOk (Unwrap.preserves_closed hc' hx)) hSR'
    · obtain ⟨x, hx, hxc, -⟩ := R1 c₁ h₁ ⟨r, h₂⟩
      exact .inr (.inl ⟨x, r, hx, by rw [hxc, h₂], h₃, rfl⟩)
    · exact .inr (.inr ⟨R2 h₁, rfl⟩)

/-- **Export equivalence from corresponding instantiations.** -/
theorem exportEquiv_of_instCorr_profile
    (allReplay : ∀ p, Good p → ChosenReverseStep p P H)
    {M M' : Module} (h : InstCorrProfile P (closedHost (H := H)) M M') :
    ExportEquiv (· = ·) P (closedHost (H := H)) M' M := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨⟨fun s xas c hs hi => ?_, fun s xas script hs bs hbs => ?_⟩,
    ⟨fun s xas c' hs hi' => ?_, fun s xas script hs bs hbs => ?_⟩⟩
  · obtain ⟨c', p, -, hi', -⟩ := h₁ s xas c hs hi
    exact ⟨c', hi'⟩
  · obtain ⟨c', hi', hrun⟩ := hbs
    obtain ⟨c, p, hG, hi, hfr, hcode, hSR⟩ := h₂ s xas c' hs hi'
    exact ⟨bs, ⟨c, hi, (obs_corr_profile hs hi hi' hG (allReplay p hG) hfr hcode hSR script).1 bs hrun⟩,
      SessionRel.refl (fun _ => rfl) bs⟩
  · obtain ⟨c, p, -, hi, -⟩ := h₂ s xas c' hs hi'
    exact ⟨c, hi⟩
  · obtain ⟨c, hi, hrun⟩ := hbs
    obtain ⟨c', p, hG, hi', hfr, hcode, hSR⟩ := h₁ s xas c hs hi
    exact ⟨bs, ⟨c', hi', (obs_corr_profile hs hi hi' hG (allReplay p hG) hfr hcode hSR script).2 bs hrun⟩,
      SessionRel.refl (R := fun b b' => (fun x1 x2 => x1 = x2) b' b) (fun _ => rfl) bs⟩

/-- **The instantiations of a module and of the module with one function's code replaced
correspond.** -/
theorem instCorr_of_set_profile {host : HostSemantics H} {M : Module} {g jf : Nat} {cg cg' cf : Func}
    (hg : M.funcs[g]? = some cg) (hf : M.funcs[jf]? = some cf) (hty : cg'.type = cg.type)
    (hval : ∀ mt, ModuleOk M mt ↔ ModuleOk { M with funcs := M.funcs.set g cg' } mt)
    (hgood : SiteGood M g jf cg cg' cf) :
    InstCorrProfile P host M { M with funcs := M.funcs.set g cg' } := by
  refine ⟨fun s xas c _ hi => ?_, fun s xas c' _ hi' => ?_⟩
  · obtain ⟨n₀, c', hi', hfr, hcode, hst, hA⟩ :=
      instantiate_set hg hty (fun mt h => (hval mt).mp h) hi
    obtain ⟨p, hG, hSR⟩ := good_sr hg hf hgood hA (instantiate_funcs_len hi) hst
    exact ⟨c', p, hG, hi', hfr, hcode, hSR⟩
  · have hlt := (List.getElem?_eq_some_iff.mp hg).1
    have hg' : (M.funcs.set g cg')[g]? = some cg' := by simp [hlt]
    have hback : ({ ({ M with funcs := M.funcs.set g cg' } : Module) with
        funcs := (M.funcs.set g cg').set g cg } : Module) = M := by
      have : (M.funcs.set g cg').set g cg = M.funcs := by
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
      instantiate_set (M := { M with funcs := M.funcs.set g cg' }) hg' hty.symm
        (fun mt h => by
          rw [hback]
          obtain ⟨mt₀, h₀⟩ : ∃ mt₀, ModuleOk M mt₀ := by
            obtain ⟨xtE, xtI, hmt, -⟩ := hi'.valid
            exact ⟨_, (hval _).mpr hmt⟩
          have h₀' := (hval mt₀).mp h₀
          rw [ModuleOk.unique h h₀']
          exact h₀) hi'
    rw [hback] at hi
    obtain ⟨hA, hst'⟩ := funcAlloc_back hg hty hA' hfr hst
    obtain ⟨p, hG, hSR⟩ := good_sr hg hf hgood hA (instantiate_funcs_len hi) hst'
    exact ⟨c, p, hG, hi, hfr.symm, hcode.symm, hSR⟩

end Silmaril.Wasm.Binaryen.InlR
