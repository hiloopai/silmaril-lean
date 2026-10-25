module

public import Silmaril.Wasm.Binaryen.GlobReadRun
public import Silmaril.Wasm.Binaryen.GlobReadBackRun

@[expose] public section

/-! # Immutable-global substitution under arbitrary numerical profiles

The backward simulation matches the choices made by the actual literal-side
run. Together with the existing forward simulation, it gives both directions
of result and divergence correspondence without a determinism assumption.
Typed store extension preserves the immutable-global invariant through runs,
repeated export calls and module observations.
-/

namespace Silmaril.Wasm.Binaryen.GlobRead

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type} {p : Prm} {P : Numerics.Profile}

/-- Closed-host terminal results and divergence correspond for the actual
choices of an arbitrary numerical profile. -/
theorem runs_corr_profile (hok : PrmOk p) {c c' : Config H} {ts : List CValType}
    (hc : ConfigOk c ts) (hinv : GInv p.lk p.mi c.store) (hMR : MR p c c')
    (hSR : SR p c.store c'.store) :
    (∀ x, Steps P closedHost c x → x.Terminal →
      ∃ x', Steps P closedHost c' x' ∧ x'.code = x.code ∧ SR p x.store x'.store) ∧
    (Diverges P closedHost c → Diverges P closedHost c') ∧
    (∀ x', Steps P closedHost c' x' → x'.Terminal →
      ∃ x, Steps P closedHost c x ∧ x.code = x'.code ∧ SR p x.store x'.store) ∧
    (Diverges P closedHost c' → Diverges P closedHost c) := by
  have hinvs : ∀ x, Steps P closedHost c x → GInv p.lk p.mi x.store :=
    fun x hx => ginv_steps hc hinv hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx ⟨r, hr⟩
    obtain ⟨x', hx', hMR', hSR'⟩ := run_sim hok hx hinvs hMR hSR
    exact ⟨x', hx', by rw [terminal_code hMR' hr, hr], hSR'⟩
  · intro hd
    exact div_sim hok hd hinvs hMR hSR
  · intro x' hx' ⟨r, hr⟩
    obtain ⟨x, hx, hMR', hSR'⟩ := Back.run_sim hok hx' hinvs hMR hSR
    obtain ⟨y, hy, hcode, hstore⟩ := Back.terminal (P := P) (hinvs x hx) hMR' hr
    exact ⟨y, hx.trans hy, by rw [hcode, hr], by simpa only [hstore] using hSR'⟩
  · intro hd
    exact Back.div_sim hok hd hinvs hMR hSR

/-! ## Repeated invocations and module observations -/

/-- **Sessions of the right module are sessions of the left one.** -/
theorem session_corr₁_profile (hok : PrmOk p) {mi : ModuleInst} {t : Store H} {script : List Call}
    {bs : List (Behaviour Val)} (h : Session P closedHost mi t script bs) :
    ∀ {s : Store H}, StoreOk s → StoreOk t → GInv p.lk p.mi s → SR p s t →
      Session P closedHost mi s script bs := by
  induction h with
  | nil => exact fun _ _ _ _ => .nil
  | stop h => exact fun _ _ _ hSR => .stop fun a ha hok' => h a ha (invokeOk_of hSR hok')
  | @done t x vs rest a c r bs ha hok' run hr tail ih =>
    intro s hs ht hinv hSR
    have hokO := invokeOk_of' hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hokO
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hok'
    obtain ⟨-, -, R3, -⟩ := runs_corr_profile hok hcO hinv (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    obtain ⟨x', hx', hcode, hSR'⟩ := R3 c run ⟨r, hr⟩
    exact .done ha hokO hx' (by rw [hcode, hr])
      (ih (ConfigOk.storeOk (Unwrap.preserves_closed hcO hx'))
        (ConfigOk.storeOk (Unwrap.preserves_closed hcN run)) (ginv_steps hcO hinv hx') hSR')
  | @diverge t x vs rest a ha hok' hd =>
    intro s hs ht hinv hSR
    have hokO := invokeOk_of' hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hokO
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hok'
    obtain ⟨-, -, -, R4⟩ := runs_corr_profile hok hcO hinv (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    exact .diverge ha hokO (R4 hd)

/-- **Sessions of the left module are sessions of the right one.** -/
theorem session_corr₂_profile (hok : PrmOk p) {mi : ModuleInst} {s : Store H} {script : List Call}
    {bs : List (Behaviour Val)} (h : Session P closedHost mi s script bs) :
    ∀ {t : Store H}, StoreOk s → StoreOk t → GInv p.lk p.mi s → SR p s t →
      Session P closedHost mi t script bs := by
  induction h with
  | nil => exact fun _ _ _ _ => .nil
  | stop h => exact fun _ _ _ hSR => .stop fun a ha hok' => h a ha (invokeOk_of' hSR hok')
  | @done s x vs rest a c r bs ha hok' run hr tail ih =>
    intro t hs ht hinv hSR
    have hokN := invokeOk_of hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hok'
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hokN
    obtain ⟨R1, -, -, -⟩ := runs_corr_profile hok hcO hinv (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    obtain ⟨x', hx', hcode, hSR'⟩ := R1 c run ⟨r, hr⟩
    exact .done ha hokN hx' (by rw [hcode, hr])
      (ih (ConfigOk.storeOk (Unwrap.preserves_closed hcO run))
        (ConfigOk.storeOk (Unwrap.preserves_closed hcN hx')) (ginv_steps hcO hinv run) hSR')
  | @diverge s x vs rest a ha hok' hd =>
    intro t hs ht hinv hSR
    have hokN := invokeOk_of hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hok'
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hokN
    obtain ⟨-, R2, -, -⟩ := runs_corr_profile hok hcO hinv (invoke_rel hSR a vs)
      (by simpa [invoke] using hSR)
    exact .diverge ha hokN (R2 hd)

/-! ## Module observations -/

/-- A correspondence between the instantiations of the left module `M` and the right module
`M'`, with the invariant on the left instantiation store. -/
def InstCorr_profile (M M' : Module) : Prop :=
  (∀ (s : Store H) xas c, StoreOk s → Instantiate P closedHost s M xas c →
    ∃ c' p, PrmOk p ∧ Instantiate P closedHost s M' xas c' ∧ c'.frame = c.frame ∧
      c'.code = c.code ∧ SR p c.store c'.store ∧ GInv p.lk p.mi c.store) ∧
  (∀ (s : Store H) xas c', StoreOk s → Instantiate P closedHost s M' xas c' →
    ∃ c p, PrmOk p ∧ Instantiate P closedHost s M xas c ∧ c'.frame = c.frame ∧
      c'.code = c.code ∧ SR p c.store c'.store ∧ GInv p.lk p.mi c.store)

theorem obs_corr_profile
    {M M' : Module} {s : Store H} (hs : StoreOk s) {xas : List ExternAddr} {c c' : Config H}
    (hi : Instantiate P closedHost s M xas c) (hi' : Instantiate P closedHost s M' xas c')
    (hok : PrmOk p) (hfr : c'.frame = c.frame) (hcode : c'.code = c.code)
    (hSR : SR p c.store c'.store) (hinv : GInv p.lk p.mi c.store) (script : List Call) :
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
  have hMR : MR p c c' := ⟨hfr.symm, by rw [hcode]; exact GL.refl _⟩
  obtain ⟨R1, R2, R3, R4⟩ := runs_corr_profile hok hc hinv hMR hSR
  refine ⟨fun bs h => ?_, fun bs h => ?_⟩
  · rcases h with ⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩
    · obtain ⟨x, hx, hxc, hSR'⟩ := R3 c₁ h₁ ⟨.values [], by rw [h₂]; rfl⟩
      refine .inl ⟨x, bs', hx, by rw [hxc, h₂], ?_, rfl⟩
      rw [← hfr]
      exact session_corr₁_profile hok h₃ (ConfigOk.storeOk (Unwrap.preserves_closed hc hx))
        (ConfigOk.storeOk (Unwrap.preserves_closed hc' h₁)) (ginv_steps hc hinv hx) hSR'
    · obtain ⟨x, hx, hxc, -⟩ := R3 c₁ h₁ ⟨r, h₂⟩
      exact .inr (.inl ⟨x, r, hx, by rw [hxc, h₂], h₃, rfl⟩)
    · exact .inr (.inr ⟨R4 h₁, rfl⟩)
  · rcases h with ⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩
    · obtain ⟨x, hx, hxc, hSR'⟩ := R1 c₁ h₁ ⟨.values [], by rw [h₂]; rfl⟩
      refine .inl ⟨x, bs', hx, by rw [hxc, h₂], ?_, rfl⟩
      rw [hfr]
      exact session_corr₂_profile hok h₃ (ConfigOk.storeOk (Unwrap.preserves_closed hc h₁))
        (ConfigOk.storeOk (Unwrap.preserves_closed hc' hx)) (ginv_steps hc hinv h₁) hSR'
    · obtain ⟨x, hx, hxc, -⟩ := R1 c₁ h₁ ⟨r, h₂⟩
      exact .inr (.inl ⟨x, r, hx, by rw [hxc, h₂], h₃, rfl⟩)
    · exact .inr (.inr ⟨R2 h₁, rfl⟩)

/-- **Export equivalence from corresponding instantiations.** -/
theorem exportEquiv_of_instCorr_profile {M M' : Module} (h : InstCorr_profile (H := H) (P := P) M M') :
    ExportEquiv (· = ·) P (closedHost (H := H)) M' M := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨⟨fun s xas c hs hi => ?_, fun s xas script hs bs hbs => ?_⟩,
    ⟨fun s xas c' hs hi' => ?_, fun s xas script hs bs hbs => ?_⟩⟩
  · obtain ⟨c', p, -, hi', -⟩ := h₁ s xas c hs hi
    exact ⟨c', hi'⟩
  · obtain ⟨c', hi', hrun⟩ := hbs
    obtain ⟨c, p, hok, hi, hfr, hcode, hSR, hinv⟩ := h₂ s xas c' hs hi'
    exact ⟨bs, ⟨c, hi, (obs_corr_profile hs hi hi' hok hfr hcode hSR hinv script).1 bs hrun⟩,
      SessionRel.refl (fun _ => rfl) bs⟩
  · obtain ⟨c, p, -, hi, -⟩ := h₂ s xas c' hs hi'
    exact ⟨c, hi⟩
  · obtain ⟨c, hi, hrun⟩ := hbs
    obtain ⟨c', p, hok, hi', hfr, hcode, hSR, hinv⟩ := h₁ s xas c hs hi
    exact ⟨bs, ⟨c', hi', (obs_corr_profile hs hi hi' hok hfr hcode hSR hinv script).2 bs hrun⟩,
      SessionRel.refl (R := fun b b' => (fun x1 x2 => x1 = x2) b' b) (fun _ => rfl) bs⟩


end Silmaril.Wasm.Binaryen.GlobRead
