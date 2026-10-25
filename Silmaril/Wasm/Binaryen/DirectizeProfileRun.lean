module

public import Silmaril.Wasm.Binaryen.DirectizeBackRun

@[expose] public section

/-! # Directize under arbitrary numerical profiles

The backward simulation follows the actual choices of each target execution.
Together with the forward simulation, it gives both directions of terminal-result
and divergence correspondence, and preserves repeated export-call sessions.
-/

namespace Silmaril.Wasm.Binaryen.DirSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type} {ok : SiteOk} {mi : ModuleInst} {P : Numerics.Profile}

/-- Actual terminal results and divergence correspond without deterministic profiles. -/
theorem runs_corr_profile {c c' : Config H} {ts : List CValType}
    (hc : ConfigOk c ts) (hinv : FInv ok mi c) (hMR : Back.MR ok mi c c')
    (hSR : SR ok mi c.store c'.store) :
    (∀ x, Steps P closedHost c x → x.Terminal →
      ∃ x', Steps P closedHost c' x' ∧ x'.code = x.code ∧ SR ok mi x.store x'.store) ∧
    (Diverges P closedHost c → Diverges P closedHost c') ∧
    (∀ x', Steps P closedHost c' x' → x'.Terminal →
      ∃ x, Steps P closedHost c x ∧ x.code = x'.code ∧ SR ok mi x.store x'.store) ∧
    (Diverges P closedHost c' → Diverges P closedHost c) := by
  have hinvs : ∀ x, Steps P closedHost c x → DInv ok mi x.store :=
    fun x hx => (finv_steps hc hinv hx).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx ⟨r, hr⟩
    obtain ⟨x', hx', hMR', hSR'⟩ := run_sim hx hinvs hMR.forward hSR
    exact ⟨x', hx', by rw [terminal_code hMR' hr, hr], hSR'⟩
  · intro hd
    exact div_sim hd hinvs hMR.forward hSR
  · intro x' hx' ⟨r, hr⟩
    obtain ⟨x, hx, hMR', hSR'⟩ := Back.run_sim hx' hinvs hMR hSR
    exact ⟨x, hx, by rw [Back.terminal_code hMR' hr, hr], hSR'⟩
  · intro hd
    exact Back.div_sim hd hinvs hMR hSR

/-- Invocation starts in the stable relation, even when call annotations differ. -/
theorem invoke_rel_profile {s t : Store H} (hSR : SR ok mi s t) (a : Nat) (vs : List Val) :
    Back.MR ok mi (invoke s a vs) (invoke t a vs) := by
  refine ⟨rfl, ?_⟩
  simp only [invoke]
  rw [funcType_eq hSR a]
  exact Back.GL.refl _

/-- **Sessions of the right module are sessions of the left one.** -/
theorem session_corr₁_profile {mj : ModuleInst} {t : Store H} {script : List Call}
    {bs : List (Behaviour Val)} (h : Session P closedHost mj t script bs) :
    ∀ {s : Store H}, StoreOk s → StoreOk t → SInv ok mi s → SR ok mi s t →
      Session P closedHost mj s script bs := by
  induction h with
  | nil => exact fun _ _ _ _ => .nil
  | stop h => exact fun _ _ _ hSR => .stop fun a ha hok' => h a ha (invokeOk_of hSR hok')
  | @done t x vs rest a c r bs ha hok' run hr tail ih =>
    intro s hs ht hinv hSR
    have hokO := invokeOk_of' hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hokO
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hok'
    obtain ⟨-, -, R3, -⟩ := runs_corr_profile hcO (finv_invoke hinv _ _) (invoke_rel_profile hSR a vs)
      (by simpa [invoke] using hSR)
    obtain ⟨x', hx', hcode, hSR'⟩ := R3 c run ⟨r, hr⟩
    exact .done ha hokO hx' (by rw [hcode, hr])
      (ih (ConfigOk.storeOk (Unwrap.preserves_closed hcO hx'))
        (ConfigOk.storeOk (Unwrap.preserves_closed hcN run)) (sinv_of (finv_steps hcO (finv_invoke hinv _ _) hx')) hSR')
  | @diverge t x vs rest a ha hok' hd =>
    intro s hs ht hinv hSR
    have hokO := invokeOk_of' hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hokO
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hok'
    obtain ⟨-, -, -, R4⟩ := runs_corr_profile hcO (finv_invoke hinv _ _) (invoke_rel_profile hSR a vs)
      (by simpa [invoke] using hSR)
    exact .diverge ha hokO (R4 hd)

/-- **Sessions of the left module are sessions of the right one.** -/
theorem session_corr₂_profile {mj : ModuleInst} {s : Store H} {script : List Call}
    {bs : List (Behaviour Val)} (h : Session P closedHost mj s script bs) :
    ∀ {t : Store H}, StoreOk s → StoreOk t → SInv ok mi s → SR ok mi s t →
      Session P closedHost mj t script bs := by
  induction h with
  | nil => exact fun _ _ _ _ => .nil
  | stop h => exact fun _ _ _ hSR => .stop fun a ha hok' => h a ha (invokeOk_of' hSR hok')
  | @done s x vs rest a c r bs ha hok' run hr tail ih =>
    intro t hs ht hinv hSR
    have hokN := invokeOk_of hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hok'
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hokN
    obtain ⟨R1, -, -, -⟩ := runs_corr_profile hcO (finv_invoke hinv _ _) (invoke_rel_profile hSR a vs)
      (by simpa [invoke] using hSR)
    obtain ⟨x', hx', hcode, hSR'⟩ := R1 c run ⟨r, hr⟩
    exact .done ha hokN hx' (by rw [hcode, hr])
      (ih (ConfigOk.storeOk (Unwrap.preserves_closed hcO run))
        (ConfigOk.storeOk (Unwrap.preserves_closed hcN hx')) (sinv_of (finv_steps hcO (finv_invoke hinv _ _) run)) hSR')
  | @diverge s x vs rest a ha hok' hd =>
    intro t hs ht hinv hSR
    have hokN := invokeOk_of hSR hok'
    obtain ⟨_, _, _, _, _, hcO⟩ := invoke_ok hs hok'
    obtain ⟨_, _, _, _, _, hcN⟩ := invoke_ok ht hokN
    obtain ⟨-, R2, -, -⟩ := runs_corr_profile hcO (finv_invoke hinv _ _) (invoke_rel_profile hSR a vs)
      (by simpa [invoke] using hSR)
    exact .diverge ha hokN (R2 hd)


variable (P) in
/-- The observations of a configuration that runs instantiation code, then a session. -/
def ObsProfile (c : Config H) (script : List Call) (bs : List (Behaviour Val)) : Prop :=
  (∃ c₁ bs', Steps P closedHost c c₁ ∧ c₁.code = [] ∧
      Session P closedHost c.frame.module c₁.store script bs' ∧ bs = .returns [] :: bs') ∨
    (∃ (c₁ : Config H) (r : Result), Steps P closedHost c c₁ ∧ c₁.code = r.toAdmin ∧
      r ≠ .values [] ∧ bs = [r.toBehaviour]) ∨
    (Diverges P closedHost c ∧ bs = [.diverges])


/-- Corresponding configurations observe the same. -/
theorem obs_core_profile {cm cm' : Config H} {ts ts' : List CValType} (hc : ConfigOk cm ts)
    (hc' : ConfigOk cm' ts') (hMR : Back.MR ok mi cm cm') (hSR : SR ok mi cm.store cm'.store)
    (hinv : FInv ok mi cm) (script : List Call) (bs : List (Behaviour Val)) :
    ObsProfile P cm script bs ↔ ObsProfile P cm' script bs := by
  obtain ⟨R1, R2, R3, R4⟩ := runs_corr_profile hc hinv hMR hSR
  have hfr := hMR.1
  constructor
  · rintro (⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩)
    · obtain ⟨x, hx, hxc, hSR'⟩ := R1 c₁ h₁ ⟨.values [], by rw [h₂]; rfl⟩
      refine .inl ⟨x, bs', hx, by rw [hxc, h₂], ?_, rfl⟩
      rw [← hfr]
      exact session_corr₂_profile h₃ (ConfigOk.storeOk (Unwrap.preserves_closed hc h₁))
        (ConfigOk.storeOk (Unwrap.preserves_closed hc' hx))
        (sinv_of (finv_steps hc hinv h₁)) hSR'
    · obtain ⟨x, hx, hxc, -⟩ := R1 c₁ h₁ ⟨r, h₂⟩
      exact .inr (.inl ⟨x, r, hx, by rw [hxc, h₂], h₃, rfl⟩)
    · exact .inr (.inr ⟨R2 h₁, rfl⟩)
  · rintro (⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩)
    · obtain ⟨x, hx, hxc, hSR'⟩ := R3 c₁ h₁ ⟨.values [], by rw [h₂]; rfl⟩
      refine .inl ⟨x, bs', hx, by rw [hxc, h₂], ?_, rfl⟩
      rw [hfr]
      exact session_corr₁_profile h₃ (ConfigOk.storeOk (Unwrap.preserves_closed hc hx))
        (ConfigOk.storeOk (Unwrap.preserves_closed hc' h₁))
        (sinv_of (finv_steps hc hinv hx)) hSR'
    · obtain ⟨x, hx, hxc, -⟩ := R3 c₁ h₁ ⟨r, h₂⟩
      exact .inr (.inl ⟨x, r, hx, by rw [hxc, h₂], h₃, rfl⟩)
    · exact .inr (.inr ⟨R4 h₁, rfl⟩)

end Silmaril.Wasm.Binaryen.DirSim
