module

public import Silmaril.Wasm.Binaryen.DirectizeProfileRun
public import Silmaril.Wasm.Binaryen.Pass.DirectizeProfileInit
public import Silmaril.Wasm.Binaryen.Pass.DirectizeInitPrefix

@[expose] public section

/-! # Directize observations through initialization prefixes

Each initialization prefix records an actual finite run through locally forced
steps or absorbing trap cleanup. The continuation can make arbitrary numerical
and growth choices. Prefix observations therefore transfer without assuming
global determinism or selecting just one nondeterministic outcome.
-/

namespace Silmaril.Wasm.Binaryen.DirSim

open Silmaril.Wasm Execution.Core Numerics Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR

variable {H : Type} {ok : SiteOk} {mi : ModuleInst} {P : Profile}

/-- A normal form has no nontrivial outgoing finite run, for any numerical profile. -/
theorem nf_eq_of_steps_profile {c x : Config H} (hx : Steps P closedHost c x)
    (hnf : ∀ z, ¬ Step P closedHost c z) : c = x := by
  rcases Relation.ReflTransGen.cases_head hx with rfl | ⟨y, hy, _⟩
  · rfl
  · exact (hnf y hy).elim

/-- All observations pass through an initialization prefix. The suffix remains
free to make its own actual choices under the arbitrary profile. -/
theorem obs_mid_profile {c cm : Config H} (hm : InitPrefix.Prefix P c cm)
    (hfm : cm.frame.module = c.frame.module) (script : List Call) (bs : List (Behaviour Val)) :
    ObsProfile P c script bs ↔ ObsProfile P cm script bs := by
  constructor
  · rintro (⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩)
    · refine .inl ⟨c₁, bs', hm.to_nf h₁ (terminal_no_step ⟨.values [], h₂⟩), h₂, ?_, rfl⟩
      rw [hfm]; exact h₃
    · exact .inr (.inl ⟨c₁, r, hm.to_nf h₁ (terminal_no_step ⟨r, h₂⟩), h₂, h₃, rfl⟩)
    · exact .inr (.inr ⟨hm.diverges h₁, rfl⟩)
  · rintro (⟨c₁, bs', h₁, h₂, h₃, rfl⟩ | ⟨c₁, r, h₁, h₂, h₃, rfl⟩ | ⟨h₁, rfl⟩)
    · refine .inl ⟨c₁, bs', hm.steps.trans h₁, h₂, ?_, rfl⟩
      rw [← hfm]; exact h₃
    · exact .inr (.inl ⟨c₁, r, hm.steps.trans h₁, h₂, h₃, rfl⟩)
    · exact .inr (.inr ⟨hm.diverges_back h₁, rfl⟩)

/-- An initialization prefix ending in a trap has the trap as its only observation. -/
theorem obs_trap_profile {c x : Config H} (hx : InitPrefix.Prefix P c x)
    (hxc : x.code = [.trap]) (script : List Call) (bs : List (Behaviour Val)) :
    ObsProfile P c script bs ↔ bs = [Result.trap.toBehaviour] := by
  have hxT : x.Terminal := ⟨.trap, hxc⟩
  have hnf : ∀ z, ¬ Step P closedHost x z := terminal_no_step hxT
  constructor
  · rintro (⟨c₁, bs', h₁, h₂, -, rfl⟩ | ⟨c₁, r, h₁, h₂, -, rfl⟩ | ⟨h₁, rfl⟩)
    · have he := nf_eq_of_steps_profile (hx.to_nf h₁ (terminal_no_step ⟨.values [], h₂⟩)) hnf
      subst he
      rw [hxc] at h₂
      cases h₂
    · have he := nf_eq_of_steps_profile (hx.to_nf h₁ (terminal_no_step ⟨r, h₂⟩)) hnf
      subst he
      rw [hxc] at h₂
      cases r with
      | values vs =>
        cases vs with
        | nil => cases h₂
        | cons v vs =>
          simp only [Result.toAdmin, vals, List.map_cons, List.cons.injEq] at h₂
          have hv := congrArg Admin.val? h₂.1.symm
          rw [Admin.val?_toAdmin] at hv
          simp [Admin.val?] at hv
      | trap => rfl
      | throw a => simp [Result.toAdmin] at h₂
    · obtain ⟨y, hy, _⟩ := InfiniteTrace.unfold (hx.diverges h₁)
      exact (hnf y hy).elim
  · rintro rfl
    exact .inr (.inl ⟨x, .trap, hx.steps, hxc, by simp, rfl⟩)

/-- Instantiation correspondence with administrative initialization prefixes. -/
abbrev PreProfile (P : Profile) (ok : SiteOk) (mi : ModuleInst) (c c' : Config H) : Prop :=
  InitAligned P ok mi c c'

/-- Initialization preserves every observation of each nondeterministic suffix. -/
theorem obs_pre_profile {c c' : Config H} {ts ts' : List CValType} (hc : ConfigOk c ts)
    (hc' : ConfigOk c' ts') (h : PreProfile P ok mi c c')
    (script : List Call) (bs : List (Behaviour Val)) :
    ObsProfile P c script bs ↔ ObsProfile P c' script bs := by
  rcases h with ⟨cm, cm', hm, hm', hfr, hcode, hSR, hinv⟩ | ⟨x, x', hx, hx', hxc, hxc'⟩
  · rw [obs_mid_profile hm (GlobRead.steps_frame_module hm.steps) script bs,
      obs_mid_profile hm' (GlobRead.steps_frame_module hm'.steps) script bs]
    exact obs_core_profile (Unwrap.preserves_closed hc hm.steps)
      (Unwrap.preserves_closed hc' hm'.steps) ⟨hfr, hcode ▸ Back.GL.refl _⟩ hSR hinv script bs
  · rw [obs_trap_profile hx hxc, obs_trap_profile hx' hxc']

/-- Corresponding instantiations with initialization prefixes, for an arbitrary profile. -/
def InstCorrProfile (P : Profile) (M M' : Module) : Prop :=
  (∀ (s : Store H) xas c, StoreOk s → Instantiate P closedHost s M xas c →
    ∃ c' ok mi, Instantiate P closedHost s M' xas c' ∧ PreProfile P ok mi c c') ∧
  (∀ (s : Store H) xas c', StoreOk s → Instantiate P closedHost s M' xas c' →
    ∃ c ok mi, Instantiate P closedHost s M xas c ∧ PreProfile P ok mi c c')

/-- Closed-host export equivalence, preserving all actual outcomes of an arbitrary
numerical profile through initialization and repeated export calls. -/
theorem exportEquiv_of_instCorr_profile {M M' : Module}
    (h : InstCorrProfile (H := H) P M M') :
    ExportEquiv (· = ·) P (closedHost (H := H)) M' M := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨⟨fun s xas c hs hi => ?_, fun s xas script hs bs hbs => ?_⟩,
    ⟨fun s xas c' hs hi' => ?_, fun s xas script hs bs hbs => ?_⟩⟩
  · obtain ⟨c', -, -, hi', -⟩ := h₁ s xas c hs hi
    exact ⟨c', hi'⟩
  · obtain ⟨c', hi', hrun⟩ := hbs
    obtain ⟨c, ok, mi, hi, hpre⟩ := h₂ s xas c' hs hi'
    have hc := Instantiate.ok divHost_ok hs (Unwrap.instantiate_of_closed_unwrap divHost hi)
    have hc' := Instantiate.ok divHost_ok hs (Unwrap.instantiate_of_closed_unwrap divHost hi')
    exact ⟨bs, ⟨c, hi, (obs_pre_profile hc hc' hpre script bs).2 hrun⟩,
      SessionRel.refl (fun _ => rfl) bs⟩
  · obtain ⟨c, -, -, hi, -⟩ := h₂ s xas c' hs hi'
    exact ⟨c, hi⟩
  · obtain ⟨c, hi, hrun⟩ := hbs
    obtain ⟨c', ok, mi, hi', hpre⟩ := h₁ s xas c hs hi
    have hc := Instantiate.ok divHost_ok hs (Unwrap.instantiate_of_closed_unwrap divHost hi)
    have hc' := Instantiate.ok divHost_ok hs (Unwrap.instantiate_of_closed_unwrap divHost hi')
    exact ⟨bs, ⟨c', hi', (obs_pre_profile hc hc' hpre script bs).1 hrun⟩,
      SessionRel.refl (R := fun b b' => (fun x1 x2 => x1 = x2) b' b) (fun _ => rfl) bs⟩

end Silmaril.Wasm.Binaryen.DirSim
