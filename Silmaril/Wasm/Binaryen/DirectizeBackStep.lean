module

public import Silmaril.Wasm.Binaryen.DirectizeBackSite

@[expose] public section

/-! # Directize: backward step simulation using actual numerical choices -/

namespace Silmaril.Wasm.Binaryen.DirSim.Back

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type} {ok : SiteOk} {mi : ModuleInst} {P : Numerics.Profile}

theorem GL.append_inv_right {cur : ModuleInst} : ∀ {A B os : List Admin},
    GL ok mi cur os (A ++ B) →
      ∃ o₁ o₂, os = o₁ ++ o₂ ∧ GL ok mi cur o₁ A ∧ GL ok mi cur o₂ B
  | [], _, os, h => ⟨[], os, rfl, .nil _, h⟩
  | _ :: _, _, _, .cons h t => by
    obtain ⟨o₁, o₂, rfl, h₁, h₂⟩ := GL.append_inv_right t
    exact ⟨_ :: o₁, o₂, rfl, .cons h h₁, h₂⟩
  | _ :: _, _, _, .site hq hok t => by
    obtain ⟨o₁, o₂, rfl, h₁, h₂⟩ := GL.append_inv_right t
    exact ⟨_ :: _ :: o₁, o₂, rfl, .site hq hok h₁, h₂⟩

section heads
variable {s t : Store H} {f : Frame} {args : List Val} {c₀ : Config H}

theorem head_rel {e e' : Admin} (IH : SimIH ok mi P H (sizeOf e'))
    (hinv : DInv ok mi s) (hh : Det.Head P t f args e' c₀)
    (he : GA ok mi f.module e e') (hSR : SR ok mi s t) :
    HRes ok mi P s f args e c₀ := by
  have hgood := hh.good
  cases he with
  | plain hi => exact head_plain hi hh hSR
  | ref _ r => exact absurd hgood.val_none (by simp)
  | ann ha hb => exact head_ann hh hSR ha hb
  | retAnn _ hb => exact absurd (Det.IsReturnCallRef.blocked hb) hgood.not_blocked
  | label hc hb => exact head_label IH hinv hh hc hb hSR
  | handler hb => exact head_handler IH hinv hh hb hSR
  | frame hb => exact head_frame IH hinv hh hb hSR
  | trap _ => exact absurd rfl hgood.ne_trap
end heads

/-- Stable related value prefixes are already identical. A site matches in three steps. -/
theorem sim_head {k : Nat} (IH : SimIH ok mi P H k) {s t : Store H} {f : Frame}
    {vs args : List Val} {e' : Admin} {rest' os : List Admin} {d₀ : Config H}
    (hsz : sizeOf (vals vs ++ (vals args ++ e' :: rest')) < k + 1)
    (hinv : DInv ok mi s) (hh : Det.Head P t f args e' d₀)
    (hrel : GL ok mi f.module os (vals vs ++ (vals args ++ e' :: rest')))
    (hSR : SR ok mi s t) :
    Res ok mi P ⟨s, f, os⟩ ⟨d₀.store, d₀.frame, vals vs ++ d₀.code ++ rest'⟩ := by
  have hlt := sizeOf_head_lt (vs := vs) (args := args) (e := e') (rest := rest')
  have hmod := head_module hh
  rw [headDec_code] at hrel
  obtain ⟨tail, rfl, hB⟩ := GL.vals_prefix_back hrel
  cases hB with
  | cons he hr =>
    rename_i e rest
    obtain ⟨c₀, hp, hsr, hfr, hrel'⟩ := head_rel (IH.mono (by omega)) hinv hh he hSR
    refine ⟨⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩,
      (by simpa using (DirSim.lift_tg (Y := [e]) hp)), ⟨hfr, ?_⟩, hsr⟩
    simp only
    rw [hfr, hmod]
    exact GL.append (GL.append (GL.of_vals vs) hrel') hr
  | site hq hok hr => exact sim_site hinv hh hq hok hr hSR

/-- Trap and exception bubbling preserves a related suffix without any numeric choice. -/
theorem sim_bubble {s t : Store H} {f : Frame} {pp q : List Val} {X u r os : List Admin}
    (hX : Det.IsBubble X) (hqu : q ≠ [] ∨ u ≠ [])
    (hrel : GL ok mi f.module os (vals (pp ++ q) ++ X ++ (u ++ r)))
    (hSR : SR ok mi s t) : Res ok mi P ⟨s, f, os⟩ ⟨t, f, vals pp ++ X ++ r⟩ := by
  have hre : GL ok mi f.module os (vals (pp ++ q) ++ (X ++ (u ++ r))) := by
    simpa only [List.append_assoc] using hrel
  obtain ⟨tail, rfl, ht⟩ := GL.vals_prefix_back hre
  obtain ⟨x, ur, rfl, hx, hur⟩ := GL.append_inv_right ht
  have hex : x = X := by
    rcases hX with rfl | ⟨a, rfl⟩
    · exact GL.abrupt_back (r := .trap) (by intro _ h; cases h) hx
    · exact GL.abrupt_back (r := .throw a) (by intro _ h; cases h) hx
  subst x
  obtain ⟨uL, rL, rfl, hu, hr⟩ := GL.append_inv_right hur
  have hquL : q ≠ [] ∨ uL ≠ [] := by
    rcases hqu with hq | hu'
    · exact .inl hq
    · right
      intro he
      subst he
      cases hu
      exact hu' rfl
  refine ⟨⟨s, f, vals pp ++ X ++ rL⟩, .single ?_,
    ⟨rfl, GL.append (GL.append (GL.of_vals pp) (GL.refl X)) hr⟩, hSR⟩
  exact Det.Bubble.toStep ⟨pp, q, X, uL, rL, by simp [List.append_assoc], hX, hquL, rfl⟩

/-- Every actual target step has a positive original match, including tail calls. -/
theorem sim : ∀ k : Nat, SimIH ok mi P H k
  | 0 => fun _ _ _ hsz => absurd hsz (Nat.not_lt_zero _)
  | k + 1 => fun d d' c hsz hstep hMR hSR hinv => by
    have IH := sim k
    obtain ⟨s, f, os⟩ := c
    obtain ⟨t, fn, ns⟩ := d
    obtain ⟨hfr, hrel⟩ := hMR
    simp only at hfr hrel hSR hinv
    subst hfr
    rcases Det.Step.decomp hstep with ⟨vs, args, e, rest, c₀, hcode, hh, rfl⟩ |
        ⟨pp, q, X, u, r, hcode, hX, hqu, rfl⟩
    · simp only at hcode
      subst hcode
      exact sim_head IH hsz hinv hh hrel hSR
    · simp only at hcode
      subst hcode
      exact sim_bubble hX hqu hrel hSR

end Silmaril.Wasm.Binaryen.DirSim.Back
