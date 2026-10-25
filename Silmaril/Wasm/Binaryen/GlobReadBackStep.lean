module

public import Silmaril.Wasm.Binaryen.GlobReadBackFrame

@[expose] public section

/-! # Immutable-global substitution: backward step simulation for arbitrary profiles -/

namespace Silmaril.Wasm.Binaryen.GlobRead.Back

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type} {p : Prm} {P : Numerics.Profile}

section heads
variable {s t : Store H} {f : Frame} {args : List Val} {c₀ : Config H}

theorem head_rel (hok : PrmOk p) {e e' : Admin} (IH : SimIH p P H (sizeOf e'))
    (hinv : GInv p.lk p.mi s)
    (hh : Det.Head P t f args e' c₀) (he : GA p.lk p.mi f.module e e') (hSR : SR p s t) :
    HRes p P s f args e c₀ := by
  have hgood := hh.good
  cases he with
  | plain hi => exact head_plain hok hi hh hSR
  | ref _ r => exact absurd hgood.val_none (by simp)
  | callRef _ d =>
    exact head_flat hok hh hSR (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h)
  | retCallRef _ d =>
    exact head_flat hok hh hSR (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h)
  | label hc hb => exact head_label IH hinv hh hc hb hSR
  | handler hb => exact head_handler IH hinv hh hb hSR
  | frame hb => exact head_frame IH hinv hh hb hSR
  | trap _ => exact absurd rfl hgood.ne_trap


end heads

/-- Prepare original value reads and then consume the exact literal-side head step. -/
theorem sim_head (hok : PrmOk p) {k : Nat} (IH : SimIH p P H k) {s t : Store H} {f : Frame}
    {vs args : List Val} {e' : Admin} {rest' os : List Admin} {d₀ : Config H}
    (hsz : sizeOf (vals vs ++ (vals args ++ e' :: rest')) < k + 1)
    (hinv : GInv p.lk p.mi s) (hh : Det.Head P t f args e' d₀)
    (hrel : GL p.lk p.mi f.module os (vals vs ++ (vals args ++ e' :: rest')))
    (hSR : SR p s t) :
    Res p P ⟨s, f, os⟩ ⟨d₀.store, d₀.frame, vals vs ++ d₀.code ++ rest'⟩ := by
  have hlt := sizeOf_head_lt (vs := vs) (args := args) (e := e') (rest := rest')
  have hmod := head_module hh
  rw [headDec_code] at hrel
  obtain ⟨_, hprep, hB⟩ := GL.prepare_prefix (P := P) hinv hrel
  cases hB with
  | cons he hr =>
    rename_i e rest
    obtain ⟨c₀, hp, hsr, hfr, hrel'⟩ := head_rel hok (IH.mono (by omega)) hinv hh he hSR
    refine ⟨⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩,
      Relation.TransGen.trans_right hprep (by simpa using (GlobRead.lift_tg (Y := [e]) hp)),
      ⟨hfr, ?_⟩, hsr⟩
    simp only
    rw [hfr, hmod]
    exact GL.append (GL.append (GL.of_vals vs) hrel') hr

/-- Trap/exception bubbling is matched after preparing the original value prefix. -/
theorem sim_bubble {s t : Store H} {f : Frame} {pp q : List Val} {X u r os : List Admin}
    (hX : Det.IsBubble X) (hqu : q ≠ [] ∨ u ≠ []) (hinv : GInv p.lk p.mi s)
    (hrel : GL p.lk p.mi f.module os (vals (pp ++ q) ++ X ++ (u ++ r)))
    (hSR : SR p s t) : Res p P ⟨s, f, os⟩ ⟨t, f, vals pp ++ X ++ r⟩ := by
  have hre : GL p.lk p.mi f.module os (vals (pp ++ q) ++ (X ++ (u ++ r))) := by
    simpa only [List.append_assoc] using hrel
  obtain ⟨tail, hp, ht⟩ := GL.prepare_prefix (P := P) hinv hre
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
  refine ⟨⟨s, f, vals pp ++ X ++ rL⟩, Relation.TransGen.tail' hp ?_,
    ⟨rfl, GL.append (GL.append (GL.of_vals pp) (GL.refl X)) hr⟩, hSR⟩
  exact Det.Bubble.toStep ⟨pp, q, X, uL, rL, by simp [List.append_assoc], hX, hquL, rfl⟩

/-- Every actual step of the literal side is matched by one or more original steps. -/
theorem sim (hok : PrmOk p) : ∀ k : Nat, SimIH p P H k
  | 0 => fun _ _ _ hsz => absurd hsz (Nat.not_lt_zero _)
  | k + 1 => fun d d' c hsz hstep hMR hSR hinv => by
    have IH := sim hok k
    obtain ⟨s, f, os⟩ := c
    obtain ⟨t, fn, ns⟩ := d
    obtain ⟨hfr, hrel⟩ := hMR
    simp only at hfr hrel hSR hinv
    subst hfr
    rcases Det.Step.decomp hstep with ⟨vs, args, e, rest, c₀, hcode, hh, rfl⟩ |
        ⟨pp, q, X, u, r, hcode, hX, hqu, rfl⟩
    · simp only at hcode
      subst hcode
      exact sim_head hok IH hsz hinv hh hrel hSR
    · simp only at hcode
      subst hcode
      exact sim_bubble hX hqu hinv hrel hSR

end Silmaril.Wasm.Binaryen.GlobRead.Back
