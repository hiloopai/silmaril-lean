module

public import Silmaril.Wasm.Binaryen.InlSeg

@[expose] public section

/-! # The inlining simulation: one step

`sim`: every host-free step of the left (original) configuration is matched by steps of
the right (inlined) one, or the right side waits while the left weight `wL` decreases; the
relation is kept in the same mode. The proof decomposes the left step (`Det.Step.decomp`)
into a head step under a value prefix and a suffix, or a bubbling trap or exception, and
dispatches on the mode; nested activations and labels use the induction hypothesis on
smaller code.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.SingleThreaded

variable {H : Type} {p : Prm} {P : Numerics.Profile}

theorem SimIH.mono {k k' : Nat} (h : SimIH p P H k) (hk : k' ≤ k) : SimIH p P H k' :=
  fun μ o o' n hsz => h μ o o' n (by omega)

theorem sizeOf_head_lt {vs args : List Val} {e : Admin} {rest : List Admin} :
    sizeOf e < sizeOf (vals vs ++ (vals args ++ e :: rest)) :=
  List.sizeOf_lt_of_mem (by simp)

theorem headDec_code {vs args : List Val} {e : Admin} {rest : List Admin} :
    vals vs ++ (vals args ++ e :: rest) = vals (vs ++ args) ++ e :: rest := by simp

/-- Lifting an element result to the whole sequence. -/
theorem lift_res {t t' : Store H} {f f' : Frame} {vs args : List Val} {e' : Admin}
    {rest' code' : List Admin} {w w₀ : Nat}
    (h : Relation.TransGen (Step P Det.noHost) ⟨t, f, vals args ++ [e']⟩ ⟨t', f', code'⟩ ∨
      (⟨t', f', code'⟩ = (⟨t, f, vals args ++ [e']⟩ : Config H) ∧ w < w₀)) :
    Relation.TransGen (Step P Det.noHost) ⟨t, f, vals (vs ++ args) ++ e' :: rest'⟩
        ⟨t', f', vals vs ++ code' ++ rest'⟩ ∨
      ((⟨t', f', vals vs ++ code' ++ rest'⟩ : Config H) = ⟨t, f, vals (vs ++ args) ++ e' :: rest'⟩ ∧
        w < w₀) := by
  rcases h with h | ⟨h, hw⟩
  · left
    have := tg_instrs h vs rest'
    simpa using this
  · right
    simp only [Config.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨by simp, hw⟩

theorem wL_lift {vs args : List Val} {e : Admin} {rest c : List Admin}
    (h : wL c < wL (vals args ++ [e])) :
    wL (vals vs ++ c ++ rest) < wL (vals vs ++ (vals args ++ e :: rest)) := by
  simp only [wL_append, wL_cons] at h ⊢
  simp only [wL_nil] at h
  omega

/-! ## Generic mode -/

theorem sim_gen_head (hok : PrmOk p) {k : Nat} (IH : SimIH p P H k) {s t : Store H} {f : Frame}
    {vs args : List Val} {e : Admin} {rest ns : List Admin} {c₀ : Config H}
    (hsz : sizeOf (vals vs ++ (vals args ++ e :: rest)) < k + 1)
    (hh : Det.Head P s f args e c₀) (hrel : LN p (vals vs ++ (vals args ++ e :: rest)) ns)
    (hSR : SR p s t) :
    Res p P .gen ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩ ⟨t, f, ns⟩
      (wL (vals vs ++ (vals args ++ e :: rest))) := by
  rw [headDec_code] at hrel
  obtain ⟨y, rest', rfl, hy, hr⟩ := LN.vals_cons_inv hrel
  have hlt := sizeOf_head_lt (vs := vs) (args := args) (e := e) (rest := rest)
  have hIH : SimIH p P H (sizeOf e) := IH.mono (by omega)
  obtain ⟨⟨t', f', code'⟩, hprog, hsr, hfr, hrel'⟩ := gen_head hok hIH hh hy hSR
  refine ⟨⟨t', f', vals vs ++ code' ++ rest'⟩, ⟨hfr, LN.append (LN.append (LN.of_vals vs) hrel') hr⟩,
    hsr, ?_⟩
  rcases lift_res (vs := vs) (rest' := rest') (w := wL c₀.code) (w₀ := wL (vals args ++ [e]))
    hprog with h | ⟨h, hw⟩
  · exact .inl h
  · exact .inr ⟨h, wL_lift hw⟩

theorem LN.length_eq : ∀ {a b : List Admin}, LN p a b → a.length = b.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ t => by simp [LN.length_eq t]

theorem sim_gen_bubble {s t : Store H} {f : Frame} {pp q : List Val} {X u r ns : List Admin}
    (hX : Det.IsBubble X) (hqu : q ≠ [] ∨ u ≠ [])
    (hrel : LN p (vals (pp ++ q) ++ X ++ (u ++ r)) ns) (hSR : SR p s t) :
    Res p P .gen ⟨s, f, vals pp ++ X ++ r⟩ ⟨t, f, ns⟩ (wL (vals (pp ++ q) ++ X ++ (u ++ r))) := by
  obtain ⟨n₁, n₂, rfl, h₁, h₂⟩ := LN.append_inv hrel
  obtain ⟨n₃, n₄, rfl, h₃, h₄⟩ := LN.append_inv h₁
  obtain ⟨n₅, n₆, rfl, h₅, h₆⟩ := LN.append_inv h₂
  rw [LN.vals_inv h₃] at *
  have hX' : X = n₄ := by
    rcases hX with rfl | ⟨a, rfl⟩
    · cases h₄ with | cons h t => cases h; cases t; rfl
    · cases h₄ with | cons h t => cases h; cases t with | cons h' t' => cases h'; cases t'; rfl
  subst hX'
  have hlen : n₅.length = u.length := (LN.length_eq h₅).symm
  refine ⟨⟨t, f, vals pp ++ X ++ n₆⟩, ⟨rfl, LN.append (LN.append (LN.of_vals pp) (LN.refl p X)) h₆⟩,
    hSR, .inl (.single (Det.Bubble.toStep ⟨pp, q, X, n₅, n₆, rfl, hX, ?_, rfl⟩))⟩
  rcases hqu with h | h
  · exact .inl h
  · right; intro h'; rw [h'] at hlen; exact h (List.eq_nil_of_length_eq_zero hlen.symm)

/-! ## Caller mode -/

theorem append_eq_append_single {vs args vs₀ : List Val} {x : Val} (h : vs ++ args = vs₀ ++ [x])
    (hne : args ≠ []) : ∃ args₀, args = args₀ ++ [x] ∧ vs₀ = vs ++ args₀ := by
  obtain ⟨args₀, y, rfl⟩ : ∃ args₀ y, args = args₀ ++ [y] :=
    ⟨args.dropLast, args.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  rw [← List.append_assoc] at h
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  simp at h2
  exact ⟨args₀, by rw [h2], h1.symm⟩

theorem sim_g_head (hok : PrmOk p) (hfx : p.mi.funcs[p.fx.toNat]? = some p.af) (hC : PrmC p)
    {k : Nat} (IH : SimIH p P H k) {s t : Store H} {fo : Frame} {E : List (Option Val)}
    (hm : fo.module = p.mi) (hl : fo.locals.length = p.base) (he : E.length = p.ext)
    {vs args : List Val} {e : Admin} {rest ns : List Admin} {c₀ : Config H}
    (hsz : sizeOf (vals vs ++ (vals args ++ e :: rest)) < k + 1)
    (hh : Det.Head P s fo args e c₀) (hrel : LG p E (vals vs ++ (vals args ++ e :: rest)) ns)
    (hSR : SR p s t) :
    Res p P .g ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩ ⟨t, ⟨fo.locals ++ E, p.mi⟩, ns⟩
      (wL (vals vs ++ (vals args ++ e :: rest))) := by
  rw [headDec_code] at hrel
  have hgood := hh.good
  have hlt := sizeOf_head_lt (vs := vs) (args := args) (e := e) (rest := rest)
  have hIH : SimIH p P H (sizeOf e) := IH.mono (by omega)
  rcases LG.vals_cons_inv hgood.val_none hrel with ⟨y, rest', rfl, hy, hr⟩ |
      ⟨vs₀, rest', hvs, rfl, rfl, hr⟩ | ⟨rfl, -⟩ | ⟨rfl, Y, rfl⟩
  · obtain ⟨⟨t', f', code'⟩, E', hprog, hsr, he', hm', hl', hfr', hrel'⟩ :=
      g_head hok hfx hIH hm hl he hh hy hSR
    refine ⟨⟨t', f', vals vs ++ code' ++ rest'⟩, ⟨hm', hl', E', he', hfr', ?_⟩, hsr, ?_⟩
    · simp only [List.append_assoc]
      exact LG.vals_append vs (LG.append_LGq hr hrel')
    · rcases lift_res (vs := vs) (rest' := rest') (w := wL c₀.code) (w₀ := wL (vals args ++ [e]))
        hprog with h | ⟨h, hw⟩
      · exact .inl h
      · exact .inr ⟨h, wL_lift hw⟩
  · have hne : args ≠ [] := by
      rintro rfl
      cases hh with
      | callRefFunc ha => simp at ha
      | parametric h => fam_dismiss
      | numeric h => fam_dismiss
      | vector h => fam_dismiss
      | «variable» h => fam_dismiss
      | table h => fam_dismiss
      | memory h => fam_dismiss
      | reference h => fam_dismiss
      | aggregate h => fam_dismiss
    obtain ⟨args₀, rfl, rfl⟩ := append_eq_append_single hvs hne
    obtain ⟨⟨t', f', code'⟩, E', hprog, hsr, he', hf₀, hfr', hrel'⟩ :=
      g_seg hok hC hm hl he hh hSR
    refine ⟨⟨t', f', vals vs ++ code' ++ rest'⟩, ⟨by rw [hf₀]; exact hm, by rw [hf₀]; exact hl, E',
      he', by rw [hfr', hf₀], ?_⟩, hsr, ?_⟩
    · simp only [List.append_assoc]
      exact LG.vals_append vs (LG.append_LGq hr hrel')
    · have := lift_res (vs := vs) (args := args₀) (rest' := rest') (w := 0) (w₀ := 0) (.inl hprog)
      rcases this with h | ⟨-, h⟩
      · exact .inl (by simpa using h)
      · omega
  · exact absurd rfl hgood.ne_trap
  · have hargs := hgood.throwRef rfl
    subst hargs
    have hc₀ : c₀ = ⟨s, fo, [.trap]⟩ := by
      cases hh with
      | throwRefNull => rfl
      | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
      | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])
      | parametric h => fam_dismiss
      | numeric h => fam_dismiss
      | vector h => fam_dismiss
      | «variable» h => fam_dismiss
      | table h => fam_dismiss
      | memory h => fam_dismiss
      | reference h => fam_dismiss
      | aggregate h => fam_dismiss
    subst hc₀
    refine ⟨⟨t, ⟨fo.locals ++ E, p.mi⟩, vals vs ++ [.trap] ++ Y⟩, ⟨hm, hl, E, he, rfl, ?_⟩, hSR, ?_⟩
    · simp only [List.append_assoc, List.cons_append, List.nil_append]
      exact LG.vals_append vs .trapT
    · rcases lift_res (vs := vs) (rest' := Y) (w := 0) (w₀ := 0)
        (.inl (tg_head (Det.Head.throwRefNull (P := P) (s := t) (f := ⟨fo.locals ++ E, p.mi⟩))))
        with h | ⟨-, h⟩
      · exact .inl (by simpa using h)
      · omega

theorem sim_g_bubble {s t : Store H} {fo : Frame} {E : List (Option Val)}
    (hm : fo.module = p.mi) (hl : fo.locals.length = p.base) (he : E.length = p.ext)
    {pp q : List Val} {X u r ns : List Admin} (hX : Det.IsBubble X) (hqu : q ≠ [] ∨ u ≠ [])
    (hrel : LG p E (vals (pp ++ q) ++ X ++ (u ++ r)) ns) (hSR : SR p s t) :
    Res p P .g ⟨s, fo, vals pp ++ X ++ r⟩ ⟨t, ⟨fo.locals ++ E, p.mi⟩, ns⟩
      (wL (vals (pp ++ q) ++ X ++ (u ++ r))) := by
  -- the right side has the same bubble, followed by some dead code `Y`
  have hns : ∃ Y, ns = vals (pp ++ q) ++ X ++ Y := by
    rcases hX with rfl | ⟨a, rfl⟩
    · rcases LG.vals_cons_inv (vs := pp ++ q) (x := .trap) (rest := u ++ r) rfl
        (by simpa using hrel) with ⟨y, rest', rfl, hy, -⟩ | ⟨_, _, _, h, _⟩ | ⟨-, Y, rfl⟩ |
          ⟨h, -⟩
      · cases hy; exact ⟨rest', by simp⟩
      · cases h
      · exact ⟨Y, by simp⟩
      · cases h
    · have e : vals (pp ++ q) ++ [Admin.ref (.exn a), .plain .throwRef] ++ (u ++ r) =
          vals (pp ++ q ++ [.ref (.exn a)]) ++ .plain .throwRef :: (u ++ r) := by
        simp [vals, Val.toAdmin]
      rw [e] at hrel
      rcases LG.vals_cons_inv rfl hrel with ⟨y, rest', rfl, hy, -⟩ | ⟨_, _, _, h, _⟩ |
          ⟨h, -⟩ | ⟨-, Y, rfl⟩
      · rw [AG.eq_of_plain (fun _ h => by cases h) rfl hy]
        exact ⟨rest', by simp [vals, Val.toAdmin]⟩
      · cases h
      · cases h
      · exact ⟨Y, by simp [vals, Val.toAdmin]⟩
  obtain ⟨Y, rfl⟩ := hns
  have hrel' : LG p E (vals pp ++ X ++ r) (vals pp ++ X) := by
    rcases hX with rfl | ⟨a, rfl⟩
    · simpa using LG.vals_append pp (LG.trapT (p := p) (E := E) (os := r) (ns := []))
    · have := LG.vals_append (pp ++ [.ref (.exn a)])
        (LG.throwT (p := p) (E := E) (os := r) (ns := []))
      simpa [vals, Val.toAdmin] using this
  by_cases hY : q = [] ∧ Y = []
  · obtain ⟨rfl, rfl⟩ := hY
    have hu : u ≠ [] := by simpa using hqu
    refine ⟨⟨t, ⟨fo.locals ++ E, p.mi⟩, vals (pp ++ []) ++ X ++ []⟩,
      ⟨hm, hl, E, he, rfl, by simpa using hrel'⟩, hSR, .inr ⟨rfl, ?_⟩⟩
    obtain ⟨x, u', rfl⟩ := List.exists_cons_of_ne_nil hu
    have := wA_pos x
    simp [wL_append]
    omega
  · refine ⟨⟨t, ⟨fo.locals ++ E, p.mi⟩, vals pp ++ X ++ []⟩,
      ⟨hm, hl, E, he, rfl, by simpa using hrel'⟩, hSR,
      .inl (.single (Det.Bubble.toStep ⟨pp, q, X, Y, [], by simp, hX, ?_, rfl⟩))⟩
    by_cases hq : q = []
    · exact .inr (fun h => hY ⟨hq, h⟩)
    · exact .inl hq

/-! ## Callee mode -/

theorem LI.length_eq {d : Nat} : ∀ {a b : List Admin}, LI p d a b → a.length = b.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ t => by simp [LI.length_eq t]

theorem sim_i_head (hok : PrmOk p) {k : Nat} (IH : SimIH p P H k) {d : Nat}
    {L : List (Option Val)} {s t : Store H} {F : Frame} (hm : F.module = p.mi)
    (hL : L.length = p.base) (he : F.locals.length = p.ext)
    {vs args : List Val} {e : Admin} {rest ns : List Admin} {c₀ : Config H}
    (hsz : sizeOf (vals vs ++ (vals args ++ e :: rest)) < k + 1)
    (hh : Det.Head P s F args e c₀) (hrel : LI p d (vals vs ++ (vals args ++ e :: rest)) ns)
    (hSR : SR p s t) :
    Res p P (.i d L) ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩
      ⟨t, ⟨L ++ F.locals, p.mi⟩, ns⟩ (wL (vals vs ++ (vals args ++ e :: rest))) := by
  rw [headDec_code] at hrel
  obtain ⟨y, rest', rfl, hy, hr⟩ := LI.vals_cons_inv hrel
  have hlt := sizeOf_head_lt (vs := vs) (args := args) (e := e) (rest := rest)
  have hIH : SimIH p P H (sizeOf e) := IH.mono (by omega)
  obtain ⟨⟨t', f', code'⟩, hprog, hsr, hm', he', hfr', hrel'⟩ := i_head hok hIH hm hL he hh hy hSR
  refine ⟨⟨t', f', vals vs ++ code' ++ rest'⟩,
    ⟨hm', hL, he', hfr', LI.append (LI.append (LI.of_vals d vs) hrel') hr⟩, hsr, ?_⟩
  rcases lift_res (vs := vs) (rest' := rest') (w := wL c₀.code) (w₀ := wL (vals args ++ [e]))
    hprog with h | ⟨h, hw⟩
  · exact .inl h
  · exact .inr ⟨h, wL_lift hw⟩

theorem sim_i_bubble {d : Nat} {L : List (Option Val)} {s t : Store H} {F : Frame}
    (hm : F.module = p.mi) (hL : L.length = p.base) (he : F.locals.length = p.ext)
    {pp q : List Val} {X u r ns : List Admin} (hX : Det.IsBubble X) (hqu : q ≠ [] ∨ u ≠ [])
    (hrel : LI p d (vals (pp ++ q) ++ X ++ (u ++ r)) ns) (hSR : SR p s t) :
    Res p P (.i d L) ⟨s, F, vals pp ++ X ++ r⟩ ⟨t, ⟨L ++ F.locals, p.mi⟩, ns⟩
      (wL (vals (pp ++ q) ++ X ++ (u ++ r))) := by
  obtain ⟨n₁, n₂, rfl, h₁, h₂⟩ := LI.append_inv hrel
  obtain ⟨n₃, n₄, rfl, h₃, h₄⟩ := LI.append_inv h₁
  obtain ⟨n₅, n₆, rfl, h₅, h₆⟩ := LI.append_inv h₂
  rw [LI.vals_inv h₃] at *
  have hX' : X = n₄ := by
    rcases hX with rfl | ⟨a, rfl⟩
    · cases h₄ with | cons h t => cases h; cases t; rfl
    · cases h₄ with | cons h t => cases h; cases t with | cons h' t' => cases h'; cases t'; rfl
  subst hX'
  have hlen : n₅.length = u.length := (LI.length_eq h₅).symm
  have hXX : LI p d X X := by
    rcases hX with rfl | ⟨a, rfl⟩
    · exact LI.of_out Out.trap
    · exact LI.of_out (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI]))
  refine ⟨⟨t, ⟨L ++ F.locals, p.mi⟩, vals pp ++ X ++ n₆⟩,
    ⟨hm, hL, he, rfl, LI.append (LI.append (LI.of_vals d pp) hXX) h₆⟩, hSR,
    .inl (.single (Det.Bubble.toStep ⟨pp, q, X, n₅, n₆, rfl, hX, ?_, rfl⟩))⟩
  rcases hqu with h | h
  · exact .inl h
  · right; intro h'; rw [h'] at hlen; exact h (List.eq_nil_of_length_eq_zero hlen.symm)

/-! ## Site mode -/

theorem sim_top {k : Nat} (IH : SimIH p P H k) {k' : Nat} {L : List (Option Val)}
    {s t : Store H} {F : Frame} {Y X : List Admin} {o' : Config H}
    (hm : F.module = p.mi) (hL : L.length = p.base) (he : F.locals.length = p.ext)
    (hsite : SiteR p k' Y X) (hsz : sizeOf Y < k + 1) (hstep : Step P Det.noHost ⟨s, F, Y⟩ o')
    (hSR : SR p s t) :
    Res p P (.top k' L) o' ⟨t, ⟨L ++ F.locals, p.mi⟩, [.label k' [] X]⟩ (wL Y) := by
  rcases Det.Step.decomp hstep with ⟨vs, args, e, rest, c₀, hcode, hh, rfl⟩ |
      ⟨pp, q, X', u, r, hcode, hX, hqu, rfl⟩
  · simp only at hcode
    rw [headDec_code] at hcode
    have hgood := hh.good
    have hv := hgood.val_none
    cases hsite with
    | @a _ bO _ hLI =>
      obtain ⟨h1, rfl, rfl⟩ := vals_append_cons_inj (vs := []) rfl hv hcode
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h1.symm
      have hlt : sizeOf [Admin.label k' [] bO] < k + 1 := hsz
      have := top_label (IH.mono (by omega)) hLI hm hL he hh hSR
      simpa using this
    | b vs₀ => exact absurd hcode (vals_ne_vals_cons hv)
    | @c _ vs₀ _ =>
      have := fnv_eq rfl hv hcode
      subst this
      exact absurd (.inr (.inl rfl)) hgood.not_blocked
    | d =>
      have := fnv_eq (vs := []) rfl hv hcode
      subst this
      exact absurd rfl hgood.ne_trap
    | e a =>
      obtain ⟨h1, rfl, -⟩ := vals_append_cons_inj (vs := [.ref (.exn a)]) rfl hv hcode
      have := hgood.throwRef rfl
      subst this
      have := congrArg List.getLast? h1
      simp at this
    | @f _ vs₀ _ _ _ _ _ => exact absurd hcode (vals_ne_vals_cons hv)
    | @g _ vs₀ l rest₀ _ =>
      rw [List.append_assoc] at hcode
      have := fnv_eq rfl hv hcode
      subst this
      exact absurd (.inl ⟨l, rfl⟩) hgood.not_blocked
  · simp only at hcode
    -- the bubble: a trap or an exception after values
    obtain ⟨W, x, hx, hW, hcode'⟩ : ∃ W x, x.val? = none ∧ (x = .trap ∨ x = .plain .throwRef) ∧
        Y = vals W ++ x :: (u ++ r) ∧ (x = .trap → W = pp ++ q) ∧
        (x = .plain .throwRef → ∃ b, W = pp ++ q ++ [.ref (.exn b)]) := by
      rcases hX with rfl | ⟨b, rfl⟩
      · exact ⟨pp ++ q, .trap, rfl, .inl rfl, by simpa using hcode, fun _ => rfl,
          fun h => by cases h⟩
      · exact ⟨pp ++ q ++ [.ref (.exn b)], .plain .throwRef, rfl, .inr rfl,
          by simp [hcode, vals, Val.toAdmin], fun h => (by cases h), fun _ => ⟨b, rfl⟩⟩
    obtain ⟨hcode'', hWt, hWr⟩ := hcode'
    have hqu' : W ≠ pp ++ q ∨ q ≠ [] ∨ u ≠ [] := .inr hqu
    have hxne : ∀ y : Admin, y ≠ .trap → y ≠ .plain .throwRef → y ≠ x := fun y h1 h2 h =>
      by rcases hW with rfl | rfl <;> simp_all
    cases hsite with
    | @a _ bO _ _ =>
      exact absurd (fnv_eq (vs := []) rfl hx hcode'') (hxne _ (by simp) (by simp))
    | b vs₀ => exact absurd hcode'' (vals_ne_vals_cons hx)
    | @c _ vs₀ _ => exact absurd (fnv_eq rfl hx hcode'') (hxne _ (by simp) (by simp))
    | d =>
      obtain ⟨h1, h2, h3⟩ := vals_append_cons_inj (vs := []) rfl hx hcode''
      subst h2
      have hW' := hWt rfl
      subst hW'
      have hq : q = [] := by simpa using (List.append_eq_nil_iff.mp h1.symm).2
      have hu : u = [] := (List.append_eq_nil_iff.mp h3.symm).1
      rcases hqu with h | h <;> contradiction
    | e a =>
      obtain ⟨h1, h2, h3⟩ := vals_append_cons_inj (vs := [.ref (.exn a)]) rfl hx hcode''
      subst h2
      obtain ⟨b, hb⟩ := hWr rfl
      subst hb
      have hq : q = [] := by
        have := congrArg List.length h1
        simp at this
        exact List.eq_nil_of_length_eq_zero (by omega)
      have hu : u = [] := (List.append_eq_nil_iff.mp h3.symm).1
      rcases hqu with h | h <;> contradiction
    | @f _ vs₀ _ _ _ _ _ => exact absurd hcode'' (vals_ne_vals_cons hx)
    | @g _ vs₀ l rest₀ _ =>
      rw [List.append_assoc] at hcode''
      exact absurd (fnv_eq rfl hx hcode'') (hxne _ (by simp) (by simp))

/-! ## The simulation -/

/-- **One step.** Every host-free step of the left configuration is simulated. -/
theorem sim (hok : PrmOk p) (hfx : p.mi.funcs[p.fx.toNat]? = some p.af) (hC : PrmC p) :
    ∀ k : Nat, SimIH p P H k
  | 0 => fun _ _ _ _ hsz => absurd hsz (Nat.not_lt_zero _)
  | k + 1 => fun μ o o' n hsz hstep hMR hSR => by
    have IH := sim hok hfx hC k
    obtain ⟨s, f, code⟩ := o
    obtain ⟨t, fn, ns⟩ := n
    cases μ with
    | gen =>
      obtain ⟨hfr, hrel⟩ := hMR
      simp only at hfr hrel hSR
      subst hfr
      rcases Det.Step.decomp hstep with ⟨vs, args, e, rest, c₀, hcode, hh, rfl⟩ |
          ⟨pp, q, X, u, r, hcode, hX, hqu, rfl⟩
      · simp only at hcode
        subst hcode
        exact sim_gen_head hok IH hsz hh hrel hSR
      · simp only at hcode
        subst hcode
        exact sim_gen_bubble hX hqu hrel hSR
    | g =>
      obtain ⟨hm, hl, E, he, hfr, hrel⟩ := hMR
      simp only at hm hl hfr hrel hSR
      subst hfr
      rcases Det.Step.decomp hstep with ⟨vs, args, e, rest, c₀, hcode, hh, rfl⟩ |
          ⟨pp, q, X, u, r, hcode, hX, hqu, rfl⟩
      · simp only at hcode
        subst hcode
        exact sim_g_head hok hfx hC IH hm hl he hsz hh hrel hSR
      · simp only at hcode
        subst hcode
        exact sim_g_bubble hm hl he hX hqu hrel hSR
    | i d L =>
      obtain ⟨hm, hL, he, hfr, hrel⟩ := hMR
      simp only at hm he hfr hrel hSR
      subst hfr
      rcases Det.Step.decomp hstep with ⟨vs, args, e, rest, c₀, hcode, hh, rfl⟩ |
          ⟨pp, q, X, u, r, hcode, hX, hqu, rfl⟩
      · simp only at hcode
        subst hcode
        exact sim_i_head hok IH hm hL he hsz hh hrel hSR
      · simp only at hcode
        subst hcode
        exact sim_i_bubble hm hL he hX hqu hrel hSR
    | top k' L =>
      obtain ⟨hm, hL, he, hfr, X, hn, hsite⟩ := hMR
      simp only at hm he hfr hn hsite hSR
      subst hfr hn
      exact sim_top IH hm hL he hsite hsz hstep hSR

end Silmaril.Wasm.Binaryen.InlR
