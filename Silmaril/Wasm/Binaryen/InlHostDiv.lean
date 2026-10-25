module

public import Silmaril.Wasm.Binaryen.InlMain

@[expose] public section

/-! # The inlining simulation: diverging host calls

A host call of the left side that diverges is matched by the same diverging host call of
the right side: the callout context carries over through the relation
(`callout_transport`), the callee is a host function, hence not the caller (whose code
alone differs), and a code-respecting host diverges in the right store as well.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.SingleThreaded

variable {H : Type} {p : Prm} {P : Numerics.Profile}

/-- The code part of the relation. -/
def CR (p : Prm) : Mode → List Admin → List Admin → Prop
  | .gen, os, ns => LN p os ns
  | .g, os, ns => ∃ E, LG p E os ns
  | .i d _, os, ns => LI p d os ns
  | .top k _, os, ns => ∃ X, ns = [.label k [] X] ∧ SiteR p k os X

theorem MR.cr {μ : Mode} {o n : Config H} (h : MR p μ o n) : CR p μ o.code n.code := by
  cases μ with
  | gen => exact h.2
  | g => obtain ⟨-, -, E, -, -, h⟩ := h; exact ⟨E, h⟩
  | i d L => exact h.2.2.2.2
  | top k L => exact h.2.2.2.2

theorem callRef_flat {yy : Admin} (h : yy.IsCallRef) :
    (∀ n c b, yy ≠ .label n c b) ∧ (∀ n cs b, yy ≠ .handler n cs b) ∧ (∀ n F b, yy ≠ .frame n F b) ∧
      yy.val? = none ∧ yy ≠ .trap ∧ yy ≠ .plain .throwRef := by
  unfold Admin.IsCallRef at h
  split at h
  · exact ⟨by simp, by simp, by simp, rfl, by simp, by simp⟩
  · exact ⟨by simp, by simp, by simp, rfl, by simp, by simp⟩
  · exact h.elim

theorem AG.eq_of_callRef {E : List (Option Val)} {yy y : Admin} (hyy : yy.IsCallRef)
    (h : AG p E yy y) : y = yy := by
  rcases yy with i | r | d | d | _ | _ | _ | _ <;> simp [Admin.IsCallRef] at hyy
  · cases i <;> simp at hyy
    cases h with | plain h => cases h; rfl
  · cases h; rfl

theorem AI.eq_of_callRef {d : Nat} {yy y : Admin} (hyy : yy.IsCallRef) (h : AI p d yy y) :
    y = yy := by
  rcases yy with i | r | dt | dt | _ | _ | _ | _ <;> simp [Admin.IsCallRef] at hyy
  · cases i <;> simp at hyy
    cases h; rfl
  · cases h; rfl

theorem not_callRef_of {yy x : Admin} (hyy : yy.IsCallRef) (hx : ¬ x.IsCallRef) : x ≠ yy := by
  rintro rfl; exact hx hyy

/-- **Callouts carry over.** -/
theorem callout_transport {args : List Val} {a : Nat} {yy : Admin} (hyy : yy.IsCallRef)
    (ha : a ≠ p.af) : ∀ (E : Ctx) (μ : Mode) {ns : List Admin},
    CR p μ (E.fill (vals args ++ [.ref (.func a), yy])) ns →
    ∃ (E' : Ctx) (yy' : Admin), yy'.IsCallRef ∧ ns = E'.fill (vals args ++ [.ref (.func a), yy'])
  | .top pre rest, μ, ns, h => by
    obtain ⟨hL, hH, hF, hv, hT, hR⟩ := callRef_flat hyy
    have e : (Ctx.top pre rest).fill (vals args ++ [.ref (.func a), yy]) =
        vals (pre ++ args ++ [.ref (.func a)]) ++ yy :: rest := by
      simp [Ctx.fill, vals, Val.toAdmin]
    rw [e] at h
    have hfin : ∀ rest', ∃ (E' : Ctx) (yy' : Admin), yy'.IsCallRef ∧
        vals (pre ++ args ++ [.ref (.func a)]) ++ yy :: rest' =
          E'.fill (vals args ++ [.ref (.func a), yy']) :=
      fun rest' => ⟨.top pre rest', yy, hyy, by simp [Ctx.fill, vals, Val.toAdmin]⟩
    cases μ with
    | gen =>
      obtain ⟨y, rest', rfl, hy, -⟩ := LN.vals_cons_inv (p := p) h
      rw [AN.eq_of_flat hy hL hH hF]
      exact hfin rest'
    | g =>
      obtain ⟨E₀, h⟩ := h
      rcases LG.vals_cons_inv hv h with ⟨y, rest', rfl, hy, -⟩ | ⟨vs₀, rest', hvs, -, -, -⟩ |
          ⟨h', -⟩ | ⟨h', -⟩
      · rw [AG.eq_of_callRef hyy hy]
        exact hfin rest'
      · have := congrArg List.getLast? hvs
        simp at this
        exact absurd this ha
      · exact absurd h' hT
      · exact absurd h' hR
    | i d L =>
      obtain ⟨y, rest', rfl, hy, -⟩ := LI.vals_cons_inv (p := p) h
      rw [AI.eq_of_callRef hyy hy]
      exact hfin rest'
    | top k L =>
      obtain ⟨X, -, hs⟩ := h
      generalize hY : vals (pre ++ args ++ [.ref (.func a)]) ++ yy :: rest = Y at hs
      cases hs with
      | a _ => exact absurd (fnv_eq (ws := []) hv rfl hY) (hL _ _ _)
      | b _ => exact absurd hY (vals_ne_vals_cons hv).symm
      | c => exact absurd (fnv_eq hv rfl hY).symm (not_callRef_of hyy (by simp [Admin.IsCallRef]))
      | d => exact absurd (fnv_eq (ws := []) hv rfl hY) hT
      | e b => exact absurd (fnv_eq (ws := [.ref (.exn b)]) hv rfl hY) hR
      | f _ _ => exact absurd hY (vals_ne_vals_cons hv).symm
      | @g _ vs₀ l rest₀ _ =>
        have hY' : vals (pre ++ args ++ [.ref (.func a)]) ++ yy :: rest =
            vals vs₀ ++ .plain (.br l) :: rest₀ := by rw [hY]; simp
        exact absurd (fnv_eq hv rfl hY').symm (not_callRef_of hyy (by simp [Admin.IsCallRef]))
  | .label pre n cont E₁ rest, μ, ns, h => by
    simp only [Ctx.fill] at h
    have e : vals pre ++ [Admin.label n cont (E₁.fill (vals args ++ [.ref (.func a), yy]))] ++ rest =
        vals pre ++ .label n cont (E₁.fill (vals args ++ [.ref (.func a), yy])) :: rest := by simp
    rw [e] at h
    cases μ with
    | gen =>
      obtain ⟨y, rest', rfl, hy, -⟩ := LN.vals_cons_inv (p := p) h
      cases hy with
      | label hb =>
        obtain ⟨E₁', yy', hyy', hb'⟩ := callout_transport hyy ha E₁ .gen hb
        exact ⟨.label pre n cont E₁' rest', yy', hyy', by rw [hb']; simp [Ctx.fill]⟩
    | g =>
      obtain ⟨E₀, h⟩ := h
      rcases LG.vals_cons_inv rfl h with ⟨y, rest', rfl, hy, -⟩ | ⟨_, _, _, h', _⟩ | ⟨h', -⟩ |
          ⟨h', -⟩
      · cases hy with
        | @label _ _ _ c' _ b' hc hb =>
          obtain ⟨E₁', yy', hyy', hb'⟩ := callout_transport hyy ha E₁ .g ⟨E₀, hb⟩
          exact ⟨.label pre n c' E₁' rest', yy', hyy', by rw [hb']; simp [Ctx.fill]⟩
      · cases h'
      · cases h'
      · cases h'
    | i d L =>
      obtain ⟨y, rest', rfl, hy, -⟩ := LI.vals_cons_inv (p := p) h
      cases hy with
      | label hc hb =>
        obtain ⟨E₁', yy', hyy', hb'⟩ := callout_transport hyy ha E₁ (.i (d + 1) L) hb
        exact ⟨.label pre n (InlineTy.xformL p.base d cont) E₁' rest', yy', hyy',
          by rw [hb']; simp [Ctx.fill]⟩
    | top k L =>
      obtain ⟨X, rfl, hs⟩ := h
      generalize hY : vals pre ++ Admin.label n cont (E₁.fill (vals args ++ [.ref (.func a), yy]))
        :: rest = Y at hs
      cases hs with
      | @a _ bO _ hLI =>
        have hY' : vals pre ++ Admin.label n cont (E₁.fill (vals args ++ [.ref (.func a), yy]))
            :: rest = vals [] ++ Admin.label k [] bO :: [] := hY
        obtain ⟨-, h2, -⟩ := vals_append_cons_inj rfl rfl hY'
        cases h2
        obtain ⟨E₁', yy', hyy', hb'⟩ := callout_transport hyy ha E₁ (.i 0 L) hLI
        exact ⟨.label [] n [] E₁' [], yy', hyy', by rw [hb']; simp [Ctx.fill]⟩
      | b _ => exact absurd hY (vals_ne_vals_cons rfl).symm
      | c => exact absurd (fnv_eq rfl rfl hY) (by simp)
      | d => exact absurd (fnv_eq (ws := []) rfl rfl hY) (by simp)
      | e b => exact absurd (fnv_eq (ws := [.ref (.exn b)]) rfl rfl hY) (by simp)
      | f _ _ => exact absurd hY (vals_ne_vals_cons rfl).symm
      | g =>
        rw [List.append_assoc] at hY
        exact absurd (fnv_eq rfl rfl hY) (by simp)
  | .handler pre n cs E₁ rest, μ, ns, h => by
    simp only [Ctx.fill] at h
    have e : vals pre ++ [Admin.handler n cs (E₁.fill (vals args ++ [.ref (.func a), yy]))] ++
        rest = vals pre ++ .handler n cs (E₁.fill (vals args ++ [.ref (.func a), yy])) :: rest := by
      simp
    rw [e] at h
    cases μ with
    | gen =>
      obtain ⟨y, rest', rfl, hy, -⟩ := LN.vals_cons_inv (p := p) h
      cases hy with
      | handler hb =>
        obtain ⟨E₁', yy', hyy', hb'⟩ := callout_transport hyy ha E₁ .gen hb
        exact ⟨.handler pre n cs E₁' rest', yy', hyy', by rw [hb']; simp [Ctx.fill]⟩
    | g =>
      obtain ⟨E₀, h⟩ := h
      rcases LG.vals_cons_inv rfl h with ⟨y, rest', rfl, hy, -⟩ | ⟨_, _, _, h', _⟩ | ⟨h', -⟩ |
          ⟨h', -⟩
      · cases hy with
        | handler hb =>
          obtain ⟨E₁', yy', hyy', hb'⟩ := callout_transport hyy ha E₁ .g ⟨E₀, hb⟩
          exact ⟨.handler pre n cs E₁' rest', yy', hyy', by rw [hb']; simp [Ctx.fill]⟩
      · cases h'
      · cases h'
      · cases h'
    | i d L =>
      obtain ⟨y, rest', rfl, hy, -⟩ := LI.vals_cons_inv (p := p) h
      cases hy with
      | handler hb =>
        obtain ⟨E₁', yy', hyy', hb'⟩ := callout_transport hyy ha E₁ (.i d L) hb
        exact ⟨.handler pre n cs E₁' rest', yy', hyy', by rw [hb']; simp [Ctx.fill]⟩
    | top k L =>
      obtain ⟨X, rfl, hs⟩ := h
      generalize hY : vals pre ++ Admin.handler n cs (E₁.fill (vals args ++ [.ref (.func a), yy]))
        :: rest = Y at hs
      cases hs with
      | a _ => exact absurd (fnv_eq (ws := []) rfl rfl hY) (by simp)
      | b _ => exact absurd hY (vals_ne_vals_cons rfl).symm
      | c => exact absurd (fnv_eq rfl rfl hY) (by simp)
      | d => exact absurd (fnv_eq (ws := []) rfl rfl hY) (by simp)
      | e b => exact absurd (fnv_eq (ws := [.ref (.exn b)]) rfl rfl hY) (by simp)
      | f _ _ => exact absurd hY (vals_ne_vals_cons rfl).symm
      | g =>
        rw [List.append_assoc] at hY
        exact absurd (fnv_eq rfl rfl hY) (by simp)
  | .frame pre n f E₁ rest, μ, ns, h => by
    simp only [Ctx.fill] at h
    have e : vals pre ++ [Admin.frame n f (E₁.fill (vals args ++ [.ref (.func a), yy]))] ++ rest =
        vals pre ++ .frame n f (E₁.fill (vals args ++ [.ref (.func a), yy])) :: rest := by simp
    rw [e] at h
    have hfr : ∀ {F' : Frame} {b' : List Admin},
        FR p f F' (E₁.fill (vals args ++ [.ref (.func a), yy])) b' →
        ∃ (E' : Ctx) (yy' : Admin), yy'.IsCallRef ∧
          b' = E'.fill (vals args ++ [.ref (.func a), yy']) := fun hfr => by
      cases hfr with
      | gen hb => exact callout_transport hyy ha E₁ .gen hb
      | g _ _ _ hb => exact callout_transport hyy ha E₁ .g ⟨_, hb⟩
    cases μ with
    | gen =>
      obtain ⟨y, rest', rfl, hy, -⟩ := LN.vals_cons_inv (p := p) h
      cases hy with
      | frame hb =>
        rename_i F' b'
        obtain ⟨E₁', yy', hyy', hb'⟩ := hfr hb
        exact ⟨.frame pre n F' E₁' rest', yy', hyy', by rw [hb']; simp [Ctx.fill]⟩
    | g =>
      obtain ⟨E₀, h⟩ := h
      rcases LG.vals_cons_inv rfl h with ⟨y, rest', rfl, hy, -⟩ | ⟨_, _, _, h', _⟩ | ⟨h', -⟩ |
          ⟨h', -⟩
      · cases hy with
        | frame hb =>
          rename_i F' b'
          obtain ⟨E₁', yy', hyy', hb'⟩ := hfr hb
          exact ⟨.frame pre n F' E₁' rest', yy', hyy', by rw [hb']; simp [Ctx.fill]⟩
        | @site _ _ _ _ X _ _ hs =>
          obtain ⟨E₁', yy', hyy', hb'⟩ := callout_transport hyy ha E₁ (.top n []) ⟨X, rfl, hs⟩
          refine ⟨E₁'.wrap pre rest', yy', hyy', ?_⟩
          rw [Ctx.fill_wrap, ← hb']
          simp
      · cases h'
      · cases h'
      · cases h'
    | i d L =>
      obtain ⟨y, rest', rfl, hy, -⟩ := LI.vals_cons_inv (p := p) h
      cases hy with
      | frame hb =>
        rename_i F' b'
        obtain ⟨E₁', yy', hyy', hb'⟩ := hfr hb
        exact ⟨.frame pre n F' E₁' rest', yy', hyy', by rw [hb']; simp [Ctx.fill]⟩
    | top k L =>
      obtain ⟨X, rfl, hs⟩ := h
      generalize hY : vals pre ++ Admin.frame n f (E₁.fill (vals args ++ [.ref (.func a), yy]))
        :: rest = Y at hs
      cases hs with
      | a _ => exact absurd (fnv_eq (ws := []) rfl rfl hY) (by simp)
      | b _ => exact absurd hY (vals_ne_vals_cons rfl).symm
      | c => exact absurd (fnv_eq rfl rfl hY) (by simp)
      | d => exact absurd (fnv_eq (ws := []) rfl rfl hY) (by simp)
      | e b => exact absurd (fnv_eq (ws := [.ref (.exn b)]) rfl rfl hY) (by simp)
      | f _ _ => exact absurd hY (vals_ne_vals_cons rfl).symm
      | g =>
        rw [List.append_assoc] at hY
        exact absurd (fnv_eq rfl rfl hY) (by simp)

/-- **A diverging host call of the left side is a diverging host call of the right side.** -/
theorem hostdiv_step {host : HostSemantics H} (hR : HostRespectsCode host) {s t : Store H}
    (hSR : SR p s t) {μ : Mode} {code ns : List Admin} (hcr : CR p μ code ns) {E : Ctx}
    {a : Nat} {hh : H} {args : List Val} (hd : decompose? s code = some (E, a, hh, args))
    (hdiv : host hh s args .diverged) (fn : Frame) :
    Step P host ⟨t, fn, ns⟩ ⟨t, fn, ns⟩ := by
  obtain ⟨fi, yy, ps, rs, hfi, hcode, hyy, he, hlen, rfl⟩ := decompose?_sound hd
  have haf : a ≠ p.af := by
    rintro rfl; rw [hSR.hf] at hfi; cases hfi; simp [fO] at hcode
  have hag : a ≠ p.ag := by
    rintro rfl; rw [hSR.hg] at hfi; cases hfi; simp [gO] at hcode
  have hfi' : t.funcs[a]? = some fi := by
    rw [hSR.get a]; simp only [hag, ↓reduceIte]; exact hfi
  obtain ⟨E', yy', hyy', rfl⟩ := callout_transport hyy haf E μ hcr
  have hdiv' : host hh t args .diverged := by
    refine hR hh s t args _ ⟨?_, ?_⟩ hdiv
    · rw [hSR.ht]; exact hSR.sameTypes.symm
    · rw [hSR.ht]; rfl
  exact Ctx.step_fill E' (fun g => .callRefHostDiv hyy' hfi' he hlen hcode hdiv') fn

end Silmaril.Wasm.Binaryen.InlR
