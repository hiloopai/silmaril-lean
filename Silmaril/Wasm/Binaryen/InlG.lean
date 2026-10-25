module

public import Silmaril.Wasm.Binaryen.InlGen

@[expose] public section

/-! # The inlining simulation, caller mode

Head steps of an activation of the caller. The right frame has the added locals `E`
after the left frame's locals; caller code is related by `IR`. The site `call f` of the
left side fetches the callee (`g_site_call`, the right side waits: `LG.seg`); the left
callee activation started there is simulated by the right inlined block (`g_site`).
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.SingleThreaded

variable {H : Type} {p : Prm} {P : Numerics.Profile}

/-- The result of a caller head step: the right side steps (or waits while the left
weight decreases); the frames keep the caller shape with new added locals `E'`. -/
def GRes (p : Prm) (P : Numerics.Profile) (t : Store H) (fn : Frame) (args : List Val)
    (e e' : Admin) (c₀ : Config H) : Prop :=
  ∃ (c₀' : Config H) (E' : List (Option Val)),
    (Relation.TransGen (Step P Det.noHost) ⟨t, fn, vals args ++ [e']⟩ c₀' ∨
      (c₀' = ⟨t, fn, vals args ++ [e']⟩ ∧ wL c₀.code < wL (vals args ++ [e]))) ∧
    SR p c₀.store c₀'.store ∧ E'.length = p.ext ∧ c₀.frame.module = p.mi ∧
    c₀.frame.locals.length = p.base ∧ c₀'.frame = ⟨c₀.frame.locals ++ E', p.mi⟩ ∧
    LG p E' c₀.code c₀'.code

theorem vals_ne_vals_cons {vs ws : List Val} {x : Admin} {r : List Admin} (hx : x.val? = none) :
    vals vs ≠ vals ws ++ x :: r := fun h => by
  have := congrArg splitVals h
  rw [splitVals_vals, splitVals_vals_cons hx] at this
  simp at this

section frames

variable {fo : Frame} {E : List (Option Val)}

/-- The caller frame shape is kept by a step that keeps the frame. -/
theorem gres_same {t : Store H} {args : List Val} {e e' : Admin} {s s₀ : Store H}
    {code₀ code₀' : List Admin} (hm : fo.module = p.mi) (hl : fo.locals.length = p.base)
    (he : E.length = p.ext) (hSR : SR p s t) (hs : s₀.funcs = s.funcs)
    (hstep : Relation.TransGen (Step P Det.noHost) ⟨t, ⟨fo.locals ++ E, p.mi⟩, vals args ++ [e']⟩
      ⟨withFuncs s₀ (newFuncs p s.funcs), ⟨fo.locals ++ E, p.mi⟩, code₀'⟩)
    (hrel : LG p E code₀ code₀') :
    GRes p P t ⟨fo.locals ++ E, p.mi⟩ args e e' ⟨s₀, fo, code₀⟩ :=
  ⟨_, E, .inl hstep, hSR.mono hs, he, hm, hl, rfl, hrel⟩

end frames

/-! ## Structured instructions -/

theorem LG.label_body {E : List (Option Val)} {n : Nat} {c c' : List Instr} {args : List Val}
    {b b' : List Instr} (hc : IRL p c c') (hb : IRL p b b') :
    LG p E [.label n c (vals args ++ expression b)] [.label n c' (vals args ++ expression b')] :=
  .head (.label hc (LG.vals_append args (.plain (LGq.of_IRL hb)))) .nil

theorem g_block {bt : BlockType} {b b' : List Instr} (hb : IRL p b b') {s t : Store H}
    {fo : Frame} {E : List (Option Val)} (hm : fo.module = p.mi)
    (hl : fo.locals.length = p.base) (he : E.length = p.ext) {args : List Val} {c₀ : Config H}
    (hh : Det.Head P s fo args (.plain (.block bt b)) c₀) (hSR : SR p s t) :
    GRes p P t ⟨fo.locals ++ E, p.mi⟩ args (.plain (.block bt b)) (.plain (.block bt b')) c₀ := by
  obtain ⟨hg, hf, rfl⟩ := hSR
  cases hh with
  | block hbt hm' =>
    refine gres_same hm hl he ⟨hg, hf, rfl⟩ rfl (tg_head (.block (by rw [← hm]; exact hbt) hm'))
      (LG.label_body .nil hb)
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])

theorem g_loop {bt : BlockType} {b b' : List Instr} (hb : IRL p b b') {s t : Store H}
    {fo : Frame} {E : List (Option Val)} (hm : fo.module = p.mi)
    (hl : fo.locals.length = p.base) (he : E.length = p.ext) {args : List Val} {c₀ : Config H}
    (hh : Det.Head P s fo args (.plain (.loop bt b)) c₀) (hSR : SR p s t) :
    GRes p P t ⟨fo.locals ++ E, p.mi⟩ args (.plain (.loop bt b)) (.plain (.loop bt b')) c₀ := by
  obtain ⟨hg, hf, rfl⟩ := hSR
  cases hh with
  | loop hbt hm' =>
    refine gres_same hm hl he ⟨hg, hf, rfl⟩ rfl (tg_head (.loop (by rw [← hm]; exact hbt) hm'))
      (LG.label_body (.cons (.loop hb) .nil) hb)
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])

theorem g_if {bt : BlockType} {b₁ b₁' b₂ b₂' : List Instr} (h₁ : IRL p b₁ b₁')
    (h₂ : IRL p b₂ b₂') {s t : Store H} {fo : Frame} {E : List (Option Val)}
    (hm : fo.module = p.mi) (hl : fo.locals.length = p.base) (he : E.length = p.ext)
    {args : List Val} {c₀ : Config H} (hh : Det.Head P s fo args (.plain (.if_ bt b₁ b₂)) c₀)
    (hSR : SR p s t) :
    GRes p P t ⟨fo.locals ++ E, p.mi⟩ args (.plain (.if_ bt b₁ b₂)) (.plain (.if_ bt b₁' b₂'))
      c₀ := by
  obtain ⟨hg, hf, rfl⟩ := hSR
  cases hh with
  | ifTrue hc =>
    exact gres_same hm hl he ⟨hg, hf, rfl⟩ rfl (tg_head (.ifTrue hc))
      (.plain (.cons (.block h₁) .nil))
  | ifFalse hc =>
    exact gres_same hm hl he ⟨hg, hf, rfl⟩ rfl (tg_head (.ifFalse hc))
      (.plain (.cons (.block h₂) .nil))
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])

theorem g_try {bt : BlockType} {cs : List Catch} {b b' : List Instr} (hb : IRL p b b')
    {s t : Store H} {fo : Frame} {E : List (Option Val)} (hm : fo.module = p.mi)
    (hl : fo.locals.length = p.base) (he : E.length = p.ext) {args : List Val} {c₀ : Config H}
    (hh : Det.Head P s fo args (.plain (.tryTable bt cs b)) c₀) (hSR : SR p s t) :
    GRes p P t ⟨fo.locals ++ E, p.mi⟩ args (.plain (.tryTable bt cs b))
      (.plain (.tryTable bt cs b')) c₀ := by
  obtain ⟨hg, hf, rfl⟩ := hSR
  cases hh with
  | tryTable hbt hm' =>
    refine gres_same hm hl he ⟨hg, hf, rfl⟩ rfl
      (tg_head (.tryTable (by rw [← hm]; exact hbt) hm'))
      (.head (.handler (LG.label_body .nil hb)) .nil)
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])

/-! ## Local accesses -/

theorem g_local {i : Instr} (hi : IsLocalI i = true) {s t : Store H} {fo : Frame}
    {E : List (Option Val)} (hm : fo.module = p.mi) (hl : fo.locals.length = p.base)
    (he : E.length = p.ext) {args : List Val} {c₀ : Config H}
    (hh : Det.Head P s fo args (.plain i) c₀) (hSR : SR p s t) :
    GRes p P t ⟨fo.locals ++ E, p.mi⟩ args (.plain i) (.plain i) c₀ := by
  obtain ⟨hg, hf, rfl⟩ := hSR
  obtain ⟨s₀, f₀, is₀⟩ := c₀
  have hfam : Det.famOf (.plain i) = .variable := by
    cases i <;> simp [IsLocalI] at hi <;> rfl
  cases hh with
  | «variable» h =>
    generalize hc : vals args ++ [Admin.plain i] = code at h
    cases h with
    | @localGet _ _ x v hx =>
      obtain ⟨rfl, rfl⟩ : args = [] ∧ i = .localGet x := by
        rcases args with _ | ⟨a, args⟩
        · simp at hc; exact ⟨rfl, hc⟩
        · simp [vals] at hc
      have hlt : x.toNat < fo.locals.length := (List.getElem?_eq_some_iff.mp hx).1
      have hx' : (Frame.mk (fo.locals ++ E) p.mi).local? x = some (some v) := by
        simp only [Frame.local?]
        rw [List.getElem?_append_left hlt]
        exact hx
      exact gres_same hm hl he ⟨hg, hf, rfl⟩ rfl (tg_head (.variable (.localGet hx')))
        (LG.of_out (Out.vals [v]))
    | @localSet _ _ x v hx =>
      obtain ⟨rfl, rfl⟩ : args = [v] ∧ i = .localSet x := by
        rcases args with _ | ⟨a, _ | ⟨b, args⟩⟩
        · simp at hc
        · simp [vals] at hc; obtain ⟨rfl, rfl⟩ := hc
          exact ⟨by rcases a with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp_all, rfl⟩
        · simp [vals] at hc
      have hx' : x.toNat < (fo.locals ++ E).length := by simp; omega
      refine ⟨_, E, .inl (tg_head (.variable (.localSet (f := ⟨fo.locals ++ E, p.mi⟩) hx'))),
        SR.mono ⟨hg, hf, rfl⟩ rfl, he, ?_, ?_, ?_, LG.of_out (Out.vals [])⟩
      · simp [Frame.setLocal, hm]
      · simp [Frame.setLocal, hl]
      · simp only [Frame.setLocal]
        rw [List.set_append_left _ _ hx]
    | @localTee _ _ x v =>
      obtain ⟨rfl, rfl⟩ : args = [v] ∧ i = .localTee x := by
        rcases args with _ | ⟨a, _ | ⟨b, args⟩⟩
        · simp at hc
        · simp [vals] at hc; obtain ⟨rfl, rfl⟩ := hc
          exact ⟨by rcases a with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp_all, rfl⟩
        · simp [vals] at hc
      exact gres_same hm hl he ⟨hg, hf, rfl⟩ rfl (tg_head (.variable .localTee))
        (.val (by simp) (.val (by simp) (.plain (.cons (.flat _) .nil))))
    | globalGet _ =>
      have h' := last_eq_of_append_singleton (l' := []) hc
      cases h'
      simp [IsLocalI] at hi
    | globalSet _ =>
      have h' := last_eq_of_append_singleton (l' := [_]) hc
      cases h'
      simp [IsLocalI] at hi
  | parametric h =>
    exact absurd ((Det.famOf_of_shape (Det.ParametricStep.shape h)).2.symm.trans hfam) (by decide)
  | numeric h =>
    exact absurd ((Det.famOf_of_shape (Det.NumericStep.shape h)).2.symm.trans hfam) (by decide)
  | vector h =>
    exact absurd ((Det.famOf_of_shape (Det.VectorStep.shape h)).2.symm.trans hfam) (by decide)
  | table h =>
    exact absurd ((Det.famOf_of_shape (Det.TableStep.shape h)).2.symm.trans hfam) (by decide)
  | memory h =>
    exact absurd ((Det.famOf_of_shape (Det.MemoryStep.shape h)).2.symm.trans hfam) (by decide)
  | reference h =>
    exact absurd ((Det.famOf_of_shape (Det.RefStep.shape h)).2.symm.trans hfam) (by decide)
  | aggregate h =>
    exact absurd ((Det.famOf_of_shape (Det.AggregateStep.shape h)).2.symm.trans hfam) (by decide)
  | callRefNull hc => cases i <;> simp [IsLocalI] at hi <;> simp [Admin.IsCallRef] at hc
  | callRefFunc _ hc => cases i <;> simp [IsLocalI] at hi <;> simp [Admin.IsCallRef] at hc
  | _ => simp [IsLocalI] at hi

/-! ## Simple heads and calls -/

theorem g_callData (hok : PrmOk p) {s t : Store H} {fo : Frame} {E : List (Option Val)}
    (hm : fo.module = p.mi) (hl : fo.locals.length = p.base) (he : E.length = p.ext)
    {args : List Val} {e : Admin} {c₀ : Config H} (hSR : SR p s t)
    (hcd : CallData s fo args e c₀) : GRes p P t ⟨fo.locals ++ E, p.mi⟩ args e e c₀ := by
  obtain ⟨vs, a, fi, ps, rs, code, rfl, hc, hf, he', hn, hcode, rfl⟩ := hcd
  obtain ⟨fi', code', hf', ht, hcode', hfr⟩ := call_rel hok hSR hf he' hn hcode
  exact ⟨_, E, .inl (tg_head (.callRefFunc rfl hc hf' (ht ▸ he') hn hcode')), hSR, he, hm, hl,
    rfl, .head (.frame hfr) .nil⟩

theorem g_simple (hok : PrmOk p) {e : Admin} (hS : SimpleE e) (hNS : ¬ StructE e)
    {s t : Store H} {fo : Frame} {E : List (Option Val)} (hm : fo.module = p.mi)
    (hl : fo.locals.length = p.base) (he : E.length = p.ext) {args : List Val} {c₀ : Config H}
    (hh : Det.Head P s fo args e c₀) (hSR : SR p s t) :
    GRes p P t ⟨fo.locals ++ E, p.mi⟩ args e e c₀ := by
  rcases head_simple hh hS hSR.sameTypes (fo.locals ++ E) with hcd | ⟨hfr, hfs, hN⟩
  · exact g_callData hok hm hl he hSR hcd
  · rcases head_out hh hS hNS with hcd | hout | ⟨-, hout⟩
    · exact g_callData hok hm hl he hSR hcd
    · obtain ⟨hg, hf, rfl⟩ := hSR
      obtain ⟨s₀, f₀, is₀⟩ := c₀
      simp only at hfr hfs hN
      subst hfr
      rw [hm] at hN
      exact gres_same hm hl he ⟨hg, hf, rfl⟩ hfs (tg_head hN) (LG.of_out hout)
    · obtain ⟨hg, hf, rfl⟩ := hSR
      obtain ⟨s₀, f₀, is₀⟩ := c₀
      simp only at hfr hfs hN
      subst hfr
      rw [hm] at hN
      exact gres_same hm hl he ⟨hg, hf, rfl⟩ hfs (tg_head hN) (LG.of_outT hout)

theorem g_site_call (hfx : p.mi.funcs[p.fx.toNat]? = some p.af) {s t : Store H} {fo : Frame}
    {E : List (Option Val)} (hm : fo.module = p.mi) (hl : fo.locals.length = p.base)
    (he : E.length = p.ext) {args : List Val} {c₀ : Config H}
    (hh : Det.Head P s fo args (.plain (.call p.fx)) c₀) (hSR : SR p s t) :
    GRes p P t ⟨fo.locals ++ E, p.mi⟩ args (.plain (.call p.fx))
      (.plain (.block (.typeIdx p.ty) p.SBL)) c₀ := by
  cases hh with
  | call hx hf =>
    rw [hm, hfx] at hx
    cases hx
    rw [hSR.hf] at hf
    cases hf
    exact ⟨_, E, .inr ⟨rfl, by simp [wA]⟩, hSR, he, hm, hl, rfl, .seg .nil⟩
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])

/-! ## Labels and handlers -/

theorem AG.of_ret {E : List (Option Val)} {c : Admin} (hc : c.IsReturnCallRef) : AG p E c c := by
  unfold Admin.IsReturnCallRef at hc
  split at hc
  · exact .plain (.flat _)
  · exact .retCallRef _
  · exact hc.elim

theorem LG.throwing_inv {E : List (Option Val)} {a : Nat} {ns : List Admin}
    (h : LG p E (throwing a) ns) : ∃ Y, ns = throwing a ++ Y := by
  rcases LG.vals_cons_inv (vs := [.ref (.exn a)]) (x := .plain .throwRef) (rest := []) rfl h
    with ⟨y, rest', rfl, hy, hr⟩ | ⟨vs₀, rest', -, h', -⟩ | ⟨h', -⟩ | ⟨-, Y, rfl⟩
  · rw [AG.eq_of_plain (fun _ h => by cases h) rfl hy, LGq.nil_inv hr]
    exact ⟨[], rfl⟩
  · cases h'
  · cases h'
  · exact ⟨Y, rfl⟩

theorem LG.trap_inv {E : List (Option Val)} {ns : List Admin} (h : LG p E [.trap] ns) :
    ∃ Y, ns = .trap :: Y := by
  rcases LG.vals_cons_inv (vs := []) (x := .trap) (rest := []) rfl h
    with ⟨y, rest', rfl, hy, hr⟩ | ⟨vs₀, rest', -, h', -⟩ | ⟨-, Y, rfl⟩ | ⟨h', -⟩
  · cases hy
    rw [LGq.nil_inv hr]
    exact ⟨[], rfl⟩
  · cases h'
  · exact ⟨Y, rfl⟩
  · cases h'

theorem g_label {n : Nat} {c c' : List Instr} {b b' : List Admin} {E : List (Option Val)}
    (IH : SimIH p P H (sizeOf (Admin.label n c b))) (hc : IRL p c c') (hb : LG p E b b')
    {s t : Store H} {fo : Frame} (hm : fo.module = p.mi) (hl : fo.locals.length = p.base)
    (he : E.length = p.ext) {args : List Val} {c₀ : Config H}
    (hh : Det.Head P s fo args (.label n c b) c₀) (hSR : SR p s t) :
    GRes p P t ⟨fo.locals ++ E, p.mi⟩ args (.label n c b) (.label n c' b') c₀ := by
  obtain ⟨hg, hf, rfl⟩ := hSR
  have hSR : SR p s (withFuncs s (newFuncs p s.funcs)) := ⟨hg, hf, rfl⟩
  have hplain : ∀ {vs : List Val} {i : Instr} {rest : List Admin}, (Admin.plain i).val? = none →
      (∀ x, i ≠ .call x) → structuredInstr i = false → i ≠ .throwRef →
      b = vals vs ++ .plain i :: rest → ∃ rest', b' = vals vs ++ .plain i :: rest' :=
    fun hv hi hs ht hb' => by
      subst hb'
      obtain ⟨rest', rfl, -⟩ := LG.flat_inv hv (by simp) (fun h => ht (by cases h; rfl))
        (by simp) (fun y hy => AG.eq_of_plain hi hs hy) hb
      exact ⟨rest', rfl⟩
  cases hh with
  | ctxtLabel h =>
    rename_i s' f' b₁
    have hsz : sizeOf b < sizeOf (Admin.label n c b) := Exec.Drv.sizeOf_label_body
    obtain ⟨n₁, ⟨hm₁, hl₁, E₁, he₁, hfr₁, hrel⟩, hsr, hprog⟩ :=
      IH .g ⟨s, fo, b⟩ ⟨s', f', b₁⟩ ⟨_, ⟨fo.locals ++ E, p.mi⟩, b'⟩ hsz h ⟨hm, hl, E, he, rfl, hb⟩
        hSR
    refine ⟨⟨n₁.store, n₁.frame, [.label n c' n₁.code]⟩, E₁, ?_, hsr, he₁, hm₁, hl₁, hfr₁,
      .head (.label hc hrel) .nil⟩
    rcases hprog with hp | ⟨rfl, hw⟩
    · exact .inl (tg_label hp n c')
    · exact .inr ⟨rfl, by simp at hw ⊢; omega⟩
  | labelVals hb' =>
    subst hb'
    rw [LG.vals_inv hb]
    exact gres_same hm hl he hSR rfl (tg_head (.labelVals rfl)) (LG.of_out (Out.vals _))
  | brLabelZero hb' hl' hn =>
    rename_i vs' vs l rest
    have e : vals vs' ++ vals vs ++ [Admin.plain (.br l)] ++ rest =
        vals (vs' ++ vs) ++ .plain (.br l) :: rest := by simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := hplain rfl (fun _ h => by cases h) rfl (by simp) hb'
    exact gres_same hm hl he hSR rfl
      (tg_head (.brLabelZero (vs' := vs') (vs := vs) (rest := rest') (by simp) hl' hn))
      (LG.vals_append vs (.plain (LGq.of_IRL hc)))
  | brLabelSucc hb' hl' =>
    rename_i vs l rest
    have e : vals vs ++ [Admin.plain (.br l)] ++ rest = vals vs ++ .plain (.br l) :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := hplain rfl (fun _ h => by cases h) rfl (by simp) hb'
    exact gres_same hm hl he hSR rfl (tg_head (.brLabelSucc (rest := rest') (by simp) hl'))
      (LG.vals_append vs (.plain (.cons (.flat _) .nil)))
  | returnCallRefLabel hb' hc' =>
    rename_i vs c₁ rest
    have e : vals vs ++ [c₁] ++ rest = vals vs ++ c₁ :: rest := by simp
    rw [e] at hb'
    subst hb'
    obtain ⟨rest', rfl, -⟩ := LG.flat_inv (Det.IsReturnCallRef.val_none hc')
      (fun h => by subst h; exact hc') (fun h => by subst h; exact hc')
      (fun h => by subst h; exact hc') (fun y hy => AG.eq_of_ret hc' hy) hb
    exact gres_same hm hl he hSR rfl (tg_head (.returnCallRefLabel (rest := rest') (by simp) hc'))
      (LG.vals_append vs (.head (AG.of_ret hc') .nil))
  | returnLabel hb' =>
    rename_i vs rest
    have e : vals vs ++ [Admin.plain .return_] ++ rest = vals vs ++ .plain .return_ :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := hplain rfl (fun _ h => by cases h) rfl (by simp) hb'
    exact gres_same hm hl he hSR rfl (tg_head (.returnLabel (rest := rest') (by simp)))
      (LG.vals_append vs (.plain (.cons (.flat _) .nil)))
  | throwRefLabel =>
    rename_i a
    obtain ⟨Y, rfl⟩ := LG.throwing_inv hb
    exact gres_same hm hl he hSR rfl bubble_label_throw (LG.of_out (.ok (by simp [okI,
      structuredInstr, IsLocalI, IsTailI])))
  | trapLabel =>
    obtain ⟨Y, rfl⟩ := LG.trap_inv hb
    exact gres_same hm hl he hSR rfl bubble_label_trap (LG.of_out Out.trap)
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

theorem handler_pre_throw {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {a : Nat}
    {Y : List Admin} :
    Relation.ReflTransGen (Step P Det.noHost) ⟨s, f, [.handler n cs (throwing a ++ Y)]⟩
      ⟨s, f, [.handler n cs (throwing a)]⟩ := by
  rcases Y with _ | ⟨y, Y⟩
  · simpa using Relation.ReflTransGen.refl
  · refine .single (.ctxtHandler ?_)
    have := Step.throwRefInstrs (P := P) (host := Det.noHost) (s := s) (f := f) (vs := [])
      (a := a) (rest := y :: Y) (.inr (by simp))
    simpa [throwing, vals] using this

theorem tg_of_pre {a b c : Config H} (h₁ : Relation.ReflTransGen (Step P Det.noHost) a b)
    (h₂ : Relation.TransGen (Step P Det.noHost) b c) :
    Relation.TransGen (Step P Det.noHost) a c := by
  induction h₁ using Relation.ReflTransGen.head_induction_on with
  | refl => exact h₂
  | head hab _ ih => exact .head hab ih

theorem g_handler {n : Nat} {cs : List Catch} {b b' : List Admin} {E : List (Option Val)}
    (IH : SimIH p P H (sizeOf (Admin.handler n cs b))) (hb : LG p E b b')
    {s t : Store H} {fo : Frame} (hm : fo.module = p.mi) (hl : fo.locals.length = p.base)
    (he : E.length = p.ext) {args : List Val} {c₀ : Config H}
    (hh : Det.Head P s fo args (.handler n cs b) c₀) (hSR : SR p s t) :
    GRes p P t ⟨fo.locals ++ E, p.mi⟩ args (.handler n cs b) (.handler n cs b') c₀ := by
  obtain ⟨hg, hf, rfl⟩ := hSR
  have hSR : SR p s (withFuncs s (newFuncs p s.funcs)) := ⟨hg, hf, rfl⟩
  have hplain : ∀ {vs : List Val} {i : Instr} {rest : List Admin}, (Admin.plain i).val? = none →
      (∀ x, i ≠ .call x) → structuredInstr i = false → i ≠ .throwRef →
      b = vals vs ++ .plain i :: rest → ∃ rest', b' = vals vs ++ .plain i :: rest' :=
    fun hv hi hs ht hb' => by
      subst hb'
      obtain ⟨rest', rfl, -⟩ := LG.flat_inv hv (by simp) (fun h => ht (by cases h; rfl))
        (by simp) (fun y hy => AG.eq_of_plain hi hs hy) hb
      exact ⟨rest', rfl⟩
  cases hh with
  | ctxtHandler h =>
    rename_i s' f' b₁
    have hsz : sizeOf b < sizeOf (Admin.handler n cs b) := Exec.Drv.sizeOf_handler_body
    obtain ⟨n₁, ⟨hm₁, hl₁, E₁, he₁, hfr₁, hrel⟩, hsr, hprog⟩ :=
      IH .g ⟨s, fo, b⟩ ⟨s', f', b₁⟩ ⟨_, ⟨fo.locals ++ E, p.mi⟩, b'⟩ hsz h ⟨hm, hl, E, he, rfl, hb⟩
        hSR
    refine ⟨⟨n₁.store, n₁.frame, [.handler n cs n₁.code]⟩, E₁, ?_, hsr, he₁, hm₁, hl₁, hfr₁,
      .head (.handler hrel) .nil⟩
    rcases hprog with hp | ⟨rfl, hw⟩
    · exact .inl (tg_handler hp n cs)
    · exact .inr ⟨rfl, by simp at hw ⊢; omega⟩
  | brHandler hb' =>
    rename_i vs l rest
    have e : vals vs ++ [Admin.plain (.br l)] ++ rest = vals vs ++ .plain (.br l) :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := hplain rfl (fun _ h => by cases h) rfl (by simp) hb'
    exact gres_same hm hl he hSR rfl (tg_head (.brHandler (rest := rest') (by simp)))
      (LG.vals_append vs (.plain (.cons (.flat _) .nil)))
  | returnCallRefHandler hb' hc' =>
    rename_i vs c₁ rest
    have e : vals vs ++ [c₁] ++ rest = vals vs ++ c₁ :: rest := by simp
    rw [e] at hb'
    subst hb'
    obtain ⟨rest', rfl, -⟩ := LG.flat_inv (Det.IsReturnCallRef.val_none hc')
      (fun h => by subst h; exact hc') (fun h => by subst h; exact hc')
      (fun h => by subst h; exact hc') (fun y hy => AG.eq_of_ret hc' hy) hb
    exact gres_same hm hl he hSR rfl
      (tg_head (.returnCallRefHandler (rest := rest') (by simp) hc'))
      (LG.vals_append vs (.head (AG.of_ret hc') .nil))
  | returnHandler hb' =>
    rename_i vs rest
    have e : vals vs ++ [Admin.plain .return_] ++ rest = vals vs ++ .plain .return_ :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := hplain rfl (fun _ h => by cases h) rfl (by simp) hb'
    exact gres_same hm hl he hSR rfl (tg_head (.returnHandler (rest := rest') (by simp)))
      (LG.vals_append vs (.plain (.cons (.flat _) .nil)))
  | throwRefHandlerEmpty =>
    obtain ⟨Y, rfl⟩ := LG.throwing_inv hb
    exact gres_same hm hl he hSR rfl (tg_of_pre handler_pre_throw (tg_head .throwRefHandlerEmpty))
      (LG.of_out (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI])))
  | throwRefHandlerCatch he' ht =>
    obtain ⟨Y, rfl⟩ := LG.throwing_inv hb
    rw [hm] at ht
    exact gres_same hm hl he hSR rfl
      (tg_of_pre handler_pre_throw
        (tg_head (.throwRefHandlerCatch (s := withFuncs s (newFuncs p s.funcs)) he' ht)))
      (LG.vals_append _ (.plain (.cons (.flat _) .nil)))
  | throwRefHandlerCatchRef he' ht =>
    obtain ⟨Y, rfl⟩ := LG.throwing_inv hb
    rw [hm] at ht
    exact gres_same hm hl he hSR rfl
      (tg_of_pre handler_pre_throw
        (tg_head (.throwRefHandlerCatchRef (s := withFuncs s (newFuncs p s.funcs)) he' ht)))
      (LG.vals_append _ (.val rfl (.plain (.cons (.flat _) .nil))))
  | throwRefHandlerCatchAll =>
    obtain ⟨Y, rfl⟩ := LG.throwing_inv hb
    exact gres_same hm hl he hSR rfl
      (tg_of_pre handler_pre_throw (tg_head .throwRefHandlerCatchAll))
      (.plain (.cons (.flat _) .nil))
  | throwRefHandlerCatchAllRef =>
    obtain ⟨Y, rfl⟩ := LG.throwing_inv hb
    exact gres_same hm hl he hSR rfl
      (tg_of_pre handler_pre_throw (tg_head .throwRefHandlerCatchAllRef))
      (.val rfl (.plain (.cons (.flat _) .nil)))
  | throwRefHandlerNext h =>
    rename_i c₁ cs₁ a₁
    obtain ⟨Y, rfl⟩ := LG.throwing_inv hb
    have h' : ¬ CatchMatches (withFuncs s (newFuncs p s.funcs)) ⟨fo.locals ++ E, p.mi⟩ a₁ c₁ := by
      rw [← hm]; exact h
    exact gres_same hm hl he hSR rfl
      (tg_of_pre handler_pre_throw (tg_head (.throwRefHandlerNext h')))
      (.head (.handler (LG.of_out (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI]))))
        .nil)
  | handlerVals hb' =>
    subst hb'
    rw [LG.vals_inv hb]
    exact gres_same hm hl he hSR rfl (tg_head (.handlerVals rfl)) (LG.of_out (Out.vals _))
  | trapHandler =>
    obtain ⟨Y, rfl⟩ := LG.trap_inv hb
    refine gres_same hm hl he hSR rfl ?_ (LG.of_out Out.trap)
    rcases Y with _ | ⟨y, Y⟩
    · exact tg_head .trapHandler
    · refine .head (.ctxtHandler (f' := ⟨fo.locals ++ E, p.mi⟩) (s' := _) ?_)
        (tg_head .trapHandler)
      have := Step.trapInstrs (P := P) (host := Det.noHost) (s := withFuncs s (newFuncs p s.funcs))
        (f := ⟨fo.locals ++ E, p.mi⟩) (vs := []) (rest := y :: Y) (.inr (by simp))
      simpa [vals] using this
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

/-! ## The site -/

theorem vals_inj : ∀ {vs ws : List Val}, vals vs = vals ws → vs = ws
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [vals] at h
  | _ :: _, [], h => by simp [vals] at h
  | v :: vs, w :: ws, h => by
    simp only [vals, List.map_cons, List.cons.injEq] at h
    have hv : v = w := by
      have := congrArg Admin.val? h.1
      simpa using this
    rw [hv, vals_inj h.2]

/-- The first non-value of a sequence, when the sequence has one. -/
theorem fnv_eq {vs ws : List Val} {x y : Admin} {r t : List Admin} (hx : x.val? = none)
    (hy : y.val? = none) (h : vals vs ++ x :: r = vals ws ++ y :: t) : x = y :=
  (vals_append_cons_inj hx hy h).2.1

theorem g_site {n : Nat} {F : Frame} {Y X : List Admin} {E : List (Option Val)}
    (IH : SimIH p P H (sizeOf (Admin.frame n F Y))) (hmF : F.module = p.mi) (hlF : F.locals = E)
    (hsite : SiteR p n Y X) {s t : Store H} {fo : Frame} (hm : fo.module = p.mi)
    (hl : fo.locals.length = p.base) (he : E.length = p.ext) {args : List Val} {c₀ : Config H}
    (hh : Det.Head P s fo args (.frame n F Y) c₀) (hSR : SR p s t) :
    GRes p P t ⟨fo.locals ++ E, p.mi⟩ args (.frame n F Y) (.label n [] X) c₀ := by
  obtain ⟨hg, hf, rfl⟩ := hSR
  have hSR : SR p s (withFuncs s (newFuncs p s.funcs)) := ⟨hg, hf, rfl⟩
  subst hlF
  cases hh with
  | ctxtFrame h =>
    rename_i s' F₁ Y₁
    have hsz : sizeOf Y < sizeOf (Admin.frame n F Y) := Exec.Drv.sizeOf_frame_body
    obtain ⟨n₁, ⟨hm₁, -, hl₁, hfr₁, X₁, hc₁, hs₁⟩, hsr, hprog⟩ :=
      IH (.top n fo.locals) ⟨s, F, Y⟩ ⟨s', F₁, Y₁⟩ ⟨_, ⟨fo.locals ++ F.locals, p.mi⟩, [.label n [] X]⟩
        hsz h ⟨hmF, hl, he, rfl, X, rfl, hsite⟩ hSR
    refine ⟨n₁, F₁.locals, ?_, hsr, hl₁, hm, hl, hfr₁, ?_⟩
    · rcases hprog with hp | ⟨rfl, hw⟩
      · exact .inl hp
      · exact .inr ⟨rfl, by simp at hw ⊢; omega⟩
    · rw [hc₁]; exact .head (.site hm₁ rfl hs₁) .nil
  | @frameVals _ _ _ _ vs hb hn =>
    -- `hb : Y = vals vs`; every non-value form is excluded by its first non-value
    have hne : ∀ {ws : List Val} {x : Admin} {r : List Admin}, x.val? = none →
        vals ws ++ x :: r ≠ vals vs := fun hx h => vals_ne_vals_cons hx h.symm
    cases hsite with
    | @a _ bO _ _ => exact absurd hb (hne (ws := []) (x := .label n [] bO) (r := []) rfl)
    | b vs₀ =>
      have h := vals_inj hb
      subst h
      exact gres_same hm hl he hSR rfl (tg_head (.labelVals rfl)) (LG.of_out (Out.vals _))
    | @c _ vs₀ _ => exact absurd hb (hne (ws := vs₀) (x := .plain .return_) (r := []) rfl)
    | d => exact absurd hb (hne (ws := []) (x := .trap) (r := []) rfl)
    | e a => exact absurd hb (hne (ws := [.ref (.exn a)]) (x := .plain .throwRef) (r := []) rfl)
    | @f _ vs₀ vs' l rest hn' hl' =>
      have h := vals_inj hb
      subst h
      exact gres_same hm hl he hSR rfl
        (tg_head (.brLabelZero (vs' := vs') (vs := vs₀) (rest := rest) rfl hl' hn))
        (by simpa [expression] using LG.of_out (p := p) (E := F.locals) (Out.vals vs₀))
    | @g _ vs₀ l rest _ =>
      rw [List.append_assoc] at hb
      exact absurd hb (hne (ws := vs₀) (x := .plain (.br l)) rfl)
  | @returnFrame _ _ _ _ vs₁ vs₂ rest hb hn =>
    have e : vals vs₁ ++ vals vs₂ ++ [Admin.plain .return_] ++ rest =
        vals (vs₁ ++ vs₂) ++ .plain .return_ :: rest := by simp
    rw [e] at hb
    have hne : ∀ {ws : List Val} {x : Admin} {r : List Admin}, x.val? = none →
        x ≠ .plain .return_ → vals ws ++ x :: r ≠ vals (vs₁ ++ vs₂) ++ .plain .return_ :: rest :=
      fun hx hxr h => hxr (fnv_eq hx rfl h)
    cases hsite with
    | @c _ vs₀ rest' =>
      obtain ⟨h1, -, h3⟩ := vals_append_cons_inj rfl rfl hb
      subst h1
      subst h3
      exact gres_same hm hl he hSR rfl
        (tg_head (.brLabelZero (vs' := vs₁) (vs := vs₂) (rest := rest') (by simp)
          (InlineTy.xLabel_toNat (by decide)) hn))
        (by simpa [expression] using LG.of_out (p := p) (E := F.locals) (Out.vals vs₂))
    | @a _ bO _ _ => exact absurd hb (hne (ws := []) (x := .label n [] bO) (r := []) rfl (by simp))
    | b vs₀ => exact absurd hb (vals_ne_vals_cons rfl)
    | d => exact absurd hb (hne (ws := []) (x := .trap) (r := []) rfl (by simp))
    | e a => exact absurd hb (hne (ws := [.ref (.exn a)]) (x := .plain .throwRef) (r := []) rfl
        (by simp))
    | @f _ vs₀ _ _ _ _ _ => exact absurd hb (vals_ne_vals_cons rfl)
    | @g _ vs₀ l rest' _ =>
      rw [List.append_assoc] at hb
      exact absurd hb (hne (ws := vs₀) (x := .plain (.br l)) rfl (by simp))
  | trapFrame =>
    generalize hY : ([Admin.trap] : List Admin) = Y at hsite
    have hne : ∀ {ws : List Val} {x : Admin} {r : List Admin}, x.val? = none → x ≠ .trap →
        (vals [] ++ Admin.trap :: [] : List Admin) ≠ vals ws ++ x :: r :=
      fun hx hxr h => hxr (fnv_eq rfl hx h).symm
    cases hsite with
    | d => exact gres_same hm hl he hSR rfl (tg_head .trapLabel) (LG.of_out Out.trap)
    | @a _ bO _ _ => exact absurd hY (hne (ws := []) (x := .label n [] bO) (r := []) rfl (by simp))
    | b vs₀ => exact absurd hY.symm (vals_ne_vals_cons (ws := []) (x := .trap) (r := []) rfl)
    | @c _ vs₀ _ => exact absurd hY (hne (ws := vs₀) (x := .plain .return_) (r := []) rfl
        (by simp))
    | e a => exact absurd hY (hne (ws := [.ref (.exn a)]) (x := .plain .throwRef) (r := []) rfl
        (by simp))
    | @f _ vs₀ _ _ _ _ _ =>
      exact absurd hY.symm (vals_ne_vals_cons (ws := []) (x := .trap) (r := []) rfl)
    | @g _ vs₀ l rest' _ =>
      rw [List.append_assoc] at hY
      exact absurd hY (hne (ws := vs₀) (x := .plain (.br l)) rfl (by simp))
  | @throwRefFrame _ _ _ a =>
    generalize hY : ([Admin.ref (.exn a), .plain .throwRef] : List Admin) = Y at hsite
    have hne : ∀ {ws : List Val} {x : Admin} {r : List Admin}, x.val? = none →
        x ≠ .plain .throwRef →
        (vals [.ref (.exn a)] ++ Admin.plain .throwRef :: [] : List Admin) ≠ vals ws ++ x :: r :=
      fun hx hxr h => hxr (fnv_eq rfl hx h).symm
    cases hsite with
    | e a' =>
      exact gres_same hm hl he hSR rfl (tg_head .throwRefLabel)
        (LG.of_out (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI])))
    | @a _ bO _ _ => exact absurd hY (hne (ws := []) (x := .label n [] bO) (r := []) rfl (by simp))
    | b vs₀ => exact absurd hY.symm (vals_ne_vals_cons (ws := [.ref (.exn a)])
        (x := .plain .throwRef) (r := []) rfl)
    | @c _ vs₀ _ => exact absurd hY (hne (ws := vs₀) (x := .plain .return_) (r := []) rfl
        (by simp))
    | d => exact absurd hY (hne (ws := []) (x := .trap) (r := []) rfl (by simp))
    | @f _ vs₀ _ _ _ _ _ => exact absurd hY.symm (vals_ne_vals_cons (ws := [.ref (.exn a)])
        (x := .plain .throwRef) (r := []) rfl)
    | @g _ vs₀ l rest' _ =>
      rw [List.append_assoc] at hY
      exact absurd hY (hne (ws := vs₀) (x := .plain (.br l)) rfl (by simp))
  | @returnCallRefFrameNull _ _ _ _ vs c rest hb hc =>
    have e : vals vs ++ [Admin.ref .null, c] ++ rest = vals (vs ++ [.ref .null]) ++ c :: rest := by
      simp [vals, Val.toAdmin]
    rw [e] at hb
    have hcv := Det.IsReturnCallRef.val_none hc
    have hne : ∀ {ws : List Val} {x : Admin} {r : List Admin}, x.val? = none →
        ¬ x.IsReturnCallRef → vals ws ++ x :: r ≠ vals (vs ++ [.ref .null]) ++ c :: rest :=
      fun hx hxr h => hxr ((fnv_eq hx hcv h) ▸ hc)
    cases hsite with
    | @a _ bO _ _ => exact absurd hb (hne (ws := []) (x := .label n [] bO) (r := []) rfl
        (by simp [Admin.IsReturnCallRef]))
    | b vs₀ => exact absurd hb (vals_ne_vals_cons hcv)
    | @c _ vs₀ _ => exact absurd hb (hne (ws := vs₀) (x := .plain .return_) (r := []) rfl
        (by simp [Admin.IsReturnCallRef]))
    | d => exact absurd hb (hne (ws := []) (x := .trap) (r := []) rfl
        (by simp [Admin.IsReturnCallRef]))
    | e a => exact absurd hb (hne (ws := [.ref (.exn a)]) (x := .plain .throwRef) (r := []) rfl
        (by simp [Admin.IsReturnCallRef]))
    | @f _ vs₀ _ _ _ _ _ => exact absurd hb (vals_ne_vals_cons hcv)
    | @g _ vs₀ l rest' _ =>
      rw [List.append_assoc] at hb
      exact absurd hb (hne (ws := vs₀) (x := .plain (.br l)) rfl
        (by simp [Admin.IsReturnCallRef]))
  | @returnCallRefFrameAddr _ _ _ _ vs' vs a c rest _ _ _ hb hc _ _ _ =>
    have e : vals vs' ++ vals vs ++ [Admin.ref (.func a), c] ++ rest =
        vals (vs' ++ vs ++ [.ref (.func a)]) ++ c :: rest := by simp [vals, Val.toAdmin]
    rw [e] at hb
    have hcv := Det.IsReturnCallRef.val_none hc
    have hne : ∀ {ws : List Val} {x : Admin} {r : List Admin}, x.val? = none →
        ¬ x.IsReturnCallRef → vals ws ++ x :: r ≠ vals (vs' ++ vs ++ [.ref (.func a)]) ++ c :: rest :=
      fun hx hxr h => hxr ((fnv_eq hx hcv h) ▸ hc)
    cases hsite with
    | @a _ bO _ _ => exact absurd hb (hne (ws := []) (x := .label n [] bO) (r := []) rfl
        (by simp [Admin.IsReturnCallRef]))
    | b vs₀ => exact absurd hb (vals_ne_vals_cons hcv)
    | @c _ vs₀ _ => exact absurd hb (hne (ws := vs₀) (x := .plain .return_) (r := []) rfl
        (by simp [Admin.IsReturnCallRef]))
    | d => exact absurd hb (hne (ws := []) (x := .trap) (r := []) rfl
        (by simp [Admin.IsReturnCallRef]))
    | e a' => exact absurd hb (hne (ws := [.ref (.exn a')]) (x := .plain .throwRef) (r := []) rfl
        (by simp [Admin.IsReturnCallRef]))
    | @f _ vs₀ _ _ _ _ _ => exact absurd hb (vals_ne_vals_cons hcv)
    | @g _ vs₀ l rest' _ =>
      rw [List.append_assoc] at hb
      exact absurd hb (hne (ws := vs₀) (x := .plain (.br l)) rfl
        (by simp [Admin.IsReturnCallRef]))
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

/-! ## Dispatch -/

theorem LG.of_flatRes {E : List (Option Val)} {c : List Admin} (h : FlatRes c) : LG p E c c := by
  rcases h with ⟨vs, rfl⟩ | rfl | ⟨a, rfl⟩ | ⟨vs, a, c', rfl, ⟨d, rfl⟩ | ⟨y, rfl⟩⟩
  · exact LG.of_out (Out.vals vs)
  · exact LG.of_out Out.trap
  · exact LG.of_out (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI]))
  · exact LG.vals_append vs (.val rfl (.head (.callRef d) .nil))
  · exact LG.vals_append vs (.val rfl (.head (.plain (.flat _)) .nil))

theorem simpleE_callRef (d : DefType) : SimpleE (.callRefType d) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all

theorem not_structE_callRef (d : DefType) : ¬ StructE (.callRefType d) := by
  rintro (⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩) <;> cases h

/-- **Caller head steps.** -/
theorem g_head (hok : PrmOk p) (hfx : p.mi.funcs[p.fx.toNat]? = some p.af) {e e' : Admin}
    (IH : SimIH p P H (sizeOf e)) {s t : Store H} {fo : Frame} {E : List (Option Val)}
    (hm : fo.module = p.mi) (hl : fo.locals.length = p.base) (he : E.length = p.ext)
    {args : List Val} {c₀ : Config H} (hh : Det.Head P s fo args e c₀) (hae : AG p E e e')
    (hSR : SR p s t) : GRes p P t ⟨fo.locals ++ E, p.mi⟩ args e e' c₀ := by
  have hgood := hh.good
  cases hae with
  | @plain _ i i' hi =>
    cases hi with
    | flat =>
      by_cases hloc : IsLocalI i = true
      · exact g_local hloc hm hl he hh hSR
      · by_cases hst : StructE (.plain i)
        · rcases hst with ⟨bt, b, h⟩ | ⟨bt, b, h⟩ | ⟨bt, b₁, b₂, h⟩ | ⟨bt, cs, b, h⟩ <;>
            cases h
          · exact g_block (IRL.refl p b) hm hl he hh hSR
          · exact g_loop (IRL.refl p b) hm hl he hh hSR
          · exact g_if (IRL.refl p b₁) (IRL.refl p b₂) hm hl he hh hSR
          · exact g_try (IRL.refl p b) hm hl he hh hSR
        · refine g_simple hok (simpleE_plain ?_ ?_ ?_) hst hm hl he hh hSR <;>
            intro x hx <;> subst hx <;> simp [IsLocalI] at hloc
    | site => exact g_site_call hfx hm hl he hh hSR
    | block h => exact g_block h hm hl he hh hSR
    | loop h => exact g_loop h hm hl he hh hSR
    | if_ h₁ h₂ => exact g_if h₁ h₂ hm hl he hh hSR
    | tryTable h => exact g_try h hm hl he hh hSR
  | ref r => exact absurd hgood.val_none (by simp)
  | callRef d => exact g_simple hok (simpleE_callRef d) (not_structE_callRef d) hm hl he hh hSR
  | retCallRef d => exact absurd (Or.inr (Or.inr trivial)) hgood.not_blocked
  | label hc hb => exact g_label IH hc hb hm hl he hh hSR
  | handler hb => exact g_handler IH hb hm hl he hh hSR
  | frame hfr =>
    obtain ⟨c₀', hprog, hsr, hf₀, hf₀', hres⟩ :=
      frame_case (fn := ⟨fo.locals ++ E, p.mi⟩) IH hh hfr hSR
    refine ⟨c₀', E, hprog, hsr, he, by rw [hf₀]; exact hm, by rw [hf₀]; exact hl,
      by rw [hf₀', hf₀], ?_⟩
    rcases hres with ⟨F₁, F₁', b₁, b₁', h₁, h₂, hfr₁⟩ | ⟨h₁, hfl⟩
    · rw [h₁, h₂]; exact .head (.frame hfr₁) .nil
    · rw [h₁]; exact LG.of_flatRes hfl
  | trap => exact absurd rfl hgood.ne_trap
  | site hmF hlF hs => exact g_site IH hmF hlF hs hm hl he hh hSR

end Silmaril.Wasm.Binaryen.InlR
