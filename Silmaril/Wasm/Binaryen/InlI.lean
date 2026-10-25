module

public import Silmaril.Wasm.Binaryen.InlG

@[expose] public section

/-! # The inlining simulation, callee mode

Head steps of the callee's code inside an inlined block, at label depth `d`: the left side
runs in the callee's frame, the right side runs the relocated code (`InlineTy.xform`) in
the caller's frame `⟨L ++ F.locals, mi⟩`, where `L` (the caller's own locals) does not
change. A `return` at depth `d` is a branch to depth `d` on the right; it leaves the
labels in step with the left side's `return`.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.SingleThreaded

variable {H : Type} {p : Prm} {P : Numerics.Profile}

/-- The result of a callee head step. -/
def IRes (p : Prm) (P : Numerics.Profile) (d : Nat) (L : List (Option Val)) (t : Store H)
    (F : Frame) (args : List Val) (e e' : Admin) (c₀ : Config H) : Prop :=
  ∃ c₀' : Config H,
    (Relation.TransGen (Step P Det.noHost) ⟨t, ⟨L ++ F.locals, p.mi⟩, vals args ++ [e']⟩ c₀' ∨
      (c₀' = ⟨t, ⟨L ++ F.locals, p.mi⟩, vals args ++ [e']⟩ ∧
        wL c₀.code < wL (vals args ++ [e]))) ∧
    SR p c₀.store c₀'.store ∧ c₀.frame.module = p.mi ∧ c₀.frame.locals.length = p.ext ∧
    c₀'.frame = ⟨L ++ c₀.frame.locals, p.mi⟩ ∧ LI p d c₀.code c₀'.code

theorem ires_same {d : Nat} {L : List (Option Val)} {F : Frame} {t : Store H} {args : List Val}
    {e e' : Admin} {s s₀ : Store H} {code₀ code₀' : List Admin} (hm : F.module = p.mi)
    (he : F.locals.length = p.ext) (hSR : SR p s t) (hs : s₀.funcs = s.funcs)
    (hstep : Relation.TransGen (Step P Det.noHost) ⟨t, ⟨L ++ F.locals, p.mi⟩, vals args ++ [e']⟩
      ⟨withFuncs s₀ (newFuncs p s.funcs), ⟨L ++ F.locals, p.mi⟩, code₀'⟩)
    (hrel : LI p d code₀ code₀') :
    IRes p P d L t F args e e' ⟨s₀, F, code₀⟩ :=
  ⟨_, .inl hstep, hSR.mono hs, hm, he, rfl, hrel⟩

/-! ## Relocated code -/

theorem LI.of_xformL {d : Nat} : ∀ {is : List Instr}, InlineTy.retGoodL d is →
    LI p d (expression is) (expression (InlineTy.xformL p.base d is))
  | [], _ => .nil
  | _ :: _, ⟨h₁, h₂⟩ => .cons (.plain h₁) (LI.of_xformL h₂)

theorem idx_ext {k : IndexKind} {x y : Idx k} (h : x.toNat = y.toNat) : x = y := by
  rcases x with ⟨⟨a, ha⟩⟩
  rcases y with ⟨⟨b, hb⟩⟩
  simp only [Idx.toNat] at h
  subst h
  rfl

theorem xLabel_pred {d : Nat} (h : d + 1 < 2 ^ 32) :
    labelPred (InlineTy.xLabel (d + 1)) = InlineTy.xLabel d := by
  have h1 := InlineTy.xLabel_toNat h
  have h2 := InlineTy.xLabel_toNat (d := d) (by omega)
  apply idx_ext
  rw [h2]
  simp only [labelPred, Idx.toNat] at h1 ⊢
  omega

theorem LI.of_flatRes {d : Nat} {c : List Admin} (h : FlatRes c) : LI p d c c := by
  rcases h with ⟨vs, rfl⟩ | rfl | ⟨a, rfl⟩ | ⟨vs, a, c', rfl, ⟨d', rfl⟩ | ⟨y, rfl⟩⟩
  · exact LI.of_vals d vs
  · exact LI.of_out Out.trap
  · exact LI.of_out (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI]))
  · exact LI.append (LI.of_vals d vs) (.cons (.ref _) (.cons (.callRef d') .nil))
  · exact LI.append (LI.of_vals d vs) (.cons (.ref _) (.cons (AI.of_okI (by
      simp [okI, structuredInstr, IsLocalI, IsTailI])) .nil))

/-! ## Structured instructions -/

section struct

variable {d : Nat} {L : List (Option Val)} {s t : Store H} {F : Frame} {args : List Val}
  {c₀ : Config H}

theorem i_block {bt : BlockType} {b : List Instr} (h : InlineTy.retGoodL (d + 1) b)
    (hm : F.module = p.mi) (he : F.locals.length = p.ext)
    (hh : Det.Head P s F args (.plain (.block bt b)) c₀) (hSR : SR p s t) :
    IRes p P d L t F args (.plain (.block bt b))
      (.plain (InlineTy.xform p.base d (.block bt b))) c₀ := by
  obtain ⟨hg, hf, rfl⟩ := hSR
  cases hh with
  | block hbt hm' =>
    exact ires_same hm he ⟨hg, hf, rfl⟩ rfl (tg_head (.block (by rw [← hm]; exact hbt) hm'))
      (.cons (.label (c := []) trivial (LI.append (LI.of_vals (d + 1) args) (LI.of_xformL h)))
        .nil)
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

theorem i_loop {bt : BlockType} {b : List Instr} (h : InlineTy.retGoodL (d + 1) b)
    (hm : F.module = p.mi) (he : F.locals.length = p.ext)
    (hh : Det.Head P s F args (.plain (.loop bt b)) c₀) (hSR : SR p s t) :
    IRes p P d L t F args (.plain (.loop bt b))
      (.plain (InlineTy.xform p.base d (.loop bt b))) c₀ := by
  obtain ⟨hg, hf, rfl⟩ := hSR
  cases hh with
  | loop hbt hm' =>
    exact ires_same hm he ⟨hg, hf, rfl⟩ rfl (tg_head (.loop (by rw [← hm]; exact hbt) hm'))
      (.cons (.label (c := [.loop bt b]) ⟨h, trivial⟩
        (LI.append (LI.of_vals (d + 1) args) (LI.of_xformL h))) .nil)
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

theorem i_if {bt : BlockType} {b₁ b₂ : List Instr} (h₁ : InlineTy.retGoodL (d + 1) b₁)
    (h₂ : InlineTy.retGoodL (d + 1) b₂) (hm : F.module = p.mi) (he : F.locals.length = p.ext)
    (hh : Det.Head P s F args (.plain (.if_ bt b₁ b₂)) c₀) (hSR : SR p s t) :
    IRes p P d L t F args (.plain (.if_ bt b₁ b₂))
      (.plain (InlineTy.xform p.base d (.if_ bt b₁ b₂))) c₀ := by
  obtain ⟨hg, hf, rfl⟩ := hSR
  cases hh with
  | ifTrue hc =>
    exact ires_same hm he ⟨hg, hf, rfl⟩ rfl (tg_head (.ifTrue hc))
      (.cons (.plain (i := .block bt b₁) h₁) .nil)
  | ifFalse hc =>
    exact ires_same hm he ⟨hg, hf, rfl⟩ rfl (tg_head (.ifFalse hc))
      (.cons (.plain (i := .block bt b₂) h₂) .nil)
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

theorem i_try {bt : BlockType} {cs : List Catch} {b : List Instr}
    (h : InlineTy.retGoodL (d + 1) b) (hm : F.module = p.mi) (he : F.locals.length = p.ext)
    (hh : Det.Head P s F args (.plain (.tryTable bt cs b)) c₀) (hSR : SR p s t) :
    IRes p P d L t F args (.plain (.tryTable bt cs b))
      (.plain (InlineTy.xform p.base d (.tryTable bt cs b))) c₀ := by
  obtain ⟨hg, hf, rfl⟩ := hSR
  cases hh with
  | tryTable hbt hm' =>
    exact ires_same hm he ⟨hg, hf, rfl⟩ rfl
      (tg_head (.tryTable (by rw [← hm]; exact hbt) hm'))
      (.cons (.handler (.cons (.label (c := []) trivial
        (LI.append (LI.of_vals (d + 1) args) (LI.of_xformL h))) .nil)) .nil)
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

end struct

/-! ## Local accesses -/

theorem i_local (hok : PrmOk p) {d : Nat} {L : List (Option Val)} {i : Instr}
    (hi : IsLocalI i = true) {s t : Store H} {F : Frame} (hm : F.module = p.mi)
    (hL : L.length = p.base) (he : F.locals.length = p.ext) {args : List Val} {c₀ : Config H}
    (hh : Det.Head P s F args (.plain i) c₀) (hSR : SR p s t) :
    IRes p P d L t F args (.plain i) (.plain (InlineTy.xform p.base d i)) c₀ := by
  obtain ⟨hg, hf, rfl⟩ := hSR
  obtain ⟨s₀, f₀, is₀⟩ := c₀
  have hfam : Det.famOf (.plain i) = .variable := by
    cases i <;> simp [IsLocalI] at hi <;> rfl
  have hb := hok.bound
  have hx : ∀ x : LocalIdx, x.toNat < F.locals.length → (InlineTy.xIdx p.base x).toNat =
      p.base + x.toNat := fun x hx => InlineTy.xIdx_toNat (by omega)
  cases hh with
  | «variable» h =>
    generalize hc : vals args ++ [Admin.plain i] = code at h
    cases h with
    | @localGet _ _ x v hxv =>
      obtain ⟨rfl, rfl⟩ : args = [] ∧ i = .localGet x := by
        rcases args with _ | ⟨a, args⟩
        · simp at hc; exact ⟨rfl, hc⟩
        · simp [vals] at hc
      have hlt : x.toNat < F.locals.length := (List.getElem?_eq_some_iff.mp hxv).1
      have hx' : (Frame.mk (L ++ F.locals) p.mi).local? (InlineTy.xIdx p.base x) =
          some (some v) := by
        simp only [Frame.local?]
        rw [hx x hlt, List.getElem?_append_right (by omega), hL, Nat.add_sub_cancel_left]
        exact hxv
      exact ires_same hm he ⟨hg, hf, rfl⟩ rfl (tg_head (.variable (.localGet hx')))
        (LI.of_vals d [v])
    | @localSet _ _ x v hxl =>
      obtain ⟨rfl, rfl⟩ : args = [v] ∧ i = .localSet x := by
        rcases args with _ | ⟨a, _ | ⟨b, args⟩⟩
        · simp at hc
        · simp [vals] at hc; obtain ⟨rfl, rfl⟩ := hc
          exact ⟨by rcases a with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp_all, rfl⟩
        · simp [vals] at hc
      have hx' : (InlineTy.xIdx p.base x).toNat < (L ++ F.locals).length := by
        rw [hx x hxl]; simp; omega
      refine ⟨_, .inl (tg_head (.variable (.localSet (f := ⟨L ++ F.locals, p.mi⟩) hx'))),
        SR.mono ⟨hg, hf, rfl⟩ rfl, ?_, ?_, ?_, .nil⟩
      · simp [Frame.setLocal, hm]
      · simp [Frame.setLocal, he]
      · simp only [Frame.setLocal]
        rw [hx x hxl, List.set_append_right _ _ (by omega), hL, Nat.add_sub_cancel_left]
    | @localTee _ _ x v =>
      obtain ⟨rfl, rfl⟩ : args = [v] ∧ i = .localTee x := by
        rcases args with _ | ⟨a, _ | ⟨b, args⟩⟩
        · simp at hc
        · simp [vals] at hc; obtain ⟨rfl, rfl⟩ := hc
          exact ⟨by rcases a with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp_all, rfl⟩
        · simp [vals] at hc
      exact ires_same hm he ⟨hg, hf, rfl⟩ rfl (tg_head (.variable .localTee))
        (.cons (AI.of_val d v) (.cons (AI.of_val d v) (.cons (.plain (i := .localSet x) trivial)
          .nil)))
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

/-! ## Simple heads -/

theorem i_callData (hok : PrmOk p) {d : Nat} {L : List (Option Val)} {s t : Store H}
    {F : Frame} (hm : F.module = p.mi) (he : F.locals.length = p.ext) {args : List Val}
    {e : Admin} {c₀ : Config H} (hSR : SR p s t) (hcd : CallData s F args e c₀) :
    IRes p P d L t F args e e c₀ := by
  obtain ⟨vs, a, fi, ps, rs, code, rfl, hc, hf, he', hn, hcode, rfl⟩ := hcd
  obtain ⟨fi', code', hf', ht, hcode', hfr⟩ := call_rel hok hSR hf he' hn hcode
  exact ⟨_, .inl (tg_head (.callRefFunc rfl hc hf' (ht ▸ he') hn hcode')), hSR, hm, he, rfl,
    .cons (.frame hfr) .nil⟩

theorem i_simple (hok : PrmOk p) {d : Nat} {L : List (Option Val)} {e : Admin}
    (hS : SimpleE e) (hNS : ¬ StructE e) (hT : ¬ TailE e) {s t : Store H} {F : Frame}
    (hm : F.module = p.mi) (he : F.locals.length = p.ext) {args : List Val} {c₀ : Config H}
    (hh : Det.Head P s F args e c₀) (hSR : SR p s t) : IRes p P d L t F args e e c₀ := by
  rcases head_simple hh hS hSR.sameTypes (L ++ F.locals) with hcd | ⟨hfr, hfs, hN⟩
  · exact i_callData hok hm he hSR hcd
  · rcases head_out hh hS hNS with hcd | hout | ⟨hT', -⟩
    · exact i_callData hok hm he hSR hcd
    · obtain ⟨hg, hf, rfl⟩ := hSR
      obtain ⟨s₀, f₀, is₀⟩ := c₀
      simp only at hfr hfs hN
      subst hfr
      rw [hm] at hN
      exact ires_same hm he ⟨hg, hf, rfl⟩ hfs (tg_head hN) (LI.of_out hout)
    · exact absurd hT' hT

/-! ## Labels and handlers -/

theorem i_label {d n : Nat} {L : List (Option Val)} {c : List Instr} {b b' : List Admin}
    (IH : SimIH p P H (sizeOf (Admin.label n c b))) (hc : InlineTy.retGoodL d c)
    (hb : LI p (d + 1) b b') {s t : Store H} {F : Frame} (hm : F.module = p.mi)
    (hL : L.length = p.base) (he : F.locals.length = p.ext) {args : List Val} {c₀ : Config H}
    (hh : Det.Head P s F args (.label n c b) c₀) (hSR : SR p s t) :
    IRes p P d L t F args (.label n c b) (.label n (InlineTy.xformL p.base d c) b') c₀ := by
  obtain ⟨hg, hf, rfl⟩ := hSR
  have hSR : SR p s (withFuncs s (newFuncs p s.funcs)) := ⟨hg, hf, rfl⟩
  have hflat : ∀ {vs : List Val} {i : Instr} {rest : List Admin},
      b = vals vs ++ .plain i :: rest →
      InlineTy.retGood (d + 1) i ∧ ∃ rest', b' = vals vs ++ .plain (InlineTy.xform p.base (d + 1) i) ::
        rest' := fun hb' => by
    subst hb'
    obtain ⟨y, rest', rfl, hy, -⟩ := LI.vals_cons_inv hb
    cases hy with
    | plain h => exact ⟨h, rest', rfl⟩
  cases hh with
  | ctxtLabel h =>
    rename_i s' f' b₁
    have hsz : sizeOf b < sizeOf (Admin.label n c b) := Exec.Drv.sizeOf_label_body
    obtain ⟨n₁, ⟨hm₁, -, he₁, hfr₁, hrel⟩, hsr, hprog⟩ :=
      IH (.i (d + 1) L) ⟨s, F, b⟩ ⟨s', f', b₁⟩ ⟨_, ⟨L ++ F.locals, p.mi⟩, b'⟩ hsz h
        ⟨hm, hL, he, rfl, hb⟩ hSR
    refine ⟨⟨n₁.store, n₁.frame, [.label n (InlineTy.xformL p.base d c) n₁.code]⟩, ?_, hsr, hm₁,
      he₁, hfr₁, .cons (.label hc hrel) .nil⟩
    rcases hprog with hp | ⟨rfl, hw⟩
    · exact .inl (tg_label hp n _)
    · exact .inr ⟨rfl, by simp at hw ⊢; omega⟩
  | labelVals hb' =>
    subst hb'
    rw [LI.vals_inv hb]
    exact ires_same hm he hSR rfl (tg_head (.labelVals rfl)) (LI.of_vals d _)
  | brLabelZero hb' hl' hn =>
    rename_i vs' vs l rest
    have e : vals vs' ++ vals vs ++ [Admin.plain (.br l)] ++ rest =
        vals (vs' ++ vs) ++ .plain (.br l) :: rest := by simp
    rw [e] at hb'
    obtain ⟨-, rest', rfl⟩ := hflat hb'
    exact ires_same hm he hSR rfl
      (tg_head (.brLabelZero (vs' := vs') (vs := vs) (rest := rest') (by simp [InlineTy.xform])
        hl' hn))
      (LI.append (LI.of_vals d vs) (LI.of_xformL hc))
  | brLabelSucc hb' hl' =>
    rename_i vs l rest
    have e : vals vs ++ [Admin.plain (.br l)] ++ rest = vals vs ++ .plain (.br l) :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨-, rest', rfl⟩ := hflat hb'
    exact ires_same hm he hSR rfl
      (tg_head (.brLabelSucc (rest := rest') (by simp [InlineTy.xform]) hl'))
      (LI.append (LI.of_vals d vs) (.cons (.plain (i := .br _) trivial) .nil))
  | returnCallRefLabel hb' hc' =>
    rename_i vs c₁ rest
    have e : vals vs ++ [c₁] ++ rest = vals vs ++ c₁ :: rest := by simp
    rw [e] at hb'
    subst hb'
    obtain ⟨y, rest', -, hy, -⟩ := LI.vals_cons_inv hb
    unfold Admin.IsReturnCallRef at hc'
    split at hc'
    · cases hy with | plain h => exact h.elim
    · cases hy
    · exact hc'.elim
  | returnLabel hb' =>
    rename_i vs rest
    have e : vals vs ++ [Admin.plain .return_] ++ rest = vals vs ++ .plain .return_ :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨hd, rest', rfl⟩ := hflat hb'
    have hd' : d + 1 < 2 ^ 32 := hd
    have hpos : 0 < (InlineTy.xLabel (d + 1)).toNat := by
      rw [InlineTy.xLabel_toNat hd']; omega
    have hN := Det.Head.brLabelSucc (P := P) (s := withFuncs s (newFuncs p s.funcs))
      (f := ⟨L ++ F.locals, p.mi⟩) (n := n) (cont := InlineTy.xformL p.base d c)
      (vs := vs) (rest := rest') (body := vals vs ++ .plain (InlineTy.xform p.base (d + 1) .return_)
        :: rest') (by simp [InlineTy.xform]) hpos
    rw [xLabel_pred hd'] at hN
    exact ires_same hm he hSR rfl (tg_head hN)
      (LI.append (LI.of_vals d vs) (.cons (.plain (i := .return_) (show d < 2 ^ 32 by omega))
        .nil))
  | throwRefLabel =>
    rename_i a
    obtain ⟨y, rest', rfl, hy, hr⟩ := LI.vals_cons_inv (vs := [.ref (.exn a)])
      (a := .plain .throwRef) (rest := []) hb
    cases hy
    cases hr
    exact ires_same hm he hSR rfl (tg_head .throwRefLabel)
      (LI.of_out (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI])))
  | trapLabel =>
    obtain ⟨y, rest', rfl, hy, hr⟩ := LI.vals_cons_inv (vs := []) (a := .trap) (rest := []) hb
    cases hy
    cases hr
    exact ires_same hm he hSR rfl (tg_head .trapLabel) (LI.of_out Out.trap)
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

theorem i_handler {d n : Nat} {L : List (Option Val)} {cs : List Catch} {b b' : List Admin}
    (IH : SimIH p P H (sizeOf (Admin.handler n cs b))) (hb : LI p d b b') {s t : Store H}
    {F : Frame} (hm : F.module = p.mi) (hL : L.length = p.base) (he : F.locals.length = p.ext)
    {args : List Val} {c₀ : Config H} (hh : Det.Head P s F args (.handler n cs b) c₀)
    (hSR : SR p s t) : IRes p P d L t F args (.handler n cs b) (.handler n cs b') c₀ := by
  obtain ⟨hg, hf, rfl⟩ := hSR
  have hSR : SR p s (withFuncs s (newFuncs p s.funcs)) := ⟨hg, hf, rfl⟩
  have hflat : ∀ {vs : List Val} {i : Instr} {rest : List Admin},
      b = vals vs ++ .plain i :: rest →
      InlineTy.retGood d i ∧ ∃ rest', b' = vals vs ++ .plain (InlineTy.xform p.base d i) ::
        rest' := fun hb' => by
    subst hb'
    obtain ⟨y, rest', rfl, hy, -⟩ := LI.vals_cons_inv hb
    cases hy with
    | plain h => exact ⟨h, rest', rfl⟩
  have hthrow : ∀ a, b = throwing a → b' = throwing a := fun a hb' => by
    subst hb'
    obtain ⟨y, rest', rfl, hy, hr⟩ := LI.vals_cons_inv (vs := [.ref (.exn a)])
      (a := .plain .throwRef) (rest := []) hb
    cases hy
    cases hr
    rfl
  have hfr : LI p d (throwing 0) (throwing 0) := LI.of_out (.ok (by simp [okI, structuredInstr,
    IsLocalI, IsTailI]))
  cases hh with
  | ctxtHandler h =>
    rename_i s' f' b₁
    have hsz : sizeOf b < sizeOf (Admin.handler n cs b) := Exec.Drv.sizeOf_handler_body
    obtain ⟨n₁, ⟨hm₁, -, he₁, hfr₁, hrel⟩, hsr, hprog⟩ :=
      IH (.i d L) ⟨s, F, b⟩ ⟨s', f', b₁⟩ ⟨_, ⟨L ++ F.locals, p.mi⟩, b'⟩ hsz h
        ⟨hm, hL, he, rfl, hb⟩ hSR
    refine ⟨⟨n₁.store, n₁.frame, [.handler n cs n₁.code]⟩, ?_, hsr, hm₁, he₁, hfr₁,
      .cons (.handler hrel) .nil⟩
    rcases hprog with hp | ⟨rfl, hw⟩
    · exact .inl (tg_handler hp n cs)
    · exact .inr ⟨rfl, by simp at hw ⊢; omega⟩
  | brHandler hb' =>
    rename_i vs l rest
    have e : vals vs ++ [Admin.plain (.br l)] ++ rest = vals vs ++ .plain (.br l) :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨-, rest', rfl⟩ := hflat hb'
    exact ires_same hm he hSR rfl
      (tg_head (.brHandler (rest := rest') (by simp [InlineTy.xform])))
      (LI.append (LI.of_vals d vs) (.cons (.plain (i := .br _) trivial) .nil))
  | returnCallRefHandler hb' hc' =>
    rename_i vs c₁ rest
    have e : vals vs ++ [c₁] ++ rest = vals vs ++ c₁ :: rest := by simp
    rw [e] at hb'
    subst hb'
    obtain ⟨y, rest', -, hy, -⟩ := LI.vals_cons_inv hb
    unfold Admin.IsReturnCallRef at hc'
    split at hc'
    · cases hy with | plain h => exact h.elim
    · cases hy
    · exact hc'.elim
  | returnHandler hb' =>
    rename_i vs rest
    have e : vals vs ++ [Admin.plain .return_] ++ rest = vals vs ++ .plain .return_ :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨hd, rest', rfl⟩ := hflat hb'
    exact ires_same hm he hSR rfl
      (tg_head (.brHandler (rest := rest') (by simp [InlineTy.xform])))
      (LI.append (LI.of_vals d vs) (.cons (.plain (i := .return_) hd) .nil))
  | throwRefHandlerEmpty =>
    rw [hthrow _ rfl]
    exact ires_same hm he hSR rfl (tg_head .throwRefHandlerEmpty)
      (LI.of_out (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI])))
  | throwRefHandlerCatch he' ht =>
    rw [hthrow _ rfl]
    rw [hm] at ht
    exact ires_same hm he hSR rfl
      (tg_head (.throwRefHandlerCatch (s := withFuncs s (newFuncs p s.funcs)) he' ht))
      (LI.append (LI.of_vals d _) (.cons (.plain (i := .br _) trivial) .nil))
  | throwRefHandlerCatchRef he' ht =>
    rw [hthrow _ rfl]
    rw [hm] at ht
    exact ires_same hm he hSR rfl
      (tg_head (.throwRefHandlerCatchRef (s := withFuncs s (newFuncs p s.funcs)) he' ht))
      (LI.append (LI.of_vals d _) (.cons (.ref _) (.cons (.plain (i := .br _) trivial) .nil)))
  | throwRefHandlerCatchAll =>
    rw [hthrow _ rfl]
    exact ires_same hm he hSR rfl (tg_head .throwRefHandlerCatchAll)
      (.cons (.plain (i := .br _) trivial) .nil)
  | throwRefHandlerCatchAllRef =>
    rw [hthrow _ rfl]
    exact ires_same hm he hSR rfl (tg_head .throwRefHandlerCatchAllRef)
      (.cons (.ref _) (.cons (.plain (i := .br _) trivial) .nil))
  | throwRefHandlerNext h =>
    rename_i c₁ cs₁ a₁
    rw [hthrow _ rfl]
    have h' : ¬ CatchMatches (withFuncs s (newFuncs p s.funcs)) ⟨L ++ F.locals, p.mi⟩ a₁ c₁ := by
      rw [← hm]; exact h
    exact ires_same hm he hSR rfl (tg_head (.throwRefHandlerNext h'))
      (.cons (.handler (LI.of_out (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI]))))
        .nil)
  | handlerVals hb' =>
    subst hb'
    rw [LI.vals_inv hb]
    exact ires_same hm he hSR rfl (tg_head (.handlerVals rfl)) (LI.of_vals d _)
  | trapHandler =>
    obtain ⟨y, rest', rfl, hy, hr⟩ := LI.vals_cons_inv (vs := []) (a := .trap) (rest := []) hb
    cases hy
    cases hr
    exact ires_same hm he hSR rfl (tg_head .trapHandler) (LI.of_out Out.trap)
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

theorem xform_flat {i : Instr} (h1 : IsLocalI i = false) (h2 : structuredInstr i = false)
    (h3 : i ≠ .return_) (base d : Nat) : InlineTy.xform base d i = i := by
  cases i <;> simp_all [IsLocalI, structuredInstr, InlineTy.xform]

/-- **Callee head steps.** -/
theorem i_head (hok : PrmOk p) {d : Nat} {L : List (Option Val)} {e e' : Admin}
    (IH : SimIH p P H (sizeOf e)) {s t : Store H} {F : Frame} (hm : F.module = p.mi)
    (hL : L.length = p.base) (he : F.locals.length = p.ext) {args : List Val} {c₀ : Config H}
    (hh : Det.Head P s F args e c₀) (hae : AI p d e e') (hSR : SR p s t) :
    IRes p P d L t F args e e' c₀ := by
  have hgood := hh.good
  cases hae with
  | @plain _ i h =>
    by_cases hloc : IsLocalI i = true
    · exact i_local hok hloc hm hL he hh hSR
    · by_cases hst : StructE (.plain i)
      · rcases hst with ⟨bt, b, h'⟩ | ⟨bt, b, h'⟩ | ⟨bt, b₁, b₂, h'⟩ | ⟨bt, cs, b, h'⟩ <;>
          cases h'
        · exact i_block h hm he hh hSR
        · exact i_loop h hm he hh hSR
        · exact i_if h.1 h.2 hm he hh hSR
        · exact i_try h hm he hh hSR
      · have hret : i ≠ .return_ := by
          rintro rfl; exact hgood.not_blocked (.inr (.inl rfl))
        have hs : structuredInstr i = false := by
          cases i <;> simp_all [structuredInstr, StructE]
        rw [xform_flat (by simpa using hloc) hs hret]
        refine i_simple hok (simpleE_plain ?_ ?_ ?_) hst ?_ hm he hh hSR
        · intro x hx; subst hx; simp [IsLocalI] at hloc
        · intro x hx; subst hx; simp [IsLocalI] at hloc
        · intro x hx; subst hx; simp [IsLocalI] at hloc
        · rintro (⟨x, hx⟩ | ⟨x, y, hx⟩) <;> cases hx <;> exact h.elim
  | ref r => exact absurd hgood.val_none (by simp)
  | callRef dt =>
    exact i_simple hok (simpleE_callRef dt) (not_structE_callRef dt)
      (by rintro (⟨x, hx⟩ | ⟨x, y, hx⟩) <;> cases hx) hm he hh hSR
  | label hc hb => exact i_label IH hc hb hm hL he hh hSR
  | handler hb => exact i_handler IH hb hm hL he hh hSR
  | frame hfr =>
    obtain ⟨c₀', hprog, hsr, hf₀, hf₀', hres⟩ :=
      frame_case (fn := ⟨L ++ F.locals, p.mi⟩) IH hh hfr hSR
    refine ⟨c₀', hprog, hsr, by rw [hf₀]; exact hm, by rw [hf₀]; exact he, by rw [hf₀', hf₀], ?_⟩
    rcases hres with ⟨F₁, F₁', b₁, b₁', h₁, h₂, hfr₁⟩ | ⟨h₁, hfl⟩
    · rw [h₁, h₂]; exact .cons (.frame hfr₁) .nil
    · rw [h₁]; exact LI.of_flatRes hfl
  | trap => exact absurd rfl hgood.ne_trap

end Silmaril.Wasm.Binaryen.InlR
