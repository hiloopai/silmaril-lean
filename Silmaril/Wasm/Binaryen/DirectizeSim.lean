module

public import Silmaril.Wasm.Binaryen.DirectizeProfileLocal

@[expose] public section

/-! # Directize: one step

Every host-free step of the left configuration (the module with `call_indirect`) is matched
by at least one step of the right configuration (the module with `call`), or the right side
stays and the size `aszs` of the left code decreases (`sim`), provided the left store
satisfies the invariant `DInv`. The steps follow `Binaryen/GlobReadSim.lean`, with three
site cases (`sim_s0`, `sim_s1`, `sim_s2`): `call_indirect` unfolds while the right side
steps `call`, then `table.get` and `ref.cast` are left-only steps. The profile is arbitrary. Table reads and reference casts at the sites are
profile-independent; their local determinism does not restrict the choices of
numerical or growth instructions in the surrounding program.
-/

namespace Silmaril.Wasm.Binaryen.DirSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type} {ok : SiteOk} {mi : ModuleInst}

theorem SR.cases {s t : Store H} (h : SR ok mi s t) :
    ∃ G, List.Forall₂ (FR ok mi) s.funcs G ∧ t = withFuncs s G :=
  ⟨t.funcs, h.funcs, h.eq⟩

theorem SR.mk' {s : Store H} {G : List (FuncInst H)} (h : List.Forall₂ (FR ok mi) s.funcs G) :
    SR ok mi s (withFuncs s G) :=
  ⟨by simpa using h, rfl⟩

theorem sameTypes_of {s : Store H} {G : List (FuncInst H)} (h : List.Forall₂ (FR ok mi) s.funcs G) :
    SameTypes G s.funcs :=
  (SR.mk' h).sameTypes

variable (ok mi) in
/-- The shape of one simulation step. -/
def Res (P : Numerics.Profile) (c' d : Config H) (w : Nat) : Prop :=
  ∃ d' : Config H, MR ok mi c' d' ∧ SR ok mi c'.store d'.store ∧
    (Relation.TransGen (Step P Det.noHost) d d' ∨ (d' = d ∧ aszs c'.code < w))

variable (ok mi) in
/-- The induction hypothesis: steps of smaller code from invariant stores are simulated. -/
def SimIH (P : Numerics.Profile) (H : Type) (k : Nat) : Prop :=
  ∀ (c c' d : Config H), sizeOf c.code < k → Step P Det.noHost c c' → MR ok mi c d →
    SR ok mi c.store d.store → DInv ok mi c.store → Res ok mi P c' d (aszs c.code)

theorem SimIH.mono {P : Numerics.Profile} {k k' : Nat} (h : SimIH ok mi P H k)
    (hk : k' ≤ k) : SimIH ok mi P H k' :=
  fun c c' d hsz => h c c' d (by omega)

variable (ok mi) in
/-- The result of a head step of `e` against the right code `Y`. -/
def HRes (P : Numerics.Profile) (t : Store H) (f : Frame) (args : List Val)
    (e : Admin) (Y : List Admin) (c₀ : Config H) : Prop :=
  ∃ c₀' : Config H, (Relation.TransGen (Step P Det.noHost) ⟨t, f, vals args ++ Y⟩ c₀' ∨
      (c₀' = ⟨t, f, vals args ++ Y⟩ ∧ aszs c₀.code < aszs (vals args ++ [e]))) ∧
    SR ok mi c₀.store c₀'.store ∧ c₀'.frame = c₀.frame ∧ GL ok mi f.module c₀.code c₀'.code

theorem head_module {P : Numerics.Profile} {s : Store H} {f : Frame} {args : List Val} {e : Admin}
    {c₀ : Config H} (hh : Det.Head P s f args e c₀) : c₀.frame.module = f.module :=
  GlobRead.step_frame_module hh.toStep

/-! ## Calls -/

theorem call_rel {s t : Store H} (hSR : SR ok mi s t) {a : Nat}
    {fi : FuncInst H} {code : Func} (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm code) :
    ∃ (fi' : FuncInst H) (code' : Func), t.funcs[a]? = some fi' ∧ fi'.type = fi.type ∧
      fi'.module = fi.module ∧ fi'.code = .wasm code' ∧ code'.locals = code.locals ∧
      GIL ok mi fi.module code.body code'.body := by
  obtain ⟨gi, hg, ht, hm, hc⟩ := hSR.get hf
  cases hgc : gi.code with
  | wasm g =>
    rw [hcode, hgc] at hc
    exact ⟨gi, g, hg, ht.symm, hm.symm, hgc, hc.2.1.symm, hc.2.2⟩
  | host h =>
    rw [hcode, hgc] at hc
    exact hc.elim

theorem head_callData {P : Numerics.Profile} {s t : Store H} {f : Frame} {args : List Val}
    {e e' : Admin} {c₀ : Config H} (hSR : SR ok mi s t) (he' : e'.IsCallRef)
    (hcd : CallData s f args e c₀) : HRes ok mi P t f args e [e'] c₀ := by
  obtain ⟨vs, a, fi, ps, rs, code, rfl, hc, hf, he, hn, hcode, rfl⟩ := hcd
  obtain ⟨fi', code', hf', ht, hm, hcode', hl, hb⟩ := call_rel hSR hf hcode
  refine ⟨_, .inl (tg_head (.callRefFunc rfl he' hf' (ht ▸ he) hn hcode')), hSR, rfl, ?_⟩
  rw [hm, hl]
  exact .cons (.frame (.cons (.label .nil (GL.of_GIL hb)) (.nil _))) (.nil _)

/-! ## Atomic heads -/

/-- Atomic heads related to themselves: the same head step. -/
theorem head_same {P : Numerics.Profile} {s t : Store H} {f : Frame}
    {args : List Val} {e : Admin} {c₀ : Config H} (hh : Det.Head P s f args e c₀)
    (hSR : SR ok mi s t) (hL : ∀ n c b, e ≠ .label n c b) (hH : ∀ n cs b, e ≠ .handler n cs b)
    (hF : ∀ n F b, e ≠ .frame n F b) : HRes ok mi P t f args e [e] c₀ := by
  by_cases hS : SimpleE e
  · rcases head_simple hh hS hSR.sameTypes f.locals with hcd | ⟨hfr, hfs, hN⟩
    · have hc : e.IsCallRef := by obtain ⟨_, _, _, _, _, _, -, hc, -⟩ := hcd; exact hc
      exact head_callData hSR hc hcd
    · obtain ⟨G, hG, rfl⟩ := hSR.cases
      exact ⟨⟨withFuncs c₀.store G, f, c₀.code⟩, .inl (tg_head hN),
        SR.mk' (by rw [hfs]; exact hG), hfr.symm, GL.refl _⟩
  · obtain ⟨G, hG, rfl⟩ := hSR.cases
    obtain ⟨s₀, f₀, is₀⟩ := c₀
    have hloc : ∃ x, e = .plain (.localGet x) ∨ e = .plain (.localSet x) ∨
        e = .plain (.localTee x) := by
      refine Classical.byContradiction fun hne => hS ⟨hL, hH, hF, ?_, ?_, ?_⟩
      · intro x hx; exact hne ⟨x, .inl hx⟩
      · intro x hx; exact hne ⟨x, .inr (.inl hx)⟩
      · intro x hx; exact hne ⟨x, .inr (.inr hx)⟩
    obtain ⟨x, hx⟩ := hloc
    have hfam : Det.famOf e = .variable := by rcases hx with rfl | rfl | rfl <;> rfl
    cases hh with
    | «variable» h =>
      obtain ⟨hfs, h'⟩ := variableStep_withFuncs h G
      exact ⟨⟨withFuncs s₀ G, f₀, is₀⟩, .inl (tg_head (.variable h')),
        SR.mk' (by simp only at hfs ⊢; rw [hfs]; exact hG), rfl, GL.refl _⟩
    | parametric h =>
      exact absurd ((Det.famOf_of_shape (Det.ParametricStep.shape h)).2.symm.trans hfam)
        (by decide)
    | numeric h =>
      exact absurd ((Det.famOf_of_shape (Det.NumericStep.shape h)).2.symm.trans hfam)
        (by decide)
    | vector h =>
      exact absurd ((Det.famOf_of_shape (Det.VectorStep.shape h)).2.symm.trans hfam) (by decide)
    | table h =>
      exact absurd ((Det.famOf_of_shape (Det.TableStep.shape h)).2.symm.trans hfam) (by decide)
    | memory h =>
      exact absurd ((Det.famOf_of_shape (Det.MemoryStep.shape h)).2.symm.trans hfam) (by decide)
    | reference h =>
      exact absurd ((Det.famOf_of_shape (Det.RefStep.shape h)).2.symm.trans hfam) (by decide)
    | aggregate h =>
      exact absurd ((Det.famOf_of_shape (Det.AggregateStep.shape h)).2.symm.trans hfam)
        (by decide)
    | _ => rcases hx with h | h | h <;> (try cases h) <;> simp_all [Admin.IsCallRef]

/-- Two call forms with different annotations: the same call. -/
theorem head_ann {P : Numerics.Profile} {s t : Store H} {f : Frame}
    {args : List Val} {e e' : Admin} {c₀ : Config H} (hh : Det.Head P s f args e c₀)
    (hSR : SR ok mi s t) (he : e.IsCallRef) (he' : e'.IsCallRef) :
    HRes ok mi P t f args e [e'] c₀ := by
  have hc := he
  unfold Admin.IsCallRef at hc
  split at hc
  all_goals first
    | exact hc.elim
    | (cases hh with
      | callRefNull =>
        exact ⟨_, .inl (tg_head (.callRefNull he')), hSR, rfl, GL.refl _⟩
      | callRefFunc ha _ hf he₁ hn hcode =>
        exact head_callData hSR he' ⟨_, _, _, _, _, _, ha, he, hf, he₁, hn, hcode, rfl⟩
      | _ => fam_dismiss)

/-! ## Inversions at non-site heads -/

theorem isCallRef_plain {i : Instr} (h : (Admin.plain i).IsCallRef) : ∃ z, i = .callRef z := by
  unfold Admin.IsCallRef at h
  split at h
  · rename_i z heq; cases heq; exact ⟨z, rfl⟩
  · rename_i heq; cases heq
  · exact h.elim

theorem isReturnCallRef_plain {i : Instr} (h : (Admin.plain i).IsReturnCallRef) :
    ∃ z, i = .returnCallRef z := by
  unfold Admin.IsReturnCallRef at h
  split at h
  · rename_i z heq; cases heq; exact ⟨z, rfl⟩
  · rename_i heq; cases heq
  · exact h.elim

/-- A non-structured, non-call plain instruction is related only to itself. -/
theorem GA.eq_plain {cur : ModuleInst} {i : Instr} {b : Admin} (hs : structuredInstr i = false)
    (hc : ∀ z, i ≠ .callRef z) (hr : ∀ z, i ≠ .returnCallRef z) (h : GA ok mi cur (.plain i) b) :
    b = .plain i := by
  cases h with
  | plain h => rw [GI.eq_of_flat h hs]
  | ann ha => obtain ⟨z, rfl⟩ := isCallRef_plain ha; exact absurd rfl (hc z)
  | retAnn ha => obtain ⟨z, rfl⟩ := isReturnCallRef_plain ha; exact absurd rfl (hr z)

theorem GL.split_pw {cur : ModuleInst} {V : List Val} {e : Admin} {rest ns : List Admin}
    (he : e.val? = none) (hT : e ≠ .trap) (hR : e ≠ .plain .throwRef)
    (hS : ∀ r t z, e ≠ .plain (ciI r t z)) (hG : ∀ t, e ≠ .plain (.tableGet t))
    (hC : ∀ z, e ≠ .plain (castY z)) (h : GL ok mi cur (vals V ++ e :: rest) ns) :
    ∃ e' rest', ns = vals V ++ e' :: rest' ∧ GA ok mi cur e e' ∧ GL ok mi cur rest rest' := by
  rcases GL.split he h with h | ⟨_, _, _, h | ⟨h, -⟩⟩ | ⟨_, _, _, _, _, _, _, -, h, -⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, -, h, -⟩ | ⟨_, _, _, _, _, _, _, _, _, _, -, h, -⟩
  · exact h
  · exact absurd h hT
  · exact absurd h hR
  · exact absurd h (hS _ _ _)
  · exact absurd h (hG _)
  · exact absurd h (hC _)

theorem flat_of {cur : ModuleInst} {b b' : List Admin} (hb : GL ok mi cur b b') {vs : List Val}
    {i : Instr} {rest : List Admin} (hs : structuredInstr i = false) (hc : ∀ z, i ≠ .callRef z)
    (hr : ∀ z, i ≠ .returnCallRef z) (hv : (Admin.plain i).val? = none) (hR : i ≠ .throwRef)
    (hS : ∀ r t z, i ≠ ciI r t z) (hG : ∀ t, i ≠ .tableGet t) (hC : ∀ z, i ≠ castY z)
    (hb' : b = vals vs ++ .plain i :: rest) : ∃ rest', b' = vals vs ++ .plain i :: rest' := by
  subst hb'
  obtain ⟨e', rest', rfl, he, -⟩ := GL.split_pw hv (by simp) (fun h => hR (Admin.plain.inj h))
    (fun r t z h => hS r t z (Admin.plain.inj h)) (fun t h => hG t (Admin.plain.inj h))
    (fun z h => hC z (Admin.plain.inj h)) hb
  exact ⟨rest', by rw [GA.eq_plain hs hc hr he]⟩

theorem flatY_br {cur : ModuleInst} {b b' : List Admin} (hb : GL ok mi cur b b') {vs : List Val}
    {l : LabelIdx} {rest : List Admin} (hb' : b = vals vs ++ .plain (.br l) :: rest) :
    ∃ rest', b' = vals vs ++ .plain (.br l) :: rest' :=
  flat_of hb rfl (fun _ h => by cases h) (fun _ h => by cases h) rfl (by simp)
    (fun r _ _ h => by cases r <;> cases h) (fun _ h => by cases h) (fun _ h => by cases h) hb'

theorem flatY_return {cur : ModuleInst} {b b' : List Admin} (hb : GL ok mi cur b b')
    {vs : List Val} {rest : List Admin} (hb' : b = vals vs ++ .plain .return_ :: rest) :
    ∃ rest', b' = vals vs ++ .plain .return_ :: rest' :=
  flat_of hb rfl (fun _ h => by cases h) (fun _ h => by cases h) rfl (by simp)
    (fun r _ _ h => by cases r <;> cases h) (fun _ h => by cases h) (fun _ h => by cases h) hb'

theorem retcall_of {cur : ModuleInst} {b b' : List Admin} (hb : GL ok mi cur b b') {vs : List Val}
    {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef) (hb' : b = vals vs ++ c :: rest) :
    ∃ c' rest', b' = vals vs ++ c' :: rest' ∧ c'.IsReturnCallRef := by
  subst hb'
  obtain ⟨e', rest', rfl, he, -⟩ := GL.split_pw (Det.IsReturnCallRef.val_none hc)
    (by rintro rfl; exact hc) (by rintro rfl; exact hc)
    (fun r t z h => by subst h; cases r <;> exact hc) (fun t h => by subst h; exact hc)
    (fun z h => by subst h; exact hc) hb
  refine ⟨e', rest', rfl, ?_⟩
  cases he with
  | plain h =>
    obtain ⟨z, rfl⟩ := isReturnCallRef_plain hc
    rw [GI.eq_of_flat h rfl]; trivial
  | ann ha =>
    exfalso
    unfold Admin.IsCallRef at ha
    split at ha
    · obtain ⟨z, h⟩ := isReturnCallRef_plain hc; cases h
    · exact hc
    · exact ha
  | retAnn _ hb => exact hb
  | ref => exact hc.elim
  | label => exact hc.elim
  | handler => exact hc.elim
  | frame => exact hc.elim
  | trap => exact hc.elim

theorem throw_of {cur : ModuleInst} {b b' : List Admin} (hb : GL ok mi cur b b') {a : Nat}
    (h : b = throwing a) : b' = throwing a := by
  subst h
  exact GL.result_inv (r := .throw a) hb

theorem trap_of {cur : ModuleInst} {b b' : List Admin} (hb : GL ok mi cur b b')
    (h : b = [.trap]) : b' = [.trap] := by
  subst h
  exact GL.result_inv (r := .trap) hb

theorem structured_cases {i : Instr} (hs : structuredInstr i = true) :
    (∃ bt b, i = .block bt b) ∨ (∃ bt b, i = .loop bt b) ∨ (∃ bt t e, i = .if_ bt t e) ∨
      ∃ bt cs b, i = .tryTable bt cs b := by
  cases i <;> simp_all [structuredInstr]

section heads

variable {P : Numerics.Profile} {s t : Store H} {f : Frame} {args : List Val}
  {c₀ : Config H}

theorem head_block {bt : BlockType} {b b' : List Instr} (hb : GIL ok mi f.module b b')
    (hh : Det.Head P s f args (.plain (.block bt b)) c₀) (hSR : SR ok mi s t) :
    HRes ok mi P t f args (.plain (.block bt b)) [.plain (.block bt b')] c₀ := by
  cases hh with
  | block hbt hm =>
    exact ⟨_, .inl (tg_head (.block hbt hm)), hSR, rfl,
      .cons (.label .nil (GL.append (GL.of_vals _) (GL.of_GIL hb))) (.nil _)⟩
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

theorem head_loop {bt : BlockType} {b b' : List Instr} (hb : GIL ok mi f.module b b')
    (hh : Det.Head P s f args (.plain (.loop bt b)) c₀) (hSR : SR ok mi s t) :
    HRes ok mi P t f args (.plain (.loop bt b)) [.plain (.loop bt b')] c₀ := by
  cases hh with
  | loop hbt hm =>
    exact ⟨_, .inl (tg_head (.loop hbt hm)), hSR, rfl,
      .cons (.label (.cons (.loop hb) .nil) (GL.append (GL.of_vals _) (GL.of_GIL hb))) (.nil _)⟩
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

theorem head_if {bt : BlockType} {b₁ b₁' b₂ b₂' : List Instr} (h₁ : GIL ok mi f.module b₁ b₁')
    (h₂ : GIL ok mi f.module b₂ b₂') (hh : Det.Head P s f args (.plain (.if_ bt b₁ b₂)) c₀)
    (hSR : SR ok mi s t) :
    HRes ok mi P t f args (.plain (.if_ bt b₁ b₂)) [.plain (.if_ bt b₁' b₂')] c₀ := by
  cases hh with
  | ifTrue hc =>
    exact ⟨_, .inl (tg_head (.ifTrue hc)), hSR, rfl, .cons (.plain (.block h₁)) (.nil _)⟩
  | ifFalse hc =>
    exact ⟨_, .inl (tg_head (.ifFalse hc)), hSR, rfl, .cons (.plain (.block h₂)) (.nil _)⟩
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

theorem head_tryTable {bt : BlockType} {cs : List Catch} {b b' : List Instr}
    (hb : GIL ok mi f.module b b')
    (hh : Det.Head P s f args (.plain (.tryTable bt cs b)) c₀) (hSR : SR ok mi s t) :
    HRes ok mi P t f args (.plain (.tryTable bt cs b)) [.plain (.tryTable bt cs b')] c₀ := by
  cases hh with
  | tryTable hbt hm =>
    exact ⟨_, .inl (tg_head (.tryTable hbt hm)), hSR, rfl,
      .cons (.handler (.cons (.label .nil (GL.append (GL.of_vals _) (GL.of_GIL hb))) (.nil _)))
        (.nil _)⟩
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

theorem head_plain {i i' : Instr} (hi : GI ok mi f.module i i')
    (hh : Det.Head P s f args (.plain i) c₀) (hSR : SR ok mi s t) :
    HRes ok mi P t f args (.plain i) [.plain i'] c₀ := by
  cases hi with
  | flat i =>
    by_cases hs : structuredInstr i = true
    · rcases structured_cases hs with ⟨bt, b, rfl⟩ | ⟨bt, b, rfl⟩ | ⟨bt, b₁, b₂, rfl⟩ |
        ⟨bt, cs, b, rfl⟩
      · exact head_block (GIL.refl b) hh hSR
      · exact head_loop (GIL.refl b) hh hSR
      · exact head_if (GIL.refl b₁) (GIL.refl b₂) hh hSR
      · exact head_tryTable (GIL.refl b) hh hSR
    · exact head_same hh hSR (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
        (fun _ _ _ h => by cases h)
  | block h => exact head_block h hh hSR
  | loop h => exact head_loop h hh hSR
  | if_ h₁ h₂ => exact head_if h₁ h₂ hh hSR
  | tryTable h => exact head_tryTable h hh hSR

/-- Labels with related continuations and bodies. -/
theorem head_label {n : Nat} {c c' : List Instr} {b b' : List Admin}
    (IH : SimIH ok mi P H (sizeOf (Admin.label n c b))) (hinv : DInv ok mi s)
    (hh : Det.Head P s f args (.label n c b) c₀) (hc : GIL ok mi f.module c c')
    (hb : GL ok mi f.module b b')
    (hSR : SR ok mi s t) : HRes ok mi P t f args (.label n c b) [.label n c' b'] c₀ := by
  cases hh with
  | ctxtLabel h =>
    rename_i s' f' b₁
    have hsz : sizeOf b < sizeOf (Admin.label n c b) := Exec.Drv.sizeOf_label_body
    obtain ⟨d₁, ⟨hfr₁, hrel⟩, hsr, hprog⟩ := IH ⟨s, f, b⟩ ⟨s', f', b₁⟩ ⟨t, f, b'⟩ hsz h
      ⟨rfl, hb⟩ hSR hinv
    have hm : f'.module = f.module := GlobRead.step_frame_module h
    simp only at hrel
    rw [hm] at hrel
    refine ⟨⟨d₁.store, d₁.frame, [.label n c' d₁.code]⟩, ?_, hsr, hfr₁.symm,
      .cons (.label hc hrel) (.nil _)⟩
    rcases hprog with hp | ⟨rfl, hw⟩
    · exact .inl (tg_label hp n c')
    · exact .inr ⟨rfl, by simp at hw ⊢; omega⟩
  | labelVals hb' =>
    subst hb'
    rw [GL.vals_inv hb]
    exact ⟨_, .inl (tg_head (.labelVals rfl)), hSR, rfl, GL.refl _⟩
  | brLabelZero hb' hl hn =>
    rename_i vs' vs l rest
    have e : vals vs' ++ vals vs ++ [Admin.plain (.br l)] ++ rest =
        vals (vs' ++ vs) ++ .plain (.br l) :: rest := by simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flatY_br hb hb'
    exact ⟨_, .inl (tg_head (.brLabelZero (vs' := vs') (vs := vs) (rest := rest') (by simp) hl hn)),
      hSR, rfl, GL.append (GL.of_vals _) (GL.of_GIL hc)⟩
  | brLabelSucc hb' hl =>
    rename_i vs l rest
    have e : vals vs ++ [Admin.plain (.br l)] ++ rest = vals vs ++ .plain (.br l) :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flatY_br hb hb'
    exact ⟨_, .inl (tg_head (.brLabelSucc (rest := rest') (by simp) hl)), hSR, rfl, GL.refl _⟩
  | returnCallRefLabel hb' hc' =>
    rename_i vs c'' rest
    have e : vals vs ++ [c''] ++ rest = vals vs ++ c'' :: rest := by simp
    rw [e] at hb'
    obtain ⟨c₂, rest', rfl, hc₂⟩ := retcall_of hb hc' hb'
    exact ⟨_, .inl (tg_head (.returnCallRefLabel (rest := rest') (by simp) hc₂)), hSR, rfl,
      GL.append (GL.of_vals vs) (.cons (.retAnn hc' hc₂) (.nil _))⟩
  | returnLabel hb' =>
    rename_i vs rest
    have e : vals vs ++ [Admin.plain .return_] ++ rest = vals vs ++ .plain .return_ :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flatY_return hb hb'
    exact ⟨_, .inl (tg_head (.returnLabel (rest := rest') (by simp))), hSR, rfl, GL.refl _⟩
  | throwRefLabel =>
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head .throwRefLabel), hSR, rfl, GL.refl _⟩
  | trapLabel =>
    rw [trap_of hb rfl]
    exact ⟨_, .inl (tg_head .trapLabel), hSR, rfl, GL.refl _⟩
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

/-- Handlers with related bodies. -/
theorem head_handler {n : Nat} {cs : List Catch} {b b' : List Admin}
    (IH : SimIH ok mi P H (sizeOf (Admin.handler n cs b))) (hinv : DInv ok mi s)
    (hh : Det.Head P s f args (.handler n cs b) c₀) (hb : GL ok mi f.module b b')
    (hSR : SR ok mi s t) : HRes ok mi P t f args (.handler n cs b) [.handler n cs b'] c₀ := by
  cases hh with
  | ctxtHandler h =>
    rename_i s' f' b₁
    have hsz : sizeOf b < sizeOf (Admin.handler n cs b) := Exec.Drv.sizeOf_handler_body
    obtain ⟨d₁, ⟨hfr₁, hrel⟩, hsr, hprog⟩ := IH ⟨s, f, b⟩ ⟨s', f', b₁⟩ ⟨t, f, b'⟩ hsz h
      ⟨rfl, hb⟩ hSR hinv
    have hm : f'.module = f.module := GlobRead.step_frame_module h
    simp only at hrel
    rw [hm] at hrel
    refine ⟨⟨d₁.store, d₁.frame, [.handler n cs d₁.code]⟩, ?_, hsr, hfr₁.symm,
      .cons (.handler hrel) (.nil _)⟩
    rcases hprog with hp | ⟨rfl, hw⟩
    · exact .inl (tg_handler hp n cs)
    · exact .inr ⟨rfl, by simp [asz] at hw ⊢; omega⟩
  | brHandler hb' =>
    rename_i vs l rest
    have e : vals vs ++ [Admin.plain (.br l)] ++ rest = vals vs ++ .plain (.br l) :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flatY_br hb hb'
    exact ⟨_, .inl (tg_head (.brHandler (rest := rest') (by simp))), hSR, rfl, GL.refl _⟩
  | returnCallRefHandler hb' hc =>
    rename_i vs c' rest
    have e : vals vs ++ [c'] ++ rest = vals vs ++ c' :: rest := by simp
    rw [e] at hb'
    obtain ⟨c₂, rest', rfl, hc₂⟩ := retcall_of hb hc hb'
    exact ⟨_, .inl (tg_head (.returnCallRefHandler (rest := rest') (by simp) hc₂)), hSR, rfl,
      GL.append (GL.of_vals vs) (.cons (.retAnn hc hc₂) (.nil _))⟩
  | returnHandler hb' =>
    rename_i vs rest
    have e : vals vs ++ [Admin.plain .return_] ++ rest = vals vs ++ .plain .return_ :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flatY_return hb hb'
    exact ⟨_, .inl (tg_head (.returnHandler (rest := rest') (by simp))), hSR, rfl, GL.refl _⟩
  | throwRefHandlerEmpty =>
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head .throwRefHandlerEmpty), hSR, rfl, GL.refl _⟩
  | throwRefHandlerCatch he ht =>
    obtain ⟨G, hG, rfl⟩ := hSR.cases
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head (.throwRefHandlerCatch he ht)), SR.mk' hG, rfl, GL.refl _⟩
  | throwRefHandlerCatchRef he ht =>
    obtain ⟨G, hG, rfl⟩ := hSR.cases
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head (.throwRefHandlerCatchRef he ht)), SR.mk' hG, rfl, GL.refl _⟩
  | throwRefHandlerCatchAll =>
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head .throwRefHandlerCatchAll), hSR, rfl, GL.refl _⟩
  | throwRefHandlerCatchAllRef =>
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head .throwRefHandlerCatchAllRef), hSR, rfl, GL.refl _⟩
  | throwRefHandlerNext h =>
    obtain ⟨G, hG, rfl⟩ := hSR.cases
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head (.throwRefHandlerNext h)), SR.mk' hG, rfl, GL.refl _⟩
  | handlerVals hb' =>
    subst hb'
    rw [GL.vals_inv hb]
    exact ⟨_, .inl (tg_head (.handlerVals rfl)), hSR, rfl, GL.refl _⟩
  | trapHandler =>
    rw [trap_of hb rfl]
    exact ⟨_, .inl (tg_head .trapHandler), hSR, rfl, GL.refl _⟩
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

/-- Activations with related bodies (equal frames), related at the activation's instance. -/
theorem head_frame {k : Nat} {F : Frame} {b b' : List Admin}
    (IH : SimIH ok mi P H (sizeOf (Admin.frame k F b))) (hinv : DInv ok mi s)
    (hh : Det.Head P s f args (.frame k F b) c₀) (hb : GL ok mi F.module b b')
    (hSR : SR ok mi s t) : HRes ok mi P t f args (.frame k F b) [.frame k F b'] c₀ := by
  cases hh with
  | ctxtFrame h =>
    rename_i s' F₁ b₁
    have hsz : sizeOf b < sizeOf (Admin.frame k F b) := Exec.Drv.sizeOf_frame_body
    obtain ⟨d₁, ⟨hfr₁, hrel⟩, hsr, hprog⟩ := IH ⟨s, F, b⟩ ⟨s', F₁, b₁⟩ ⟨t, F, b'⟩ hsz h
      ⟨rfl, hb⟩ hSR hinv
    have e : F₁ = d₁.frame := hfr₁
    refine ⟨⟨d₁.store, f, [.frame k d₁.frame d₁.code]⟩, ?_, hsr, rfl, ?_⟩
    · rcases hprog with hp | ⟨rfl, hw⟩
      · exact .inl (tg_frame hp k f)
      · exact .inr ⟨rfl, by simp [asz] at hw ⊢; omega⟩
    · rw [← e]
      exact .cons (.frame hrel) (.nil _)
  | frameVals hb' hn =>
    subst hb'
    rw [GL.vals_inv hb]
    exact ⟨_, .inl (tg_head (.frameVals rfl hn)), hSR, rfl, GL.refl _⟩
  | returnFrame hb' hn =>
    rename_i vs' vs rest
    have e : vals vs' ++ vals vs ++ [Admin.plain .return_] ++ rest =
        vals (vs' ++ vs) ++ .plain .return_ :: rest := by simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flatY_return hb hb'
    exact ⟨_, .inl (tg_head (.returnFrame (vs' := vs') (rest := rest') (by simp) hn)), hSR, rfl,
      GL.refl _⟩
  | returnCallRefFrameNull hb' hc =>
    rename_i vs c rest
    have e : vals vs ++ [Admin.ref .null, c] ++ rest = vals (vs ++ [.ref .null]) ++ c :: rest := by
      simp [vals, Val.toAdmin]
    rw [e] at hb'
    obtain ⟨c₂, rest', rfl, hc₂⟩ := retcall_of hb hc hb'
    have e' : vals (vs ++ [.ref .null]) ++ c₂ :: rest' = vals vs ++ [Admin.ref .null, c₂] ++ rest' :=
      by simp [vals, Val.toAdmin]
    rw [e']
    exact ⟨_, .inl (tg_head (.returnCallRefFrameNull rfl hc₂)), hSR, rfl, GL.refl _⟩
  | returnCallRefFrameAddr hb' hc hf he hn =>
    rename_i vs' vs a c rest fi ps rs
    have e : vals vs' ++ vals vs ++ [Admin.ref (.func a), c] ++ rest =
        vals (vs' ++ vs ++ [.ref (.func a)]) ++ c :: rest := by
      simp [vals, Val.toAdmin]
    rw [e] at hb'
    obtain ⟨c₂, rest', rfl, hc₂⟩ := retcall_of hb hc hb'
    have e' : vals (vs' ++ vs ++ [.ref (.func a)]) ++ c₂ :: rest' =
        vals vs' ++ vals vs ++ [Admin.ref (.func a), c₂] ++ rest' := by
      simp [vals, Val.toAdmin]
    rw [e']
    obtain ⟨fi', hf', ht⟩ := hSR.sameTypes.get hf
    have hN := Det.Head.returnCallRefFrameAddr (P := P) (s := t) (f := f) (fi := F) (k := k)
      (vs' := vs') (vs := vs) (rest := rest') rfl hc₂ hf' (ht ▸ he) hn
    exact ⟨_, .inl (tg_head hN), hSR, rfl, GL.append (GL.of_vals vs) (.cons (.ref _ _)
      (.cons (.ann (isCallRef_retToCallIn hc _) (isCallRef_retToCallIn hc₂ _)) (.nil _)))⟩
  | throwRefFrame =>
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head .throwRefFrame), hSR, rfl, GL.refl _⟩
  | trapFrame =>
    rw [trap_of hb rfl]
    exact ⟨_, .inl (tg_head .trapFrame), hSR, rfl, GL.refl _⟩
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


/-- **Related head steps** (the pointwise case). -/
theorem head_rel {e e' : Admin} (IH : SimIH ok mi P H (sizeOf e))
    (hinv : DInv ok mi s)
    (hh : Det.Head P s f args e c₀) (he : GA ok mi f.module e e') (hSR : SR ok mi s t) :
    HRes ok mi P t f args e [e'] c₀ := by
  have hgood := hh.good
  cases he with
  | plain hi => exact head_plain hi hh hSR
  | ref _ r => exact absurd hgood.val_none (by simp)
  | ann ha hb => exact head_ann hh hSR ha hb
  | retAnn ha _ => exact absurd (Det.IsReturnCallRef.blocked ha) hgood.not_blocked
  | label hc hb => exact head_label IH hinv hh hc hb hSR
  | handler hb => exact head_handler IH hinv hh hb hSR
  | frame hb => exact head_frame IH hinv hh hb hSR
  | trap _ => exact absurd rfl hgood.ne_trap

end heads

/-! ## The simulation -/

section main

variable {P : Numerics.Profile}

variable {o : Numerics.GrowKind → Nat → Nat → Nat → Bool}

local notation "PD" => Numerics.Profile.deterministic o

theorem lift_tg {P : Numerics.Profile} {t t' : Store H} {f f' : Frame} {vs args : List Val}
    {Y code' rest' : List Admin}
    (h : Relation.TransGen (Step P Det.noHost) ⟨t, f, vals args ++ Y⟩ ⟨t', f', code'⟩) :
    Relation.TransGen (Step P Det.noHost) ⟨t, f, vals (vs ++ args) ++ (Y ++ rest')⟩
      ⟨t', f', vals vs ++ code' ++ rest'⟩ := by
  have := tg_instrs h vs rest'
  simpa using this

/-- A non-control head whose operands end the value prefix is determined by any one of its
head steps. -/
theorem head_det_last {s : Store H} {f : Frame} {args vs V₀ : List Val} {v : Val} {e : Admin}
    {c₀ c₂ : Config H} (hc : Det.famOf e ≠ .control) (hh : Det.Head PD s f args e c₀)
    (h₂ : Det.Head PD s f [v] e c₂) (hV : vs ++ args = V₀ ++ [v]) :
    vs = V₀ ∧ args = [v] ∧ c₀ = c₂ := by
  rcases List.eq_nil_or_concat args with rfl | ⟨L, w, rfl⟩
  · have := (Det.Head.det_fam hc h₂ hh (p := [v]) (by simp)).1
    cases this
  · simp only [List.concat_eq_append] at hh hV ⊢
    rw [← List.append_assoc] at hV
    obtain ⟨hL, hw⟩ := List.append_inj' hV rfl
    obtain rfl := List.singleton_inj.mp hw
    obtain ⟨rfl, rfl⟩ := Det.Head.det_fam hc hh h₂ (p := L) rfl
    exact ⟨by simpa using hL, rfl, rfl⟩

theorem aszs_vals_append (V : List Val) (l : List Admin) :
    aszs (vals V ++ l) = aszs (vals V) + aszs l := aszs_append _ _

theorem asz_crI (r : Bool) (y : TypeIdx) : asz (.plain (crI r y)) = 2 := by cases r <;> rfl

/-- **The site, first step**: `call_indirect` unfolds while the right side steps `call`. -/
theorem sim_s0 {s t : Store H} {f : Frame} {vs args V₀ : List Val} {r : Bool} {tt : TableIdx}
    {kk : BitVec 32} {y : TypeIdx} {fx : FuncIdx} {rest ns' : List Admin} {c₀ : Config H} {w : Nat}
    (hinv : DInv ok mi s) (hh : Det.Head P s f args (.plain (ciI r tt y)) c₀)
    (hV : vs ++ args = V₀ ++ [.i32 kk]) (hq : f.module = mi) (hok : ok tt kk y fx)
    (hns : GL ok mi f.module rest ns') (hSR : SR ok mi s t) :
    Res ok mi P ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩
      ⟨t, f, vals V₀ ++ .plain (clI r fx) :: ns'⟩ w := by
  have hc : args = [] ∧ c₀ = ⟨s, f, [.plain (.tableGet tt), .plain (castY y), .plain (crI r y)]⟩ := by
    cases r <;> simp only [ciI] at hh <;> cases hh <;> first | exact ⟨rfl, rfl⟩ | fam_dismiss |
      simp_all [Admin.IsCallRef]
  obtain ⟨rfl, rfl⟩ := hc
  simp only [List.append_nil] at hV
  subst hV
  obtain ⟨a, ta, ti, hfa, hta, hti, hk, hcast, halt⟩ := hinv tt kk y fx hok
  have hlt : a < t.funcs.length := by rw [hSR.length]; exact halt
  obtain ⟨gi, hgi⟩ : ∃ gi, t.funcs[a]? = some gi := ⟨_, List.getElem?_eq_getElem hlt⟩
  have hx : f.module.funcs[fx.toNat]? = some a := by rw [hq]; exact hfa
  have hstep : Relation.TransGen (Step P Det.noHost) ⟨t, f, vals [] ++ [.plain (clI r fx)]⟩
      ⟨t, f, [.ref (.func a), crT r gi.type]⟩ := by
    cases r
    · exact tg_head (.call hx hgi)
    · exact tg_head (.returnCall hx hgi)
  refine ⟨⟨t, f, vals V₀ ++ [.ref (.func a), crT r gi.type] ++ ns'⟩, ⟨rfl, ?_⟩, hSR,
    .inl (by simpa using lift_tg (vs := V₀) (rest' := ns') hstep)⟩
  simpa [vals, constI32, Val.toAdmin, Val.i32] using
    GL.append (GL.of_vals (ok := ok) (mi := mi) (cur := f.module) V₀)
      (GL.s1 (d := gi.type) (r := r) hq hok hfa hns)

/-- **The site, second step**: `table.get` reads the slot; the right side stays. -/
theorem sim_s1 {s t : Store H} {f : Frame} {vs args V₀ : List Val} {r : Bool} {tt : TableIdx}
    {kk : BitVec 32} {y : TypeIdx} {fx : FuncIdx} {a : Nat} {d : DefType} {os ns' : List Admin}
    {c₀ : Config H}
    (hinv : DInv ok mi s) (hh : Det.Head P s f args (.plain (.tableGet tt)) c₀)
    (hV : vs ++ args = V₀ ++ [.i32 kk]) (hq : f.module = mi) (hok : ok tt kk y fx)
    (hfa : mi.funcs[fx.toNat]? = some a)
    (hns : GL ok mi f.module os ns') (hSR : SR ok mi s t) :
    Res ok mi P ⟨c₀.store, c₀.frame,
        vals vs ++ c₀.code ++ (.plain (castY y) :: .plain (crI r y) :: os)⟩
      ⟨t, f, vals V₀ ++ .ref (.func a) :: crT r d :: ns'⟩
      (aszs (vals vs ++ (vals args ++ .plain (.tableGet tt) ::
        .plain (castY y) :: .plain (crI r y) :: os))) := by
  obtain ⟨a', ta, ti, hfa', hta, hti, hk, -, -⟩ := hinv tt kk y fx hok
  rw [hfa] at hfa'
  cases hfa'
  have ht : s.table? f tt = some (ta, ti) := by simp [Store.table?, hq, hta, hti]
  have h₂ : Det.Head (Numerics.Profile.deterministic (fun _ _ _ _ => false)) s f [.i32 kk] (.plain (.tableGet tt)) ⟨s, f, [.ref (.func a)]⟩ :=
    .table (TableStep.getVal (a := .i32) (i := kk) ht hk)
  obtain ⟨rfl, rfl, rfl⟩ := head_det_last (by simp [Det.famOf]) (head_tableGet_profile hh) h₂ hV
  refine ⟨⟨t, f, vals vs ++ .ref (.func a) :: crT r d :: ns'⟩, ⟨rfl, ?_⟩, hSR, .inr ⟨rfl, ?_⟩⟩
  · simpa using GL.append (GL.of_vals (ok := ok) (mi := mi) (cur := f.module) vs)
      (GL.s2 (d := d) (r := r) hq hok hfa hns)
  · simp only [aszs_append, aszs_cons, asz_crI]
    simp [vals, Val.toAdmin, Val.i32, asz, isz, castY]
    omega

/-- **The site, third step**: `ref.cast` succeeds; the right side stays. -/
theorem sim_s2 {s t : Store H} {f : Frame} {vs args V₀ : List Val} {r : Bool} {tt : TableIdx}
    {kk : BitVec 32} {y : TypeIdx} {fx : FuncIdx} {a : Nat} {d : DefType} {os ns' : List Admin}
    {c₀ : Config H}
    (hinv : DInv ok mi s) (hh : Det.Head P s f args (.plain (castY y)) c₀)
    (hV : vs ++ args = V₀ ++ [.ref (.func a)]) (hq : f.module = mi) (hok : ok tt kk y fx)
    (hfa : mi.funcs[fx.toNat]? = some a)
    (hns : GL ok mi f.module os ns') (hSR : SR ok mi s t) :
    Res ok mi P ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ (.plain (crI r y) :: os)⟩
      ⟨t, f, vals V₀ ++ .ref (.func a) :: crT r d :: ns'⟩
      (aszs (vals vs ++ (vals args ++ .plain (castY y) :: .plain (crI r y) :: os))) := by
  obtain ⟨a', ta, ti, hfa', -, -, -, hcast, -⟩ := hinv tt kk y fx hok
  rw [hfa] at hfa'
  cases hfa'
  have hcast' : RefOk s (.func a) (f.module.instRef ⟨true, .typeIdx y⟩) := by rw [hq]; exact hcast
  have h₂ : Det.Head (Numerics.Profile.deterministic (fun _ _ _ _ => false)) s f [.ref (.func a)] (.plain (castY y)) ⟨s, f, [.ref (.func a)]⟩ :=
    .reference (RefStep.castSucceed hcast')
  obtain ⟨rfl, rfl, rfl⟩ := head_det_last (by simp [Det.famOf]) (head_refCast_profile hh) h₂ hV
  refine ⟨⟨t, f, vals vs ++ .ref (.func a) :: crT r d :: ns'⟩, ⟨rfl, ?_⟩, hSR, .inr ⟨rfl, ?_⟩⟩
  · simpa using GL.append (GL.of_vals (ok := ok) (mi := mi) (cur := f.module) vs)
      (GL.cons (.ref _ _) (GL.cons (GA.crI_crT r y d) hns))
  · simp only [aszs_append, aszs_cons, asz_crI]
    simp [vals, Val.toAdmin, asz, isz, castY]
    omega

theorem sim_head {k : Nat} (IH : SimIH ok mi P H k) {s t : Store H} {f : Frame}
    {vs args : List Val} {e : Admin} {rest ns : List Admin} {c₀ : Config H}
    (hsz : sizeOf (vals vs ++ (vals args ++ e :: rest)) < k + 1) (hinv : DInv ok mi s)
    (hh : Det.Head P s f args e c₀)
    (hrel : GL ok mi f.module (vals vs ++ (vals args ++ e :: rest)) ns)
    (hSR : SR ok mi s t) :
    Res ok mi P ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩ ⟨t, f, ns⟩
      (aszs (vals vs ++ (vals args ++ e :: rest))) := by
  have hlt := sizeOf_head_lt (vs := vs) (args := args) (e := e) (rest := rest)
  have hmod := head_module hh
  have hgood := hh.good
  rw [headDec_code] at hrel
  rcases GL.split hgood.val_none hrel with ⟨e', rest', rfl, he, hr⟩ | ⟨rest', rfl, -, hd⟩ |
      ⟨V₀, r, tt, kk, y, fx, ns', hV, rfl, hq, hok, rfl, hns⟩ |
      ⟨V₀, r, tt, kk, y, fx, a, d, os, ns', hV, rfl, rfl, hq, hok, hfa, rfl, hns⟩ |
      ⟨V₀, r, tt, kk, y, fx, a, d, os, ns', hV, rfl, rfl, hq, hok, hfa, rfl, hns⟩
  · obtain ⟨c₀', hprog, hsr, hfr, hrel'⟩ := head_rel (IH.mono (by omega)) hinv hh he hSR
    refine ⟨⟨c₀'.store, c₀'.frame, vals vs ++ c₀'.code ++ rest'⟩, ⟨hfr.symm, ?_⟩, hsr, ?_⟩
    · simp only
      rw [hmod]
      exact GL.append (GL.append (GL.of_vals vs) hrel') hr
    · rcases hprog with hp | ⟨rfl, hw⟩
      · left
        have := lift_tg (vs := vs) (Y := [e']) (rest' := rest') hp
        simpa using this
      · right
        refine ⟨by simp, ?_⟩
        simp only [aszs_append, aszs_cons, aszs_nil] at hw ⊢
        omega
  · exfalso
    rcases hd with rfl | ⟨rfl, V₀, a, hV⟩
    · exact hgood.ne_trap rfl
    · have := hgood.throwRef rfl
      subst this
      obtain ⟨-, hw⟩ := List.append_inj' hV rfl
      cases hw
  · exact sim_s0 hinv hh hV hq hok hns hSR
  · exact sim_s1 hinv hh hV hq hok hfa hns hSR
  · exact sim_s2 hinv hh hV hq hok hfa hns hSR

theorem bubble_inv {cur : ModuleInst} {V : List Val} {X rest ns : List Admin}
    (hX : Det.IsBubble X) (h : GL ok mi cur (vals V ++ X ++ rest) ns) :
    ∃ rest', ns = vals V ++ X ++ rest' := by
  rcases hX with rfl | ⟨a, rfl⟩
  · rw [List.append_assoc, List.singleton_append] at h
    rcases GL.split (by simp [Admin.val?]) h with ⟨e', rest', rfl, he, -⟩ | ⟨rest', rfl, -⟩ |
        ⟨_, _, _, _, _, _, _, -, h, -⟩ | ⟨_, _, _, _, _, _, _, _, _, _, -, h, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, -, h, -⟩
    · have : e' = .trap := by
        cases he with
        | trap => rfl
        | ann ha => exact ha.elim
        | retAnn ha => exact ha.elim
      subst this
      exact ⟨rest', by simp⟩
    · exact ⟨rest', by simp⟩
    · cases h
    · cases h
    · cases h
  · have e : vals V ++ [Admin.ref (.exn a), .plain .throwRef] ++ rest =
        vals (V ++ [.ref (.exn a)]) ++ .plain .throwRef :: rest := by simp [vals, Val.toAdmin]
    rw [e] at h
    rcases GL.split rfl h with ⟨e', rest', rfl, he, -⟩ | ⟨rest', rfl, -⟩ |
        ⟨_, r, _, _, _, _, _, -, h, -⟩ | ⟨_, _, _, _, _, _, _, _, _, _, -, h, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, -, h, -⟩
    · rw [GA.eq_plain rfl (fun _ h => by cases h) (fun _ h => by cases h) he]
      exact ⟨rest', by simp [vals, Val.toAdmin]⟩
    · exact ⟨rest', by simp [vals, Val.toAdmin]⟩
    · cases r <;> cases h
    · cases h
    · cases h

theorem dead_rel {cur : ModuleInst} (pp : List Val) {X : List Admin} (hX : Det.IsBubble X)
    (r : List Admin) : GL ok mi cur (vals pp ++ X ++ r) (vals pp ++ X) := by
  by_cases hr : r = []
  · subst hr; simpa using GL.refl _
  · rw [List.append_assoc]
    refine GL.append (GL.of_vals pp) ?_
    rcases hX with rfl | ⟨a, rfl⟩
    · simpa using GL.deadTrap (ok := ok) (mi := mi) (cur := cur) (ns := []) hr
    · simpa using GL.deadThrow (ok := ok) (mi := mi) (cur := cur) (a := a) (ns := []) hr

theorem sim_bubble {P : Numerics.Profile} {s t : Store H} {f : Frame} {pp q : List Val}
    {X u r ns : List Admin} (hX : Det.IsBubble X) (hqu : q ≠ [] ∨ u ≠ [])
    (hrel : GL ok mi f.module (vals (pp ++ q) ++ X ++ (u ++ r)) ns) (hSR : SR ok mi s t) :
    Res ok mi P ⟨s, f, vals pp ++ X ++ r⟩ ⟨t, f, ns⟩ (aszs (vals (pp ++ q) ++ X ++ (u ++ r))) := by
  obtain ⟨rest', rfl⟩ := bubble_inv hX hrel
  by_cases hq : q ≠ [] ∨ rest' ≠ []
  · refine ⟨⟨t, f, vals pp ++ X ++ []⟩, ⟨rfl, by simpa using dead_rel pp hX r⟩, hSR,
      .inl (.single (Det.Bubble.toStep ⟨pp, q, X, rest', [], by simp, hX, hq, rfl⟩))⟩
  · simp only [ne_eq, not_or, not_not] at hq
    obtain ⟨rfl, rfl⟩ := hq
    have hu : u ≠ [] := hqu.resolve_left (fun h => h rfl)
    have hpos := aszs_pos hu
    refine ⟨⟨t, f, vals (pp ++ []) ++ X ++ []⟩, ⟨rfl, by simpa using dead_rel pp hX r⟩, hSR,
      .inr ⟨rfl, ?_⟩⟩
    simp only [aszs_append, List.append_nil] at hpos ⊢
    omega

/-- **One step.** Every host-free step of the left configuration from an invariant store is
simulated. -/
theorem sim : ∀ k : Nat, SimIH ok mi P H k
  | 0 => fun _ _ _ hsz => absurd hsz (Nat.not_lt_zero _)
  | k + 1 => fun c c' d hsz hstep hMR hSR hinv => by
    have IH := sim k
    obtain ⟨s, f, code⟩ := c
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

end main

end Silmaril.Wasm.Binaryen.DirSim
