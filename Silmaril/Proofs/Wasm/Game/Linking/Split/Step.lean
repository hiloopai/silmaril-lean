module

public import Silmaril.Proofs.Wasm.Game.Linking.Split.Aggregate

/-!
# Static linking, separation: Silmaril.Games.Step

Original module documentation:

# Part steps in the shared store (M3 step B, #1977)

Game semantics of WebAssembly modules (tracking issue #1982), milestone M3, step (B).

`step_sim`: a host-free Core step of a part (provider or consumer, in its own store `p`) from a
configuration that holds only owned references and module instances is matched by one
host-free Core step of the renamed configuration in the shared store `σ`; the relation
`PartRel` is re-established for a grown ownership, and the shared store changes only at what
the part owns (`Touch`), so the relation of the other part survives (`PartRel.touch`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Game.Linking.Split

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Numerics

variable {H : Type}

theorem Ren.code_callRef (ρ : Ren) {c : Admin} (hc : c.IsCallRef) (l : List Admin) :
    ρ.code (c :: l) = c :: ρ.code l := by
  cases c <;> simp_all [Admin.IsCallRef]

theorem Ren.code_returnCallRef (ρ : Ren) {c : Admin} (hc : c.IsReturnCallRef) (l : List Admin) :
    ρ.code (c :: l) = c :: ρ.code l := by
  cases c <;> simp_all [Admin.IsReturnCallRef]

theorem Ren.code_retToCallIn (ρ : Ren) {c : Admin} (hc : c.IsReturnCallRef) (m : ModuleInst)
    (l : List Admin) : ρ.code (c.retToCallIn m :: l) = c.retToCallIn m :: ρ.code l := by
  rcases c with ⟨_⟩ | _ | _ | _ | _ | _ | _ | _ <;>
    simp_all [Admin.IsReturnCallRef, Admin.retToCallIn]
  rename_i i
  cases i <;> simp_all
  split <;> simp

theorem Ren.frame_forCall (ρ : Ren) (m : ModuleInst) (vs : List Val) (ls : List ValType) :
    ρ.frame (Frame.forCall m vs ls) = Frame.forCall m (vs.map ρ.val) ls := by
  simp only [Ren.frame, Frame.forCall, List.map_append, List.map_map, Frame.mk.injEq, and_true]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  cases h : defaultVal? ((liftVal t).substAll (m.types.map .dt)) with
  | none => rfl
  | some v => simp [defaultVal?_ren h]

theorem Own.frameGood_forCall {O : Own} {m : ModuleInst} (hm : O.ModGood m) {vs : List Val}
    (hvs : ∀ v ∈ vs, O.GoodVal v) (ls : List ValType) : O.FrameGood (Frame.forCall m vs ls) := by
  refine ⟨hm, fun v hv => ?_⟩
  simp only [Frame.forCall, List.mem_append, List.mem_map] at hv
  rcases hv with ⟨w, hw, hw'⟩ | ⟨t, -, ht⟩
  · cases hw'; exact hvs v hw
  · exact defaultVal?_good ht

theorem Own.codeGood_callRef {O : Own} {c : Admin} (hc : c.IsCallRef) :
    O.CodeGood [c] := by
  cases c <;> simp_all [Admin.IsCallRef]

theorem Own.codeGood_returnCallRef {O : Own} {c : Admin} (hc : c.IsReturnCallRef) :
    O.CodeGood [c] := by
  cases c <;> simp_all [Admin.IsReturnCallRef]

theorem Own.codeGood_retToCallIn {O : Own} {c : Admin} (hc : c.IsReturnCallRef)
    (m : ModuleInst) : O.CodeGood [c.retToCallIn m] := by
  rcases c with ⟨_⟩ | _ | _ | _ | _ | _ | _ | _ <;>
    simp_all [Admin.IsReturnCallRef, Admin.retToCallIn]
  rename_i i
  cases i <;> simp_all
  split <;> simp

theorem Own.not_codeGood_throwing {O : Own} {a : Nat} {l : List Admin}
    (h : O.CodeGood l) (hl : Admin.ref (.exn a) ∈ l) : False := by
  have : Ref.exn a ∈ codeRefs l := by
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hl
    simp
  exact h.1 _ this

/-- The function a part owns at `a` has the same type in the shared store, and the same
instance when the part runs its code. -/
private theorem PartRel.fn_of {ρ : Ren} {O : Own} {p σ : Store H} (hR : PartRel ρ O p σ)
    {a : Nat} (ha : O.fn a) {fi : FuncInst H} (hfi : p.funcs[a]? = some fi) :
    ∃ fi', σ.funcs[a]? = some fi' ∧ fi'.type = fi.type ∧
      ∀ c, fi.code = .wasm c → fi' = fi ∧ O.ModGood fi.module := by
  obtain ⟨fi₀, h1, fi', h2, h3, h4⟩ := hR.fn a ha
  have hfi₀ : fi₀ = fi := Option.some.inj (h1.symm.trans hfi)
  exact hfi₀ ▸ ⟨fi', h2, h3, h4⟩

/-- **One part step in the shared store.** -/
theorem step_sim {P : Profile} {c c' : Config H} (h : Silmaril.Games.Step P noHost c c') :
    ∀ {ρ : Ren} {O : Own} {σ : Store H}, PartRel ρ O c.store σ → O.FrameGood c.frame →
      O.CodeGood c.code → SimGoal P ρ O σ ⟨σ, ρ.frame c.frame, ρ.code c.code⟩ c' := by
  induction h with
  | parametric h =>
    intro ρ O σ hR hf hc
    exact .same hR hf (ParametricStep.good h hc) (Silmaril.Games.Step.parametric (ParametricStep.ren h ρ))
  | numeric h =>
    intro ρ O σ hR hf hc
    obtain ⟨e1, e2⟩ := NumericStep.ren_eq h ρ
    exact .same hR hf (NumericStep.good h hc) (by rw [e1, e2]; exact .numeric h)
  | vector h =>
    intro ρ O σ hR hf hc
    obtain ⟨e1, e2⟩ := VectorStep.ren_eq h ρ
    exact .same hR hf (VectorStep.good h hc) (by rw [e1, e2]; exact .vector h)
  | «variable» h => intro ρ O σ hR hf hc; exact VariableStep.sim h hR hf hc
  | table h => intro ρ O σ hR hf hc; exact (TableStep.not_good h hf).elim
  | memory h => intro ρ O σ hR hf hc; exact (MemoryStep.not_good h hf).elim
  | reference h => intro ρ O σ hR hf hc; exact RefStep.sim h hR hf hc
  | aggregate h => intro ρ O σ hR hf hc; exact AggregateStep.sim h hR hf hc
  | @ctxtInstrs s s' f f' vs is is' rest _ hne ih =>
    show ∀ {ρ : Ren} {O : Own} {σ : Store H}, PartRel ρ O s σ → O.FrameGood f →
      O.CodeGood (vals vs ++ is ++ rest) →
      SimGoal P ρ O σ ⟨σ, ρ.frame f, ρ.code (vals vs ++ is ++ rest)⟩
        ⟨s', f', vals vs ++ is' ++ rest⟩
    intro ρ O σ hR hf hc
    obtain ⟨hcvi, hcr⟩ := O.codeGood_append.mp hc
    obtain ⟨hcv, hci⟩ := O.codeGood_append.mp hcvi
    obtain ⟨ρ', O', σ', hst, hR', hf', hc', hg, ht⟩ := ih hR hf hci
    refine ⟨ρ', O', σ', ?_, hR', hf', ?_, hg, ht⟩
    · simp only [Ren.code_append]
      rw [(hg.code hcv).1, (hg.code hcr).1, Ren.code_vals]
      refine Silmaril.Games.Step.ctxtInstrs hst ?_
      simpa [Ren.code_eq_nil_iff] using hne
    · exact O'.codeGood_append.mpr ⟨O'.codeGood_append.mpr ⟨(hg.code hcv).2, hc'⟩,
        (hg.code hcr).2⟩
  | ctxtLabel _ ih =>
    intro ρ O σ hR hf hc
    obtain ⟨ρ', O', σ', hst, hR', hf', hc', hg, ht⟩ := ih hR hf ((O.codeGood_single_label ..).mp hc)
    exact ⟨ρ', O', σ', by simpa using Silmaril.Games.Step.ctxtLabel (n := ‹Nat›) (cont := ‹List Instr›) hst,
      hR', hf', (O'.codeGood_single_label ..).mpr hc', hg, ht⟩
  | ctxtHandler _ ih =>
    intro ρ O σ hR hf hc
    obtain ⟨ρ', O', σ', hst, hR', hf', hc', hg, ht⟩ :=
      ih hR hf ((O.codeGood_single_handler ..).mp hc)
    exact ⟨ρ', O', σ', by simpa using Silmaril.Games.Step.ctxtHandler (n := ‹Nat›) (cs := ‹List Catch›) hst,
      hR', hf', (O'.codeGood_single_handler ..).mpr hc', hg, ht⟩
  | @ctxtFrame s s' f fi fi' n is is' _ ih =>
    show ∀ {ρ : Ren} {O : Own} {σ : Store H}, PartRel ρ O s σ → O.FrameGood f →
      O.CodeGood [.frame n fi is] →
      SimGoal P ρ O σ ⟨σ, ρ.frame f, ρ.code [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩
    intro ρ O σ hR hf hc
    obtain ⟨hfi, hcb⟩ := (O.codeGood_single_frame ..).mp hc
    obtain ⟨ρ', O', σ', hst, hR', hf', hc', hg, ht⟩ := ih hR hfi hcb
    refine ⟨ρ', O', σ', ?_, hR', (hg.frameGood hf).2, (O'.codeGood_single_frame ..).mpr ⟨hf', hc'⟩,
      hg, ht⟩
    rw [(hg.frameGood hf).1]
    simpa using Silmaril.Games.Step.ctxtFrame (f := ρ.frame f) (n := n) hst
  | @block s f bt body vs t₁ t₂ hbt hm =>
    intro ρ O σ hR hf hc
    refine .same hR hf (by sub_good hc) ?_
    simpa using Silmaril.Games.Step.block (P := P) (host := noHost) (s := σ) (f := ρ.frame f)
      (vs := vs.map ρ.val) (body := body) hbt (by simpa using hm)
  | @loop s f bt body vs t₁ t₂ hbt hm =>
    intro ρ O σ hR hf hc
    refine .same hR hf (by sub_good hc) ?_
    simpa using Silmaril.Games.Step.loop (P := P) (host := noHost) (s := σ) (f := ρ.frame f)
      (vs := vs.map ρ.val) (body := body) hbt (by simpa using hm)
  | @ifTrue s f c bt b₁ b₂ hc0 =>
    intro ρ O σ hR hf hc
    refine .same hR hf (by simp) ?_
    simpa using Silmaril.Games.Step.ifTrue (P := P) (host := noHost) (s := σ) (f := ρ.frame f) (bt := bt)
      (b₁ := b₁) (b₂ := b₂) hc0
  | @ifFalse s f bt b₁ b₂ =>
    intro ρ O σ hR hf hc
    refine .same hR hf (by simp) ?_
    simpa using Silmaril.Games.Step.ifFalse (P := P) (host := noHost) (s := σ) (f := ρ.frame f) (bt := bt)
      (b₁ := b₁) (b₂ := b₂)
  | @labelVals s f n cont vs =>
    intro ρ O σ hR hf hc
    refine .same hR hf ((O.codeGood_single_label ..).mp hc) ?_
    simpa using Silmaril.Games.Step.labelVals (P := P) (host := noHost) (s := σ) (f := ρ.frame f) (n := n)
      (cont := cont) (vs := vs.map ρ.val)
  | @brLabelZero s f n cont vs' vs l rest hl hn =>
    intro ρ O σ hR hf hc
    refine .same hR hf (by sub_good hc) ?_
    simpa using Silmaril.Games.Step.brLabelZero (P := P) (host := noHost) (s := σ) (f := ρ.frame f)
      (cont := cont) (vs' := vs'.map ρ.val) (vs := vs.map ρ.val) (rest := ρ.code rest) hl
      (by simpa using hn)
  | @brLabelSucc s f n cont vs l rest hl =>
    intro ρ O σ hR hf hc
    refine .same hR hf (by sub_good hc) ?_
    simpa using Silmaril.Games.Step.brLabelSucc (P := P) (host := noHost) (s := σ) (f := ρ.frame f) (n := n)
      (cont := cont) (vs := vs.map ρ.val) (rest := ρ.code rest) hl
  | @brHandler s f n cs vs l rest =>
    intro ρ O σ hR hf hc
    refine .same hR hf (by sub_good hc) ?_
    simpa using Silmaril.Games.Step.brHandler (P := P) (host := noHost) (s := σ) (f := ρ.frame f) (n := n)
      (cs := cs) (vs := vs.map ρ.val) (l := l) (rest := ρ.code rest)
  | @brIfTrue s f c l hc0 =>
    intro ρ O σ hR hf hc
    refine .same hR hf (by simp) ?_
    simpa using Silmaril.Games.Step.brIfTrue (P := P) (host := noHost) (s := σ) (f := ρ.frame f) (l := l) hc0
  | @brIfFalse s f l =>
    intro ρ O σ hR hf hc
    refine .same hR hf O.codeGood_nil ?_
    simpa using Silmaril.Games.Step.brIfFalse (P := P) (host := noHost) (s := σ) (f := ρ.frame f) (l := l)
  | @brTableLt s f i ls l' l hi =>
    intro ρ O σ hR hf hc
    refine .same hR hf (by simp) ?_
    simpa using Silmaril.Games.Step.brTableLt (P := P) (host := noHost) (s := σ) (f := ρ.frame f) (l' := l') hi
  | @brTableGe s f i ls l' hi =>
    intro ρ O σ hR hf hc
    refine .same hR hf (by simp) ?_
    simpa using Silmaril.Games.Step.brTableGe (P := P) (host := noHost) (s := σ) (f := ρ.frame f) (l' := l') hi
  | @brOnNullNull s f l =>
    intro ρ O σ hR hf hc
    refine .same hR hf (by simp) ?_
    simpa using Silmaril.Games.Step.brOnNullNull (P := P) (host := noHost) (s := σ) (f := ρ.frame f) (l := l)
  | @brOnNullAddr s f v l hv =>
    intro ρ O σ hR hf hc
    have hv' : ρ.val v ≠ .ref .null := by
      cases v <;> simp_all [Ren.ref_eq_null_iff]
    refine .same hR hf ((O.codeGood_single_toAdmin v).mpr hc.head_val) ?_
    simpa using Silmaril.Games.Step.brOnNullAddr (P := P) (host := noHost) (s := σ) (f := ρ.frame f) (l := l) hv'
  | @brOnNonNullNull s f l =>
    intro ρ O σ hR hf hc
    refine .same hR hf O.codeGood_nil ?_
    simpa using Silmaril.Games.Step.brOnNonNullNull (P := P) (host := noHost) (s := σ) (f := ρ.frame f) (l := l)
  | @brOnNonNullAddr s f v l hv =>
    intro ρ O σ hR hf hc
    have hv' : ρ.val v ≠ .ref .null := by
      cases v <;> simp_all [Ren.ref_eq_null_iff]
    refine .same hR hf (.cons_val hc.head_val (O.codeGood_single_plain _)) ?_
    simpa using Silmaril.Games.Step.brOnNonNullAddr (P := P) (host := noHost) (s := σ) (f := ρ.frame f) (l := l)
      hv'
  | @brOnCastSucceed s f r l rt₁ rt₂ hr =>
    intro ρ O σ hR hf hc
    have hg : O.GoodRef r := hc.head_ref
    refine .same hR hf (.cons_ref hg (O.codeGood_single_plain _)) ?_
    simpa using Silmaril.Games.Step.brOnCastSucceed (P := P) (host := noHost) (s := σ) (f := ρ.frame f) (l := l)
      (rt₁ := rt₁) ((hR.refOk_iff hg).mpr hr)
  | @brOnCastFail s f r l rt₁ rt₂ hr =>
    intro ρ O σ hR hf hc
    have hg : O.GoodRef r := hc.head_ref
    refine .same hR hf ((O.codeGood_single_ref r).mpr hg) ?_
    simpa using Silmaril.Games.Step.brOnCastFail (P := P) (host := noHost) (s := σ) (f := ρ.frame f) (l := l)
      (rt₁ := rt₁) (fun h' => hr ((hR.refOk_iff hg).mp h'))
  | @brOnCastFailSucceed s f r l rt₁ rt₂ hr =>
    intro ρ O σ hR hf hc
    have hg : O.GoodRef r := hc.head_ref
    refine .same hR hf ((O.codeGood_single_ref r).mpr hg) ?_
    simpa using Silmaril.Games.Step.brOnCastFailSucceed (P := P) (host := noHost) (s := σ) (f := ρ.frame f)
      (l := l) (rt₁ := rt₁) ((hR.refOk_iff hg).mpr hr)
  | @brOnCastFailFail s f r l rt₁ rt₂ hr =>
    intro ρ O σ hR hf hc
    have hg : O.GoodRef r := hc.head_ref
    refine .same hR hf (.cons_ref hg (O.codeGood_single_plain _)) ?_
    simpa using Silmaril.Games.Step.brOnCastFailFail (P := P) (host := noHost) (s := σ) (f := ρ.frame f)
      (l := l) (rt₁ := rt₁) (fun h' => hr ((hR.refOk_iff hg).mp h'))
  | @call s f x a fi hx hfi =>
    intro ρ O σ hR hf hc
    have ha : O.fn a := hf.1.funcs a (List.mem_of_getElem? hx)
    obtain ⟨fi', h2, h3, -⟩ := hR.fn_of ha hfi
    refine .same hR hf (.cons_ref ha (O.codeGood_single_callRefType _)) ?_
    simpa [h3] using Silmaril.Games.Step.call (P := P) (host := noHost) (s := σ) (f := ρ.frame f) hx h2
  | @callRefNull s f c hcr =>
    intro ρ O σ hR hf hc
    refine .same hR hf (by simp) ?_
    simpa [Ren.code_callRef ρ hcr] using
      Silmaril.Games.Step.callRefNull (P := P) (host := noHost) (s := σ) (f := ρ.frame f) hcr
  | @callRefFunc s f c vs a fi ps rs code hcr hfi he hn hcode =>
    show ∀ {ρ : Ren} {O : Own} {σ : Store H}, PartRel ρ O s σ → O.FrameGood f →
      O.CodeGood (vals vs ++ [.ref (.func a), c]) →
      SimGoal P ρ O σ ⟨σ, ρ.frame f, ρ.code (vals vs ++ [.ref (.func a), c])⟩
        ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
          [.label rs.length [] (expression code.body)]]⟩
    intro ρ O σ hR hf hc
    obtain ⟨hcv, hcr'⟩ := O.codeGood_append.mp hc
    have ha : O.fn a := hcr'.head_ref
    obtain ⟨fi', h2, -, h4⟩ := hR.fn_of ha hfi
    obtain ⟨hfi', hm⟩ : fi' = fi ∧ O.ModGood fi.module := h4 code hcode
    have h2' : σ.funcs[a]? = some fi := hfi' ▸ h2
    refine .same hR hf ((O.codeGood_single_frame ..).mpr ⟨Own.frameGood_forCall hm
      ((O.codeGood_vals).mp hcv) _, (O.codeGood_single_label ..).mpr (O.codeGood_expression _)⟩) ?_
    simpa [Ren.code_callRef ρ hcr, Ren.frame_forCall] using
      Silmaril.Games.Step.callRefFunc (P := P) (host := noHost) (s := σ) (f := ρ.frame f)
        (vs := vs.map ρ.val) hcr h2' he (by simpa using hn) hcode
  | callRefHost _ _ _ _ _ hhost => intro ρ O σ hR hf hc; exact hhost.elim
  | callRefHostDiv _ _ _ _ _ hhost => intro ρ O σ hR hf hc; exact hhost.elim
  | @returnCall s f x a fi hx hfi =>
    intro ρ O σ hR hf hc
    have ha : O.fn a := hf.1.funcs a (List.mem_of_getElem? hx)
    obtain ⟨fi', h2, h3, -⟩ := hR.fn_of ha hfi
    refine .same hR hf (.cons_ref ha (O.codeGood_single_returnCallRefType _)) ?_
    simpa [h3] using Silmaril.Games.Step.returnCall (P := P) (host := noHost) (s := σ) (f := ρ.frame f) hx h2
  | @returnCallRefLabel s f k cont vs c rest hcr =>
    intro ρ O σ hR hf hc
    have hb : O.CodeGood (vals vs ++ [c] ++ rest) := (O.codeGood_single_label ..).mp hc
    refine .same hR hf (O.codeGood_append.mp hb).1 ?_
    simpa [Ren.code_returnCallRef ρ hcr] using
      Silmaril.Games.Step.returnCallRefLabel (P := P) (host := noHost) (s := σ) (f := ρ.frame f)
        (k := k) (cont := cont) (vs := vs.map ρ.val) (rest := ρ.code rest) hcr
  | @returnCallRefHandler s f k cs vs c rest hcr =>
    intro ρ O σ hR hf hc
    have hb : O.CodeGood (vals vs ++ [c] ++ rest) := (O.codeGood_single_handler ..).mp hc
    refine .same hR hf (O.codeGood_append.mp hb).1 ?_
    simpa [Ren.code_returnCallRef ρ hcr] using
      Silmaril.Games.Step.returnCallRefHandler (P := P) (host := noHost) (s := σ) (f := ρ.frame f)
        (k := k) (cs := cs) (vs := vs.map ρ.val) (rest := ρ.code rest) hcr
  | @returnCallRefFrameNull s f fi k vs c rest hcr =>
    intro ρ O σ hR hf hc
    refine .same hR hf (by simp) ?_
    simpa [Ren.code_returnCallRef ρ hcr] using
      Silmaril.Games.Step.returnCallRefFrameNull (P := P) (host := noHost) (s := σ) (f := ρ.frame f)
        (fi := ρ.frame fi) (k := k) (vs := vs.map ρ.val) (rest := ρ.code rest) hcr
  | @returnCallRefFrameAddr s f fi k vs' vs a c rest fn ps rs hcr hfn he hn =>
    show ∀ {ρ : Ren} {O : Own} {σ : Store H}, PartRel ρ O s σ → O.FrameGood f →
      O.CodeGood [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)] →
      SimGoal P ρ O σ
        ⟨σ, ρ.frame f, ρ.code [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩
        ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fi.module]⟩
    intro ρ O σ hR hf hc
    have hb : O.CodeGood (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest) :=
      ((O.codeGood_single_frame ..).mp hc).2
    obtain ⟨hb₁, -⟩ := O.codeGood_append.mp hb
    obtain ⟨hb₂, hb₃⟩ := O.codeGood_append.mp hb₁
    obtain ⟨-, hvs⟩ := O.codeGood_append.mp hb₂
    have ha : O.fn a := hb₃.head_ref
    obtain ⟨fn', h2, h3, -⟩ := hR.fn_of ha hfn
    refine .same hR hf
      (O.codeGood_append.mpr ⟨hvs, .cons_ref ha (Own.codeGood_retToCallIn hcr _)⟩) ?_
    simpa [Ren.code_returnCallRef ρ hcr, Ren.code_retToCallIn ρ hcr] using
      Silmaril.Games.Step.returnCallRefFrameAddr (P := P) (host := noHost) (s := σ) (f := ρ.frame f)
        (fi := ρ.frame fi) (k := k) (vs' := vs'.map ρ.val) (vs := vs.map ρ.val)
        (rest := ρ.code rest) hcr h2 (by rw [h3]; exact he) (by simpa using hn)
  | @callIndirect s f x y =>
    intro ρ O σ hR hf hc
    refine .same hR hf (by sub_good hc) ?_
    simpa using Silmaril.Games.Step.callIndirect (P := P) (host := noHost) (s := σ) (f := ρ.frame f) (x := x)
      (y := y)
  | @returnCallIndirect s f x y =>
    intro ρ O σ hR hf hc
    refine .same hR hf (by sub_good hc) ?_
    simpa using Silmaril.Games.Step.returnCallIndirect (P := P) (host := noHost) (s := σ) (f := ρ.frame f)
      (x := x) (y := y)
  | @frameVals s f fi n vs hn =>
    intro ρ O σ hR hf hc
    refine .same hR hf ((O.codeGood_single_frame ..).mp hc).2 ?_
    simpa using Silmaril.Games.Step.frameVals (P := P) (host := noHost) (s := σ) (f := ρ.frame f)
      (fi := ρ.frame fi) (vs := vs.map ρ.val) (by simpa using hn)
  | @returnFrame s f fi n vs' vs rest hn =>
    show ∀ {ρ : Ren} {O : Own} {σ : Store H}, PartRel ρ O s σ → O.FrameGood f →
      O.CodeGood [.frame n fi (vals vs' ++ vals vs ++ [.plain .return_] ++ rest)] →
      SimGoal P ρ O σ
        ⟨σ, ρ.frame f, ρ.code [.frame n fi (vals vs' ++ vals vs ++ [.plain .return_] ++ rest)]⟩
        ⟨s, f, vals vs⟩
    intro ρ O σ hR hf hc
    have hb : O.CodeGood (vals vs' ++ vals vs ++ [.plain .return_] ++ rest) :=
      ((O.codeGood_single_frame ..).mp hc).2
    have hvs : O.CodeGood (vals vs) :=
      (O.codeGood_append.mp (O.codeGood_append.mp (O.codeGood_append.mp hb).1).1).2
    refine .same hR hf hvs ?_
    simpa using Silmaril.Games.Step.returnFrame (P := P) (host := noHost) (s := σ) (f := ρ.frame f)
      (fi := ρ.frame fi) (vs' := vs'.map ρ.val) (vs := vs.map ρ.val) (rest := ρ.code rest)
      (by simpa using hn)
  | @returnLabel s f n cont vs rest =>
    intro ρ O σ hR hf hc
    have hb : O.CodeGood (vals vs ++ [.plain .return_] ++ rest) :=
      (O.codeGood_single_label ..).mp hc
    refine .same hR hf (O.codeGood_append.mp hb).1 ?_
    simpa using Silmaril.Games.Step.returnLabel (P := P) (host := noHost) (s := σ) (f := ρ.frame f) (n := n)
      (cont := cont) (vs := vs.map ρ.val) (rest := ρ.code rest)
  | @returnHandler s f n cs vs rest =>
    intro ρ O σ hR hf hc
    have hb : O.CodeGood (vals vs ++ [.plain .return_] ++ rest) :=
      (O.codeGood_single_handler ..).mp hc
    refine .same hR hf (O.codeGood_append.mp hb).1 ?_
    simpa using Silmaril.Games.Step.returnHandler (P := P) (host := noHost) (s := σ) (f := ρ.frame f) (n := n)
      (cs := cs) (vs := vs.map ρ.val) (rest := ρ.code rest)
  | throw ht =>
    intro ρ O σ hR hf hc
    exact absurd ht (by simp [tag?_none hf.1.tags])
  | @throwRefNull s f =>
    intro ρ O σ hR hf hc
    refine .same hR hf (by simp) ?_
    simpa using Silmaril.Games.Step.throwRefNull (P := P) (host := noHost) (s := σ) (f := ρ.frame f)
  | throwRefInstrs _ =>
    intro ρ O σ hR hf hc
    exact (Own.not_codeGood_throwing hc (by simp [throwing]; exact .inr (.inl rfl))).elim
  | throwRefLabel =>
    intro ρ O σ hR hf hc
    exact (Own.not_codeGood_throwing ((O.codeGood_single_label ..).mp hc)
      (by simp [throwing]; try rfl)).elim
  | throwRefFrame =>
    intro ρ O σ hR hf hc
    exact (Own.not_codeGood_throwing ((O.codeGood_single_frame ..).mp hc).2
      (by simp [throwing]; try rfl)).elim
  | throwRefHandlerEmpty =>
    intro ρ O σ hR hf hc
    exact (Own.not_codeGood_throwing ((O.codeGood_single_handler ..).mp hc)
      (by simp [throwing]; try rfl)).elim
  | throwRefHandlerCatch _ _ =>
    intro ρ O σ hR hf hc
    exact (Own.not_codeGood_throwing ((O.codeGood_single_handler ..).mp hc)
      (by simp [throwing]; try rfl)).elim
  | throwRefHandlerCatchRef _ _ =>
    intro ρ O σ hR hf hc
    exact (Own.not_codeGood_throwing ((O.codeGood_single_handler ..).mp hc)
      (by simp [throwing]; try rfl)).elim
  | throwRefHandlerCatchAll =>
    intro ρ O σ hR hf hc
    exact (Own.not_codeGood_throwing ((O.codeGood_single_handler ..).mp hc)
      (by simp [throwing]; try rfl)).elim
  | throwRefHandlerCatchAllRef =>
    intro ρ O σ hR hf hc
    exact (Own.not_codeGood_throwing ((O.codeGood_single_handler ..).mp hc)
      (by simp [throwing]; try rfl)).elim
  | throwRefHandlerNext _ =>
    intro ρ O σ hR hf hc
    exact (Own.not_codeGood_throwing ((O.codeGood_single_handler ..).mp hc)
      (by simp [throwing]; try rfl)).elim
  | @tryTable s f bt cs body vs t₁ t₂ hbt hm =>
    intro ρ O σ hR hf hc
    refine .same hR hf (by sub_good hc) ?_
    simpa using Silmaril.Games.Step.tryTable (P := P) (host := noHost) (s := σ) (f := ρ.frame f) (cs := cs)
      (body := body) (vs := vs.map ρ.val) hbt (by simpa using hm)
  | @handlerVals s f n cs vs =>
    intro ρ O σ hR hf hc
    refine .same hR hf ((O.codeGood_single_handler ..).mp hc) ?_
    simpa using Silmaril.Games.Step.handlerVals (P := P) (host := noHost) (s := σ) (f := ρ.frame f) (n := n)
      (cs := cs) (vs := vs.map ρ.val)
  | @trapInstrs s f vs rest hne =>
    intro ρ O σ hR hf hc
    refine .same hR hf (by simp) ?_
    simpa using Silmaril.Games.Step.trapInstrs (P := P) (host := noHost) (s := σ) (f := ρ.frame f)
      (vs := vs.map ρ.val) (rest := ρ.code rest) (by simpa [Ren.code_eq_nil_iff] using hne)
  | @trapLabel s f n cont =>
    intro ρ O σ hR hf hc
    refine .same hR hf (by simp) ?_
    simpa using Silmaril.Games.Step.trapLabel (P := P) (host := noHost) (s := σ) (f := ρ.frame f) (n := n)
      (cont := cont)
  | @trapHandler s f n cs =>
    intro ρ O σ hR hf hc
    refine .same hR hf (by simp) ?_
    simpa using Silmaril.Games.Step.trapHandler (P := P) (host := noHost) (s := σ) (f := ρ.frame f) (n := n)
      (cs := cs)
  | @trapFrame s f fi n =>
    intro ρ O σ hR hf hc
    refine .same hR hf (by simp) ?_
    simpa using Silmaril.Games.Step.trapFrame (P := P) (host := noHost) (s := σ) (f := ρ.frame f)
      (fi := ρ.frame fi) (n := n)

end Silmaril.Proofs.Wasm.Game.Linking.Split
