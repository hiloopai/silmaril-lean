module

public import Silmaril.Proofs.Wasm.Models.FXRenameVSim.Basic

/-!
# Exception renaming for `StepFX'`: the forward simulation, one step

`Fwd P n c c'` says that the step `c → c'` is matched, from every renamed configuration of `c`
(an `ExnRen n` store and a `KRn n` continuation store), by one `StepFX'` step to a renamed
configuration of `c'`. **`stepV_rn`**: every host-free `StepFX'` step without FX functions has
this property. Each rule is one lemma (`fwd_*`):

* `core`: Silmaril's Core step under `blockFX noHost noFX = noHost` (`blockFX_noHost'`) and
  the Core renaming `step_rn`;
* the structural rules, branches, returns, traps and throws keep both stores;
* `cont.new`, `cont.bind`, `suspend` and `switch` push the renamed continuation (`kRn_push`):
  the continuation captured by `suspend`/`switch` from the renamed code is the renamed context
  (`contRn_ctx`);
* `resume`, `resume_throw`: clauses resolve alike in both stores (`resolve_rn`); the exception
  of `resume_throw` is allocated at `rnIdx n s.exns.length` in the target (`exns_length_rn`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXRenameVSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXRename
open Silmaril.Wasm.Models.FXRenameV Silmaril.Wasm.Models.FXRenameVSim
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {n : Nat}

/-- Without FX functions the Core host of `StepFX'` is `noHost`. -/
theorem blockFX_noHost' : blockFX (noHost (H := H)) noFX = noHost := by
  funext h s vs out
  exact propext ⟨fun hb => hb.2, fun hb => hb.elim⟩

/-- Tags are looked up alike in a renamed store and frame. -/
theorem tag?_rn {s t : Store H} (h : ExnRen n s t) (f : Frame) (x : TagIdx) :
    t.tag? (rnFrame n f) x = s.tag? f x := by
  simp only [Store.tag?, Silmaril.Proofs.Wasm.Models.FXRenameSim.rnFrame_module, h.tags]

/-- Handler clauses resolve alike in a renamed store and frame. -/
theorem resolve_rn {s t : Store H} (h : ExnRen n s t) (f : Frame) :
    resolve t (rnFrame n f) = resolve s f := by
  funext c
  cases c <;> simp only [resolve, tag?_rn h]

/-- The renamed configuration. -/
abbrev rnCfgV (n : Nat) (c : ConfigFX H) (t : Store H) (K₂ : List (Option ContFX)) :
    ConfigFX H :=
  ⟨t, K₂, rnFrame n c.frame, rnL n c.code⟩

/-- **One step of `c` is matched from every renamed configuration of `c`.** -/
def Fwd (P : Profile) (n : Nat) (c c' : ConfigFX H) : Prop :=
  ∀ {t : Store H} {K₂ : List (Option ContFX)}, ExnRen n c.store t → KRn n c.conts K₂ →
    ∃ t' K₂', StepFX' P noHost noFX (rnCfgV n c t K₂) (rnCfgV n c' t' K₂') ∧
      ExnRen n c'.store t' ∧ KRn n c'.conts K₂'

variable {s s' : Store H} {K K' : List (Option ContFX)} {f f' fi fi' : Frame}
  {vs vs' : List FVal} {es es' rest : List AdminFX} {m : Nat} {k : List InstrFX}

/-- A step that keeps both stores, matched with both stores kept. -/
theorem fwd_pure {code code' : List AdminFX}
    (hstep : ∀ (t : Store H) (K₂ : List (Option ContFX)),
      StepFX' P noHost noFX ⟨t, K₂, rnFrame n f, rnL n code⟩ ⟨t, K₂, rnFrame n f', rnL n code'⟩) :
    Fwd P n ⟨s, K, f, code⟩ ⟨s, K, f', code'⟩ :=
  fun h hK => ⟨_, _, hstep _ _, h, hK⟩

theorem fwd_core {cs cs' : List Admin}
    (hs : Step P (blockFX noHost noFX) ⟨s, f, cs⟩ ⟨s', f', cs'⟩) :
    Fwd P n ⟨s, K, f, cs.map .core⟩ ⟨s', K, f', cs'.map .core⟩ := by
  intro t K₂ h hK
  have h₀ : Step P noHost ⟨s, f, cs⟩ ⟨s', f', cs'⟩ := by rw [← blockFX_noHost']; exact hs
  obtain ⟨t', hst, ht'⟩ := Silmaril.Wasm.Models.FXRenameSim.step_rn h₀ h
  have h₁ : Step P (blockFX noHost noFX) ⟨t, rnFrame n f, rnAdmins n cs⟩
      ⟨t', rnFrame n f', rnAdmins n cs'⟩ := by rw [blockFX_noHost']; exact hst
  refine ⟨t', K₂, ?_, ht', hK⟩
  show StepFX' P noHost noFX ⟨t, K₂, rnFrame n f, rnL n (cs.map .core)⟩
    ⟨t', K₂, rnFrame n f', rnL n (cs'.map .core)⟩
  rw [rnL_map_core', rnL_map_core']
  exact .core h₁

theorem fwd_seq (ih : Fwd P n ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) (hne : vs ≠ [] ∨ rest ≠ []) :
    Fwd P n ⟨s, K, f, fvals vs ++ es ++ rest⟩ ⟨s', K', f', fvals vs ++ es' ++ rest⟩ := by
  intro t K₂ h hK
  obtain ⟨t', K₂', hst, ht', hK'⟩ := ih h hK
  have hne' : vs.map (rnFV n) ≠ [] ∨ rnL n rest ≠ [] := by
    simpa only [ne_eq, List.map_eq_nil_iff, rnL_eq_nil_iff] using hne
  refine ⟨t', K₂', ?_, ht', hK'⟩
  simpa only [rnCfgV, rnL_append, rnL_fvals] using StepFX'.seq (vs := vs.map (rnFV n)) hst hne'

theorem fwd_ctxLabel (ih : Fwd P n ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
    Fwd P n ⟨s, K, f, [.label m k es]⟩ ⟨s', K', f', [.label m k es']⟩ := by
  intro t K₂ h hK
  obtain ⟨t', K₂', hst, ht', hK'⟩ := ih h hK
  refine ⟨t', K₂', ?_, ht', hK'⟩
  simpa only [rnCfgV, rnL_cons, rnL_nil, rnA_label] using StepFX'.ctxLabel (n := m) (k := k) hst

theorem fwd_ctxFrame (ih : Fwd P n ⟨s, K, fi, es⟩ ⟨s', K', fi', es'⟩) :
    Fwd P n ⟨s, K, f, [.frame m fi es]⟩ ⟨s', K', f, [.frame m fi' es']⟩ := by
  intro t K₂ h hK
  obtain ⟨t', K₂', hst, ht', hK'⟩ := ih h hK
  refine ⟨t', K₂', ?_, ht', hK'⟩
  simpa only [rnCfgV, rnL_cons, rnL_nil, rnA_frame]
    using StepFX'.ctxFrame (f := rnFrame n f) (n := m) hst

theorem fwd_ctxHandler {hs : List HClause} (ih : Fwd P n ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
    Fwd P n ⟨s, K, f, [.handler hs es]⟩ ⟨s', K', f', [.handler hs es']⟩ := by
  intro t K₂ h hK
  obtain ⟨t', K₂', hst, ht', hK'⟩ := ih h hK
  refine ⟨t', K₂', ?_, ht', hK'⟩
  simpa only [rnCfgV, rnL_cons, rnL_nil, rnA_handler] using StepFX'.ctxHandler (hs := hs) hst

theorem fwd_contNew {a : Nat} {fi : FuncInst H} {ct : TypeIdx} (hf : s.funcs[a]? = some fi) :
    Fwd P n ⟨s, K, f, [.core (.ref (.func a)), .fx (.contNew ct)]⟩
      ⟨s, K ++ [some ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType fi.type)]⟩], f,
        [.contRef K.length]⟩ := by
  intro t K₂ h hK
  have hf' : t.funcs[a]? = some fi := by rw [h.funcs]; exact hf
  have hC : ContRn n ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType fi.type)]⟩
      ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType fi.type)]⟩ := fun c => by
    simp
  refine ⟨t, _, ?_, h, kRn_push hK hC⟩
  simpa [rnCfgV, kRn_length hK] using
    StepFX'.contNew (P := P) (host := noHost) (fx := noFX) (K := K₂) (f := rnFrame n f) (ct := ct) hf'

theorem fwd_contBind {kk : Nat} {C : ContFX} {ct ct' : TypeIdx} (hk : K[kk]? = some (some C)) :
    Fwd P n ⟨s, K, f, fvals vs ++ [.contRef kk, .fx (.contBind ct ct')]⟩
      ⟨s, K.set kk none ++ [some ⟨fun c => C.plug (fvals vs ++ c)⟩], f, [.contRef K.length]⟩ := by
  intro t K₂ h hK
  obtain ⟨C₂, hk₂, hC⟩ := kRn_some hK hk
  have hC' : ContRn n ⟨fun c => C.plug (fvals vs ++ c)⟩
      ⟨fun c => C₂.plug (fvals (vs.map (rnFV n)) ++ c)⟩ := fun c => by
    show C₂.plug (fvals (vs.map (rnFV n)) ++ rnL n c) = rnL n (C.plug (fvals vs ++ c))
    rw [← hC, rnL_append, rnL_fvals]
  refine ⟨t, _, ?_, h, kRn_push (kRn_set hK kk) hC'⟩
  simpa [rnCfgV, kRn_length hK] using
    StepFX'.contBind (P := P) (host := noHost) (fx := noFX) (s := t) (f := rnFrame n f)
      (vs := vs.map (rnFV n)) (ct := ct) (ct' := ct') hk₂

theorem fwd_contBindUsed {kk : Nat} {ct ct' : TypeIdx} (hk : K[kk]? = some none) :
    Fwd P n ⟨s, K, f, fvals vs ++ [.contRef kk, .fx (.contBind ct ct')]⟩ ⟨s, K, f, [.core .trap]⟩ :=
  fun h hK => ⟨_, _, by
    simpa [rnCfgV] using StepFX'.contBindUsed (P := P) (host := noHost) (fx := noFX)
      (f := rnFrame n f) (vs := vs.map (rnFV n)) (ct := ct) (ct' := ct') (kRn_none hK hk), h, hK⟩

theorem fwd_resume {kk : Nat} {C : ContFX} {ct : TypeIdx} {hs : List OnClause}
    {hs' : List HClause} (hk : K[kk]? = some (some C)) (hr : hs.mapM (resolve s f) = some hs') :
    Fwd P n ⟨s, K, f, fvals vs ++ [.contRef kk, .fx (.resume ct hs)]⟩
      ⟨s, K.set kk none, f, [.handler hs' (C.plug (fvals vs))]⟩ := by
  intro t K₂ h hK
  obtain ⟨C₂, hk₂, hC⟩ := kRn_some hK hk
  have hr' : hs.mapM (resolve t (rnFrame n f)) = some hs' := by rw [resolve_rn h]; exact hr
  refine ⟨t, _, ?_, h, kRn_set hK kk⟩
  have hplug : C₂.plug (fvals (vs.map (rnFV n))) = rnL n (C.plug (fvals vs)) := by
    rw [← hC, rnL_fvals]
  simpa [rnCfgV, hplug] using StepFX'.resume (P := P) (host := noHost) (fx := noFX)
    (vs := vs.map (rnFV n)) (ct := ct) hk₂ hr'

theorem fwd_resumeUsed {kk : Nat} {ct : TypeIdx} {hs : List OnClause} (hk : K[kk]? = some none) :
    Fwd P n ⟨s, K, f, fvals vs ++ [.contRef kk, .fx (.resume ct hs)]⟩ ⟨s, K, f, [.core .trap]⟩ :=
  fun h hK => ⟨_, _, by
    simpa [rnCfgV] using StepFX'.resumeUsed (P := P) (host := noHost) (fx := noFX)
      (f := rnFrame n f) (vs := vs.map (rnFV n)) (ct := ct) (hs := hs) (kRn_none hK hk), h, hK⟩

theorem fwd_resumeThrow {ws : List Val} {kk : Nat} {C : ContFX} {ct : TypeIdx} {x : TagIdx}
    {hs : List OnClause} {hs' : List HClause} {ta : Nat} {ti : TagInst}
    (hk : K[kk]? = some (some C)) (ht : s.tag? f x = some (ta, ti))
    (hr : hs.mapM (resolve s f) = some hs') :
    Fwd P n ⟨s, K, f, cvals ws ++ [.contRef kk, .fx (.resumeThrow ct x hs)]⟩
      ⟨s.addExn ⟨ta, ws⟩, K.set kk none, f, [.handler hs' (C.plug (cthrowing s.exns.length))]⟩ := by
  intro t K₂ h hK
  obtain ⟨C₂, hk₂, hC⟩ := kRn_some hK hk
  have hr' : hs.mapM (resolve t (rnFrame n f)) = some hs' := by rw [resolve_rn h]; exact hr
  have ht' : t.tag? (rnFrame n f) x = some (ta, ti) := by rw [tag?_rn h]; exact ht
  have hlen : t.exns.length = rnIdx n s.exns.length :=
    Silmaril.Proofs.Wasm.Models.FXRenameSim.exns_length_rn h
  have hplug : C₂.plug (cthrowing t.exns.length) = rnL n (C.plug (cthrowing s.exns.length)) := by
    rw [← hC, rnL_cthrowing, hlen]
  have hs' : ExnRen n (s.addExn ⟨ta, ws⟩) (t.addExn ⟨ta, ws.map (rnVal n)⟩) :=
    Silmaril.Proofs.Wasm.Models.FXRenameSim.addExn_rn h ⟨ta, ws⟩
  refine ⟨_, _, ?_, hs', kRn_set hK kk⟩
  simpa [rnCfgV, hplug] using StepFX'.resumeThrow (P := P) (host := noHost) (fx := noFX)
    (vs := ws.map (rnVal n)) (ct := ct) hk₂ ht' hr'

theorem fwd_suspend {hs : List HClause} {E : CtxV} {x : TagIdx} {ta : Nat} {ti : TagInst}
    {l : LabelIdx} (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
    Fwd P n ⟨s, K, f, [.handler hs (E.plug (fvals vs ++ [.fx (.suspend x)]))]⟩
      ⟨s, K ++ [some ⟨E.plug⟩], f, fvals vs ++ [.contRef K.length, .core (.plain (.br l))]⟩ := by
  intro t K₂ h hK
  have ht' : t.tag? ((rnCtx n E).frameAt (rnFrame n f)) x = some (ta, ti) := by
    rw [rnCtx_frameAt, tag?_rn h]; exact ht
  have hE' : ¬ (rnCtx n E).Handles ta := by rw [rnCtx_handles]; exact hE
  have hcode : rnL n [.handler hs (E.plug (fvals vs ++ [.fx (.suspend x)]))] =
      [.handler hs ((rnCtx n E).plug (fvals (vs.map (rnFV n)) ++ [.fx (.suspend x)]))] := by
    rw [rnL_cons, rnL_nil, rnA_handler, ← rnCtx_plug, rnL_append, rnL_fvals, rnL_cons, rnL_nil,
      rnA_fx]
  refine ⟨t, _, ?_, h, kRn_push hK (contRn_ctx E)⟩
  show StepFX' P noHost noFX ⟨t, K₂, rnFrame n f, rnL n _⟩ ⟨t, _, rnFrame n f, rnL n _⟩
  rw [hcode]
  simpa [rnCfgV, kRn_length hK] using StepFX'.suspend (P := P) (host := noHost) (fx := noFX) (s := t)
    (K := K₂) (vs := vs.map (rnFV n)) ht' hE' hc

theorem fwd_switch {hs : List HClause} {E : CtxV} {kk : Nat} {C : ContFX} {ct : TypeIdx}
    {x : TagIdx} {ta : Nat} {ti : TagInst} (hk : K[kk]? = some (some C))
    (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
    (hc : hs.find? (fun c => c.tag == ta) = some (.onSwitch ta)) :
    Fwd P n ⟨s, K, f, [.handler hs (E.plug (fvals vs ++ [.contRef kk, .fx (.switch ct x)]))]⟩
      ⟨s, K.set kk none ++ [some ⟨E.plug⟩], f,
        [.handler hs (C.plug (fvals vs ++ [.contRef K.length]))]⟩ := by
  intro t K₂ h hK
  obtain ⟨C₂, hk₂, hC⟩ := kRn_some hK hk
  have ht' : t.tag? ((rnCtx n E).frameAt (rnFrame n f)) x = some (ta, ti) := by
    rw [rnCtx_frameAt, tag?_rn h]; exact ht
  have hE' : ¬ (rnCtx n E).Handles ta := by rw [rnCtx_handles]; exact hE
  have hcode : rnL n [.handler hs (E.plug (fvals vs ++ [.contRef kk, .fx (.switch ct x)]))] =
      [.handler hs ((rnCtx n E).plug
        (fvals (vs.map (rnFV n)) ++ [.contRef kk, .fx (.switch ct x)]))] := by
    rw [rnL_cons, rnL_nil, rnA_handler, ← rnCtx_plug, rnL_append, rnL_fvals, rnL_cons, rnL_cons,
      rnL_nil, rnA_fx, rnA_contRef]
  have hplug : C₂.plug (fvals (vs.map (rnFV n)) ++ [.contRef K₂.length]) =
      rnL n (C.plug (fvals vs ++ [.contRef K.length])) := by
    rw [← hC, rnL_append, rnL_fvals, rnL_cons, rnL_nil, rnA_contRef, kRn_length hK]
  refine ⟨t, _, ?_, h, kRn_push (kRn_set hK kk) (contRn_ctx E)⟩
  show StepFX' P noHost noFX ⟨t, K₂, rnFrame n f, rnL n _⟩ ⟨t, _, rnFrame n f, rnL n _⟩
  rw [hcode, rnL_cons, rnL_nil, rnA_handler, ← hplug]
  exact StepFX'.switch (P := P) (host := noHost) (fx := noFX) (s := t) (vs := vs.map (rnFV n))
    hk₂ ht' hE' hc

/-- **The forward renaming simulation for `StepFX'`, one step.** -/
theorem stepV_rn {c c' : ConfigFX H} (hs : StepFX' P noHost noFX c c') : Fwd P n c c' := by
  induction hs with
  | core h => exact fwd_core h
  | seq _ hne ih => exact fwd_seq ih hne
  | ctxLabel _ ih => exact fwd_ctxLabel ih
  | ctxFrame _ ih => exact fwd_ctxFrame ih
  | ctxHandler _ ih => exact fwd_ctxHandler ih
  | block hbt hm => exact fwd_pure fun _ _ => by simpa using StepFX'.block (f := rnFrame n _) (vs := List.map (rnFV n) _) hbt (by simpa using hm)
  | loop hbt hm => exact fwd_pure fun _ _ => by simpa using StepFX'.loop (f := rnFrame n _) (vs := List.map (rnFV n) _) hbt (by simpa using hm)
  | ifTrue hc => exact fwd_pure fun _ _ => by simpa using StepFX'.ifTrue hc
  | ifFalse => exact fwd_pure fun _ _ => by simpa using StepFX'.ifFalse
  | labelVals => exact fwd_pure fun _ _ => by simpa using StepFX'.labelVals
  | brLabelZero hl hn =>
    exact fwd_pure fun _ _ => by simpa using StepFX'.brLabelZero hl (by simpa using hn)
  | brLabelSucc hl => exact fwd_pure fun _ _ => by simpa using StepFX'.brLabelSucc hl
  | brHandler => exact fwd_pure fun _ _ => by simpa using StepFX'.brHandler
  | returnLabel => exact fwd_pure fun _ _ => by simpa using StepFX'.returnLabel
  | returnHandler => exact fwd_pure fun _ _ => by simpa using StepFX'.returnHandler
  | frameVals hn => exact fwd_pure fun _ _ => by simpa using StepFX'.frameVals (by simpa using hn)
  | returnFrame hn =>
    exact fwd_pure fun _ _ => by simpa using StepFX'.returnFrame (by simpa using hn)
  | handlerVals => exact fwd_pure fun _ _ => by simpa using StepFX'.handlerVals
  | dropCont => exact fwd_pure fun _ _ => by simpa using StepFX'.dropCont
  | trapSeq hne => exact fwd_pure fun _ _ => by simpa using StepFX'.trapSeq (vs := List.map (rnFV n) _) (by simpa using hne)
  | trapLabel => exact fwd_pure fun _ _ => by simpa using StepFX'.trapLabel
  | trapFrame => exact fwd_pure fun _ _ => by simpa using StepFX'.trapFrame
  | trapHandler => exact fwd_pure fun _ _ => by simpa using StepFX'.trapHandler
  | throwSeq hne => exact fwd_pure fun _ _ => by simpa using StepFX'.throwSeq (vs := List.map (rnFV n) _) (by simpa using hne)
  | throwLabel => exact fwd_pure fun _ _ => by simpa using StepFX'.throwLabel
  | throwFrame => exact fwd_pure fun _ _ => by simpa using StepFX'.throwFrame
  | throwHandler => exact fwd_pure fun _ _ => by simpa using StepFX'.throwHandler
  | invoke _ _ _ hfx => exact absurd hfx (by simp [noFX])
  | contNew hf => exact fwd_contNew hf
  | contNewNull => exact fwd_pure fun _ _ => by simpa using StepFX'.contNewNull
  | contBind hk => exact fwd_contBind hk
  | contBindNull => exact fwd_pure fun _ _ => by simpa using StepFX'.contBindNull
  | contBindUsed hk => exact fwd_contBindUsed hk
  | resume hk hr => exact fwd_resume hk hr
  | resumeNull => exact fwd_pure fun _ _ => by simpa using StepFX'.resumeNull
  | resumeUsed hk => exact fwd_resumeUsed hk
  | resumeThrow hk ht hr => exact fwd_resumeThrow hk ht hr
  | resumeThrowNull => exact fwd_pure fun _ _ => by simpa using StepFX'.resumeThrowNull
  | suspend ht hE hc => exact fwd_suspend ht hE hc
  | switch hk ht hE hc => exact fwd_switch hk ht hE hc

end Silmaril.Proofs.Wasm.Models.FXRenameVSim
