module

public import Silmaril.Proofs.Wasm.Models.FXRenameVSim.Back

/-!
# Exception renaming for `StepFX'`: the backward simulation at the continuation rules

The rules that change the continuation store (`cont.new`, `cont.bind`, `resume`,
`resume_throw`, `suspend`, `switch`) read back (`bwd_*`), and **`stepV_rn_back`**: every
host-free `StepFX'` step without FX functions from a renamed configuration is the renamed image
of a step of the source. At `suspend` and `switch` the target's context is read back as a
renamed source context (`inv_handler_plug`); a target split of the payload is a split of the
source payload, so both choices of `suspend_nondet` are matched.

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
variable {t : Store H} {K₂ : List (Option ContFX)} {f₀ : Frame} {vs : List FVal}

theorem bwd_contNew {a : Nat} {fi : FuncInst H} {ct : TypeIdx} (hf : t.funcs[a]? = some fi) :
    Bwd P n ⟨t, K₂, f₀, [.core (.ref (.func a)), .fx (.contNew ct)]⟩
      ⟨t, K₂ ++ [some ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType fi.type)]⟩], f₀,
        [.contRef K₂.length]⟩ := by
  intro s K f code h hK hfr hc
  obtain ⟨a₀, c₀, rfl, ha, hc'⟩ := inv_two hc
  have ha₀ : a₀ = .core (.ref (.func a)) := inv_refFunc ha
  have hc₀ : c₀ = .fx (.contNew ct) := inv_fx hc'
  have hf' : s.funcs[a]? = some fi := by rw [← h.funcs]; exact hf
  have hC : ContRn n ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType fi.type)]⟩
      ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType fi.type)]⟩ := fun c => by
    simp
  refine ⟨_, t, _, by rw [ha₀, hc₀]; exact StepFX'.contNew (K := K) (f := f) (ct := ct) hf', ?_, h,
    kRn_push hK hC⟩
  have hfr' : f₀ = rnFrame n f := hfr
  simp [rnCfgV, hfr', kRn_length hK]

theorem bwd_contBind {kk : Nat} {C : ContFX} {ct ct' : TypeIdx} (hk : K₂[kk]? = some (some C)) :
    Bwd P n ⟨t, K₂, f₀, fvals vs ++ [.contRef kk, .fx (.contBind ct ct')]⟩
      ⟨t, K₂.set kk none ++ [some ⟨fun c => C.plug (fvals vs ++ c)⟩], f₀,
        [.contRef K₂.length]⟩ := by
  intro s K f code h hK hfr hc
  obtain ⟨vs₀, a₀, c₀, rfl, rfl, ha, hc'⟩ := inv_fv_two hc
  have ha₀ : a₀ = .contRef kk := inv_contRef ha
  have hc₀ : c₀ = .fx (.contBind ct ct') := inv_fx hc'
  obtain ⟨C₀, hk₀, hC⟩ := kRn_some_back hK hk
  have hC' : ContRn n ⟨fun c => C₀.plug (fvals vs₀ ++ c)⟩
      ⟨fun c => C.plug (fvals (vs₀.map (rnFV n)) ++ c)⟩ := fun c => by
    show C.plug (fvals (vs₀.map (rnFV n)) ++ rnL n c) = rnL n (C₀.plug (fvals vs₀ ++ c))
    rw [← hC, rnL_append, rnL_fvals]
  have hst := StepFX'.contBind (P := P) (host := noHost) (fx := noFX) (s := s) (f := f)
    (vs := vs₀) (ct := ct) (ct' := ct') hk₀
  refine ⟨_, t, _, by rw [ha₀, hc₀]; exact hst, ?_, h, kRn_push (kRn_set hK kk) hC'⟩
  have hfr' : f₀ = rnFrame n f := hfr
  simp [rnCfgV, hfr', kRn_length hK]

theorem bwd_resume {kk : Nat} {C : ContFX} {ct : TypeIdx} {hs : List OnClause}
    {hs' : List HClause} (hk : K₂[kk]? = some (some C)) (hr : hs.mapM (resolve t f₀) = some hs') :
    Bwd P n ⟨t, K₂, f₀, fvals vs ++ [.contRef kk, .fx (.resume ct hs)]⟩
      ⟨t, K₂.set kk none, f₀, [.handler hs' (C.plug (fvals vs))]⟩ := by
  intro s K f code h hK hfr hc
  obtain ⟨vs₀, a₀, c₀, rfl, rfl, ha, hc'⟩ := inv_fv_two hc
  have ha₀ : a₀ = .contRef kk := inv_contRef ha
  have hc₀ : c₀ = .fx (.resume ct hs) := inv_fx hc'
  obtain ⟨C₀, hk₀, hC⟩ := kRn_some_back hK hk
  have hfr' : f₀ = rnFrame n f := hfr
  have hr₀ : hs.mapM (resolve s f) = some hs' := by rw [← resolve_rn h, ← hfr']; exact hr
  have hplug : C.plug (fvals (vs₀.map (rnFV n))) = rnL n (C₀.plug (fvals vs₀)) := by
    rw [← hC, rnL_fvals]
  refine ⟨_, t, _, by rw [ha₀, hc₀]; exact StepFX'.resume (s := s) (f := f) (vs := vs₀) hk₀ hr₀, ?_, h,
    kRn_set hK kk⟩
  simp [rnCfgV, hfr', hplug]

theorem bwd_resumeThrow {ws : List Val} {kk : Nat} {C : ContFX} {ct : TypeIdx} {x : TagIdx}
    {hs : List OnClause} {hs' : List HClause} {ta : Nat} {ti : TagInst}
    (hk : K₂[kk]? = some (some C)) (ht : t.tag? f₀ x = some (ta, ti))
    (hr : hs.mapM (resolve t f₀) = some hs') :
    Bwd P n ⟨t, K₂, f₀, cvals ws ++ [.contRef kk, .fx (.resumeThrow ct x hs)]⟩
      ⟨t.addExn ⟨ta, ws⟩, K₂.set kk none, f₀, [.handler hs' (C.plug (cthrowing t.exns.length))]⟩ := by
  intro s K f code h hK hfr hc
  obtain ⟨L₁, L₂, rfl, h₁, h₂⟩ := inv_app hc
  obtain ⟨ws₀, rfl, rfl⟩ := inv_cv h₁
  obtain ⟨a₀, c₀, rfl, ha, hc'⟩ := inv_two h₂
  have ha₀ : a₀ = .contRef kk := inv_contRef ha
  have hc₀ : c₀ = .fx (.resumeThrow ct x hs) := inv_fx hc'
  obtain ⟨C₀, hk₀, hC⟩ := kRn_some_back hK hk
  have hfr' : f₀ = rnFrame n f := hfr
  have hr₀ : hs.mapM (resolve s f) = some hs' := by rw [← resolve_rn h, ← hfr']; exact hr
  have ht₀ : s.tag? f x = some (ta, ti) := by rw [← tag?_rn h, ← hfr']; exact ht
  have hlen : t.exns.length = rnIdx n s.exns.length :=
    Silmaril.Proofs.Wasm.Models.FXRenameSim.exns_length_rn h
  have hplug : C.plug (cthrowing t.exns.length) = rnL n (C₀.plug (cthrowing s.exns.length)) := by
    rw [← hC, rnL_cthrowing, hlen]
  have hs' : ExnRen n (s.addExn ⟨ta, ws₀⟩) (t.addExn ⟨ta, ws₀.map (rnVal n)⟩) :=
    Silmaril.Proofs.Wasm.Models.FXRenameSim.addExn_rn h ⟨ta, ws₀⟩
  have hst := StepFX'.resumeThrow (P := P) (host := noHost) (fx := noFX) (s := s) (f := f)
    (vs := ws₀) (ct := ct) hk₀ ht₀ hr₀
  refine ⟨_, _, _, by rw [ha₀, hc₀]; exact hst, ?_, hs', kRn_set hK kk⟩
  simp [rnCfgV, hfr', hplug]

theorem bwd_suspend {hs : List HClause} {E : CtxV} {x : TagIdx} {ta : Nat} {ti : TagInst}
    {l : LabelIdx} (ht : t.tag? (E.frameAt f₀) x = some (ta, ti)) (hE : ¬ E.Handles ta)
    (hcl : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
    Bwd P n ⟨t, K₂, f₀, [.handler hs (E.plug (fvals vs ++ [.fx (.suspend x)]))]⟩
      ⟨t, K₂ ++ [some ⟨E.plug⟩], f₀, fvals vs ++ [.contRef K₂.length, .core (.plain (.br l))]⟩ := by
  intro s K f code h hK hfr hc
  obtain ⟨E₀, X₀, rfl, rfl, hX⟩ := inv_handler_plug hc
  obtain ⟨vs₀, a₀, rfl, rfl, ha⟩ := inv_fv_one hX
  have ha₀ : a₀ = .fx (.suspend x) := inv_fx ha
  have hfr' : f₀ = rnFrame n f := hfr
  have ht₀ : s.tag? (E₀.frameAt f) x = some (ta, ti) := by
    rw [← tag?_rn h, ← rnCtx_frameAt, ← hfr']; exact ht
  have hE₀ : ¬ E₀.Handles ta := by rw [← rnCtx_handles (n := n)]; exact hE
  refine ⟨_, t, _, by rw [ha₀]; exact StepFX'.suspend (s := s) (K := K) (vs := vs₀) ht₀ hE₀ hcl, ?_, h,
    kRn_push hK (contRn_ctx E₀)⟩
  simp [rnCfgV, hfr', kRn_length hK]

theorem bwd_switch {hs : List HClause} {E : CtxV} {kk : Nat} {C : ContFX} {ct : TypeIdx}
    {x : TagIdx} {ta : Nat} {ti : TagInst} (hk : K₂[kk]? = some (some C))
    (ht : t.tag? (E.frameAt f₀) x = some (ta, ti)) (hE : ¬ E.Handles ta)
    (hcl : hs.find? (fun c => c.tag == ta) = some (.onSwitch ta)) :
    Bwd P n ⟨t, K₂, f₀, [.handler hs (E.plug (fvals vs ++ [.contRef kk, .fx (.switch ct x)]))]⟩
      ⟨t, K₂.set kk none ++ [some ⟨E.plug⟩], f₀,
        [.handler hs (C.plug (fvals vs ++ [.contRef K₂.length]))]⟩ := by
  intro s K f code h hK hfr hc
  obtain ⟨E₀, X₀, rfl, rfl, hX⟩ := inv_handler_plug hc
  obtain ⟨vs₀, a₀, c₀, rfl, rfl, ha, hc'⟩ := inv_fv_two hX
  have ha₀ : a₀ = .contRef kk := inv_contRef ha
  have hc₀ : c₀ = .fx (.switch ct x) := inv_fx hc'
  obtain ⟨C₀, hk₀, hC⟩ := kRn_some_back hK hk
  have hfr' : f₀ = rnFrame n f := hfr
  have ht₀ : s.tag? (E₀.frameAt f) x = some (ta, ti) := by
    rw [← tag?_rn h, ← rnCtx_frameAt, ← hfr']; exact ht
  have hE₀ : ¬ E₀.Handles ta := by rw [← rnCtx_handles (n := n)]; exact hE
  have hplug : C.plug (fvals (vs₀.map (rnFV n)) ++ [.contRef K₂.length]) =
      rnL n (C₀.plug (fvals vs₀ ++ [.contRef K.length])) := by
    rw [← hC, rnL_append, rnL_fvals, rnL_cons, rnL_nil, rnA_contRef, kRn_length hK]
  refine ⟨_, t, _, by rw [ha₀, hc₀]; exact StepFX'.switch (s := s) (vs := vs₀) (ct := ct) hk₀ ht₀ hE₀ hcl,
    ?_, h, kRn_push (kRn_set hK kk) (contRn_ctx E₀)⟩
  simp [rnCfgV, hfr', hplug]

/-- **The backward renaming simulation for `StepFX'`, one step.** -/
theorem stepV_rn_back {d₀ d : ConfigFX H} (hs : StepFX' P noHost noFX d₀ d) : Bwd P n d₀ d := by
  induction hs with
  | core h => exact bwd_core h
  | seq _ hne ih => exact bwd_seq ih hne
  | ctxLabel _ ih => exact bwd_ctxLabel ih
  | ctxFrame _ ih => exact bwd_ctxFrame ih
  | ctxHandler _ ih => exact bwd_ctxHandler ih
  | block hbt hm => exact bwd_block hbt hm
  | loop hbt hm => exact bwd_loop hbt hm
  | ifTrue hc => exact bwd_ifTrue hc
  | ifFalse => exact bwd_ifFalse
  | labelVals => exact bwd_labelVals
  | brLabelZero hl hn => exact bwd_brLabelZero hl hn
  | brLabelSucc hl => exact bwd_brLabelSucc hl
  | brHandler => exact bwd_brHandler
  | returnLabel => exact bwd_returnLabel
  | returnHandler => exact bwd_returnHandler
  | frameVals hn => exact bwd_frameVals hn
  | returnFrame hn => exact bwd_returnFrame hn
  | handlerVals => exact bwd_handlerVals
  | dropCont => exact bwd_dropCont
  | trapSeq hne => exact bwd_trapSeq hne
  | trapLabel => exact bwd_trapLabel
  | trapFrame => exact bwd_trapFrame
  | trapHandler => exact bwd_trapHandler
  | throwSeq hne => exact bwd_throwSeq hne
  | throwLabel => exact bwd_throwLabel
  | throwFrame => exact bwd_throwFrame
  | throwHandler => exact bwd_throwHandler
  | invoke _ _ _ hfx => exact absurd hfx (by simp [noFX])
  | contNew hf => exact bwd_contNew hf
  | contNewNull => exact bwd_contNewNull
  | contBind hk => exact bwd_contBind hk
  | contBindNull => exact bwd_contBindNull
  | contBindUsed hk => exact bwd_contBindUsed hk
  | resume hk hr => exact bwd_resume hk hr
  | resumeNull => exact bwd_resumeNull
  | resumeUsed hk => exact bwd_resumeUsed hk
  | resumeThrow hk ht hr => exact bwd_resumeThrow hk ht hr
  | resumeThrowNull => exact bwd_resumeThrowNull
  | suspend ht hE hc => exact bwd_suspend ht hE hc
  | switch hk ht hE hc => exact bwd_switch hk ht hE hc

end Silmaril.Proofs.Wasm.Models.FXRenameVSim
