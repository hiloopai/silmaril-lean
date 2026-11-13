module

public import Silmaril.Proofs.Wasm.Models.FXResumeT.KRen

/-!
# The simulation that ignores consumed slots: one step of `StepFXR`

**`sim_step`**: if `K₂` is `K₁` with the slots in `B` ignored and the rest renamed by `ρ`
(`KRel ρ B K₁ K₂`), and the code avoids `B`, then every `StepFXR` step of `⟨s, K₁, f, c⟩` is
matched by one step of `⟨s, K₂, f, rnL ρ c⟩`, to a configuration related in the same way. Any
host and any FX function table.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXResumeT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXResume Silmaril.Wasm.Models.FXResumeT
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}
  {ρ : Nat → Nat} {B : Nat → Prop}

/-- Normalise renamed code. -/
macro "rn_norm" : tactic => `(tactic| simp only [rnL_append, rnL_fvals, rnL_map_core, rnL_cvals,
  rnL_cthrowing, rnL_toAdmin, rnL, rnA, ← rnE_plug])

/-- Normalise avoidance. -/
macro "av_norm" h:ident : tactic => `(tactic| simp only [avL_append, avL, avA, avL_plug,
  avL_map_core, avL_cvals, avL_cthrowing, avL_toAdmin, and_true, true_and] at $h:ident)

/-- Close an avoidance goal from the hypotheses. -/
macro "av_tac" : tactic => `(tactic| (try simp only [avL_append, avL, avA, avL_plug,
  avL_map_core, avL_cvals, avL_cthrowing, avL_toAdmin, and_true, true_and] at *) <;> try tauto)

/-- The conclusion of `sim_step`. -/
def SimC (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX) (ρ : Nat → Nat)
    (B : Nat → Prop) (x y : ConfigFX H) : Prop :=
  ∀ K₂, KRel ρ B x.conts K₂ → avL B x.code →
    ∃ K₂', StepFXR P host fx ⟨x.store, K₂, x.frame, rnL ρ x.code⟩
        ⟨y.store, K₂', y.frame, rnL ρ y.code⟩ ∧ KRel ρ B y.conts K₂' ∧ avL B y.code

/-- A step that keeps the continuation store, with renamed code given. -/
theorem simC_same {s s' : Store H} {K : List (Option ContFX)} {f f' : Frame}
    {c c' : List AdminFX}
    (h : ∀ K₂ : List (Option ContFX), StepFXR P host fx ⟨s, K₂, f, rnL ρ c⟩ ⟨s', K₂, f', rnL ρ c'⟩)
    (hav : avL B c → avL B c') : SimC P host fx ρ B ⟨s, K, f, c⟩ ⟨s', K, f', c'⟩ :=
  fun K₂ hK hc => ⟨K₂, h K₂, hK, hav hc⟩

/-- The continuation of `cont.new`: plug, then call. -/
theorem contR_call (a : Nat) (t : Silmaril.Wasm.Validation.DefType) :
    ContR ρ B ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType t)]⟩
      ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType t)]⟩ := by
  intro c hc
  refine ⟨?_, ?_⟩
  · simp only [avL_append, avL, avA, and_true]
    exact hc
  · simp

/-- The continuation of `cont.bind`: the bound values go first. -/
theorem contR_bind {C₁ C₂ : ContFX} {vs : List FVal} (hC : ContR ρ B C₁ C₂)
    (hv : avL B (fvals vs)) :
    ContR ρ B ⟨fun c => C₁.plug (fvals vs ++ c)⟩ ⟨fun c => C₂.plug (fvals (rnV ρ vs) ++ c)⟩ := by
  intro c hc
  have h := hC (fvals vs ++ c) ((avL_append _ _).mpr ⟨hv, hc⟩)
  refine ⟨h.1, ?_⟩
  have he : fvals (rnV ρ vs) ++ rnL ρ c = rnL ρ (fvals vs ++ c) := by simp
  show C₂.plug (fvals (rnV ρ vs) ++ rnL ρ c) = rnL ρ (C₁.plug (fvals vs ++ c))
  rw [he]
  exact h.2

/-- The continuation captured by `suspend` and `switch`. -/
theorem contR_ctx {E : CtxV} (hE : avE B E) : ContR ρ B ⟨E.plug⟩ ⟨(rnE ρ E).plug⟩ := by
  intro c hc
  exact ⟨(avL_plug E c).mpr ⟨hE, hc⟩, rnE_plug E c⟩

/-! ## The structural cases -/

theorem simC_seq {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
    {vs : List FVal} {es es' rest : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ [])
    (ih : SimC P host fx ρ B ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
    SimC P host fx ρ B ⟨s, K, f, fvals vs ++ es ++ rest⟩ ⟨s', K', f', fvals vs ++ es' ++ rest⟩ := by
  intro K₂ hK hav
  simp only [avL_append] at hav
  obtain ⟨K₂', hst, hK', hes'⟩ := ih K₂ hK hav.1.2
  refine ⟨K₂', ?_, hK', ?_⟩
  · rn_norm
    exact .seq hst (by simpa using hne)
  · simp only [avL_append]
    exact ⟨⟨hav.1.1, hes'⟩, hav.2⟩

theorem simC_label {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame} {n : Nat}
    {k : List InstrFX} {es es' : List AdminFX}
    (ih : SimC P host fx ρ B ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
    SimC P host fx ρ B ⟨s, K, f, [.label n k es]⟩ ⟨s', K', f', [.label n k es']⟩ := by
  intro K₂ hK hav
  obtain ⟨K₂', hst, hK', hes'⟩ := ih K₂ hK hav.1
  exact ⟨K₂', by rn_norm; exact .ctxLabel hst, hK', hes', trivial⟩

theorem simC_frame {s s' : Store H} {K K' : List (Option ContFX)} {f fi fi' : Frame} {n : Nat}
    {es es' : List AdminFX} (ih : SimC P host fx ρ B ⟨s, K, fi, es⟩ ⟨s', K', fi', es'⟩) :
    SimC P host fx ρ B ⟨s, K, f, [.frame n fi es]⟩ ⟨s', K', f, [.frame n fi' es']⟩ := by
  intro K₂ hK hav
  obtain ⟨K₂', hst, hK', hes'⟩ := ih K₂ hK hav.1
  exact ⟨K₂', by rn_norm; exact .ctxFrame hst, hK', hes', trivial⟩

theorem simC_handler {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
    {hs : List HClause} {es es' : List AdminFX}
    (ih : SimC P host fx ρ B ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
    SimC P host fx ρ B ⟨s, K, f, [.handler hs es]⟩ ⟨s', K', f', [.handler hs es']⟩ := by
  intro K₂ hK hav
  obtain ⟨K₂', hst, hK', hes'⟩ := ih K₂ hK hav.1
  exact ⟨K₂', by rn_norm; exact .ctxHandler hst, hK', hes', trivial⟩

/-! ## The continuation cases -/

theorem simC_contNew {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct : TypeIdx} (hf : s.funcs[a]? = some fi) :
    SimC P host fx ρ B ⟨s, K, f, [.core (.ref (.func a)), .fx (.contNew ct)]⟩
      ⟨s, K ++ [some ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType fi.type)]⟩], f,
        [.contRef K.length]⟩ := by
  intro K₂ hK _
  refine ⟨_, ?_, kRel_append_some hK (contR_call a fi.type), ?_⟩
  · rn_norm
    rw [alloc_length hK]
    exact .contNew hf
  · exact ⟨fresh_length hK, trivial⟩

theorem simC_contBind {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal}
    {k : Nat} {C : ContFX} {ct ct' : TypeIdx} (hk : K[k]? = some (some C))
    (ha : BindArity f.module ct ct' vs.length) :
    SimC P host fx ρ B ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.contBind ct ct')]⟩
      ⟨s, K.set k none ++ [some ⟨fun c => C.plug (fvals vs ++ c)⟩], f, [.contRef K.length]⟩ := by
  intro K₂ hK hav
  av_norm hav
  obtain ⟨hv, hB⟩ := hav
  obtain ⟨C₂, hC₂, hCR⟩ := kRel_live hK hB hk
  refine ⟨_, ?_, kRel_append_some (kRel_set hK hB hk) (contR_bind hCR hv), fresh_length hK, trivial⟩
  rn_norm
  rw [alloc_length hK]
  exact .contBind hC₂ (by simpa using ha)

theorem simC_contBindUsed {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal}
    {k : Nat} {ct ct' : TypeIdx} (hk : K[k]? = some none)
    (ha : BindArity f.module ct ct' vs.length) :
    SimC P host fx ρ B ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.contBind ct ct')]⟩
      ⟨s, K, f, [.core .trap]⟩ := by
  intro K₂ hK hav
  av_norm hav
  refine ⟨K₂, ?_, hK, trivial, trivial⟩
  rn_norm
  exact .contBindUsed (kRel_used hK hav.2 hk) (by simpa using ha)

theorem simC_resume {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal}
    {k : Nat} {C : ContFX} {ct : TypeIdx} {hs : List OnClause} {hs' : List HClause}
    (hk : K[k]? = some (some C)) (hr : hs.mapM (resolve s f) = some hs')
    (ha : ResumeArity f.module ct vs.length) :
    SimC P host fx ρ B ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.resume ct hs)]⟩
      ⟨s, K.set k none, f, [.handler hs' (C.plug (fvals vs))]⟩ := by
  intro K₂ hK hav
  av_norm hav
  obtain ⟨hv, hB⟩ := hav
  obtain ⟨C₂, hC₂, hCR⟩ := kRel_live hK hB hk
  obtain ⟨hav', hpl⟩ := hCR (fvals vs) hv
  refine ⟨_, ?_, kRel_set hK hB hk, hav', trivial⟩
  rn_norm
  rw [← hpl, rnL_fvals]
  exact .resume hC₂ hr (by simpa using ha)

theorem simC_resumeUsed {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal}
    {k : Nat} {ct : TypeIdx} {hs : List OnClause} (hk : K[k]? = some none)
    (ha : ResumeArity f.module ct vs.length) :
    SimC P host fx ρ B ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.resume ct hs)]⟩
      ⟨s, K, f, [.core .trap]⟩ := by
  intro K₂ hK hav
  av_norm hav
  refine ⟨K₂, ?_, hK, trivial, trivial⟩
  rn_norm
  exact .resumeUsed (kRel_used hK hav.2 hk) (by simpa using ha)

theorem simC_resumeThrow {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val}
    {k : Nat} {C : ContFX} {ct : TypeIdx} {x : TagIdx} {hs : List OnClause}
    {hs' : List HClause} {ta : Nat} {ti : TagInst} (hk : K[k]? = some (some C))
    (ht : s.tag? f x = some (ta, ti)) (hr : hs.mapM (resolve s f) = some hs') :
    SimC P host fx ρ B ⟨s, K, f, cvals vs ++ [.contRef k, .fx (.resumeThrow ct x hs)]⟩
      ⟨s.addExn ⟨ta, vs⟩, K.set k none, f, [.handler hs' (C.plug (cthrowing s.exns.length))]⟩ := by
  intro K₂ hK hav
  av_norm hav
  obtain ⟨C₂, hC₂, hCR⟩ := kRel_live hK hav hk
  obtain ⟨hav', hpl⟩ := hCR (cthrowing s.exns.length) (avL_cthrowing _)
  refine ⟨_, ?_, kRel_set hK hav hk, hav', trivial⟩
  rn_norm
  rw [← hpl, rnL_cthrowing]
  exact .resumeThrow hC₂ ht hr

theorem simC_suspend {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
    {E : CtxV} {vs : List FVal} {x : TagIdx} {ta : Nat} {ti : TagInst} {l : LabelIdx}
    (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
    SimC P host fx ρ B ⟨s, K, f, [.handler hs (E.plug (fvals vs ++ [.fx (.suspend x)]))]⟩
      ⟨s, K ++ [some ⟨E.plug⟩], f, fvals vs ++ [.contRef K.length, .core (.plain (.br l))]⟩ := by
  intro K₂ hK hav
  av_norm hav
  refine ⟨_, ?_, kRel_append_some hK (contR_ctx hav.1), ?_⟩
  · rn_norm
    rw [alloc_length hK]
    exact .suspend (by simpa using ht) (by simpa using hE) hc
  · simp only [avL_append, avL, avA, and_true]
    exact ⟨hav.2, fresh_length hK⟩

theorem simC_switch {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
    {E : CtxV} {vs : List FVal} {k : Nat} {C : ContFX} {ct : TypeIdx} {x : TagIdx} {ta : Nat}
    {ti : TagInst} (hk : K[k]? = some (some C))
    (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
    (hc : hs.find? (fun c => c.tag == ta) = some (.onSwitch ta)) :
    SimC P host fx ρ B
      ⟨s, K, f, [.handler hs (E.plug (fvals vs ++ [.contRef k, .fx (.switch ct x)]))]⟩
      ⟨s, K.set k none ++ [some ⟨E.plug⟩], f,
        [.handler hs (C.plug (fvals vs ++ [.contRef K.length]))]⟩ := by
  intro K₂ hK hav
  av_norm hav
  obtain ⟨hEav, hv, hB⟩ := hav
  obtain ⟨C₂, hC₂, hCR⟩ := kRel_live hK hB hk
  have hcav : avL B (fvals vs ++ [.contRef K.length]) := by
    simp only [avL_append, avL, avA, and_true]
    exact ⟨hv, fresh_length hK⟩
  obtain ⟨hav', hpl⟩ := hCR _ hcav
  refine ⟨_, ?_, kRel_append_some (kRel_set hK hB hk) (contR_ctx hEav), hav', trivial⟩
  rn_norm
  rw [← hpl]
  rn_norm
  rw [alloc_length hK]
  exact .switch hC₂ (by simpa using ht) (by simpa using hE) hc

/-! ## One step -/

/-- **The simulation that ignores consumed slots, one step.** -/
theorem sim_step {x y : ConfigFX H} (h : StepFXR P host fx x y) : SimC P host fx ρ B x y := by
  induction h with
  | core h => exact simC_same (fun _ => by rn_norm; exact .core h) (fun _ => avL_map_core _)
  | seq _ hne ih => exact simC_seq hne ih
  | ctxLabel _ ih => exact simC_label ih
  | ctxFrame _ ih => exact simC_frame ih
  | ctxHandler _ ih => exact simC_handler ih
  | block hbt hm =>
    exact simC_same (fun _ => by rn_norm; exact .block hbt (by simpa using hm)) (fun _ => by av_tac)
  | loop hbt hm =>
    exact simC_same (fun _ => by rn_norm; exact .loop hbt (by simpa using hm)) (fun _ => by av_tac)
  | ifTrue hc => exact simC_same (fun _ => by rn_norm; exact .ifTrue hc) (fun _ => by av_tac)
  | ifFalse => exact simC_same (fun _ => by rn_norm; exact .ifFalse) (fun _ => by av_tac)
  | labelVals => exact simC_same (fun _ => by rn_norm; exact .labelVals) (fun _ => by av_tac)
  | brLabelZero hl hn =>
    exact simC_same (fun _ => by rn_norm; exact .brLabelZero hl (by simpa using hn))
      (fun _ => by av_tac)
  | brLabelSucc hl =>
    exact simC_same (fun _ => by rn_norm; exact .brLabelSucc hl) (fun _ => by av_tac)
  | brHandler => exact simC_same (fun _ => by rn_norm; exact .brHandler) (fun _ => by av_tac)
  | returnLabel => exact simC_same (fun _ => by rn_norm; exact .returnLabel) (fun _ => by av_tac)
  | returnHandler =>
    exact simC_same (fun _ => by rn_norm; exact .returnHandler) (fun _ => by av_tac)
  | frameVals hn =>
    exact simC_same (fun _ => by rn_norm; exact .frameVals (by simpa using hn))
      (fun _ => by av_tac)
  | returnFrame hn =>
    exact simC_same (fun _ => by rn_norm; exact .returnFrame (by simpa using hn))
      (fun _ => by av_tac)
  | handlerVals => exact simC_same (fun _ => by rn_norm; exact .handlerVals) (fun _ => by av_tac)
  | dropCont => exact simC_same (fun _ => by rn_norm; exact .dropCont) (fun _ => trivial)
  | trapSeq hne =>
    exact simC_same (fun _ => by rn_norm; exact .trapSeq (by simpa using hne))
      (fun _ => by av_tac)
  | trapLabel => exact simC_same (fun _ => by rn_norm; exact .trapLabel) (fun _ => by av_tac)
  | trapFrame => exact simC_same (fun _ => by rn_norm; exact .trapFrame) (fun _ => by av_tac)
  | trapHandler => exact simC_same (fun _ => by rn_norm; exact .trapHandler) (fun _ => by av_tac)
  | throwSeq hne =>
    exact simC_same (fun _ => by rn_norm; exact .throwSeq (by simpa using hne))
      (fun _ => by av_tac)
  | throwLabel => exact simC_same (fun _ => by rn_norm; exact .throwLabel) (fun _ => by av_tac)
  | throwFrame => exact simC_same (fun _ => by rn_norm; exact .throwFrame) (fun _ => by av_tac)
  | throwHandler =>
    exact simC_same (fun _ => by rn_norm; exact .throwHandler) (fun _ => by av_tac)
  | invoke hc hf hcode hfx hn =>
    exact simC_same (fun _ => by rn_norm; exact .invoke hc hf hcode hfx hn) (fun _ => by av_tac)
  | contNew hf => exact simC_contNew hf
  | contNewNull => exact simC_same (fun _ => by rn_norm; exact .contNewNull) (fun _ => by av_tac)
  | contBind hk ha => exact simC_contBind hk ha
  | contBindNull ha =>
    exact simC_same (fun _ => by rn_norm; exact .contBindNull (by simpa using ha))
      (fun _ => by av_tac)
  | contBindUsed hk ha => exact simC_contBindUsed hk ha
  | resume hk hr ha => exact simC_resume hk hr ha
  | resumeNull ha =>
    exact simC_same (fun _ => by rn_norm; exact .resumeNull (by simpa using ha))
      (fun _ => by av_tac)
  | resumeUsed hk ha => exact simC_resumeUsed hk ha
  | resumeThrow hk ht hr => exact simC_resumeThrow hk ht hr
  | resumeThrowNull =>
    exact simC_same (fun _ => by rn_norm; exact .resumeThrowNull) (fun _ => by av_tac)
  | suspend ht hE hc => exact simC_suspend ht hE hc
  | switch hk ht hE hc => exact simC_switch hk ht hE hc

end Silmaril.Proofs.Wasm.Models.FXResumeT
