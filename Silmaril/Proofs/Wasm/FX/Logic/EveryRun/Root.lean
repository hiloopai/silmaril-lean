module

public import Silmaril.Proofs.Wasm.FX.Logic.EveryRun.Split

/-!
# Inverting `StepFX'` at the last instruction: root steps

`Root P fx s K f V a y` lists the rules of `StepFX'` (`Silmaril.Wasm.Models.FXV`, no host calls)
whose left-hand side is exactly `fvals V ++ [a]`: every rule but `seq`, with the `trap` and
exception rules at an empty rest. **`step_last`**: a step of `fvals V ++ [a]` (for a non-value
`a`) is a root step of `fvals V₂ ++ [a]` for a suffix `V₂` of `V`, under the other values. Rules
for one instruction then invert by `cases` on `Root`, which discards every constructor for
another instruction.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Logic.EveryRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
  Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Logic (Conts)
open Silmaril.Proofs.Wasm.Models.FXVRuns (fval? fnvF fvals_append_cons_inj seq_splitF
  no_step_fvals' invoke_eq fvals_liftV')
open Silmaril.Proofs.Wasm.Models.FXLower (blockFX_noHost)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **The root steps** of `fvals V ++ [a]` from `s, K, f`. -/
inductive Root (P : Profile) (fx : H → Option FuncFX) (s : Store H) (K : Conts) (f : Frame) :
    List FVal → AdminFX → ConfigFX H → Prop where
  | core {W : List Val} {a : Admin} {s' : Store H} {f' : Frame} {cs' : List Admin}
      (h : Step P noHost ⟨s, f, vals W ++ [a]⟩ ⟨s', f', cs'⟩) :
      Root P fx s K f (liftV W) (.core a) ⟨s', K, f', cs'.map .core⟩
  | ctxLabel {n : Nat} {k : List InstrFX} {es es' : List AdminFX} {s' : Store H} {K' : Conts}
      {f' : Frame} (h : StepFX' P noHost fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
      Root P fx s K f [] (.label n k es) ⟨s', K', f', [.label n k es']⟩
  | ctxFrame {n : Nat} {fi fi' : Frame} {es es' : List AdminFX} {s' : Store H} {K' : Conts}
      (h : StepFX' P noHost fx ⟨s, K, fi, es⟩ ⟨s', K', fi', es'⟩) :
      Root P fx s K f [] (.frame n fi es) ⟨s', K', f, [.frame n fi' es']⟩
  | ctxHandler {hs : List HClause} {es es' : List AdminFX} {s' : Store H} {K' : Conts}
      {f' : Frame} (h : StepFX' P noHost fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
      Root P fx s K f [] (.handler hs es) ⟨s', K', f', [.handler hs es']⟩
  | block {bt : BlockType} {body : List InstrFX} {vs : List FVal} {t₁ t₂ : List CValType}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
      Root P fx s K f vs (.block bt body)
        ⟨s, K, f, [.label t₂.length [] (fvals vs ++ body.map InstrFX.toAdmin)]⟩
  | loop {bt : BlockType} {body : List InstrFX} {vs : List FVal} {t₁ t₂ : List CValType}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
      Root P fx s K f vs (.loop bt body)
        ⟨s, K, f, [.label t₁.length [.loop bt body] (fvals vs ++ body.map InstrFX.toAdmin)]⟩
  | ifTrue {c : BitVec 32} {bt : BlockType} {b₁ b₂ : List InstrFX} (hc : c ≠ 0) :
      Root P fx s K f [.val (Val.i32 c)] (.if_ bt b₁ b₂) ⟨s, K, f, [.block bt b₁]⟩
  | ifFalse {bt : BlockType} {b₁ b₂ : List InstrFX} :
      Root P fx s K f [.val (Val.i32 0)] (.if_ bt b₁ b₂) ⟨s, K, f, [.block bt b₂]⟩
  | labelVals {n : Nat} {k : List InstrFX} {vs : List FVal} :
      Root P fx s K f [] (.label n k (fvals vs)) ⟨s, K, f, fvals vs⟩
  | brLabelZero {n : Nat} {k : List InstrFX} {vs' vs : List FVal} {l : LabelIdx}
      {rest : List AdminFX} (hl : l.toNat = 0) (hn : vs.length = n) :
      Root P fx s K f [] (.label n k (fvals vs' ++ fvals vs ++ [.core (.plain (.br l))] ++ rest))
        ⟨s, K, f, fvals vs ++ k.map InstrFX.toAdmin⟩
  | brLabelSucc {n : Nat} {k : List InstrFX} {vs : List FVal} {l : LabelIdx}
      {rest : List AdminFX} (hl : 0 < l.toNat) :
      Root P fx s K f [] (.label n k (fvals vs ++ [.core (.plain (.br l))] ++ rest))
        ⟨s, K, f, fvals vs ++ [.core (.plain (.br (labelPred l)))]⟩
  | brHandler {hs : List HClause} {vs : List FVal} {l : LabelIdx} {rest : List AdminFX} :
      Root P fx s K f [] (.handler hs (fvals vs ++ [.core (.plain (.br l))] ++ rest))
        ⟨s, K, f, fvals vs ++ [.core (.plain (.br l))]⟩
  | returnLabel {n : Nat} {k : List InstrFX} {vs : List FVal} {rest : List AdminFX} :
      Root P fx s K f [] (.label n k (fvals vs ++ [.core (.plain .return_)] ++ rest))
        ⟨s, K, f, fvals vs ++ [.core (.plain .return_)]⟩
  | returnHandler {hs : List HClause} {vs : List FVal} {rest : List AdminFX} :
      Root P fx s K f [] (.handler hs (fvals vs ++ [.core (.plain .return_)] ++ rest))
        ⟨s, K, f, fvals vs ++ [.core (.plain .return_)]⟩
  | frameVals {n : Nat} {fi : Frame} {vs : List FVal} (hn : vs.length = n) :
      Root P fx s K f [] (.frame n fi (fvals vs)) ⟨s, K, f, fvals vs⟩
  | returnFrame {n : Nat} {fi : Frame} {vs' vs : List FVal} {rest : List AdminFX}
      (hn : vs.length = n) :
      Root P fx s K f [] (.frame n fi (fvals vs' ++ fvals vs ++ [.core (.plain .return_)] ++ rest))
        ⟨s, K, f, fvals vs⟩
  | handlerVals {hs : List HClause} {vs : List FVal} :
      Root P fx s K f [] (.handler hs (fvals vs)) ⟨s, K, f, fvals vs⟩
  | dropCont {k : Nat} : Root P fx s K f [.cont k] (.core (.plain .drop)) ⟨s, K, f, []⟩
  | trapSeq {vs : List FVal} (hne : vs ≠ []) :
      Root P fx s K f vs (.core .trap) ⟨s, K, f, [.core .trap]⟩
  | trapLabel {n : Nat} {k : List InstrFX} :
      Root P fx s K f [] (.label n k [.core .trap]) ⟨s, K, f, [.core .trap]⟩
  | trapFrame {n : Nat} {fi : Frame} :
      Root P fx s K f [] (.frame n fi [.core .trap]) ⟨s, K, f, [.core .trap]⟩
  | trapHandler {hs : List HClause} :
      Root P fx s K f [] (.handler hs [.core .trap]) ⟨s, K, f, [.core .trap]⟩
  | throwSeq {vs : List FVal} {a : Nat} (hne : vs ≠ []) :
      Root P fx s K f (vs ++ [.val (.ref (.exn a))]) (.core (.plain .throwRef))
        ⟨s, K, f, cthrowing a⟩
  | throwLabel {n : Nat} {k : List InstrFX} {a : Nat} :
      Root P fx s K f [] (.label n k (cthrowing a)) ⟨s, K, f, cthrowing a⟩
  | throwFrame {n : Nat} {fi : Frame} {a : Nat} :
      Root P fx s K f [] (.frame n fi (cthrowing a)) ⟨s, K, f, cthrowing a⟩
  | throwHandler {hs : List HClause} {a : Nat} :
      Root P fx s K f [] (.handler hs (cthrowing a)) ⟨s, K, f, cthrowing a⟩
  | invoke {c : Admin} {vs : List Val} {a : Nat} {fi : FuncInst H} {h : H} {F : FuncFX}
      (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host h)
      (hfx : fx h = some F) (hn : vs.length = F.nparams) :
      Root P fx s K f (liftV vs ++ [.val (.ref (.func a))]) (.core c)
        ⟨s, K, f, [.frame F.nresults (Frame.forCall F.module vs F.locals)
          [.label F.nresults [] (F.body.map InstrFX.toAdmin)]]⟩
  | contNew {a : Nat} {fi : FuncInst H} {ct : TypeIdx} (hf : s.funcs[a]? = some fi) :
      Root P fx s K f [.val (.ref (.func a))] (.fx (.contNew ct))
        ⟨s, K ++ [some ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType fi.type)]⟩],
          f, [.contRef K.length]⟩
  | contNewNull {ct : TypeIdx} :
      Root P fx s K f [.val (.ref .null)] (.fx (.contNew ct)) ⟨s, K, f, [.core .trap]⟩
  | contBind {vs : List FVal} {k : Nat} {C : ContFX} {ct ct' : TypeIdx}
      (hk : K[k]? = some (some C)) :
      Root P fx s K f (vs ++ [.cont k]) (.fx (.contBind ct ct'))
        ⟨s, K.set k none ++ [some ⟨fun c => C.plug (fvals vs ++ c)⟩], f, [.contRef K.length]⟩
  | contBindNull {vs : List FVal} {ct ct' : TypeIdx} :
      Root P fx s K f (vs ++ [.val (.ref .null)]) (.fx (.contBind ct ct')) ⟨s, K, f, [.core .trap]⟩
  | contBindUsed {vs : List FVal} {k : Nat} {ct ct' : TypeIdx} (hk : K[k]? = some none) :
      Root P fx s K f (vs ++ [.cont k]) (.fx (.contBind ct ct')) ⟨s, K, f, [.core .trap]⟩
  | resume {vs : List FVal} {k : Nat} {C : ContFX} {ct : TypeIdx} {hs : List OnClause}
      {hs' : List HClause} (hk : K[k]? = some (some C)) (hr : hs.mapM (resolve s f) = some hs') :
      Root P fx s K f (vs ++ [.cont k]) (.fx (.resume ct hs))
        ⟨s, K.set k none, f, [.handler hs' (C.plug (fvals vs))]⟩
  | resumeNull {vs : List FVal} {ct : TypeIdx} {hs : List OnClause} :
      Root P fx s K f (vs ++ [.val (.ref .null)]) (.fx (.resume ct hs)) ⟨s, K, f, [.core .trap]⟩
  | resumeUsed {vs : List FVal} {k : Nat} {ct : TypeIdx} {hs : List OnClause}
      (hk : K[k]? = some none) :
      Root P fx s K f (vs ++ [.cont k]) (.fx (.resume ct hs)) ⟨s, K, f, [.core .trap]⟩
  | resumeThrow {vs : List Val} {k : Nat} {C : ContFX} {ct : TypeIdx} {x : TagIdx}
      {hs : List OnClause} {hs' : List HClause} {ta : Nat} {ti : TagInst}
      (hk : K[k]? = some (some C)) (ht : s.tag? f x = some (ta, ti))
      (hr : hs.mapM (resolve s f) = some hs') :
      Root P fx s K f (liftV vs ++ [.cont k]) (.fx (.resumeThrow ct x hs))
        ⟨s.addExn ⟨ta, vs⟩, K.set k none, f, [.handler hs' (C.plug (cthrowing s.exns.length))]⟩
  | resumeThrowNull {vs : List Val} {ct : TypeIdx} {x : TagIdx} {hs : List OnClause} :
      Root P fx s K f (liftV vs ++ [.val (.ref .null)]) (.fx (.resumeThrow ct x hs))
        ⟨s, K, f, [.core .trap]⟩
  | suspend {hs : List HClause} {E : CtxV} {vs : List FVal} {x : TagIdx} {ta : Nat}
      {ti : TagInst} {l : LabelIdx}
      (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
      (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
      Root P fx s K f [] (.handler hs (E.plug (fvals vs ++ [.fx (.suspend x)])))
        ⟨s, K ++ [some ⟨E.plug⟩], f, fvals vs ++ [.contRef K.length, .core (.plain (.br l))]⟩
  | switch {hs : List HClause} {E : CtxV} {vs : List FVal} {k : Nat} {C : ContFX}
      {ct : TypeIdx} {x : TagIdx} {ta : Nat} {ti : TagInst} (hk : K[k]? = some (some C))
      (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
      (hc : hs.find? (fun c => c.tag == ta) = some (.onSwitch ta)) :
      Root P fx s K f [] (.handler hs (E.plug (fvals vs ++ [.contRef k, .fx (.switch ct x)])))
        ⟨s, K.set k none ++ [some ⟨E.plug⟩], f,
          [.handler hs (C.plug (fvals vs ++ [.contRef K.length]))]⟩

variable {P : Profile} {fx : H → Option FuncFX}

/-- What a step of `fvals V ++ [a]` is (`step_last`). -/
def LastRes (P : Profile) (fx : H → Option FuncFX) (s : Store H) (K : Conts) (f : Frame)
    (V : List FVal) (a : AdminFX) (y : ConfigFX H) : Prop :=
  ∃ V₁ V₂ y', V = V₁ ++ V₂ ∧ Root P fx s K f V₂ a y' ∧
    y = ⟨y'.store, y'.conts, y'.frame, fvals V₁ ++ y'.code⟩

theorem root_last {s : Store H} {K : Conts} {f : Frame} {vs V : List FVal} {e a : AdminFX}
    {c : List AdminFX} {y : ConfigFX H} (hr : Root P fx s K f vs e y) (hc : c = fvals vs ++ [e])
    (he : fval? e = none) (ha : fval? a = none) (hx : c = fvals V ++ [a]) :
    LastRes P fx s K f V a y := by
  obtain ⟨rfl, rfl, -⟩ := fvals_append_cons_inj (hc.symm.trans hx) he ha
  exact ⟨[], vs, y, rfl, hr, rfl⟩

theorem LastRes.lift {s s' : Store H} {K K' : Conts} {f f' : Frame} {V₂ : List FVal}
    {a : AdminFX} {es' : List AdminFX} (vs : List FVal)
    (h : LastRes P fx s K f V₂ a ⟨s', K', f', es'⟩) :
    LastRes P fx s K f (vs ++ V₂) a ⟨s', K', f', fvals vs ++ es'⟩ := by
  obtain ⟨V₁, V₃, y', rfl, hr, hy⟩ := h
  refine ⟨vs ++ V₁, V₃, y', by simp, hr, ?_⟩
  simp only [ConfigFX.mk.injEq] at hy ⊢
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hy
  simp

theorem core_last {s s' : Store H} {K : Conts} {f f' : Frame} {cs cs' : List Admin}
    (h : Step P (blockFX noHost fx) ⟨s, f, cs⟩ ⟨s', f', cs'⟩) {V : List FVal} {a : AdminFX}
    (ha : fval? a = none) (hx : cs.map AdminFX.core = fvals V ++ [a]) :
    LastRes P fx s K f V a ⟨s', K, f', cs'.map .core⟩ := by
  obtain ⟨W, a', R', rfl, rfl, hR, rfl, -⟩ := map_core_split ha hx
  have hR' : R' = [] := List.map_eq_nil_iff.mp hR.symm
  rw [hR'] at h
  rw [blockFX_noHost] at h
  exact ⟨[], liftV W, _, rfl, .core h, rfl⟩

theorem seq_last {s s' : Store H} {K K' : Conts} {f f' : Frame} {vs : List FVal}
    {es es' rest : List AdminFX} (h : StepFX' P noHost fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩)
    (ih : ∀ V a, fval? a = none → es = fvals V ++ [a] → LastRes P fx s K f V a ⟨s', K', f', es'⟩)
    {V : List FVal} {a : AdminFX} (ha : fval? a = none)
    (hx : fvals vs ++ es ++ rest = fvals V ++ [a]) :
    LastRes P fx s K f V a ⟨s', K', f', fvals vs ++ es' ++ rest⟩ := by
  rcases seq_splitF ha hx with ⟨U, hU⟩ | ⟨V₂, T₁, rfl, hes, hT⟩
  · exact absurd hU (no_step_fvals' h U)
  · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hT.symm
    simpa using (ih V₂ a ha (by simpa using hes)).lift vs

theorem trapSeq_last {s : Store H} {K : Conts} {f : Frame} {vs : List FVal}
    {rest : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ []) {V : List FVal} {a : AdminFX}
    (ha : fval? a = none) (hx : fvals vs ++ [.core .trap] ++ rest = fvals V ++ [a]) :
    LastRes P fx s K f V a ⟨s, K, f, [.core .trap]⟩ := by
  have hx' : fvals vs ++ .core .trap :: rest = fvals V ++ a :: [] := by rw [← hx]; simp
  obtain ⟨rfl, rfl, rfl⟩ := fvals_append_cons_inj hx' rfl ha
  exact ⟨[], vs, _, rfl, .trapSeq (by simpa using hne), rfl⟩

theorem throwSeq_last {s : Store H} {K : Conts} {f : Frame} {vs : List FVal} {b : Nat}
    {rest : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ []) {V : List FVal} {a : AdminFX}
    (ha : fval? a = none) (hx : fvals vs ++ cthrowing b ++ rest = fvals V ++ [a]) :
    LastRes P fx s K f V a ⟨s, K, f, cthrowing b⟩ := by
  have hx' : fvals (vs ++ [.val (.ref (.exn b))]) ++ .core (.plain .throwRef) :: rest =
      fvals V ++ a :: [] := by
    rw [← hx]; simp [cthrowing, throwing, FVal.toAdmin, Val.toAdmin]
  obtain ⟨rfl, rfl, rfl⟩ := fvals_append_cons_inj hx' rfl ha
  have hv : vs ≠ [] := by simpa using hne
  exact ⟨[], _, _, rfl, .throwSeq hv, rfl⟩

/-- **A step of `fvals V ++ [a]` is a root step under some of the values.** -/
theorem step_last {x y : ConfigFX H} (h : StepFX' P noHost fx x y) :
    ∀ V a, fval? a = none → x.code = fvals V ++ [a] → LastRes P fx x.store x.conts x.frame V a y := by
  induction h with
  | core h => exact fun V a ha hx => core_last h ha hx
  | seq h _ ih => exact fun V a ha hx => seq_last h ih ha hx
  | ctxLabel h => exact fun V a ha hx => root_last (.ctxLabel h) rfl rfl ha hx
  | ctxFrame h => exact fun V a ha hx => root_last (.ctxFrame h) rfl rfl ha hx
  | ctxHandler h => exact fun V a ha hx => root_last (.ctxHandler h) rfl rfl ha hx
  | block hbt hm => exact fun V a ha hx => root_last (.block hbt hm) rfl rfl ha hx
  | loop hbt hm => exact fun V a ha hx => root_last (.loop hbt hm) rfl rfl ha hx
  | ifTrue hc => exact fun V a ha hx => root_last (.ifTrue hc) rfl rfl ha hx
  | ifFalse => exact fun V a ha hx => root_last .ifFalse rfl rfl ha hx
  | labelVals => exact fun V a ha hx => root_last .labelVals rfl rfl ha hx
  | brLabelZero hl hn => exact fun V a ha hx => root_last (.brLabelZero hl hn) rfl rfl ha hx
  | brLabelSucc hl => exact fun V a ha hx => root_last (.brLabelSucc hl) rfl rfl ha hx
  | brHandler => exact fun V a ha hx => root_last .brHandler rfl rfl ha hx
  | returnLabel => exact fun V a ha hx => root_last .returnLabel rfl rfl ha hx
  | returnHandler => exact fun V a ha hx => root_last .returnHandler rfl rfl ha hx
  | frameVals hn => exact fun V a ha hx => root_last (.frameVals hn) rfl rfl ha hx
  | returnFrame hn => exact fun V a ha hx => root_last (.returnFrame hn) rfl rfl ha hx
  | handlerVals => exact fun V a ha hx => root_last .handlerVals rfl rfl ha hx
  | dropCont => exact fun V a ha hx => root_last .dropCont rfl rfl ha hx
  | trapSeq hne => exact fun V a ha hx => trapSeq_last hne ha hx
  | trapLabel => exact fun V a ha hx => root_last .trapLabel rfl rfl ha hx
  | trapFrame => exact fun V a ha hx => root_last .trapFrame rfl rfl ha hx
  | trapHandler => exact fun V a ha hx => root_last .trapHandler rfl rfl ha hx
  | throwSeq hne => exact fun V a ha hx => throwSeq_last hne ha hx
  | throwLabel => exact fun V a ha hx => root_last .throwLabel rfl rfl ha hx
  | throwFrame => exact fun V a ha hx => root_last .throwFrame rfl rfl ha hx
  | throwHandler => exact fun V a ha hx => root_last .throwHandler rfl rfl ha hx
  | @invoke s K f c vs a fi h F hc hf hcode hfx hn =>
    intro V b hb hx
    have hcv : fval? (.core c) = none := by
      simpa [fval?] using Silmaril.Proofs.Wasm.Models.FXLower.IsCallRef.val?_none hc
    exact root_last (.invoke hc hf hcode hfx hn) (invoke_eq vs a c) hcv hb hx
  | contNew hf => exact fun V a ha hx => root_last (.contNew hf) rfl rfl ha hx
  | contNewNull => exact fun V a ha hx => root_last .contNewNull rfl rfl ha hx
  | @contBind s K f vs k C ct ct' hk =>
    intro V b hb hx
    exact root_last (.contBind (vs := vs) (ct := ct) (ct' := ct') hk) (by simp [FVal.toAdmin]) rfl hb hx
  | @contBindNull s K f vs ct ct' =>
    intro V b hb hx
    exact root_last (.contBindNull (vs := vs) (ct := ct) (ct' := ct')) (by simp [FVal.toAdmin, Val.toAdmin]) rfl hb hx
  | @contBindUsed s K f vs k ct ct' hk =>
    intro V b hb hx
    exact root_last (.contBindUsed (vs := vs) (ct := ct) (ct' := ct') hk) (by simp [FVal.toAdmin]) rfl hb hx
  | @resume s K f vs k C ct hs hs' hk hr =>
    intro V b hb hx
    exact root_last (.resume (vs := vs) (ct := ct) hk hr) (by simp [FVal.toAdmin]) rfl hb hx
  | @resumeNull s K f vs ct hs =>
    intro V b hb hx
    exact root_last (.resumeNull (vs := vs) (ct := ct) (hs := hs)) (by simp [FVal.toAdmin, Val.toAdmin]) rfl hb hx
  | @resumeUsed s K f vs k ct hs hk =>
    intro V b hb hx
    exact root_last (.resumeUsed (vs := vs) (ct := ct) (hs := hs) hk) (by simp [FVal.toAdmin]) rfl hb hx
  | @resumeThrow s K f vs k C ct x hs hs' ta ti hk ht hr =>
    intro V a ha hx
    exact root_last (.resumeThrow (vs := vs) (ct := ct) hk ht hr) (by simp [FVal.toAdmin]) rfl ha hx
  | @resumeThrowNull s K f vs ct x hs =>
    intro V a ha hx
    exact root_last (.resumeThrowNull (vs := vs) (ct := ct) (x := x) (hs := hs))
      (by simp; rfl) rfl ha hx
  | suspend ht hE hc => exact fun V a ha hx => root_last (.suspend ht hE hc) rfl rfl ha hx
  | switch hk ht hE hc => exact fun V a ha hx => root_last (.switch hk ht hE hc) rfl rfl ha hx

end Silmaril.Proofs.Wasm.FX.Logic.EveryRun
