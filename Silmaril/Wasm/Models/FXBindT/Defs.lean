module

public import Silmaril.Wasm.Models.FXV.Defs

/-!
# CoreFX with a typed `cont.bind`: `StepFXT`

Track H's `StepFX` and its corrected form `StepFX'` (`Silmaril.Wasm.Models.FXV`) are untyped:
`cont.bind $ct $ct'` binds **any** suffix of the operand stack. In the typed proposal it binds
exactly as many values as `$ct` has parameters beyond `$ct'`. This module adds a third
reduction relation **next to** the other two, without changing them:

* `contParams? m ct`: the parameter types of the continuation type `ct` in the module instance
  `m`. Silmaril's types have no continuation types, so the continuation type `cont $ft` is
  represented by its function type: `ct` is read as the index of `$ft`, and its parameters are
  those of the function type that `m.types[ct]` expands to (as `ModuleInst.blockType?` reads a
  block type index).
* `BindArity m ct ct' n`: `ct` and `ct'` resolve to function types and `n + |params ct'| =
  |params ct|`, so `cont.bind $ct $ct'` binds exactly `n` values.
* **`StepFXT P host fx`**: `StepFX'` with the three `cont.bind` rules (`contBind`,
  `contBindNull`, `contBindUsed`) restricted to operand lists of length `n` with
  `BindArity (frame's module) ct ct' n`. Every other rule is `StepFX'`'s, unchanged.
* `StepsFXT`, `behavioursFXT`: runs and behaviours, as for `StepFX'`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXBindT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Numerics (Profile)

/-- The parameter types of the continuation type `ct` (read as its function type). -/
def contParams? (m : ModuleInst) (ct : TypeIdx) : Option (List CValType) :=
  (m.types[ct.toNat]? >>= DefType.funcType?).map Prod.fst

/-- `cont.bind $ct $ct'` binds exactly `n` values in module instance `m`. -/
def BindArity (m : ModuleInst) (ct ct' : TypeIdx) (n : Nat) : Prop :=
  ∃ ps ps', contParams? m ct = some ps ∧ contParams? m ct' = some ps' ∧
    n + ps'.length = ps.length

variable {H : Type}

/-- **CoreFX with continuation values and a typed `cont.bind`.** `StepFX'` with the
`cont.bind` rules typed (`BindArity`). -/
inductive StepFXT (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX) :
    ConfigFX H → ConfigFX H → Prop where
  /-- A Core step on Core code (FX function codes refused). -/
  | core {s s' : Store H} {K : List (Option ContFX)} {f f' : Frame} {cs cs' : List Admin}
      (h : Step P (blockFX host fx) ⟨s, f, cs⟩ ⟨s', f', cs'⟩) :
      StepFXT P host fx ⟨s, K, f, cs.map .core⟩ ⟨s', K, f', cs'.map .core⟩
  /-- `ctxt-instrs`, skipping FX values. -/
  | seq {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame} {vs : List FVal}
      {es es' rest : List AdminFX} (h : StepFXT P host fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩)
      (hne : vs ≠ [] ∨ rest ≠ []) :
      StepFXT P host fx ⟨s, K, f, fvals vs ++ es ++ rest⟩ ⟨s', K', f', fvals vs ++ es' ++ rest⟩
  | ctxLabel {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame} {n : Nat}
      {k : List InstrFX} {es es' : List AdminFX}
      (h : StepFXT P host fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
      StepFXT P host fx ⟨s, K, f, [.label n k es]⟩ ⟨s', K', f', [.label n k es']⟩
  | ctxFrame {s s' : Store H} {K K' : List (Option ContFX)} {f fi fi' : Frame} {n : Nat}
      {es es' : List AdminFX} (h : StepFXT P host fx ⟨s, K, fi, es⟩ ⟨s', K', fi', es'⟩) :
      StepFXT P host fx ⟨s, K, f, [.frame n fi es]⟩ ⟨s', K', f, [.frame n fi' es']⟩
  | ctxHandler {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
      {hs : List HClause} {es es' : List AdminFX}
      (h : StepFXT P host fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
      StepFXT P host fx ⟨s, K, f, [.handler hs es]⟩ ⟨s', K', f', [.handler hs es']⟩
  -- Structured control on FX code
  | block {s : Store H} {K : List (Option ContFX)} {f : Frame} {bt : BlockType}
      {body : List InstrFX} {vs : List FVal} {t₁ t₂ : List CValType}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
      StepFXT P host fx ⟨s, K, f, fvals vs ++ [.block bt body]⟩
        ⟨s, K, f, [.label t₂.length [] (fvals vs ++ body.map InstrFX.toAdmin)]⟩
  | loop {s : Store H} {K : List (Option ContFX)} {f : Frame} {bt : BlockType}
      {body : List InstrFX} {vs : List FVal} {t₁ t₂ : List CValType}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
      StepFXT P host fx ⟨s, K, f, fvals vs ++ [.loop bt body]⟩
        ⟨s, K, f, [.label t₁.length [.loop bt body] (fvals vs ++ body.map InstrFX.toAdmin)]⟩
  | ifTrue {s : Store H} {K : List (Option ContFX)} {f : Frame} {c : BitVec 32}
      {bt : BlockType} {b₁ b₂ : List InstrFX} (hc : c ≠ 0) :
      StepFXT P host fx ⟨s, K, f, [.core (constI32 c), .if_ bt b₁ b₂]⟩ ⟨s, K, f, [.block bt b₁]⟩
  | ifFalse {s : Store H} {K : List (Option ContFX)} {f : Frame} {bt : BlockType}
      {b₁ b₂ : List InstrFX} :
      StepFXT P host fx ⟨s, K, f, [.core (constI32 0), .if_ bt b₁ b₂]⟩ ⟨s, K, f, [.block bt b₂]⟩
  | labelVals {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs : List FVal} :
      StepFXT P host fx ⟨s, K, f, [.label n k (fvals vs)]⟩ ⟨s, K, f, fvals vs⟩
  | brLabelZero {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs' vs : List FVal} {l : LabelIdx} {rest : List AdminFX}
      (hl : l.toNat = 0) (hn : vs.length = n) :
      StepFXT P host fx
        ⟨s, K, f, [.label n k (fvals vs' ++ fvals vs ++ [.core (.plain (.br l))] ++ rest)]⟩
        ⟨s, K, f, fvals vs ++ k.map InstrFX.toAdmin⟩
  | brLabelSucc {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs : List FVal} {l : LabelIdx} {rest : List AdminFX}
      (hl : 0 < l.toNat) :
      StepFXT P host fx ⟨s, K, f, [.label n k (fvals vs ++ [.core (.plain (.br l))] ++ rest)]⟩
        ⟨s, K, f, fvals vs ++ [.core (.plain (.br (labelPred l)))]⟩
  | brHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {vs : List FVal} {l : LabelIdx} {rest : List AdminFX} :
      StepFXT P host fx ⟨s, K, f, [.handler hs (fvals vs ++ [.core (.plain (.br l))] ++ rest)]⟩
        ⟨s, K, f, fvals vs ++ [.core (.plain (.br l))]⟩
  | returnLabel {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs : List FVal} {rest : List AdminFX} :
      StepFXT P host fx ⟨s, K, f, [.label n k (fvals vs ++ [.core (.plain .return_)] ++ rest)]⟩
        ⟨s, K, f, fvals vs ++ [.core (.plain .return_)]⟩
  | returnHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {vs : List FVal} {rest : List AdminFX} :
      StepFXT P host fx ⟨s, K, f, [.handler hs (fvals vs ++ [.core (.plain .return_)] ++ rest)]⟩
        ⟨s, K, f, fvals vs ++ [.core (.plain .return_)]⟩
  | frameVals {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat}
      {vs : List FVal} (hn : vs.length = n) :
      StepFXT P host fx ⟨s, K, f, [.frame n fi (fvals vs)]⟩ ⟨s, K, f, fvals vs⟩
  | returnFrame {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat}
      {vs' vs : List FVal} {rest : List AdminFX} (hn : vs.length = n) :
      StepFXT P host fx
        ⟨s, K, f, [.frame n fi (fvals vs' ++ fvals vs ++ [.core (.plain .return_)] ++ rest)]⟩
        ⟨s, K, f, fvals vs⟩
  | handlerVals {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {vs : List FVal} :
      StepFXT P host fx ⟨s, K, f, [.handler hs (fvals vs)]⟩ ⟨s, K, f, fvals vs⟩
  /-- Core's `drop` on a continuation reference (new). -/
  | dropCont {s : Store H} {K : List (Option ContFX)} {f : Frame} {k : Nat} :
      StepFXT P host fx ⟨s, K, f, [.contRef k, .core (.plain .drop)]⟩ ⟨s, K, f, []⟩
  -- Traps and exceptions through FX code
  | trapSeq {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal}
      {rest : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ []) :
      StepFXT P host fx ⟨s, K, f, fvals vs ++ [.core .trap] ++ rest⟩ ⟨s, K, f, [.core .trap]⟩
  | trapLabel {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} :
      StepFXT P host fx ⟨s, K, f, [.label n k [.core .trap]]⟩ ⟨s, K, f, [.core .trap]⟩
  | trapFrame {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat} :
      StepFXT P host fx ⟨s, K, f, [.frame n fi [.core .trap]]⟩ ⟨s, K, f, [.core .trap]⟩
  | trapHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause} :
      StepFXT P host fx ⟨s, K, f, [.handler hs [.core .trap]]⟩ ⟨s, K, f, [.core .trap]⟩
  | throwSeq {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {a : Nat}
      {rest : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ []) :
      StepFXT P host fx ⟨s, K, f, fvals vs ++ cthrowing a ++ rest⟩ ⟨s, K, f, cthrowing a⟩
  | throwLabel {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {a : Nat} :
      StepFXT P host fx ⟨s, K, f, [.label n k (cthrowing a)]⟩ ⟨s, K, f, cthrowing a⟩
  | throwFrame {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat} {a : Nat} :
      StepFXT P host fx ⟨s, K, f, [.frame n fi (cthrowing a)]⟩ ⟨s, K, f, cthrowing a⟩
  | throwHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {a : Nat} :
      StepFXT P host fx ⟨s, K, f, [.handler hs (cthrowing a)]⟩ ⟨s, K, f, cthrowing a⟩
  -- FX functions (arguments become locals, so they are Core values)
  | invoke {s : Store H} {K : List (Option ContFX)} {f : Frame} {c : Admin} {vs : List Val}
      {a : Nat} {fi : FuncInst H} {h : H} {F : FuncFX} (hc : c.IsCallRef)
      (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host h) (hfx : fx h = some F)
      (hn : vs.length = F.nparams) :
      StepFXT P host fx ⟨s, K, f, cvals vs ++ [.core (.ref (.func a)), .core c]⟩
        ⟨s, K, f, [.frame F.nresults (Frame.forCall F.module vs F.locals)
          [.label F.nresults [] (F.body.map InstrFX.toAdmin)]]⟩
  -- Continuations
  | contNew {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat} {fi : FuncInst H}
      {ct : TypeIdx} (hf : s.funcs[a]? = some fi) :
      StepFXT P host fx ⟨s, K, f, [.core (.ref (.func a)), .fx (.contNew ct)]⟩
        ⟨s, K ++ [some ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType fi.type)]⟩], f,
          [.contRef K.length]⟩
  | contNewNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {ct : TypeIdx} :
      StepFXT P host fx ⟨s, K, f, [.core (.ref .null), .fx (.contNew ct)]⟩
        ⟨s, K, f, [.core .trap]⟩
  | contBind {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {k : Nat}
      {C : ContFX} {ct ct' : TypeIdx} (hk : K[k]? = some (some C))
      (ha : BindArity f.module ct ct' vs.length) :
      StepFXT P host fx ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.contBind ct ct')]⟩
        ⟨s, K.set k none ++ [some ⟨fun c => C.plug (fvals vs ++ c)⟩], f, [.contRef K.length]⟩
  | contBindNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal}
      {ct ct' : TypeIdx} (ha : BindArity f.module ct ct' vs.length) :
      StepFXT P host fx ⟨s, K, f, fvals vs ++ [.core (.ref .null), .fx (.contBind ct ct')]⟩
        ⟨s, K, f, [.core .trap]⟩
  | contBindUsed {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {k : Nat}
      {ct ct' : TypeIdx} (hk : K[k]? = some none) (ha : BindArity f.module ct ct' vs.length) :
      StepFXT P host fx ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.contBind ct ct')]⟩
        ⟨s, K, f, [.core .trap]⟩
  | resume {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {k : Nat}
      {C : ContFX} {ct : TypeIdx} {hs : List OnClause} {hs' : List HClause}
      (hk : K[k]? = some (some C)) (hr : hs.mapM (resolve s f) = some hs') :
      StepFXT P host fx ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.resume ct hs)]⟩
        ⟨s, K.set k none, f, [.handler hs' (C.plug (fvals vs))]⟩
  | resumeNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal}
      {ct : TypeIdx} {hs : List OnClause} :
      StepFXT P host fx ⟨s, K, f, fvals vs ++ [.core (.ref .null), .fx (.resume ct hs)]⟩
        ⟨s, K, f, [.core .trap]⟩
  | resumeUsed {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {k : Nat}
      {ct : TypeIdx} {hs : List OnClause} (hk : K[k]? = some none) :
      StepFXT P host fx ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.resume ct hs)]⟩
        ⟨s, K, f, [.core .trap]⟩
  /-- `resume_throw`: the payload is the exception's fields, so Core values. -/
  | resumeThrow {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val} {k : Nat}
      {C : ContFX} {ct : TypeIdx} {x : TagIdx} {hs : List OnClause} {hs' : List HClause}
      {ta : Nat} {ti : TagInst} (hk : K[k]? = some (some C)) (ht : s.tag? f x = some (ta, ti))
      (hr : hs.mapM (resolve s f) = some hs') :
      StepFXT P host fx ⟨s, K, f, cvals vs ++ [.contRef k, .fx (.resumeThrow ct x hs)]⟩
        ⟨s.addExn ⟨ta, vs⟩, K.set k none, f, [.handler hs' (C.plug (cthrowing s.exns.length))]⟩
  | resumeThrowNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val}
      {ct : TypeIdx} {x : TagIdx} {hs : List OnClause} :
      StepFXT P host fx ⟨s, K, f, cvals vs ++ [.core (.ref .null), .fx (.resumeThrow ct x hs)]⟩
        ⟨s, K, f, [.core .trap]⟩
  /-- `suspend x` under a handler with clause `(on x l)` and no inner handler for `x`. -/
  | suspend {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {E : CtxV} {vs : List FVal} {x : TagIdx} {ta : Nat} {ti : TagInst} {l : LabelIdx}
      (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
      (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
      StepFXT P host fx ⟨s, K, f, [.handler hs (E.plug (fvals vs ++ [.fx (.suspend x)]))]⟩
        ⟨s, K ++ [some ⟨E.plug⟩], f, fvals vs ++ [.contRef K.length, .core (.plain (.br l))]⟩
  /-- `switch ct x` under a handler with clause `(on x switch)`. -/
  | switch {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {E : CtxV} {vs : List FVal} {k : Nat} {C : ContFX} {ct : TypeIdx} {x : TagIdx} {ta : Nat}
      {ti : TagInst} (hk : K[k]? = some (some C))
      (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
      (hc : hs.find? (fun c => c.tag == ta) = some (.onSwitch ta)) :
      StepFXT P host fx
        ⟨s, K, f, [.handler hs (E.plug (fvals vs ++ [.contRef k, .fx (.switch ct x)]))]⟩
        ⟨s, K.set k none ++ [some ⟨E.plug⟩], f,
          [.handler hs (C.plug (fvals vs ++ [.contRef K.length]))]⟩


/-- Runs of `StepFXT`. -/
abbrev StepsFXT (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX) :=
  Relation.ReflTransGen (StepFXT P host fx)

/-- The observable behaviours under `StepFXT`: results of finite runs, and divergence. -/
def behavioursFXT (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX)
    (c : ConfigFX H) : Set (Behaviour Val) :=
  {b | ∃ (d : ConfigFX H) (r : Result), StepsFXT P host fx c d ∧
      d.code = r.toAdmin.map .core ∧ b = r.toBehaviour} ∪
  {b | b = .diverges ∧ Silmaril.InfiniteTrace (StepFXT P host fx) c}

end Silmaril.Wasm.Models.FXBindT
