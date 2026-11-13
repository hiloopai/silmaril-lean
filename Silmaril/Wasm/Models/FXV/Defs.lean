module

public import Silmaril.Wasm.Models.FX.Defs

/-!
# CoreFX with continuation values: `StepFX'`

Track H's `StepFX` moves Core values `cvals vs` only, so a continuation reference `contRef k`
can never cross a label, a handler or a frame (`suspend_to_label_stuck` in
`Silmaril.Proofs.Wasm.Models.FXLower.ContStuck`). This module adds a second reduction relation
**next to** `StepFX`, without changing it:

* `FVal`: an **FX value**, a Core value or a continuation reference; `FVal.toAdmin`, `fvals`;
  `liftV vs` sees Core values as FX values, and `fvals (liftV vs) = cvals vs`.
* `CtxV`: contexts of suspension whose value prefixes are FX values (`Ctx` with `FVal`s).
* **`StepFX' P host fx`**: `StepFX` with `fvals` instead of `cvals` in every rule that moves,
  skips or passes values: `seq`, `block`, `loop`, `labelVals`, `brLabelZero`, `brLabelSucc`,
  `brHandler`, `returnLabel`, `returnHandler`, `frameVals`, `returnFrame`, `handlerVals`,
  `trapSeq`, `throwSeq`, and the operands of `contBind`, `resume`, `suspend` and `switch` (an
  argument of a continuation may itself be a continuation). One rule is new: `dropCont`, Core's
  `drop` on a continuation reference.

Values stay Core values where the store or a frame holds them: the arguments of an FX function
(`invoke`; locals are Core values), the payload of `resume_throw` (exception fields), and every
Core step (`core`). `select` and `local.set`/`global.set` of a continuation are not modelled.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXV

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Numerics (Profile)

/-- An FX value: a Core value or a continuation reference. -/
inductive FVal where
  | val (v : Val)
  | cont (k : Nat)

/-- An FX value as FX code. -/
def FVal.toAdmin : FVal → AdminFX
  | .val v => .core v.toAdmin
  | .cont k => .contRef k

/-- FX values as FX code. -/
def fvals (vs : List FVal) : List AdminFX := vs.map FVal.toAdmin

/-- Core values as FX values. -/
def liftV (vs : List Val) : List FVal := vs.map .val

/-! ## Contexts of suspension with FX values -/

/-- Evaluation contexts between a handler frame and a `suspend`/`switch`, with FX values. -/
inductive CtxV where
  | hole
  | seq (vs : List FVal) (E : CtxV) (rest : List AdminFX)
  | label (n : Nat) (cont : List InstrFX) (E : CtxV)
  | frame (n : Nat) (f : Frame) (E : CtxV)
  | handler (hs : List HClause) (E : CtxV)

/-- Fill the hole of a context. -/
def CtxV.plug : CtxV → List AdminFX → List AdminFX
  | .hole, c => c
  | .seq vs E rest, c => fvals vs ++ E.plug c ++ rest
  | .label n k E, c => [.label n k (E.plug c)]
  | .frame n f E, c => [.frame n f (E.plug c)]
  | .handler hs E, c => [.handler hs (E.plug c)]

/-- The frame in effect at the hole, starting from frame `f`. -/
def CtxV.frameAt (f : Frame) : CtxV → Frame
  | .hole => f
  | .seq _ E _ => E.frameAt f
  | .label _ _ E => E.frameAt f
  | .frame _ fi E => E.frameAt fi
  | .handler _ E => E.frameAt f

/-- A handler frame of the context has a clause for tag address `ta`. -/
def CtxV.Handles (ta : Nat) : CtxV → Prop
  | .hole => False
  | .seq _ E _ => E.Handles ta
  | .label _ _ E => E.Handles ta
  | .frame _ _ E => E.Handles ta
  | .handler hs E => (∃ c ∈ hs, c.tag = ta) ∨ E.Handles ta

/-- A context of `StepFX` as a context with FX values. -/
def _root_.Silmaril.Wasm.Models.FX.Ctx.toV : Ctx → CtxV
  | .hole => .hole
  | .seq vs E rest => .seq (liftV vs) E.toV rest
  | .label n k E => .label n k E.toV
  | .frame n f E => .frame n f E.toV
  | .handler hs E => .handler hs E.toV

/-! ## Reduction -/

variable {H : Type}

/-- **CoreFX with continuation values.** `StepFX` with FX values in the value-moving rules. -/
inductive StepFX' (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX) :
    ConfigFX H → ConfigFX H → Prop where
  /-- A Core step on Core code (FX function codes refused). -/
  | core {s s' : Store H} {K : List (Option ContFX)} {f f' : Frame} {cs cs' : List Admin}
      (h : Step P (blockFX host fx) ⟨s, f, cs⟩ ⟨s', f', cs'⟩) :
      StepFX' P host fx ⟨s, K, f, cs.map .core⟩ ⟨s', K, f', cs'.map .core⟩
  /-- `ctxt-instrs`, skipping FX values. -/
  | seq {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame} {vs : List FVal}
      {es es' rest : List AdminFX} (h : StepFX' P host fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩)
      (hne : vs ≠ [] ∨ rest ≠ []) :
      StepFX' P host fx ⟨s, K, f, fvals vs ++ es ++ rest⟩ ⟨s', K', f', fvals vs ++ es' ++ rest⟩
  | ctxLabel {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame} {n : Nat}
      {k : List InstrFX} {es es' : List AdminFX}
      (h : StepFX' P host fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
      StepFX' P host fx ⟨s, K, f, [.label n k es]⟩ ⟨s', K', f', [.label n k es']⟩
  | ctxFrame {s s' : Store H} {K K' : List (Option ContFX)} {f fi fi' : Frame} {n : Nat}
      {es es' : List AdminFX} (h : StepFX' P host fx ⟨s, K, fi, es⟩ ⟨s', K', fi', es'⟩) :
      StepFX' P host fx ⟨s, K, f, [.frame n fi es]⟩ ⟨s', K', f, [.frame n fi' es']⟩
  | ctxHandler {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
      {hs : List HClause} {es es' : List AdminFX}
      (h : StepFX' P host fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
      StepFX' P host fx ⟨s, K, f, [.handler hs es]⟩ ⟨s', K', f', [.handler hs es']⟩
  -- Structured control on FX code
  | block {s : Store H} {K : List (Option ContFX)} {f : Frame} {bt : BlockType}
      {body : List InstrFX} {vs : List FVal} {t₁ t₂ : List CValType}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
      StepFX' P host fx ⟨s, K, f, fvals vs ++ [.block bt body]⟩
        ⟨s, K, f, [.label t₂.length [] (fvals vs ++ body.map InstrFX.toAdmin)]⟩
  | loop {s : Store H} {K : List (Option ContFX)} {f : Frame} {bt : BlockType}
      {body : List InstrFX} {vs : List FVal} {t₁ t₂ : List CValType}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
      StepFX' P host fx ⟨s, K, f, fvals vs ++ [.loop bt body]⟩
        ⟨s, K, f, [.label t₁.length [.loop bt body] (fvals vs ++ body.map InstrFX.toAdmin)]⟩
  | ifTrue {s : Store H} {K : List (Option ContFX)} {f : Frame} {c : BitVec 32}
      {bt : BlockType} {b₁ b₂ : List InstrFX} (hc : c ≠ 0) :
      StepFX' P host fx ⟨s, K, f, [.core (constI32 c), .if_ bt b₁ b₂]⟩ ⟨s, K, f, [.block bt b₁]⟩
  | ifFalse {s : Store H} {K : List (Option ContFX)} {f : Frame} {bt : BlockType}
      {b₁ b₂ : List InstrFX} :
      StepFX' P host fx ⟨s, K, f, [.core (constI32 0), .if_ bt b₁ b₂]⟩ ⟨s, K, f, [.block bt b₂]⟩
  | labelVals {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs : List FVal} :
      StepFX' P host fx ⟨s, K, f, [.label n k (fvals vs)]⟩ ⟨s, K, f, fvals vs⟩
  | brLabelZero {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs' vs : List FVal} {l : LabelIdx} {rest : List AdminFX}
      (hl : l.toNat = 0) (hn : vs.length = n) :
      StepFX' P host fx
        ⟨s, K, f, [.label n k (fvals vs' ++ fvals vs ++ [.core (.plain (.br l))] ++ rest)]⟩
        ⟨s, K, f, fvals vs ++ k.map InstrFX.toAdmin⟩
  | brLabelSucc {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs : List FVal} {l : LabelIdx} {rest : List AdminFX}
      (hl : 0 < l.toNat) :
      StepFX' P host fx ⟨s, K, f, [.label n k (fvals vs ++ [.core (.plain (.br l))] ++ rest)]⟩
        ⟨s, K, f, fvals vs ++ [.core (.plain (.br (labelPred l)))]⟩
  | brHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {vs : List FVal} {l : LabelIdx} {rest : List AdminFX} :
      StepFX' P host fx ⟨s, K, f, [.handler hs (fvals vs ++ [.core (.plain (.br l))] ++ rest)]⟩
        ⟨s, K, f, fvals vs ++ [.core (.plain (.br l))]⟩
  | returnLabel {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs : List FVal} {rest : List AdminFX} :
      StepFX' P host fx ⟨s, K, f, [.label n k (fvals vs ++ [.core (.plain .return_)] ++ rest)]⟩
        ⟨s, K, f, fvals vs ++ [.core (.plain .return_)]⟩
  | returnHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {vs : List FVal} {rest : List AdminFX} :
      StepFX' P host fx ⟨s, K, f, [.handler hs (fvals vs ++ [.core (.plain .return_)] ++ rest)]⟩
        ⟨s, K, f, fvals vs ++ [.core (.plain .return_)]⟩
  | frameVals {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat}
      {vs : List FVal} (hn : vs.length = n) :
      StepFX' P host fx ⟨s, K, f, [.frame n fi (fvals vs)]⟩ ⟨s, K, f, fvals vs⟩
  | returnFrame {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat}
      {vs' vs : List FVal} {rest : List AdminFX} (hn : vs.length = n) :
      StepFX' P host fx
        ⟨s, K, f, [.frame n fi (fvals vs' ++ fvals vs ++ [.core (.plain .return_)] ++ rest)]⟩
        ⟨s, K, f, fvals vs⟩
  | handlerVals {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {vs : List FVal} :
      StepFX' P host fx ⟨s, K, f, [.handler hs (fvals vs)]⟩ ⟨s, K, f, fvals vs⟩
  /-- Core's `drop` on a continuation reference (new). -/
  | dropCont {s : Store H} {K : List (Option ContFX)} {f : Frame} {k : Nat} :
      StepFX' P host fx ⟨s, K, f, [.contRef k, .core (.plain .drop)]⟩ ⟨s, K, f, []⟩
  -- Traps and exceptions through FX code
  | trapSeq {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal}
      {rest : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ []) :
      StepFX' P host fx ⟨s, K, f, fvals vs ++ [.core .trap] ++ rest⟩ ⟨s, K, f, [.core .trap]⟩
  | trapLabel {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} :
      StepFX' P host fx ⟨s, K, f, [.label n k [.core .trap]]⟩ ⟨s, K, f, [.core .trap]⟩
  | trapFrame {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat} :
      StepFX' P host fx ⟨s, K, f, [.frame n fi [.core .trap]]⟩ ⟨s, K, f, [.core .trap]⟩
  | trapHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause} :
      StepFX' P host fx ⟨s, K, f, [.handler hs [.core .trap]]⟩ ⟨s, K, f, [.core .trap]⟩
  | throwSeq {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {a : Nat}
      {rest : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ []) :
      StepFX' P host fx ⟨s, K, f, fvals vs ++ cthrowing a ++ rest⟩ ⟨s, K, f, cthrowing a⟩
  | throwLabel {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {a : Nat} :
      StepFX' P host fx ⟨s, K, f, [.label n k (cthrowing a)]⟩ ⟨s, K, f, cthrowing a⟩
  | throwFrame {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat} {a : Nat} :
      StepFX' P host fx ⟨s, K, f, [.frame n fi (cthrowing a)]⟩ ⟨s, K, f, cthrowing a⟩
  | throwHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {a : Nat} :
      StepFX' P host fx ⟨s, K, f, [.handler hs (cthrowing a)]⟩ ⟨s, K, f, cthrowing a⟩
  -- FX functions (arguments become locals, so they are Core values)
  | invoke {s : Store H} {K : List (Option ContFX)} {f : Frame} {c : Admin} {vs : List Val}
      {a : Nat} {fi : FuncInst H} {h : H} {F : FuncFX} (hc : c.IsCallRef)
      (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host h) (hfx : fx h = some F)
      (hn : vs.length = F.nparams) :
      StepFX' P host fx ⟨s, K, f, cvals vs ++ [.core (.ref (.func a)), .core c]⟩
        ⟨s, K, f, [.frame F.nresults (Frame.forCall F.module vs F.locals)
          [.label F.nresults [] (F.body.map InstrFX.toAdmin)]]⟩
  -- Continuations
  | contNew {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat} {fi : FuncInst H}
      {ct : TypeIdx} (hf : s.funcs[a]? = some fi) :
      StepFX' P host fx ⟨s, K, f, [.core (.ref (.func a)), .fx (.contNew ct)]⟩
        ⟨s, K ++ [some ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType fi.type)]⟩], f,
          [.contRef K.length]⟩
  | contNewNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {ct : TypeIdx} :
      StepFX' P host fx ⟨s, K, f, [.core (.ref .null), .fx (.contNew ct)]⟩
        ⟨s, K, f, [.core .trap]⟩
  | contBind {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {k : Nat}
      {C : ContFX} {ct ct' : TypeIdx} (hk : K[k]? = some (some C)) :
      StepFX' P host fx ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.contBind ct ct')]⟩
        ⟨s, K.set k none ++ [some ⟨fun c => C.plug (fvals vs ++ c)⟩], f, [.contRef K.length]⟩
  | contBindNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal}
      {ct ct' : TypeIdx} :
      StepFX' P host fx ⟨s, K, f, fvals vs ++ [.core (.ref .null), .fx (.contBind ct ct')]⟩
        ⟨s, K, f, [.core .trap]⟩
  | contBindUsed {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {k : Nat}
      {ct ct' : TypeIdx} (hk : K[k]? = some none) :
      StepFX' P host fx ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.contBind ct ct')]⟩
        ⟨s, K, f, [.core .trap]⟩
  | resume {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {k : Nat}
      {C : ContFX} {ct : TypeIdx} {hs : List OnClause} {hs' : List HClause}
      (hk : K[k]? = some (some C)) (hr : hs.mapM (resolve s f) = some hs') :
      StepFX' P host fx ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.resume ct hs)]⟩
        ⟨s, K.set k none, f, [.handler hs' (C.plug (fvals vs))]⟩
  | resumeNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal}
      {ct : TypeIdx} {hs : List OnClause} :
      StepFX' P host fx ⟨s, K, f, fvals vs ++ [.core (.ref .null), .fx (.resume ct hs)]⟩
        ⟨s, K, f, [.core .trap]⟩
  | resumeUsed {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {k : Nat}
      {ct : TypeIdx} {hs : List OnClause} (hk : K[k]? = some none) :
      StepFX' P host fx ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.resume ct hs)]⟩
        ⟨s, K, f, [.core .trap]⟩
  /-- `resume_throw`: the payload is the exception's fields, so Core values. -/
  | resumeThrow {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val} {k : Nat}
      {C : ContFX} {ct : TypeIdx} {x : TagIdx} {hs : List OnClause} {hs' : List HClause}
      {ta : Nat} {ti : TagInst} (hk : K[k]? = some (some C)) (ht : s.tag? f x = some (ta, ti))
      (hr : hs.mapM (resolve s f) = some hs') :
      StepFX' P host fx ⟨s, K, f, cvals vs ++ [.contRef k, .fx (.resumeThrow ct x hs)]⟩
        ⟨s.addExn ⟨ta, vs⟩, K.set k none, f, [.handler hs' (C.plug (cthrowing s.exns.length))]⟩
  | resumeThrowNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val}
      {ct : TypeIdx} {x : TagIdx} {hs : List OnClause} :
      StepFX' P host fx ⟨s, K, f, cvals vs ++ [.core (.ref .null), .fx (.resumeThrow ct x hs)]⟩
        ⟨s, K, f, [.core .trap]⟩
  /-- `suspend x` under a handler with clause `(on x l)` and no inner handler for `x`. -/
  | suspend {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {E : CtxV} {vs : List FVal} {x : TagIdx} {ta : Nat} {ti : TagInst} {l : LabelIdx}
      (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
      (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
      StepFX' P host fx ⟨s, K, f, [.handler hs (E.plug (fvals vs ++ [.fx (.suspend x)]))]⟩
        ⟨s, K ++ [some ⟨E.plug⟩], f, fvals vs ++ [.contRef K.length, .core (.plain (.br l))]⟩
  /-- `switch ct x` under a handler with clause `(on x switch)`. -/
  | switch {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {E : CtxV} {vs : List FVal} {k : Nat} {C : ContFX} {ct : TypeIdx} {x : TagIdx} {ta : Nat}
      {ti : TagInst} (hk : K[k]? = some (some C))
      (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
      (hc : hs.find? (fun c => c.tag == ta) = some (.onSwitch ta)) :
      StepFX' P host fx
        ⟨s, K, f, [.handler hs (E.plug (fvals vs ++ [.contRef k, .fx (.switch ct x)]))]⟩
        ⟨s, K.set k none ++ [some ⟨E.plug⟩], f,
          [.handler hs (C.plug (fvals vs ++ [.contRef K.length]))]⟩

/-- Runs of `StepFX'`. -/
abbrev StepsFX' (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX) :=
  Relation.ReflTransGen (StepFX' P host fx)

/-- The observable behaviours under `StepFX'`: results of finite runs, and divergence. -/
def behavioursFX' (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX)
    (c : ConfigFX H) : Set (Behaviour Val) :=
  {b | ∃ (d : ConfigFX H) (r : Result), StepsFX' P host fx c d ∧
      d.code = r.toAdmin.map .core ∧ b = r.toBehaviour} ∪
  {b | b = .diverges ∧ Silmaril.InfiniteTrace (StepFX' P host fx) c}

end Silmaril.Wasm.Models.FXV
