module

public import Silmaril.Wasm.Models.FXResume.Defs

/-!
# CoreFX with a typed `resume`, and an FX typing judgement

`StepFXT` (`Silmaril.Wasm.Models.FXBindT`) types `cont.bind` but leaves `resume` untyped:
`resume $ct` resumes with **any** suffix of the operand stack (`FXResume.resume_untyped`). In
the typed proposal it takes exactly as many values as `$ct` has parameters. This module adds a
fourth reduction relation **next to** `StepFX`, `StepFX'` and `StepFXT`, without changing them,
and a typing judgement for a straight-line fragment of FX code:

* **`StepFXR P host fx`**: `StepFXT` with the three `resume` rules (`resume`, `resumeNull`,
  `resumeUsed`) restricted to operand lists of length `n` with
  `ResumeArity (frame's module) ct n` (`Silmaril.Wasm.Models.FXResume`). Every other rule is
  `StepFXT`'s, unchanged. `resume_throw` and `switch` stay untyped (their operand counts are
  given by tag types, which `StepFXT` does not read either);
* `StepsFXR`, `behavioursFXR`: runs and behaviours, as for `StepFXT`;
* `FTy`: FX operand types, a Core value type or a continuation type `(ref null $ct)`;
  `contType? m ct`: the function type that `$ct` stands for (as in `contParams?`);
* **`TypedFX core m is t₁ t₂`**: the FX typing judgement for straight-line FX code. Core
  instructions are typed by a parameter `core` (for instance Silmaril's instruction typing),
  and `cont.new`, `cont.bind` and `resume` by the typed proposal's rules; sequencing and
  stack weakening (`frame`) are the usual structural rules. `cont.new`'s function-reference
  operand is not checked against `$ct`, and `resume`'s handler clauses are not checked against
  tag types. Blocks, `suspend`, `switch` and `resume_throw` are outside the fragment;
* `FValTy VT KT`: runtime FX values at FX types, with Core values typed by `VT` and the
  continuation in slot `k` at type `$ct` when `KT k ct`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXResumeT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXResume
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **CoreFX with typed `cont.bind` and typed `resume`.** `StepFXT` with the `resume` rules
typed (`ResumeArity`). -/
inductive StepFXR (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX) :
    ConfigFX H → ConfigFX H → Prop where
  /-- A Core step on Core code (FX function codes refused). -/
  | core {s s' : Store H} {K : List (Option ContFX)} {f f' : Frame} {cs cs' : List Admin}
      (h : Step P (blockFX host fx) ⟨s, f, cs⟩ ⟨s', f', cs'⟩) :
      StepFXR P host fx ⟨s, K, f, cs.map .core⟩ ⟨s', K, f', cs'.map .core⟩
  /-- `ctxt-instrs`, skipping FX values. -/
  | seq {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame} {vs : List FVal}
      {es es' rest : List AdminFX} (h : StepFXR P host fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩)
      (hne : vs ≠ [] ∨ rest ≠ []) :
      StepFXR P host fx ⟨s, K, f, fvals vs ++ es ++ rest⟩ ⟨s', K', f', fvals vs ++ es' ++ rest⟩
  | ctxLabel {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame} {n : Nat}
      {k : List InstrFX} {es es' : List AdminFX}
      (h : StepFXR P host fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
      StepFXR P host fx ⟨s, K, f, [.label n k es]⟩ ⟨s', K', f', [.label n k es']⟩
  | ctxFrame {s s' : Store H} {K K' : List (Option ContFX)} {f fi fi' : Frame} {n : Nat}
      {es es' : List AdminFX} (h : StepFXR P host fx ⟨s, K, fi, es⟩ ⟨s', K', fi', es'⟩) :
      StepFXR P host fx ⟨s, K, f, [.frame n fi es]⟩ ⟨s', K', f, [.frame n fi' es']⟩
  | ctxHandler {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
      {hs : List HClause} {es es' : List AdminFX}
      (h : StepFXR P host fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
      StepFXR P host fx ⟨s, K, f, [.handler hs es]⟩ ⟨s', K', f', [.handler hs es']⟩
  -- Structured control on FX code
  | block {s : Store H} {K : List (Option ContFX)} {f : Frame} {bt : BlockType}
      {body : List InstrFX} {vs : List FVal} {t₁ t₂ : List CValType}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
      StepFXR P host fx ⟨s, K, f, fvals vs ++ [.block bt body]⟩
        ⟨s, K, f, [.label t₂.length [] (fvals vs ++ body.map InstrFX.toAdmin)]⟩
  | loop {s : Store H} {K : List (Option ContFX)} {f : Frame} {bt : BlockType}
      {body : List InstrFX} {vs : List FVal} {t₁ t₂ : List CValType}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
      StepFXR P host fx ⟨s, K, f, fvals vs ++ [.loop bt body]⟩
        ⟨s, K, f, [.label t₁.length [.loop bt body] (fvals vs ++ body.map InstrFX.toAdmin)]⟩
  | ifTrue {s : Store H} {K : List (Option ContFX)} {f : Frame} {c : BitVec 32}
      {bt : BlockType} {b₁ b₂ : List InstrFX} (hc : c ≠ 0) :
      StepFXR P host fx ⟨s, K, f, [.core (constI32 c), .if_ bt b₁ b₂]⟩ ⟨s, K, f, [.block bt b₁]⟩
  | ifFalse {s : Store H} {K : List (Option ContFX)} {f : Frame} {bt : BlockType}
      {b₁ b₂ : List InstrFX} :
      StepFXR P host fx ⟨s, K, f, [.core (constI32 0), .if_ bt b₁ b₂]⟩ ⟨s, K, f, [.block bt b₂]⟩
  | labelVals {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs : List FVal} :
      StepFXR P host fx ⟨s, K, f, [.label n k (fvals vs)]⟩ ⟨s, K, f, fvals vs⟩
  | brLabelZero {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs' vs : List FVal} {l : LabelIdx} {rest : List AdminFX}
      (hl : l.toNat = 0) (hn : vs.length = n) :
      StepFXR P host fx
        ⟨s, K, f, [.label n k (fvals vs' ++ fvals vs ++ [.core (.plain (.br l))] ++ rest)]⟩
        ⟨s, K, f, fvals vs ++ k.map InstrFX.toAdmin⟩
  | brLabelSucc {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs : List FVal} {l : LabelIdx} {rest : List AdminFX}
      (hl : 0 < l.toNat) :
      StepFXR P host fx ⟨s, K, f, [.label n k (fvals vs ++ [.core (.plain (.br l))] ++ rest)]⟩
        ⟨s, K, f, fvals vs ++ [.core (.plain (.br (labelPred l)))]⟩
  | brHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {vs : List FVal} {l : LabelIdx} {rest : List AdminFX} :
      StepFXR P host fx ⟨s, K, f, [.handler hs (fvals vs ++ [.core (.plain (.br l))] ++ rest)]⟩
        ⟨s, K, f, fvals vs ++ [.core (.plain (.br l))]⟩
  | returnLabel {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs : List FVal} {rest : List AdminFX} :
      StepFXR P host fx ⟨s, K, f, [.label n k (fvals vs ++ [.core (.plain .return_)] ++ rest)]⟩
        ⟨s, K, f, fvals vs ++ [.core (.plain .return_)]⟩
  | returnHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {vs : List FVal} {rest : List AdminFX} :
      StepFXR P host fx ⟨s, K, f, [.handler hs (fvals vs ++ [.core (.plain .return_)] ++ rest)]⟩
        ⟨s, K, f, fvals vs ++ [.core (.plain .return_)]⟩
  | frameVals {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat}
      {vs : List FVal} (hn : vs.length = n) :
      StepFXR P host fx ⟨s, K, f, [.frame n fi (fvals vs)]⟩ ⟨s, K, f, fvals vs⟩
  | returnFrame {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat}
      {vs' vs : List FVal} {rest : List AdminFX} (hn : vs.length = n) :
      StepFXR P host fx
        ⟨s, K, f, [.frame n fi (fvals vs' ++ fvals vs ++ [.core (.plain .return_)] ++ rest)]⟩
        ⟨s, K, f, fvals vs⟩
  | handlerVals {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {vs : List FVal} :
      StepFXR P host fx ⟨s, K, f, [.handler hs (fvals vs)]⟩ ⟨s, K, f, fvals vs⟩
  /-- Core's `drop` on a continuation reference (new). -/
  | dropCont {s : Store H} {K : List (Option ContFX)} {f : Frame} {k : Nat} :
      StepFXR P host fx ⟨s, K, f, [.contRef k, .core (.plain .drop)]⟩ ⟨s, K, f, []⟩
  -- Traps and exceptions through FX code
  | trapSeq {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal}
      {rest : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ []) :
      StepFXR P host fx ⟨s, K, f, fvals vs ++ [.core .trap] ++ rest⟩ ⟨s, K, f, [.core .trap]⟩
  | trapLabel {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} :
      StepFXR P host fx ⟨s, K, f, [.label n k [.core .trap]]⟩ ⟨s, K, f, [.core .trap]⟩
  | trapFrame {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat} :
      StepFXR P host fx ⟨s, K, f, [.frame n fi [.core .trap]]⟩ ⟨s, K, f, [.core .trap]⟩
  | trapHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause} :
      StepFXR P host fx ⟨s, K, f, [.handler hs [.core .trap]]⟩ ⟨s, K, f, [.core .trap]⟩
  | throwSeq {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {a : Nat}
      {rest : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ []) :
      StepFXR P host fx ⟨s, K, f, fvals vs ++ cthrowing a ++ rest⟩ ⟨s, K, f, cthrowing a⟩
  | throwLabel {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {a : Nat} :
      StepFXR P host fx ⟨s, K, f, [.label n k (cthrowing a)]⟩ ⟨s, K, f, cthrowing a⟩
  | throwFrame {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat} {a : Nat} :
      StepFXR P host fx ⟨s, K, f, [.frame n fi (cthrowing a)]⟩ ⟨s, K, f, cthrowing a⟩
  | throwHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {a : Nat} :
      StepFXR P host fx ⟨s, K, f, [.handler hs (cthrowing a)]⟩ ⟨s, K, f, cthrowing a⟩
  -- FX functions (arguments become locals, so they are Core values)
  | invoke {s : Store H} {K : List (Option ContFX)} {f : Frame} {c : Admin} {vs : List Val}
      {a : Nat} {fi : FuncInst H} {h : H} {F : FuncFX} (hc : c.IsCallRef)
      (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host h) (hfx : fx h = some F)
      (hn : vs.length = F.nparams) :
      StepFXR P host fx ⟨s, K, f, cvals vs ++ [.core (.ref (.func a)), .core c]⟩
        ⟨s, K, f, [.frame F.nresults (Frame.forCall F.module vs F.locals)
          [.label F.nresults [] (F.body.map InstrFX.toAdmin)]]⟩
  -- Continuations
  | contNew {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat} {fi : FuncInst H}
      {ct : TypeIdx} (hf : s.funcs[a]? = some fi) :
      StepFXR P host fx ⟨s, K, f, [.core (.ref (.func a)), .fx (.contNew ct)]⟩
        ⟨s, K ++ [some ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType fi.type)]⟩], f,
          [.contRef K.length]⟩
  | contNewNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {ct : TypeIdx} :
      StepFXR P host fx ⟨s, K, f, [.core (.ref .null), .fx (.contNew ct)]⟩
        ⟨s, K, f, [.core .trap]⟩
  | contBind {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {k : Nat}
      {C : ContFX} {ct ct' : TypeIdx} (hk : K[k]? = some (some C))
      (ha : BindArity f.module ct ct' vs.length) :
      StepFXR P host fx ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.contBind ct ct')]⟩
        ⟨s, K.set k none ++ [some ⟨fun c => C.plug (fvals vs ++ c)⟩], f, [.contRef K.length]⟩
  | contBindNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal}
      {ct ct' : TypeIdx} (ha : BindArity f.module ct ct' vs.length) :
      StepFXR P host fx ⟨s, K, f, fvals vs ++ [.core (.ref .null), .fx (.contBind ct ct')]⟩
        ⟨s, K, f, [.core .trap]⟩
  | contBindUsed {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {k : Nat}
      {ct ct' : TypeIdx} (hk : K[k]? = some none) (ha : BindArity f.module ct ct' vs.length) :
      StepFXR P host fx ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.contBind ct ct')]⟩
        ⟨s, K, f, [.core .trap]⟩
  | resume {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {k : Nat}
      {C : ContFX} {ct : TypeIdx} {hs : List OnClause} {hs' : List HClause}
      (hk : K[k]? = some (some C)) (hr : hs.mapM (resolve s f) = some hs')
      (ha : ResumeArity f.module ct vs.length) :
      StepFXR P host fx ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.resume ct hs)]⟩
        ⟨s, K.set k none, f, [.handler hs' (C.plug (fvals vs))]⟩
  | resumeNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal}
      {ct : TypeIdx} {hs : List OnClause} (ha : ResumeArity f.module ct vs.length) :
      StepFXR P host fx ⟨s, K, f, fvals vs ++ [.core (.ref .null), .fx (.resume ct hs)]⟩
        ⟨s, K, f, [.core .trap]⟩
  | resumeUsed {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {k : Nat}
      {ct : TypeIdx} {hs : List OnClause} (hk : K[k]? = some none)
      (ha : ResumeArity f.module ct vs.length) :
      StepFXR P host fx ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.resume ct hs)]⟩
        ⟨s, K, f, [.core .trap]⟩
  /-- `resume_throw`: the payload is the exception's fields, so Core values. -/
  | resumeThrow {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val} {k : Nat}
      {C : ContFX} {ct : TypeIdx} {x : TagIdx} {hs : List OnClause} {hs' : List HClause}
      {ta : Nat} {ti : TagInst} (hk : K[k]? = some (some C)) (ht : s.tag? f x = some (ta, ti))
      (hr : hs.mapM (resolve s f) = some hs') :
      StepFXR P host fx ⟨s, K, f, cvals vs ++ [.contRef k, .fx (.resumeThrow ct x hs)]⟩
        ⟨s.addExn ⟨ta, vs⟩, K.set k none, f, [.handler hs' (C.plug (cthrowing s.exns.length))]⟩
  | resumeThrowNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val}
      {ct : TypeIdx} {x : TagIdx} {hs : List OnClause} :
      StepFXR P host fx ⟨s, K, f, cvals vs ++ [.core (.ref .null), .fx (.resumeThrow ct x hs)]⟩
        ⟨s, K, f, [.core .trap]⟩
  /-- `suspend x` under a handler with clause `(on x l)` and no inner handler for `x`. -/
  | suspend {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {E : CtxV} {vs : List FVal} {x : TagIdx} {ta : Nat} {ti : TagInst} {l : LabelIdx}
      (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
      (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
      StepFXR P host fx ⟨s, K, f, [.handler hs (E.plug (fvals vs ++ [.fx (.suspend x)]))]⟩
        ⟨s, K ++ [some ⟨E.plug⟩], f, fvals vs ++ [.contRef K.length, .core (.plain (.br l))]⟩
  /-- `switch ct x` under a handler with clause `(on x switch)`. -/
  | switch {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {E : CtxV} {vs : List FVal} {k : Nat} {C : ContFX} {ct : TypeIdx} {x : TagIdx} {ta : Nat}
      {ti : TagInst} (hk : K[k]? = some (some C))
      (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
      (hc : hs.find? (fun c => c.tag == ta) = some (.onSwitch ta)) :
      StepFXR P host fx
        ⟨s, K, f, [.handler hs (E.plug (fvals vs ++ [.contRef k, .fx (.switch ct x)]))]⟩
        ⟨s, K.set k none ++ [some ⟨E.plug⟩], f,
          [.handler hs (C.plug (fvals vs ++ [.contRef K.length]))]⟩


/-- Runs of `StepFXR`. -/
abbrev StepsFXR (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX) :=
  Relation.ReflTransGen (StepFXR P host fx)

/-- The observable behaviours under `StepFXR`: results of finite runs, and divergence. -/
def behavioursFXR (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX)
    (c : ConfigFX H) : Set (Behaviour Val) :=
  {b | ∃ (d : ConfigFX H) (r : Result), StepsFXR P host fx c d ∧
      d.code = r.toAdmin.map .core ∧ b = r.toBehaviour} ∪
  {b | b = .diverges ∧ Silmaril.InfiniteTrace (StepFXR P host fx) c}

/-! ## An FX typing judgement for straight-line code -/

/-- FX operand types: a Core value type, or a continuation type `(ref null $ct)`. -/
inductive FTy where
  | val (t : CValType)
  | cont (ct : TypeIdx)

/-- Core value types as FX operand types. -/
def vtys (ts : List CValType) : List FTy := ts.map .val

/-- The function type that the continuation type `ct` stands for in module instance `m`. -/
def contType? (m : ModuleInst) (ct : TypeIdx) : Option (List CValType × List CValType) :=
  m.types[ct.toNat]? >>= DefType.funcType?

/-- **The FX typing judgement** for straight-line FX code, with Core instructions typed by
`core`. -/
inductive TypedFX (core : Instr → List CValType → List CValType → Prop) (m : ModuleInst) :
    List InstrFX → List FTy → List FTy → Prop where
  | nil {ts : List FTy} : TypedFX core m [] ts ts
  | core {i : Instr} {t₁ t₂ : List CValType} (h : core i t₁ t₂) :
      TypedFX core m [.core i] (vtys t₁) (vtys t₂)
  /-- `cont.new $ct : [t] → [(ref $ct)]` (the operand's type is not checked). -/
  | contNew {ct : TypeIdx} {t : CValType} {ty : List CValType × List CValType}
      (h : contType? m ct = some ty) : TypedFX core m [.fx (.contNew ct)] [.val t] [.cont ct]
  /-- `cont.bind $ct $ct' : [t₁* (ref null $ct)] → [(ref $ct')]` with
  `$ct = [t₁* t₂*] → rs` and `$ct' = [t₂*] → rs`. -/
  | contBind {ct ct' : TypeIdx} {ps₁ ps₂ rs : List CValType}
      (h : contType? m ct = some (ps₁ ++ ps₂, rs)) (h' : contType? m ct' = some (ps₂, rs)) :
      TypedFX core m [.fx (.contBind ct ct')] (vtys ps₁ ++ [.cont ct]) [.cont ct']
  /-- `resume $ct hs : [ps* (ref null $ct)] → [rs*]` with `$ct = [ps*] → rs`. -/
  | resume {ct : TypeIdx} {hs : List OnClause} {ps rs : List CValType}
      (h : contType? m ct = some (ps, rs)) :
      TypedFX core m [.fx (.resume ct hs)] (vtys ps ++ [.cont ct]) (vtys rs)
  | append {is js : List InstrFX} {t₁ t₂ t₃ : List FTy} (h₁ : TypedFX core m is t₁ t₂)
      (h₂ : TypedFX core m js t₂ t₃) : TypedFX core m (is ++ js) t₁ t₃
  /-- Stack weakening. -/
  | frame {is : List InstrFX} {t₁ t₂ : List FTy} (ts : List FTy) (h : TypedFX core m is t₁ t₂) :
      TypedFX core m is (ts ++ t₁) (ts ++ t₂)

/-- Runtime FX values at FX types: Core values by `VT`, continuation slots by `KT`. -/
inductive FValTy (VT : Val → CValType → Prop) (KT : Nat → TypeIdx → Prop) :
    FVal → FTy → Prop where
  | val {v : Val} {t : CValType} (h : VT v t) : FValTy VT KT (.val v) (.val t)
  | cont {k : Nat} {ct : TypeIdx} (h : KT k ct) : FValTy VT KT (.cont k) (.cont ct)

end Silmaril.Wasm.Models.FXResumeT
