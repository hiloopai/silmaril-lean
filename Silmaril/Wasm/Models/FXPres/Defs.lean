module

public import Silmaril.Wasm.Models.FXResumeT.Defs

/-!
# Preservation for typed WasmFX: a configuration typing beyond straight-line code

`TypedFX` (`Silmaril.Wasm.Models.FXResumeT`) types straight-line FX code and is local to one
instruction. This module adds a typing of whole FX **configurations** (administrative code with
labels, frames, handler frames and continuation references; blocks, `loop`, `if`, `br`,
`return`, `suspend` and `resume_throw` included), and the reduction relation it is preserved
by. Nothing existing is changed.

* **`StepFXS P host fx`**: `StepFXR` with two more rules typed. `suspend` takes exactly as many
  operands as its tag has parameters, and so does `resume_throw` (`TagArity`). Under `StepFXR`
  (and `StepFXT`, `StepFX'`) both take **any** split of the operand stack, so a typed
  configuration can step to an untyped one (the suspended values do not match the label's
  arity). Every other rule is `StepFXR`'s, unchanged; `switch` stays untyped and is outside the
  typed fragment.
* **`TyEnv H`**: what the typing is relative to.
  - `m₀`: the module instance of every frame (programs of **one** module instance);
  - `ι`: how a declared value type reads as an FX type (the model has no `cont` type
    constructor: `contType? m ct` reads `$ct` as a function type, so whether `(ref $ct)` in a
    block or tag type is a continuation is a choice, made by `ι`);
  - `ct`: a typing of Core administrative instructions at base types, indexed by the store
    (a parameter, like `TypedFX`'s `core`);
  - `ext`: store extension (for instance Silmaril's `Extend`);
  - `newTy ct`: the operand type of `cont.new $ct`.
* **`TL E s Γ Ls R code i o`**: FX administrative code at the stack type `i → o`, in store `s`,
  with continuation slot `k` at type `Γ[k]`, label types `Ls` and return type `R`. Every head
  constructor builds in stack weakening (`pre`). Handler frames type their body with no labels
  and no return (`[]`, `none`); their `(on $tag $label)` clauses must fit the label
  (`HClauseOk`): the label takes the tag's parameters and a continuation from the tag's results
  to the handler's results. `(on $tag switch)` clauses are not typed.
* **`ContTy`**: a continuation at `$ct = [ps] → rs` is a **Kripke context**: in every extended
  store and slot typing, it fills code of type `[] → ps` (no labels, no return) to code of type
  `[] → rs`. `KOk`: every slot of `Γ` is consumed or holds a continuation at its type.
* **`CoreHyp E P host fx`**: the hypotheses on the Core part (preservation of `ct` by Core steps,
  monotonicity, the shapes of values, `trap`, `throw_ref` and `drop`, the exception allocated by
  `resume_throw`, and the typing of `cont.new` and FX function bodies). They are hypotheses,
  not `Task`s: they describe a Core type system (Silmaril's `Step.preservation` is one
  candidate), and none is instantiated here.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXPres

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXResume
open Silmaril.Wasm.Models.FXResumeT
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- The tag instance `ti` has `n` parameters. -/
def TagArity (ti : TagInst) (n : Nat) : Prop :=
  ∃ tp tr, ti.type.funcType? = some (tp, tr) ∧ tp.length = n

/-- **CoreFX with typed `cont.bind`, `resume`, `suspend` and `resume_throw`.** `StepFXR` with
`suspend` and `resume_throw` taking the tag's number of operands (`TagArity`). -/
inductive StepFXS (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX) :
    ConfigFX H → ConfigFX H → Prop where
  /-- A Core step on Core code (FX function codes refused). -/
  | core {s s' : Store H} {K : List (Option ContFX)} {f f' : Frame} {cs cs' : List Admin}
      (h : Step P (blockFX host fx) ⟨s, f, cs⟩ ⟨s', f', cs'⟩) :
      StepFXS P host fx ⟨s, K, f, cs.map .core⟩ ⟨s', K, f', cs'.map .core⟩
  /-- `ctxt-instrs`, skipping FX values. -/
  | seq {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame} {vs : List FVal}
      {es es' rest : List AdminFX} (h : StepFXS P host fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩)
      (hne : vs ≠ [] ∨ rest ≠ []) :
      StepFXS P host fx ⟨s, K, f, fvals vs ++ es ++ rest⟩ ⟨s', K', f', fvals vs ++ es' ++ rest⟩
  | ctxLabel {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame} {n : Nat}
      {k : List InstrFX} {es es' : List AdminFX}
      (h : StepFXS P host fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
      StepFXS P host fx ⟨s, K, f, [.label n k es]⟩ ⟨s', K', f', [.label n k es']⟩
  | ctxFrame {s s' : Store H} {K K' : List (Option ContFX)} {f fi fi' : Frame} {n : Nat}
      {es es' : List AdminFX} (h : StepFXS P host fx ⟨s, K, fi, es⟩ ⟨s', K', fi', es'⟩) :
      StepFXS P host fx ⟨s, K, f, [.frame n fi es]⟩ ⟨s', K', f, [.frame n fi' es']⟩
  | ctxHandler {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
      {hs : List HClause} {es es' : List AdminFX}
      (h : StepFXS P host fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
      StepFXS P host fx ⟨s, K, f, [.handler hs es]⟩ ⟨s', K', f', [.handler hs es']⟩
  -- Structured control on FX code
  | block {s : Store H} {K : List (Option ContFX)} {f : Frame} {bt : BlockType}
      {body : List InstrFX} {vs : List FVal} {t₁ t₂ : List CValType}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
      StepFXS P host fx ⟨s, K, f, fvals vs ++ [.block bt body]⟩
        ⟨s, K, f, [.label t₂.length [] (fvals vs ++ body.map InstrFX.toAdmin)]⟩
  | loop {s : Store H} {K : List (Option ContFX)} {f : Frame} {bt : BlockType}
      {body : List InstrFX} {vs : List FVal} {t₁ t₂ : List CValType}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
      StepFXS P host fx ⟨s, K, f, fvals vs ++ [.loop bt body]⟩
        ⟨s, K, f, [.label t₁.length [.loop bt body] (fvals vs ++ body.map InstrFX.toAdmin)]⟩
  | ifTrue {s : Store H} {K : List (Option ContFX)} {f : Frame} {c : BitVec 32}
      {bt : BlockType} {b₁ b₂ : List InstrFX} (hc : c ≠ 0) :
      StepFXS P host fx ⟨s, K, f, [.core (constI32 c), .if_ bt b₁ b₂]⟩ ⟨s, K, f, [.block bt b₁]⟩
  | ifFalse {s : Store H} {K : List (Option ContFX)} {f : Frame} {bt : BlockType}
      {b₁ b₂ : List InstrFX} :
      StepFXS P host fx ⟨s, K, f, [.core (constI32 0), .if_ bt b₁ b₂]⟩ ⟨s, K, f, [.block bt b₂]⟩
  | labelVals {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs : List FVal} :
      StepFXS P host fx ⟨s, K, f, [.label n k (fvals vs)]⟩ ⟨s, K, f, fvals vs⟩
  | brLabelZero {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs' vs : List FVal} {l : LabelIdx} {rest : List AdminFX}
      (hl : l.toNat = 0) (hn : vs.length = n) :
      StepFXS P host fx
        ⟨s, K, f, [.label n k (fvals vs' ++ fvals vs ++ [.core (.plain (.br l))] ++ rest)]⟩
        ⟨s, K, f, fvals vs ++ k.map InstrFX.toAdmin⟩
  | brLabelSucc {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs : List FVal} {l : LabelIdx} {rest : List AdminFX}
      (hl : 0 < l.toNat) :
      StepFXS P host fx ⟨s, K, f, [.label n k (fvals vs ++ [.core (.plain (.br l))] ++ rest)]⟩
        ⟨s, K, f, fvals vs ++ [.core (.plain (.br (labelPred l)))]⟩
  | brHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {vs : List FVal} {l : LabelIdx} {rest : List AdminFX} :
      StepFXS P host fx ⟨s, K, f, [.handler hs (fvals vs ++ [.core (.plain (.br l))] ++ rest)]⟩
        ⟨s, K, f, fvals vs ++ [.core (.plain (.br l))]⟩
  | returnLabel {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs : List FVal} {rest : List AdminFX} :
      StepFXS P host fx ⟨s, K, f, [.label n k (fvals vs ++ [.core (.plain .return_)] ++ rest)]⟩
        ⟨s, K, f, fvals vs ++ [.core (.plain .return_)]⟩
  | returnHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {vs : List FVal} {rest : List AdminFX} :
      StepFXS P host fx ⟨s, K, f, [.handler hs (fvals vs ++ [.core (.plain .return_)] ++ rest)]⟩
        ⟨s, K, f, fvals vs ++ [.core (.plain .return_)]⟩
  | frameVals {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat}
      {vs : List FVal} (hn : vs.length = n) :
      StepFXS P host fx ⟨s, K, f, [.frame n fi (fvals vs)]⟩ ⟨s, K, f, fvals vs⟩
  | returnFrame {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat}
      {vs' vs : List FVal} {rest : List AdminFX} (hn : vs.length = n) :
      StepFXS P host fx
        ⟨s, K, f, [.frame n fi (fvals vs' ++ fvals vs ++ [.core (.plain .return_)] ++ rest)]⟩
        ⟨s, K, f, fvals vs⟩
  | handlerVals {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {vs : List FVal} :
      StepFXS P host fx ⟨s, K, f, [.handler hs (fvals vs)]⟩ ⟨s, K, f, fvals vs⟩
  /-- Core's `drop` on a continuation reference (new). -/
  | dropCont {s : Store H} {K : List (Option ContFX)} {f : Frame} {k : Nat} :
      StepFXS P host fx ⟨s, K, f, [.contRef k, .core (.plain .drop)]⟩ ⟨s, K, f, []⟩
  -- Traps and exceptions through FX code
  | trapSeq {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal}
      {rest : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ []) :
      StepFXS P host fx ⟨s, K, f, fvals vs ++ [.core .trap] ++ rest⟩ ⟨s, K, f, [.core .trap]⟩
  | trapLabel {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} :
      StepFXS P host fx ⟨s, K, f, [.label n k [.core .trap]]⟩ ⟨s, K, f, [.core .trap]⟩
  | trapFrame {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat} :
      StepFXS P host fx ⟨s, K, f, [.frame n fi [.core .trap]]⟩ ⟨s, K, f, [.core .trap]⟩
  | trapHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause} :
      StepFXS P host fx ⟨s, K, f, [.handler hs [.core .trap]]⟩ ⟨s, K, f, [.core .trap]⟩
  | throwSeq {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {a : Nat}
      {rest : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ []) :
      StepFXS P host fx ⟨s, K, f, fvals vs ++ cthrowing a ++ rest⟩ ⟨s, K, f, cthrowing a⟩
  | throwLabel {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {a : Nat} :
      StepFXS P host fx ⟨s, K, f, [.label n k (cthrowing a)]⟩ ⟨s, K, f, cthrowing a⟩
  | throwFrame {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat} {a : Nat} :
      StepFXS P host fx ⟨s, K, f, [.frame n fi (cthrowing a)]⟩ ⟨s, K, f, cthrowing a⟩
  | throwHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {a : Nat} :
      StepFXS P host fx ⟨s, K, f, [.handler hs (cthrowing a)]⟩ ⟨s, K, f, cthrowing a⟩
  -- FX functions (arguments become locals, so they are Core values)
  | invoke {s : Store H} {K : List (Option ContFX)} {f : Frame} {c : Admin} {vs : List Val}
      {a : Nat} {fi : FuncInst H} {h : H} {F : FuncFX} (hc : c.IsCallRef)
      (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host h) (hfx : fx h = some F)
      (hn : vs.length = F.nparams) :
      StepFXS P host fx ⟨s, K, f, cvals vs ++ [.core (.ref (.func a)), .core c]⟩
        ⟨s, K, f, [.frame F.nresults (Frame.forCall F.module vs F.locals)
          [.label F.nresults [] (F.body.map InstrFX.toAdmin)]]⟩
  -- Continuations
  | contNew {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat} {fi : FuncInst H}
      {ct : TypeIdx} (hf : s.funcs[a]? = some fi) :
      StepFXS P host fx ⟨s, K, f, [.core (.ref (.func a)), .fx (.contNew ct)]⟩
        ⟨s, K ++ [some ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType fi.type)]⟩], f,
          [.contRef K.length]⟩
  | contNewNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {ct : TypeIdx} :
      StepFXS P host fx ⟨s, K, f, [.core (.ref .null), .fx (.contNew ct)]⟩
        ⟨s, K, f, [.core .trap]⟩
  | contBind {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {k : Nat}
      {C : ContFX} {ct ct' : TypeIdx} (hk : K[k]? = some (some C))
      (ha : BindArity f.module ct ct' vs.length) :
      StepFXS P host fx ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.contBind ct ct')]⟩
        ⟨s, K.set k none ++ [some ⟨fun c => C.plug (fvals vs ++ c)⟩], f, [.contRef K.length]⟩
  | contBindNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal}
      {ct ct' : TypeIdx} (ha : BindArity f.module ct ct' vs.length) :
      StepFXS P host fx ⟨s, K, f, fvals vs ++ [.core (.ref .null), .fx (.contBind ct ct')]⟩
        ⟨s, K, f, [.core .trap]⟩
  | contBindUsed {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {k : Nat}
      {ct ct' : TypeIdx} (hk : K[k]? = some none) (ha : BindArity f.module ct ct' vs.length) :
      StepFXS P host fx ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.contBind ct ct')]⟩
        ⟨s, K, f, [.core .trap]⟩
  | resume {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {k : Nat}
      {C : ContFX} {ct : TypeIdx} {hs : List OnClause} {hs' : List HClause}
      (hk : K[k]? = some (some C)) (hr : hs.mapM (resolve s f) = some hs')
      (ha : ResumeArity f.module ct vs.length) :
      StepFXS P host fx ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.resume ct hs)]⟩
        ⟨s, K.set k none, f, [.handler hs' (C.plug (fvals vs))]⟩
  | resumeNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal}
      {ct : TypeIdx} {hs : List OnClause} (ha : ResumeArity f.module ct vs.length) :
      StepFXS P host fx ⟨s, K, f, fvals vs ++ [.core (.ref .null), .fx (.resume ct hs)]⟩
        ⟨s, K, f, [.core .trap]⟩
  | resumeUsed {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List FVal} {k : Nat}
      {ct : TypeIdx} {hs : List OnClause} (hk : K[k]? = some none)
      (ha : ResumeArity f.module ct vs.length) :
      StepFXS P host fx ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.resume ct hs)]⟩
        ⟨s, K, f, [.core .trap]⟩
  /-- `resume_throw`: the payload is the exception's fields, so Core values. -/
  | resumeThrow {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val} {k : Nat}
      {C : ContFX} {ct : TypeIdx} {x : TagIdx} {hs : List OnClause} {hs' : List HClause}
      {ta : Nat} {ti : TagInst} (hk : K[k]? = some (some C)) (ht : s.tag? f x = some (ta, ti))
      (hr : hs.mapM (resolve s f) = some hs') (ha : TagArity ti vs.length) :
      StepFXS P host fx ⟨s, K, f, cvals vs ++ [.contRef k, .fx (.resumeThrow ct x hs)]⟩
        ⟨s.addExn ⟨ta, vs⟩, K.set k none, f, [.handler hs' (C.plug (cthrowing s.exns.length))]⟩
  | resumeThrowNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val}
      {ct : TypeIdx} {x : TagIdx} {hs : List OnClause} :
      StepFXS P host fx ⟨s, K, f, cvals vs ++ [.core (.ref .null), .fx (.resumeThrow ct x hs)]⟩
        ⟨s, K, f, [.core .trap]⟩
  /-- `suspend x` under a handler with clause `(on x l)` and no inner handler for `x`. -/
  | suspend {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {E : CtxV} {vs : List FVal} {x : TagIdx} {ta : Nat} {ti : TagInst} {l : LabelIdx}
      (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
      (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l))
      (ha : TagArity ti vs.length) :
      StepFXS P host fx ⟨s, K, f, [.handler hs (E.plug (fvals vs ++ [.fx (.suspend x)]))]⟩
        ⟨s, K ++ [some ⟨E.plug⟩], f, fvals vs ++ [.contRef K.length, .core (.plain (.br l))]⟩
  /-- `switch ct x` under a handler with clause `(on x switch)`. -/
  | switch {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {E : CtxV} {vs : List FVal} {k : Nat} {C : ContFX} {ct : TypeIdx} {x : TagIdx} {ta : Nat}
      {ti : TagInst} (hk : K[k]? = some (some C))
      (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
      (hc : hs.find? (fun c => c.tag == ta) = some (.onSwitch ta)) :
      StepFXS P host fx
        ⟨s, K, f, [.handler hs (E.plug (fvals vs ++ [.contRef k, .fx (.switch ct x)]))]⟩
        ⟨s, K.set k none ++ [some ⟨E.plug⟩], f,
          [.handler hs (C.plug (fvals vs ++ [.contRef K.length]))]⟩



/-- Runs of `StepFXS`. -/
abbrev StepsFXS (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX) :=
  Relation.ReflTransGen (StepFXS P host fx)

/-! ## The typing environment -/

/-- What the configuration typing is relative to. -/
structure TyEnv (H : Type) where
  /-- The module instance of every frame. -/
  m₀ : ModuleInst
  /-- A declared value type as an FX type. -/
  ι : CValType → FTy
  /-- Core administrative instructions at base types. -/
  ct : Store H → Admin → List FTy → List FTy → Prop
  /-- Store extension. -/
  ext : Store H → Store H → Prop
  /-- The operand type of `cont.new $ct`. -/
  newTy : TypeIdx → FTy

/-- Declared value types as FX types. -/
def TyEnv.tys (E : TyEnv H) (ts : List CValType) : List FTy := ts.map E.ι

/-- The condition type of `if`. -/
def condTy : FTy := .val (.num (.int .i32))

/-- `br` and `return`, typed by the FX judgement, not by `ct`. -/
def IsCtl : Admin → Prop
  | .plain (.br _) => True
  | .plain .return_ => True
  | _ => False

/-- A resolved handler clause fits the labels `Ls` of the `resume` and the handler's result
types `ts`. `(on $tag switch)` is not typed. -/
def HClauseOk (E : TyEnv H) (s : Store H) (Ls : List (List FTy)) (ts : List FTy) :
    HClause → Prop
  | .onLabel ta l => ∃ ti tp tr ct' rs, s.tags[ta]? = some ti ∧
      ti.type.funcType? = some (tp, tr) ∧ contType? E.m₀ ct' = some (tr, rs) ∧ E.tys rs = ts ∧
      Ls[l.toNat]? = some (E.tys tp ++ [.cont ct'])
  | .onSwitch _ => False

/-- A source handler clause, resolved in module `m₀`, fits. -/
def OnClauseOk (E : TyEnv H) (s : Store H) (Ls : List (List FTy)) (ts : List FTy) :
    OnClause → Prop
  | .onLabel x l => ∃ ta, E.m₀.tags[x.toNat]? = some ta ∧ HClauseOk E s Ls ts (.onLabel ta l)
  | .onSwitch _ => False

/-- **The configuration typing.** `TL E s Γ Ls R code i o`: `code` has stack type `i → o`.
Each head constructor carries its own stack weakening `pre`. -/
inductive TL (E : TyEnv H) (s : Store H) (Γ : List TypeIdx) :
    List (List FTy) → Option (List FTy) → List AdminFX → List FTy → List FTy → Prop where
  | nil {Ls : List (List FTy)} {R : Option (List FTy)} {t : List FTy} : TL E s Γ Ls R [] t t
  /-- A Core administrative instruction other than `br` and `return`, by `ct`. -/
  | core {Ls : List (List FTy)} {R : Option (List FTy)} {a : Admin} {as : List AdminFX}
      {pre i₀ o₀ t : List FTy} (hc : E.ct s a i₀ o₀) (hn : ¬ IsCtl a)
      (hr : TL E s Γ Ls R as (pre ++ o₀) t) : TL E s Γ Ls R (.core a :: as) (pre ++ i₀) t
  /-- `br l`: the label's types, then any stack (stack-polymorphic). -/
  | br {Ls : List (List FTy)} {R : Option (List FTy)} {l : LabelIdx} {as : List AdminFX}
      {pre ts o₀ t : List FTy} (hl : Ls[l.toNat]? = some ts) (hr : TL E s Γ Ls R as o₀ t) :
      TL E s Γ Ls R (.core (.plain (.br l)) :: as) (pre ++ ts) t
  | ret {Ls : List (List FTy)} {R : Option (List FTy)} {as : List AdminFX}
      {pre ts o₀ t : List FTy} (hR : R = some ts) (hr : TL E s Γ Ls R as o₀ t) :
      TL E s Γ Ls R (.core (.plain .return_) :: as) (pre ++ ts) t
  | contRef {Ls : List (List FTy)} {R : Option (List FTy)} {k : Nat} {ct : TypeIdx}
      {as : List AdminFX} {pre t : List FTy} (hk : Γ[k]? = some ct)
      (hr : TL E s Γ Ls R as (pre ++ [.cont ct]) t) : TL E s Γ Ls R (.contRef k :: as) pre t
  /-- `cont.new $ct : [newTy ct] → [(ref $ct)]`. -/
  | contNew {Ls : List (List FTy)} {R : Option (List FTy)} {ct : TypeIdx}
      {ty : List CValType × List CValType} {as : List AdminFX} {pre t : List FTy}
      (h : contType? E.m₀ ct = some ty) (hr : TL E s Γ Ls R as (pre ++ [.cont ct]) t) :
      TL E s Γ Ls R (.fx (.contNew ct) :: as) (pre ++ [E.newTy ct]) t
  /-- `cont.bind $ct $ct' : [ps₁ (ref $ct)] → [(ref $ct')]`. -/
  | contBind {Ls : List (List FTy)} {R : Option (List FTy)} {ct ct' : TypeIdx}
      {ps₁ ps₂ rs : List CValType} {as : List AdminFX} {pre t : List FTy}
      (h : contType? E.m₀ ct = some (ps₁ ++ ps₂, rs)) (h' : contType? E.m₀ ct' = some (ps₂, rs))
      (hr : TL E s Γ Ls R as (pre ++ [.cont ct']) t) :
      TL E s Γ Ls R (.fx (.contBind ct ct') :: as) (pre ++ E.tys ps₁ ++ [.cont ct]) t
  /-- `resume $ct hs : [ps (ref $ct)] → [rs]`, with the clauses fitting. -/
  | resume {Ls : List (List FTy)} {R : Option (List FTy)} {ct : TypeIdx} {hs : List OnClause}
      {ps rs : List CValType} {as : List AdminFX} {pre t : List FTy}
      (h : contType? E.m₀ ct = some (ps, rs)) (hh : ∀ c ∈ hs, OnClauseOk E s Ls (E.tys rs) c)
      (hr : TL E s Γ Ls R as (pre ++ E.tys rs) t) :
      TL E s Γ Ls R (.fx (.resume ct hs) :: as) (pre ++ E.tys ps ++ [.cont ct]) t
  /-- `resume_throw $ct $x hs : [tp (ref $ct)] → [rs]`, `tp` the tag's parameters. -/
  | resumeThrow {Ls : List (List FTy)} {R : Option (List FTy)} {ct : TypeIdx} {x : TagIdx}
      {hs : List OnClause} {ps rs tp tr : List CValType} {ta : Nat} {ti : TagInst}
      {as : List AdminFX} {pre t : List FTy}
      (h : contType? E.m₀ ct = some (ps, rs)) (hx : E.m₀.tags[x.toNat]? = some ta)
      (ht : s.tags[ta]? = some ti) (htt : ti.type.funcType? = some (tp, tr))
      (hh : ∀ c ∈ hs, OnClauseOk E s Ls (E.tys rs) c)
      (hr : TL E s Γ Ls R as (pre ++ E.tys rs) t) :
      TL E s Γ Ls R (.fx (.resumeThrow ct x hs) :: as) (pre ++ E.tys tp ++ [.cont ct]) t
  /-- `suspend $x : [tp] → [tr]`. -/
  | suspend {Ls : List (List FTy)} {R : Option (List FTy)} {x : TagIdx}
      {tp tr : List CValType} {ta : Nat} {ti : TagInst} {as : List AdminFX} {pre t : List FTy}
      (hx : E.m₀.tags[x.toNat]? = some ta) (ht : s.tags[ta]? = some ti)
      (htt : ti.type.funcType? = some (tp, tr)) (hr : TL E s Γ Ls R as (pre ++ E.tys tr) t) :
      TL E s Γ Ls R (.fx (.suspend x) :: as) (pre ++ E.tys tp) t
  | block {Ls : List (List FTy)} {R : Option (List FTy)} {bt : BlockType}
      {body : List InstrFX} {t₁ t₂ : List CValType} {as : List AdminFX} {pre t : List FTy}
      (hb : E.m₀.blockType? bt = some (t₁, t₂))
      (hbody : TL E s Γ (E.tys t₂ :: Ls) R (body.map InstrFX.toAdmin) (E.tys t₁) (E.tys t₂))
      (hr : TL E s Γ Ls R as (pre ++ E.tys t₂) t) :
      TL E s Γ Ls R (.block bt body :: as) (pre ++ E.tys t₁) t
  | loop {Ls : List (List FTy)} {R : Option (List FTy)} {bt : BlockType}
      {body : List InstrFX} {t₁ t₂ : List CValType} {as : List AdminFX} {pre t : List FTy}
      (hb : E.m₀.blockType? bt = some (t₁, t₂))
      (hbody : TL E s Γ (E.tys t₁ :: Ls) R (body.map InstrFX.toAdmin) (E.tys t₁) (E.tys t₂))
      (hr : TL E s Γ Ls R as (pre ++ E.tys t₂) t) :
      TL E s Γ Ls R (.loop bt body :: as) (pre ++ E.tys t₁) t
  | if_ {Ls : List (List FTy)} {R : Option (List FTy)} {bt : BlockType}
      {b₁ b₂ : List InstrFX} {t₁ t₂ : List CValType} {as : List AdminFX} {pre t : List FTy}
      (hb : E.m₀.blockType? bt = some (t₁, t₂))
      (h₁ : TL E s Γ (E.tys t₂ :: Ls) R (b₁.map InstrFX.toAdmin) (E.tys t₁) (E.tys t₂))
      (h₂ : TL E s Γ (E.tys t₂ :: Ls) R (b₂.map InstrFX.toAdmin) (E.tys t₁) (E.tys t₂))
      (hr : TL E s Γ Ls R as (pre ++ E.tys t₂) t) :
      TL E s Γ Ls R (.if_ bt b₁ b₂ :: as) (pre ++ E.tys t₁ ++ [condTy]) t
  /-- A label: the continuation `k` from the label's types `tl` to the result `te`, the body
  under the label. -/
  | label {Ls : List (List FTy)} {R : Option (List FTy)} {n : Nat} {k : List InstrFX}
      {body : List AdminFX} {tl te : List FTy} {as : List AdminFX} {pre t : List FTy}
      (hn : n = tl.length) (hk : TL E s Γ Ls R (k.map InstrFX.toAdmin) tl te)
      (hb : TL E s Γ (tl :: Ls) R body [] te) (hr : TL E s Γ Ls R as (pre ++ te) t) :
      TL E s Γ Ls R (.label n k body :: as) pre t
  /-- A frame of module `m₀`: the body with no labels and return type `ts`. -/
  | frame {Ls : List (List FTy)} {R : Option (List FTy)} {n : Nat} {fi : Frame}
      {body : List AdminFX} {ts : List FTy} {as : List AdminFX} {pre t : List FTy}
      (hm : fi.module = E.m₀) (hn : n = ts.length) (hb : TL E s Γ [] (some ts) body [] ts)
      (hr : TL E s Γ Ls R as (pre ++ ts) t) : TL E s Γ Ls R (.frame n fi body :: as) pre t
  /-- A handler frame: the body with no labels and no return, the clauses fitting `Ls`. -/
  | handler {Ls : List (List FTy)} {R : Option (List FTy)} {hs : List HClause}
      {body : List AdminFX} {ts : List FTy} {as : List AdminFX} {pre t : List FTy}
      (hh : ∀ c ∈ hs, HClauseOk E s Ls ts c) (hb : TL E s Γ [] none body [] ts)
      (hr : TL E s Γ Ls R as (pre ++ ts) t) : TL E s Γ Ls R (.handler hs body :: as) pre t

/-! ## Continuations and the continuation store -/

/-- **A continuation at `$ct = [ps] → rs`**: in every extension, it fills code of type
`[] → ps` to code of type `[] → rs` (no labels, no return). -/
def ContTy (E : TyEnv H) (s : Store H) (Γ : List TypeIdx) (C : ContFX) (ct : TypeIdx) : Prop :=
  ∃ ps rs, contType? E.m₀ ct = some (ps, rs) ∧
    ∀ (s' : Store H) (Γ' : List TypeIdx) (c : List AdminFX), E.ext s s' → Γ <+: Γ' →
      TL E s' Γ' [] none c [] (E.tys ps) → TL E s' Γ' [] none (C.plug c) [] (E.tys rs)

/-- **The continuation store fits `Γ`**: one type per slot; a typed slot is consumed or holds a
continuation at its type. -/
def KOk (E : TyEnv H) (s : Store H) (Γ : List TypeIdx) (K : List (Option ContFX)) : Prop :=
  Γ.length = K.length ∧ ∀ (k : Nat) (ct : TypeIdx), Γ[k]? = some ct →
    K[k]? = some none ∨ ∃ C, K[k]? = some (some C) ∧ ContTy E s Γ C ct

/-- **A typed configuration** at result types `ts`: frame of module `m₀`, slot typing `Γ`. -/
def ConfigOk (E : TyEnv H) (Γ : List TypeIdx) (c : ConfigFX H) (ts : List FTy) : Prop :=
  c.frame.module = E.m₀ ∧ KOk E c.store Γ c.conts ∧ TL E c.store Γ [] none c.code [] ts

/-! ## Hypotheses on the Core part -/

/-- **What preservation needs from the Core typing `E.ct`** (and from the FX function table). -/
structure CoreHyp (E : TyEnv H) (P : Profile) (host : HostSemantics H)
    (fx : H → Option FuncFX) : Prop where
  ext_refl : ∀ s, E.ext s s
  ext_trans : ∀ {s₁ s₂ s₃}, E.ext s₁ s₂ → E.ext s₂ s₃ → E.ext s₁ s₃
  ct_mono : ∀ {s s' a i o}, E.ext s s' → E.ct s a i o → E.ct s' a i o
  tags_mono : ∀ {s s' : Store H} {ta : Nat} {ti : TagInst}, E.ext s s' → s.tags[ta]? = some ti →
    s'.tags[ta]? = some ti
  /-- A value pushes one type. -/
  val : ∀ {s v i o}, E.ct s (Val.toAdmin v) i o → i = [] ∧ ∃ t, o = [t]
  /-- `trap` has every type. -/
  trap : ∀ s i o, E.ct s .trap i o
  /-- `throw_ref` takes one operand and is stack-polymorphic. -/
  throwRef : ∀ {s i o}, E.ct s (.plain .throwRef) i o → ∃ x, (∃ i₁, i = i₁ ++ [x]) ∧
    ∀ i' o', E.ct s (.plain .throwRef) (i' ++ [x]) o'
  /-- `drop` takes one operand. -/
  drop : ∀ {s i o}, E.ct s (.plain .drop) i o → ∃ x, i = [x] ∧ o = []
  /-- **Core preservation**: a Core step on typed Core code (frame of module `m₀`) extends the
  store, keeps the module and the type. -/
  core : ∀ {s s' : Store H} {f f' : Frame} {cs cs' : List Admin} {Γ : List TypeIdx}
    {Ls : List (List FTy)} {R : Option (List FTy)} {i o : List FTy},
    Step P (blockFX host fx) ⟨s, f, cs⟩ ⟨s', f', cs'⟩ → f.module = E.m₀ →
    TL E s Γ Ls R (cs.map .core) i o →
    E.ext s s' ∧ f'.module = E.m₀ ∧ TL E s' Γ Ls R (cs'.map .core) i o
  /-- The exception allocated by `resume_throw` is thrown at every type. -/
  exn : ∀ (s : Store H) (e : ExnInst) (Γ : List TypeIdx) (i o : List FTy),
    E.ext s (s.addExn e) ∧ TL E (s.addExn e) Γ [] none (cthrowing s.exns.length) i o
  /-- `cont.new` of a function reference at `newTy ct` makes a continuation of type `$ct`. -/
  new : ∀ {s : Store H} {a : Nat} {fi : FuncInst H} {ct : TypeIdx} {ps rs : List CValType},
    s.funcs[a]? = some fi → E.ct s (.ref (.func a)) [] [E.newTy ct] →
    contType? E.m₀ ct = some (ps, rs) → ∀ (s' : Store H) (Γ : List TypeIdx), E.ext s s' →
    TL E s' Γ [] none [.core (.ref (.func a)), .core (.callRefType fi.type)] (E.tys ps) (E.tys rs)
  /-- A call of an FX function: the call's type is the function's, and the body is typed. -/
  invoke : ∀ {s : Store H} {Γ : List TypeIdx} {a : Nat} {fi : FuncInst H} {h : H} {F : FuncFX}
    {c : Admin} {t : FTy} {i o : List FTy}, c.IsCallRef → s.funcs[a]? = some fi →
    fi.code = .host h → fx h = some F → E.ct s (.ref (.func a)) [] [t] → E.ct s c i o →
    ∃ ps rs, i = ps ++ [t] ∧ o = rs ∧ ps.length = F.nparams ∧ F.module = E.m₀ ∧
      F.nresults = rs.length ∧ TL E s Γ [rs] (some rs) (F.body.map InstrFX.toAdmin) [] rs

end Silmaril.Wasm.Models.FXPres
