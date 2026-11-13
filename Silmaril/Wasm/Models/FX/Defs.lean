module

public import Silmaril.Wasm.Models.Model.Thms

/-!
# CoreFX: Core 3.0 with stack switching (WasmFX), as an extension of Core `Step`

A reduction semantics for the stack-switching proposal (WasmFX; Phipps-Costin et al.,
"Continuing WebAssembly with Effect Handlers", OOPSLA 2023, and the Phase 3 proposal's
overview), built **on top of** silmaril-lean's Core 3.0 `Step` rather than beside it:

* **Syntax.** `FXInstr` is the six instructions `cont.new`, `cont.bind`, `resume`,
  `resume_throw`, `suspend` and `switch` (with `(on $tag $label)` / `(on $tag switch)` handler
  clauses, `OnClause`). `InstrFX` is FX source code: a Core instruction, an FX instruction, or a
  structured `block`/`loop`/`if` whose bodies are FX code. `AdminFX` is FX administrative code:
  a Core administrative instruction (`core`, which carries Core code with Core bodies), the FX
  instructions and structured instructions, FX `label`/`frame` frames, the **handler frame**
  `handler hs` that `resume` installs, and the continuation reference `contRef k`.
* **Configurations.** `ConfigFX H`: a Core store, the **continuation store** (`conts`, a list of
  one-shot continuations: `none` once consumed), a frame and FX code. A continuation `ContFX` is
  a code context with a hole (`plug`); suspension captures a context `Ctx` between a handler and
  the `suspend`.
* **FX functions.** A Core store holds Core functions only, so FX function bodies are given by a
  table `fx : H → Option FuncFX` on host codes: a host function whose code `h` has
  `fx h = some F` is an FX function with body `F.body`. Core steps run with the host
  `blockFX host fx`, which refuses FX codes, and the FX rule `invoke` enters them. With no FX
  functions (`noFX`), `blockFX host noFX = host`.
* **Reduction** `StepFX P host fx`. The rule `core` lifts a Core step on Core code
  (`Step P (blockFX host fx)`). The rule `seq` is Core's `ctxt-instrs` for FX code, and the
  structural rules (block entry, `br`, `return`, values, traps and exceptions through FX
  labels, frames and handlers) mirror Core's. The FX rules follow the proposal:
  `cont.new` allocates a continuation from a function reference; `cont.bind` partially applies
  one; `resume` consumes one and runs it under a handler frame; `resume_throw` does the same with
  an exception raised at the hole; `suspend x` (inside a handler with clause `(on x l)` and no
  inner handler for `x`) captures the context as a new continuation and branches to `l` with it;
  `switch` (clause `(on x switch)`) swaps the current context for the target continuation,
  passing the captured context to it. Null and consumed continuations trap.

Not modelled: validation of FX code (continuation types are carried as immediates and not
checked; the reduction is untyped), FX bodies under `try_table` (exceptions do propagate through
FX frames, but are caught only by Core handlers on Core code), tail calls to FX functions, and FX
module syntax and instantiation (FX programs are Core stores with FX function tables).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

/-! ## Syntax -/

/-- A `resume` handler clause: `(on $tag $label)` or `(on $tag switch)`. -/
inductive OnClause where
  | onLabel (x : TagIdx) (l : LabelIdx)
  | onSwitch (x : TagIdx)

/-- The stack-switching instructions. Continuation type immediates are not used by the untyped
reduction. -/
inductive FXInstr where
  | contNew (ct : TypeIdx)
  | contBind (ct ct' : TypeIdx)
  | resume (ct : TypeIdx) (hs : List OnClause)
  | resumeThrow (ct : TypeIdx) (x : TagIdx) (hs : List OnClause)
  | suspend (x : TagIdx)
  | switch (ct : TypeIdx) (x : TagIdx)

/-- FX source instructions. -/
inductive InstrFX where
  | core (i : Instr)
  | fx (i : FXInstr)
  | block (bt : BlockType) (body : List InstrFX)
  | loop (bt : BlockType) (body : List InstrFX)
  | if_ (bt : BlockType) (b₁ b₂ : List InstrFX)

/-- A resolved handler clause (a tag address). -/
inductive HClause where
  | onLabel (ta : Nat) (l : LabelIdx)
  | onSwitch (ta : Nat)
  deriving DecidableEq

/-- The tag address of a clause. -/
def HClause.tag : HClause → Nat
  | .onLabel ta _ | .onSwitch ta => ta

/-- FX administrative code. -/
inductive AdminFX where
  /-- A Core administrative instruction (with Core bodies). -/
  | core (a : Admin)
  | fx (i : FXInstr)
  | block (bt : BlockType) (body : List InstrFX)
  | loop (bt : BlockType) (body : List InstrFX)
  | if_ (bt : BlockType) (b₁ b₂ : List InstrFX)
  | label (n : Nat) (cont : List InstrFX) (body : List AdminFX)
  | frame (n : Nat) (f : Frame) (body : List AdminFX)
  /-- The handler frame installed by `resume`. -/
  | handler (hs : List HClause) (body : List AdminFX)
  /-- `ref.cont k`. -/
  | contRef (k : Nat)

/-- FX source code as administrative code. -/
def InstrFX.toAdmin : InstrFX → AdminFX
  | .core i => .core (.plain i)
  | .fx i => .fx i
  | .block bt b => .block bt b
  | .loop bt b => .loop bt b
  | .if_ bt b₁ b₂ => .if_ bt b₁ b₂

/-- Core values as FX code. -/
def cvals (vs : List Val) : List AdminFX := (vals vs).map .core

/-- A thrown exception as FX code. -/
def cthrowing (a : Nat) : List AdminFX := (throwing a).map .core

/-- A one-shot continuation: code with a hole. -/
structure ContFX where
  /-- Fill the hole. -/
  plug : List AdminFX → List AdminFX

/-- An FX function: the body runs in a frame of `module` with `locals`. -/
structure FuncFX where
  module : ModuleInst
  nparams : Nat
  nresults : Nat
  locals : List ValType
  body : List InstrFX

/-- FX configurations: a Core store, the continuation store, a frame and FX code. -/
structure ConfigFX (H : Type) where
  store : Store H
  conts : List (Option ContFX)
  frame : Frame
  code : List AdminFX

/-- The Core configuration as an FX configuration (no continuations). -/
def ofCore {H : Type} (c : Config H) : ConfigFX H := ⟨c.store, [], c.frame, c.code.map .core⟩

/-- No FX functions. -/
def noFX {H : Type} : H → Option FuncFX := fun _ => none

/-- The Core host of an FX program: FX function codes have no host behaviour. -/
def blockFX {H : Type} (host : HostSemantics H) (fx : H → Option FuncFX) : HostSemantics H :=
  fun h s vs out => fx h = none ∧ host h s vs out

/-! ## Contexts of suspension -/

/-- Evaluation contexts between a handler frame and a `suspend`/`switch`. -/
inductive Ctx where
  | hole
  | seq (vs : List Val) (E : Ctx) (rest : List AdminFX)
  | label (n : Nat) (cont : List InstrFX) (E : Ctx)
  | frame (n : Nat) (f : Frame) (E : Ctx)
  | handler (hs : List HClause) (E : Ctx)

/-- Fill the hole of a context. -/
def Ctx.plug : Ctx → List AdminFX → List AdminFX
  | .hole, c => c
  | .seq vs E rest, c => cvals vs ++ E.plug c ++ rest
  | .label n k E, c => [.label n k (E.plug c)]
  | .frame n f E, c => [.frame n f (E.plug c)]
  | .handler hs E, c => [.handler hs (E.plug c)]

/-- The frame in effect at the hole, starting from frame `f`. -/
def Ctx.frameAt (f : Frame) : Ctx → Frame
  | .hole => f
  | .seq _ E _ => E.frameAt f
  | .label _ _ E => E.frameAt f
  | .frame _ fi E => E.frameAt fi
  | .handler _ E => E.frameAt f

/-- A handler frame of the context has a clause for tag address `ta`. -/
def Ctx.Handles (ta : Nat) : Ctx → Prop
  | .hole => False
  | .seq _ E _ => E.Handles ta
  | .label _ _ E => E.Handles ta
  | .frame _ _ E => E.Handles ta
  | .handler hs E => (∃ c ∈ hs, c.tag = ta) ∨ E.Handles ta

/-- Resolve a handler clause in the frame of the `resume`. -/
def resolve {H : Type} (s : Store H) (f : Frame) : OnClause → Option HClause
  | .onLabel x l => (s.tag? f x).map fun p => .onLabel p.1 l
  | .onSwitch x => (s.tag? f x).map fun p => .onSwitch p.1

/-! ## Reduction -/

variable {H : Type}

/-- **The CoreFX step relation.** -/
inductive StepFX (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX) :
    ConfigFX H → ConfigFX H → Prop where
  /-- A Core step on Core code (FX function codes refused). -/
  | core {s s' : Store H} {K : List (Option ContFX)} {f f' : Frame} {cs cs' : List Admin}
      (h : Step P (blockFX host fx) ⟨s, f, cs⟩ ⟨s', f', cs'⟩) :
      StepFX P host fx ⟨s, K, f, cs.map .core⟩ ⟨s', K, f', cs'.map .core⟩
  /-- `ctxt-instrs`. -/
  | seq {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame} {vs : List Val}
      {es es' rest : List AdminFX} (h : StepFX P host fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩)
      (hne : vs ≠ [] ∨ rest ≠ []) :
      StepFX P host fx ⟨s, K, f, cvals vs ++ es ++ rest⟩ ⟨s', K', f', cvals vs ++ es' ++ rest⟩
  | ctxLabel {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame} {n : Nat}
      {k : List InstrFX} {es es' : List AdminFX}
      (h : StepFX P host fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
      StepFX P host fx ⟨s, K, f, [.label n k es]⟩ ⟨s', K', f', [.label n k es']⟩
  | ctxFrame {s s' : Store H} {K K' : List (Option ContFX)} {f fi fi' : Frame} {n : Nat}
      {es es' : List AdminFX} (h : StepFX P host fx ⟨s, K, fi, es⟩ ⟨s', K', fi', es'⟩) :
      StepFX P host fx ⟨s, K, f, [.frame n fi es]⟩ ⟨s', K', f, [.frame n fi' es']⟩
  | ctxHandler {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
      {hs : List HClause} {es es' : List AdminFX}
      (h : StepFX P host fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
      StepFX P host fx ⟨s, K, f, [.handler hs es]⟩ ⟨s', K', f', [.handler hs es']⟩
  -- Structured control on FX code
  | block {s : Store H} {K : List (Option ContFX)} {f : Frame} {bt : BlockType}
      {body : List InstrFX} {vs : List Val} {t₁ t₂ : List CValType}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
      StepFX P host fx ⟨s, K, f, cvals vs ++ [.block bt body]⟩
        ⟨s, K, f, [.label t₂.length [] (cvals vs ++ body.map InstrFX.toAdmin)]⟩
  | loop {s : Store H} {K : List (Option ContFX)} {f : Frame} {bt : BlockType}
      {body : List InstrFX} {vs : List Val} {t₁ t₂ : List CValType}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
      StepFX P host fx ⟨s, K, f, cvals vs ++ [.loop bt body]⟩
        ⟨s, K, f, [.label t₁.length [.loop bt body] (cvals vs ++ body.map InstrFX.toAdmin)]⟩
  | ifTrue {s : Store H} {K : List (Option ContFX)} {f : Frame} {c : BitVec 32}
      {bt : BlockType} {b₁ b₂ : List InstrFX} (hc : c ≠ 0) :
      StepFX P host fx ⟨s, K, f, [.core (constI32 c), .if_ bt b₁ b₂]⟩ ⟨s, K, f, [.block bt b₁]⟩
  | ifFalse {s : Store H} {K : List (Option ContFX)} {f : Frame} {bt : BlockType}
      {b₁ b₂ : List InstrFX} :
      StepFX P host fx ⟨s, K, f, [.core (constI32 0), .if_ bt b₁ b₂]⟩ ⟨s, K, f, [.block bt b₂]⟩
  | labelVals {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs : List Val} :
      StepFX P host fx ⟨s, K, f, [.label n k (cvals vs)]⟩ ⟨s, K, f, cvals vs⟩
  | brLabelZero {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs' vs : List Val} {l : LabelIdx} {rest : List AdminFX}
      (hl : l.toNat = 0) (hn : vs.length = n) :
      StepFX P host fx
        ⟨s, K, f, [.label n k (cvals vs' ++ cvals vs ++ [.core (.plain (.br l))] ++ rest)]⟩
        ⟨s, K, f, cvals vs ++ k.map InstrFX.toAdmin⟩
  | brLabelSucc {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs : List Val} {l : LabelIdx} {rest : List AdminFX}
      (hl : 0 < l.toNat) :
      StepFX P host fx ⟨s, K, f, [.label n k (cvals vs ++ [.core (.plain (.br l))] ++ rest)]⟩
        ⟨s, K, f, cvals vs ++ [.core (.plain (.br (labelPred l)))]⟩
  | brHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {vs : List Val} {l : LabelIdx} {rest : List AdminFX} :
      StepFX P host fx ⟨s, K, f, [.handler hs (cvals vs ++ [.core (.plain (.br l))] ++ rest)]⟩
        ⟨s, K, f, cvals vs ++ [.core (.plain (.br l))]⟩
  | returnLabel {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {vs : List Val} {rest : List AdminFX} :
      StepFX P host fx ⟨s, K, f, [.label n k (cvals vs ++ [.core (.plain .return_)] ++ rest)]⟩
        ⟨s, K, f, cvals vs ++ [.core (.plain .return_)]⟩
  | returnHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {vs : List Val} {rest : List AdminFX} :
      StepFX P host fx ⟨s, K, f, [.handler hs (cvals vs ++ [.core (.plain .return_)] ++ rest)]⟩
        ⟨s, K, f, cvals vs ++ [.core (.plain .return_)]⟩
  | frameVals {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat}
      {vs : List Val} (hn : vs.length = n) :
      StepFX P host fx ⟨s, K, f, [.frame n fi (cvals vs)]⟩ ⟨s, K, f, cvals vs⟩
  | returnFrame {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat}
      {vs' vs : List Val} {rest : List AdminFX} (hn : vs.length = n) :
      StepFX P host fx
        ⟨s, K, f, [.frame n fi (cvals vs' ++ cvals vs ++ [.core (.plain .return_)] ++ rest)]⟩
        ⟨s, K, f, cvals vs⟩
  | handlerVals {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {vs : List Val} :
      StepFX P host fx ⟨s, K, f, [.handler hs (cvals vs)]⟩ ⟨s, K, f, cvals vs⟩
  -- Traps and exceptions through FX code
  | trapSeq {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val}
      {rest : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ []) :
      StepFX P host fx ⟨s, K, f, cvals vs ++ [.core .trap] ++ rest⟩ ⟨s, K, f, [.core .trap]⟩
  | trapLabel {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} :
      StepFX P host fx ⟨s, K, f, [.label n k [.core .trap]]⟩ ⟨s, K, f, [.core .trap]⟩
  | trapFrame {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat} :
      StepFX P host fx ⟨s, K, f, [.frame n fi [.core .trap]]⟩ ⟨s, K, f, [.core .trap]⟩
  | trapHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause} :
      StepFX P host fx ⟨s, K, f, [.handler hs [.core .trap]]⟩ ⟨s, K, f, [.core .trap]⟩
  | throwSeq {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val} {a : Nat}
      {rest : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ []) :
      StepFX P host fx ⟨s, K, f, cvals vs ++ cthrowing a ++ rest⟩ ⟨s, K, f, cthrowing a⟩
  | throwLabel {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
      {k : List InstrFX} {a : Nat} :
      StepFX P host fx ⟨s, K, f, [.label n k (cthrowing a)]⟩ ⟨s, K, f, cthrowing a⟩
  | throwFrame {s : Store H} {K : List (Option ContFX)} {f fi : Frame} {n : Nat} {a : Nat} :
      StepFX P host fx ⟨s, K, f, [.frame n fi (cthrowing a)]⟩ ⟨s, K, f, cthrowing a⟩
  /-- Exceptions pass through handler frames (they handle tags of `suspend`, not exceptions). -/
  | throwHandler {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {a : Nat} :
      StepFX P host fx ⟨s, K, f, [.handler hs (cthrowing a)]⟩ ⟨s, K, f, cthrowing a⟩
  -- FX functions
  /-- Calling an FX function enters its body (the analogue of `call_ref-func`). -/
  | invoke {s : Store H} {K : List (Option ContFX)} {f : Frame} {c : Admin} {vs : List Val}
      {a : Nat} {fi : FuncInst H} {h : H} {F : FuncFX} (hc : c.IsCallRef)
      (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host h) (hfx : fx h = some F)
      (hn : vs.length = F.nparams) :
      StepFX P host fx ⟨s, K, f, cvals vs ++ [.core (.ref (.func a)), .core c]⟩
        ⟨s, K, f, [.frame F.nresults (Frame.forCall F.module vs F.locals)
          [.label F.nresults [] (F.body.map InstrFX.toAdmin)]]⟩
  -- Continuations
  | contNew {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat} {fi : FuncInst H}
      {ct : TypeIdx} (hf : s.funcs[a]? = some fi) :
      StepFX P host fx ⟨s, K, f, [.core (.ref (.func a)), .fx (.contNew ct)]⟩
        ⟨s, K ++ [some ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType fi.type)]⟩], f,
          [.contRef K.length]⟩
  | contNewNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {ct : TypeIdx} :
      StepFX P host fx ⟨s, K, f, [.core (.ref .null), .fx (.contNew ct)]⟩
        ⟨s, K, f, [.core .trap]⟩
  | contBind {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val} {k : Nat}
      {C : ContFX} {ct ct' : TypeIdx} (hk : K[k]? = some (some C)) :
      StepFX P host fx ⟨s, K, f, cvals vs ++ [.contRef k, .fx (.contBind ct ct')]⟩
        ⟨s, K.set k none ++ [some ⟨fun c => C.plug (cvals vs ++ c)⟩], f, [.contRef K.length]⟩
  | contBindNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val}
      {ct ct' : TypeIdx} :
      StepFX P host fx ⟨s, K, f, cvals vs ++ [.core (.ref .null), .fx (.contBind ct ct')]⟩
        ⟨s, K, f, [.core .trap]⟩
  | contBindUsed {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val} {k : Nat}
      {ct ct' : TypeIdx} (hk : K[k]? = some none) :
      StepFX P host fx ⟨s, K, f, cvals vs ++ [.contRef k, .fx (.contBind ct ct')]⟩
        ⟨s, K, f, [.core .trap]⟩
  | resume {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val} {k : Nat}
      {C : ContFX} {ct : TypeIdx} {hs : List OnClause} {hs' : List HClause}
      (hk : K[k]? = some (some C)) (hr : hs.mapM (resolve s f) = some hs') :
      StepFX P host fx ⟨s, K, f, cvals vs ++ [.contRef k, .fx (.resume ct hs)]⟩
        ⟨s, K.set k none, f, [.handler hs' (C.plug (cvals vs))]⟩
  | resumeNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val}
      {ct : TypeIdx} {hs : List OnClause} :
      StepFX P host fx ⟨s, K, f, cvals vs ++ [.core (.ref .null), .fx (.resume ct hs)]⟩
        ⟨s, K, f, [.core .trap]⟩
  | resumeUsed {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val} {k : Nat}
      {ct : TypeIdx} {hs : List OnClause} (hk : K[k]? = some none) :
      StepFX P host fx ⟨s, K, f, cvals vs ++ [.contRef k, .fx (.resume ct hs)]⟩
        ⟨s, K, f, [.core .trap]⟩
  /-- `resume_throw`: the exception (tag resolved at the `resume_throw`, payload `vs`) is raised
  at the hole of the continuation. -/
  | resumeThrow {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val} {k : Nat}
      {C : ContFX} {ct : TypeIdx} {x : TagIdx} {hs : List OnClause} {hs' : List HClause}
      {ta : Nat} {ti : TagInst} (hk : K[k]? = some (some C)) (ht : s.tag? f x = some (ta, ti))
      (hr : hs.mapM (resolve s f) = some hs') :
      StepFX P host fx ⟨s, K, f, cvals vs ++ [.contRef k, .fx (.resumeThrow ct x hs)]⟩
        ⟨s.addExn ⟨ta, vs⟩, K.set k none, f, [.handler hs' (C.plug (cthrowing s.exns.length))]⟩
  | resumeThrowNull {s : Store H} {K : List (Option ContFX)} {f : Frame} {vs : List Val}
      {ct : TypeIdx} {x : TagIdx} {hs : List OnClause} :
      StepFX P host fx ⟨s, K, f, cvals vs ++ [.core (.ref .null), .fx (.resumeThrow ct x hs)]⟩
        ⟨s, K, f, [.core .trap]⟩
  /-- `suspend x` under a handler with clause `(on x l)` and no inner handler for `x`. -/
  | suspend {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {E : Ctx} {vs : List Val} {x : TagIdx} {ta : Nat} {ti : TagInst} {l : LabelIdx}
      (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
      (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
      StepFX P host fx ⟨s, K, f, [.handler hs (E.plug (cvals vs ++ [.fx (.suspend x)]))]⟩
        ⟨s, K ++ [some ⟨E.plug⟩], f, cvals vs ++ [.contRef K.length, .core (.plain (.br l))]⟩
  /-- `switch ct x` under a handler with clause `(on x switch)`: the target continuation runs
  under the same handler, with the current context as its last argument. -/
  | switch {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
      {E : Ctx} {vs : List Val} {k : Nat} {C : ContFX} {ct : TypeIdx} {x : TagIdx} {ta : Nat}
      {ti : TagInst} (hk : K[k]? = some (some C))
      (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
      (hc : hs.find? (fun c => c.tag == ta) = some (.onSwitch ta)) :
      StepFX P host fx
        ⟨s, K, f, [.handler hs (E.plug (cvals vs ++ [.contRef k, .fx (.switch ct x)]))]⟩
        ⟨s, K.set k none ++ [some ⟨E.plug⟩], f,
          [.handler hs (C.plug (cvals vs ++ [.contRef K.length]))]⟩

/-- Runs of CoreFX. -/
abbrev StepsFX (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX) :=
  Relation.ReflTransGen (StepFX P host fx)

/-- The observable behaviours of a CoreFX configuration: the results of finite runs, and
divergence. -/
def behavioursFX (P : Profile) (host : HostSemantics H) (fx : H → Option FuncFX)
    (c : ConfigFX H) : Set (Behaviour Val) :=
  {b | ∃ (d : ConfigFX H) (r : Result), StepsFX P host fx c d ∧
      d.code = r.toAdmin.map .core ∧ b = r.toBehaviour} ∪
  {b | b = .diverges ∧ Silmaril.InfiniteTrace (StepFX P host fx) c}

/-- No host function of the store is an FX function. -/
def NoFX (fx : H → Option FuncFX) (s : Store H) : Prop :=
  ∀ (a : Nat) (fi : FuncInst H) (h : H), s.funcs[a]? = some fi → fi.code = .host h →
    fx h = none

end Silmaril.Wasm.Models.FX
