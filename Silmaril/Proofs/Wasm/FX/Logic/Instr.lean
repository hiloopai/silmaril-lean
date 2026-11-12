module

public import Silmaril.Proofs.Wasm.FX.Logic.Rules
public import Silmaril.Wasm.Logic.Core.Thms

/-!
# Instruction rules of the WasmFX calculus, Core code, and adequacy

* stack switching, at the head of `us; · ; rest`: `wp_contNew`, `wp_contBind`, `wp_resume`,
  `wp_resumeThrow`, `wp_dropCont`, and the trapping forms on a null or consumed continuation
  (`wp_contNew_null`, `wp_contBind_null`, `wp_contBind_used`, `wp_resume_null`,
  `wp_resume_used`, `wp_resumeThrow_null`); `suspend` and `switch` are final forms
  (`wp_suspend`, `wp_switch`), handled by `wp_handler`;
* the **effect-handler rules**: `wp_resume_handle` (resume a continuation under its handler,
  with the handler's postcondition) and `wp_resumeThrow_handle`;
* FX functions: `wp_invoke`, and `wp_call_fx` (enter the body with the label and frame
  postconditions);
* structured control: `wp_block`, `wp_block_enter`, `wp_loop`, `wp_if_true`, `wp_if_false`;
* Core code: `wp_coreStep` (one Core step), `wp_refFunc`, **`wp_exec`** (straight-line Core
  code evaluated by `Silmaril.Wasm.Logic.Core.exec`, the interpreter behind `wasm_step`), and
  **`wp_coreWP`** (a Core `Silmaril.Wasm.Logic.Core.WP` proof, with the host `blockFX host fx`, is
  an FX one);
* adequacy: **`WP.behaviour`**: a proved `WP` with a result postcondition gives that result's
  behaviour in `behavioursFX'`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Logic

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}
  {s : Store H} {K : Conts} {f : Frame} {Q : PostFX H}

/-! ## Stack switching -/

theorem wp_contNew (us : List FVal) (rest : List AdminFX) {a : Nat} {fi : FuncInst H}
    {ct : TypeIdx} (hf : s.funcs[a]? = some fi)
    (h : WP P host fx s (K ++ [some (newCont a fi)]) f (fvals us ++ [.contRef K.length] ++ rest)
      Q) :
    WP P host fx s K f (fvals us ++ [.core (.ref (.func a)), .fx (.contNew ct)] ++ rest) Q :=
  wp_head us rest (StepFX'.contNew hf) h

theorem wp_contNew_null (us : List FVal) (rest : List AdminFX) {ct : TypeIdx}
    (h : WP P host fx s K f (fvals us ++ [.core .trap] ++ rest) Q) :
    WP P host fx s K f (fvals us ++ [.core (.ref .null), .fx (.contNew ct)] ++ rest) Q :=
  wp_head us rest StepFX'.contNewNull h

theorem wp_contBind (us : List FVal) (rest : List AdminFX) {vs : List FVal} {k : Nat}
    {C : ContFX} {ct ct' : TypeIdx} (hk : K[k]? = some (some C))
    (h : WP P host fx s (K.set k none ++ [some (bindCont C vs)]) f
      (fvals us ++ [.contRef K.length] ++ rest) Q) :
    WP P host fx s K f
      (fvals us ++ (fvals vs ++ [.contRef k, .fx (.contBind ct ct')]) ++ rest) Q :=
  wp_head us rest (StepFX'.contBind hk) h

theorem wp_contBind_null (us : List FVal) (rest : List AdminFX) {vs : List FVal}
    {ct ct' : TypeIdx} (h : WP P host fx s K f (fvals us ++ [.core .trap] ++ rest) Q) :
    WP P host fx s K f
      (fvals us ++ (fvals vs ++ [.core (.ref .null), .fx (.contBind ct ct')]) ++ rest) Q :=
  wp_head us rest StepFX'.contBindNull h

theorem wp_contBind_used (us : List FVal) (rest : List AdminFX) {vs : List FVal} {k : Nat}
    {ct ct' : TypeIdx} (hk : K[k]? = some none)
    (h : WP P host fx s K f (fvals us ++ [.core .trap] ++ rest) Q) :
    WP P host fx s K f
      (fvals us ++ (fvals vs ++ [.contRef k, .fx (.contBind ct ct')]) ++ rest) Q :=
  wp_head us rest (StepFX'.contBindUsed hk) h

theorem wp_resume (us : List FVal) (rest : List AdminFX) {vs : List FVal} {k : Nat}
    {C : ContFX} {ct : TypeIdx} {hs : List OnClause} {hs' : List HClause}
    (hk : K[k]? = some (some C)) (hr : hs.mapM (resolve s f) = some hs')
    (h : WP P host fx s (K.set k none) f (fvals us ++ [.handler hs' (C.plug (fvals vs))] ++ rest)
      Q) :
    WP P host fx s K f (fvals us ++ (fvals vs ++ [.contRef k, .fx (.resume ct hs)]) ++ rest) Q :=
  wp_head us rest (StepFX'.resume hk hr) h

/-- **The effect-handler rule for `resume`.** Resuming `k` runs its continuation on the
operands under the resolved handler; the continuation's code is verified with the handler's
postcondition (`handlerPost`), which says what each caught effect continues with. The slot `k`
is consumed (one-shot). -/
theorem wp_resume_handle {vs : List FVal} {k : Nat} {C : ContFX} {ct : TypeIdx}
    {hs : List OnClause} {hs' : List HClause} (hk : K[k]? = some (some C))
    (hr : hs.mapM (resolve s f) = some hs')
    (h : WP P host fx s (K.set k none) f (C.plug (fvals vs)) (handlerPost P host fx hs' Q)) :
    WP P host fx s K f (fvals vs ++ [.contRef k, .fx (.resume ct hs)]) Q :=
  WP.step (StepFX'.resume hk hr) (wp_handler h)

theorem wp_resume_null (us : List FVal) (rest : List AdminFX) {vs : List FVal} {ct : TypeIdx}
    {hs : List OnClause} (h : WP P host fx s K f (fvals us ++ [.core .trap] ++ rest) Q) :
    WP P host fx s K f
      (fvals us ++ (fvals vs ++ [.core (.ref .null), .fx (.resume ct hs)]) ++ rest) Q :=
  wp_head us rest StepFX'.resumeNull h

/-- Resuming a consumed continuation traps (one-shot). -/
theorem wp_resume_used (us : List FVal) (rest : List AdminFX) {vs : List FVal} {k : Nat}
    {ct : TypeIdx} {hs : List OnClause} (hk : K[k]? = some none)
    (h : WP P host fx s K f (fvals us ++ [.core .trap] ++ rest) Q) :
    WP P host fx s K f (fvals us ++ (fvals vs ++ [.contRef k, .fx (.resume ct hs)]) ++ rest) Q :=
  wp_head us rest (StepFX'.resumeUsed hk) h

theorem wp_resumeThrow (us : List FVal) (rest : List AdminFX) {vs : List Val} {k : Nat}
    {C : ContFX} {ct : TypeIdx} {x : TagIdx} {hs : List OnClause} {hs' : List HClause}
    {ta : Nat} {ti : TagInst} (hk : K[k]? = some (some C)) (ht : s.tag? f x = some (ta, ti))
    (hr : hs.mapM (resolve s f) = some hs')
    (h : WP P host fx (s.addExn ⟨ta, vs⟩) (K.set k none) f
      (fvals us ++ [.handler hs' (C.plug (cthrowing s.exns.length))] ++ rest) Q) :
    WP P host fx s K f
      (fvals us ++ (cvals vs ++ [.contRef k, .fx (.resumeThrow ct x hs)]) ++ rest) Q :=
  wp_head us rest (StepFX'.resumeThrow hk ht hr) h

/-- **The effect-handler rule for `resume_throw`**: the exception is raised at the
continuation's hole, under the handler. -/
theorem wp_resumeThrow_handle {vs : List Val} {k : Nat} {C : ContFX} {ct : TypeIdx}
    {x : TagIdx} {hs : List OnClause} {hs' : List HClause} {ta : Nat} {ti : TagInst}
    (hk : K[k]? = some (some C)) (ht : s.tag? f x = some (ta, ti))
    (hr : hs.mapM (resolve s f) = some hs')
    (h : WP P host fx (s.addExn ⟨ta, vs⟩) (K.set k none) f (C.plug (cthrowing s.exns.length))
      (handlerPost P host fx hs' Q)) :
    WP P host fx s K f (cvals vs ++ [.contRef k, .fx (.resumeThrow ct x hs)]) Q :=
  WP.step (StepFX'.resumeThrow hk ht hr) (wp_handler h)

theorem wp_resumeThrow_null (us : List FVal) (rest : List AdminFX) {vs : List Val}
    {ct : TypeIdx} {x : TagIdx} {hs : List OnClause}
    (h : WP P host fx s K f (fvals us ++ [.core .trap] ++ rest) Q) :
    WP P host fx s K f
      (fvals us ++ (cvals vs ++ [.core (.ref .null), .fx (.resumeThrow ct x hs)]) ++ rest) Q :=
  wp_head us rest StepFX'.resumeThrowNull h

theorem wp_dropCont (us : List FVal) (rest : List AdminFX) {k : Nat}
    (h : WP P host fx s K f (fvals us ++ [] ++ rest) Q) :
    WP P host fx s K f (fvals us ++ [.contRef k, .core (.plain .drop)] ++ rest) Q :=
  wp_head us rest StepFX'.dropCont h

/-! ## FX functions -/

theorem wp_invoke (us : List FVal) (rest : List AdminFX) {c : Admin} {vs : List Val} {a : Nat}
    {fi : FuncInst H} {h : H} {F : FuncFX} (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .host h) (hfx : fx h = some F) (hn : vs.length = F.nparams)
    (hw : WP P host fx s K f (fvals us ++ [.frame F.nresults (Frame.forCall F.module vs F.locals)
      [.label F.nresults [] (F.body.map InstrFX.toAdmin)]] ++ rest) Q) :
    WP P host fx s K f (fvals us ++ (cvals vs ++ [.core (.ref (.func a)), .core c]) ++ rest) Q :=
  wp_head us rest (StepFX'.invoke hc hf hcode hfx hn) hw

/-- **The call rule for FX functions**: the body runs in a fresh frame, under its label. -/
theorem wp_call_fx {c : Admin} {vs : List Val} {a : Nat} {fi : FuncInst H} {h : H} {F : FuncFX}
    (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host h)
    (hfx : fx h = some F) (hn : vs.length = F.nparams)
    (hw : WP P host fx s K (Frame.forCall F.module vs F.locals) (F.body.map InstrFX.toAdmin)
      (labelPost P host fx F.nresults [] (framePost F.nresults f Q))) :
    WP P host fx s K f (cvals vs ++ [.core (.ref (.func a)), .core c]) Q :=
  WP.step (StepFX'.invoke hc hf hcode hfx hn) (wp_frame (wp_label hw))

/-! ## Structured control -/

theorem wp_block (us : List FVal) (rest : List AdminFX) {bt : BlockType} {body : List InstrFX}
    {vs : List FVal} {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
    (hm : vs.length = t₁.length)
    (h : WP P host fx s K f
      (fvals us ++ [.label t₂.length [] (fvals vs ++ body.map InstrFX.toAdmin)] ++ rest) Q) :
    WP P host fx s K f (fvals us ++ (fvals vs ++ [.block bt body]) ++ rest) Q :=
  wp_head us rest (StepFX'.block hbt hm) h

/-- Enter a block and verify its body with the label's postcondition. -/
theorem wp_block_enter {bt : BlockType} {body : List InstrFX} {vs : List FVal}
    {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
    (hm : vs.length = t₁.length)
    (h : WP P host fx s K f (fvals vs ++ body.map InstrFX.toAdmin)
      (labelPost P host fx t₂.length [] Q)) :
    WP P host fx s K f (fvals vs ++ [.block bt body]) Q :=
  WP.step (StepFX'.block hbt hm) (wp_label h)

theorem wp_loop (us : List FVal) (rest : List AdminFX) {bt : BlockType} {body : List InstrFX}
    {vs : List FVal} {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
    (hm : vs.length = t₁.length)
    (h : WP P host fx s K f (fvals us ++
      [.label t₁.length [.loop bt body] (fvals vs ++ body.map InstrFX.toAdmin)] ++ rest) Q) :
    WP P host fx s K f (fvals us ++ (fvals vs ++ [.loop bt body]) ++ rest) Q :=
  wp_head us rest (StepFX'.loop hbt hm) h

theorem wp_if_true (us : List FVal) (rest : List AdminFX) {c : BitVec 32} {bt : BlockType}
    {b₁ b₂ : List InstrFX} (hc : c ≠ 0)
    (h : WP P host fx s K f (fvals us ++ [.block bt b₁] ++ rest) Q) :
    WP P host fx s K f (fvals us ++ [.core (constI32 c), .if_ bt b₁ b₂] ++ rest) Q :=
  wp_head us rest (StepFX'.ifTrue hc) h

theorem wp_if_false (us : List FVal) (rest : List AdminFX) {bt : BlockType}
    {b₁ b₂ : List InstrFX} (h : WP P host fx s K f (fvals us ++ [.block bt b₂] ++ rest) Q) :
    WP P host fx s K f (fvals us ++ [.core (constI32 0), .if_ bt b₁ b₂] ++ rest) Q :=
  wp_head us rest StepFX'.ifFalse h

/-! ## Core code -/

/-- One Core step (FX function codes refused) at the head of `us; · ; rest`. -/
theorem wp_coreStep (us : List FVal) (rest : List AdminFX) {s' : Store H} {f' : Frame}
    {cs cs' : List Admin} (hs : Step P (blockFX host fx) ⟨s, f, cs⟩ ⟨s', f', cs'⟩)
    (h : WP P host fx s' K f' (fvals us ++ cs'.map .core ++ rest) Q) :
    WP P host fx s K f (fvals us ++ cs.map .core ++ rest) Q :=
  wp_head us rest (StepFX'.core hs) h

/-- `ref.func x` (a Core step). -/
theorem wp_refFunc (us : List FVal) (rest : List AdminFX) {x : FuncIdx} {a : Nat}
    (hx : f.module.funcs[x.toNat]? = some a)
    (h : WP P host fx s K f (fvals us ++ [.core (.ref (.func a))] ++ rest) Q) :
    WP P host fx s K f (fvals us ++ [.core (.plain (.refFunc x))] ++ rest) Q :=
  wp_coreStep (cs := [.plain (.refFunc x)]) (cs' := [.ref (.func a)]) us rest
    (Step.reference (.refFunc hx)) h

/-- **Straight-line Core code** on Core values `vs`, evaluated by the Core calculus's
interpreter `exec` (the evaluator behind `wasm_step`). -/
theorem wp_exec (us : List FVal) (rest : List AdminFX) {vs : List Val} {is : List Instr}
    (h : match Silmaril.Wasm.Logic.Core.exec s f vs.reverse is with
      | some (s', f', rs') =>
          WP P host fx s' K f' (fvals us ++ fvals (liftV rs'.reverse) ++ rest) Q
      | none => False) :
    WP P host fx s K f
      (fvals us ++ (fvals (liftV vs) ++ is.map fun i => .core (.plain i)) ++ rest) Q :=
  match he : Silmaril.Wasm.Logic.Core.exec s f vs.reverse is, h with
  | some (s', f', rs'), hw => by
    have run : Steps P (blockFX host fx) ⟨s, f, vals vs.reverse.reverse ++ expression is ++ []⟩
        ⟨s', f', vals rs'.reverse ++ []⟩ := Silmaril.Wasm.Logic.Core.exec_sound [] he
    have run' : StepsFX' P host fx
        ⟨s, K, f, fvals (liftV vs) ++ is.map fun i => .core (.plain i)⟩
        ⟨s', K, f', fvals (liftV rs'.reverse)⟩ := by
      simpa only [List.reverse_reverse, List.append_nil, List.map_append, ← fvals_lift,
        map_core_expression] using steps_core K run
    exact wp_heads us rest run' hw
  | none, hw => hw.elim

/-- A Core final form, read through `corePost`. -/
theorem core_ends : ∀ (o : Silmaril.Wasm.Logic.Core.Outcome) {c : List Admin}, o.Ends c →
    corePost K Q s f o → WP P host fx s K f (c.map .core) Q
  | .normal vs, _, he, hq => by
    rw [he, ← fvals_lift]
    exact wp_val hq
  | .br l vs, _, ⟨x, r, hx, he⟩, hq => by
    have e : (vals vs ++ .plain (.br x) :: r).map AdminFX.core =
        fvals (liftV vs) ++ .core (.plain (.br x)) :: r.map .core := by
      simp only [List.map_append, List.map_cons, fvals_lift]
    have hq' : Q s K f (.br x.toNat (liftV vs)) := by rw [hx]; exact hq
    rw [he, e]
    exact wp_br hq'
  | .ret vs, _, ⟨r, he⟩, hq => by
    have e : (vals vs ++ .plain .return_ :: r).map AdminFX.core =
        fvals (liftV vs) ++ .core (.plain .return_) :: r.map .core := by
      simp only [List.map_append, List.map_cons, fvals_lift]
    rw [he, e]
    exact wp_ret hq
  | .trap, _, he, hq => by
    rw [he]
    exact wp_trap hq
  | .throw a, _, he, hq => by
    rw [he]
    exact wp_throwing hq
  | .tail _ _ _, _, _, hq => hq.elim

/-- **Core proofs are FX proofs.** A proof in the Core calculus `Silmaril.Wasm.Logic.Core.WP`
(with the Core host `blockFX host fx`, so the tactics `wasm_step`, `wasm_block`, … apply) is a
proof in the FX calculus, with any continuation store. -/
theorem wp_coreWP {cs : List Admin}
    (h : Silmaril.Wasm.Logic.Core.WP P (blockFX host fx) s f cs (corePost K Q)) :
    WP P host fx s K f (cs.map .core) Q :=
  let ⟨_, _, _, o, hr, he, hq⟩ := h
  WP.steps (steps_core K hr) (core_ends o he hq)

/-! ## Adequacy -/

theorem ofResult_ends {r : Result} {c : List AdminFX} (h : (OutcomeFX.ofResult r).Ends c) :
    c = r.toAdmin.map .core :=
  match r, h with
  | .values vs, h => h.trans (fvals_lift vs)
  | .throw _, h => h
  | .trap, h => h

/-- **Adequacy.** A proved `WP` whose postcondition is the outcome of a result gives that
result's behaviour under `StepFX'`. -/
theorem WP.behaviour {code : List AdminFX} {r : Result}
    (h : WP P host fx s K f code fun _ _ _ o => o = .ofResult r) :
    r.toBehaviour ∈ behavioursFX' P host fx ⟨s, K, f, code⟩ :=
  let ⟨s', K', f', c', _, hr, he, hq⟩ := h
  Or.inl ⟨⟨s', K', f', c'⟩, r, hr, ofResult_ends (hq ▸ he), rfl⟩

end Silmaril.Wasm.FX.Logic
