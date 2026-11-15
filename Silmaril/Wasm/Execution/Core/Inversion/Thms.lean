module

public import Silmaril.Wasm.Execution.Core.Inversion.Defs
public import Silmaril.Wasm.Execution.Core.Sim.Context
public import Silmaril.Wasm.SingleThreaded.Determinism.Family
import Silmaril.Proofs.Wasm.Execution.Core.Inversion

@[expose] public section

/-! # Inversion of Core 3.0 steps

What a single `Step P host` (any profile, any host) can do from a given code. These are the
case analyses that simulation and adequacy proofs need about the actual Core 3.0 relation:

* **stuck codes**: `[TRAP]`, `(REF.EXN_ADDR a) THROW_REF`, `[BR l]`, `[RETURN]` do not step
  (they are results, or exits that only an enclosing context removes);
* **single instructions**: `unreachable` only traps; `block`/`loop` only enter their label
  (with no arguments, so the block type takes none); `call x` only resolves to `call_ref`; a
  `call_ref` of Wasm code only enters the callee's frame (after the values it does not take);
* **contexts**: a `LABEL`, `HANDLER` or `FRAME` configuration steps either inside, by the
  corresponding context rule, or by exactly one of the exit rules listed in
  `LabelExit`/`HandlerExit`/`FrameExit`. A frame's inner step does not see the outer frame,
  and its exits do not depend on it;
* **`loop (br 0)`**: it alternates between `loopBr0` and `labelBr0` only, diverges, and never
  reaches a result.

The `noHost` determinism toolkit (`SingleThreaded.Det`) gives some of these for the empty host;
these are stated for every host, since a host call can only fire on `val* (ref.func a)
call_ref` of host code.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
  {c : Config H}

/-! ## Stuck codes -/

theorem Step.trap_stuck : ¬ Step P host ⟨s, f, [.trap]⟩ c :=
  fun h => Proofs.Inversion.trap_stuck h rfl

theorem Step.throwing_stuck {a : Nat} : ¬ Step P host ⟨s, f, throwing a⟩ c :=
  fun h => Proofs.Inversion.throwing_stuck h rfl

theorem Step.br_stuck {l : LabelIdx} : ¬ Step P host ⟨s, f, [.plain (.br l)]⟩ c :=
  fun h => Proofs.Inversion.br_stuck h rfl

theorem Step.return_stuck : ¬ Step P host ⟨s, f, [.plain .return_]⟩ c :=
  fun h => Proofs.Inversion.return_stuck h rfl

/-- A result does not step. -/
theorem Step.result_stuck (r : Result) : ¬ Step P host ⟨s, f, r.toAdmin⟩ c := by
  cases r <;> first | exact Step.not_vals | exact Step.throwing_stuck | exact Step.trap_stuck

/-! ## Single instructions -/

theorem Step.unreachable_inv (h : Step P host ⟨s, f, [.plain .unreachable]⟩ c) :
    c = ⟨s, f, [.trap]⟩ :=
  Proofs.Inversion.unreachable_inv h rfl

theorem Step.block_inv {bt : BlockType} {body : List Instr}
    (h : Step P host ⟨s, f, [.plain (.block bt body)]⟩ c) :
    ∃ t₂, f.module.blockType? bt = some ([], t₂) ∧
      c = ⟨s, f, [.label t₂.length [] (expression body)]⟩ :=
  Proofs.Inversion.block_inv h rfl

theorem Step.loop_inv {bt : BlockType} {body : List Instr}
    (h : Step P host ⟨s, f, [.plain (.loop bt body)]⟩ c) :
    ∃ t₂, f.module.blockType? bt = some ([], t₂) ∧
      c = ⟨s, f, [.label 0 [.loop bt body] (expression body)]⟩ :=
  Proofs.Inversion.loop_inv h rfl

theorem Step.call_inv {x : FuncIdx} (h : Step P host ⟨s, f, [.plain (.call x)]⟩ c) :
    ∃ a fi, f.module.funcs[x.toNat]? = some a ∧ s.funcs[a]? = some fi ∧
      c = ⟨s, f, [.ref (.func a), .callRefType fi.type]⟩ :=
  Proofs.Inversion.call_inv h rfl

/-- `call x` only resolves to `call_ref` of the function it names. -/
theorem Step.call_inv_of {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (h : Step P host ⟨s, f, [.plain (.call x)]⟩ c) :
    c = ⟨s, f, [.ref (.func a), .callRefType fi.type]⟩ :=
  Proofs.Inversion.call_inv_of hx hf h

/-- A `call_ref` of Wasm code only enters the callee's frame: `call_ref-func` on the top
`ps.length` values, under the values below them (`ctxt-instrs`). -/
theorem Step.callRef_wasm_inv {vs : List Val} {a : Nat} {r : Admin} {fi : FuncInst H}
    {code : Func} (hr : r.IsCallRef) (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm code)
    (h : Step P host ⟨s, f, vals vs ++ [.ref (.func a), r]⟩ c) :
    ∃ vs₁ vs₂ ps rs, vs = vs₁ ++ vs₂ ∧ Expand fi.type (.func ps rs) ∧ vs₂.length = ps.length ∧
      c = ⟨s, f, vals vs₁ ++ [.frame rs.length (Frame.forCall fi.module vs₂ code.locals)
        [.label rs.length [] (expression code.body)]]⟩ :=
  Proofs.Inversion.callRef_wasm_inv h hr hf hcode rfl

/-- A `call_ref` of a host function only calls the host (`call_ref-hostfunc-res`, or the
diverging stutter `call_ref-hostfunc-div`) on the top `ps.length` values, under the values below
them (`ctxt-instrs`). -/
theorem Step.callRef_host_inv {vs : List Val} {a : Nat} {r : Admin} {fi : FuncInst H} {hh : H}
    (hr : r.IsCallRef) (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (h : Step P host ⟨s, f, vals vs ++ [.ref (.func a), r]⟩ c) :
    ∃ vs₁ vs₂ ps rs, vs = vs₁ ++ vs₂ ∧ Expand fi.type (.func ps rs) ∧ vs₂.length = ps.length ∧
      ((∃ s' res, host hh s vs₂ (.returned s' res) ∧ c = ⟨s', f, vals vs₁ ++ res.toAdmin⟩) ∨
        (host hh s vs₂ .diverged ∧ c = ⟨s, f, vals vs ++ [.ref (.func a), r]⟩)) :=
  Proofs.Inversion.callRef_host_inv h hr hf hcode rfl

/-- With exactly the callee's arguments, the step is the `call_ref-func` rule. -/
theorem Step.callRef_wasm_inv_exact {vs : List Val} {a : Nat} {r : Admin} {fi : FuncInst H}
    {code : Func} {ps rs : Ty (.list .val)} (hr : r.IsCallRef) (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) (he : Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) (h : Step P host ⟨s, f, vals vs ++ [.ref (.func a), r]⟩ c) :
    c = ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
      [.label rs.length [] (expression code.body)]]⟩ :=
  Proofs.Inversion.callRef_wasm_inv_exact hr hf hcode he hn h

/-! ## Structured instructions under values

Under a value prefix the rule may take only the top values (`ctxt-instrs`): the prefix splits
as `ws ++ vs`, the instruction consumes `vs`, and `ws` stays in front. Store and frame are
unchanged.
-/

theorem Step.block_vals_inv {us : List Val} {bt : BlockType} {body : List Instr}
    (h : Step P host ⟨s, f, vals us ++ [.plain (.block bt body)]⟩ c) :
    ∃ ws vs t₁ t₂, us = ws ++ vs ∧ f.module.blockType? bt = some (t₁, t₂) ∧
      vs.length = t₁.length ∧
      c = ⟨s, f, vals ws ++ [.label t₂.length [] (vals vs ++ expression body)]⟩ :=
  Proofs.Inversion.block_vals_inv h rfl

/-- `call x` under values resolves its callee (`call`, under `ctxt-instrs`), leaving the values. -/
theorem Step.call_vals_inv {us : List Val} {x : FuncIdx}
    (h : Step P host ⟨s, f, vals us ++ [.plain (.call x)]⟩ c) :
    ∃ a fi, f.module.funcs[x.toNat]? = some a ∧ s.funcs[a]? = some fi ∧
      c = ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩ :=
  Proofs.Inversion.call_vals_inv h rfl

theorem Step.loop_vals_inv {us : List Val} {bt : BlockType} {body : List Instr}
    (h : Step P host ⟨s, f, vals us ++ [.plain (.loop bt body)]⟩ c) :
    ∃ ws vs t₁ t₂, us = ws ++ vs ∧ f.module.blockType? bt = some (t₁, t₂) ∧
      vs.length = t₁.length ∧
      c = ⟨s, f, vals ws ++ [.label t₁.length [.loop bt body] (vals vs ++ expression body)]⟩ :=
  Proofs.Inversion.loop_vals_inv h rfl

theorem Step.tryTable_vals_inv {us : List Val} {bt : BlockType} {cs : List Catch}
    {body : List Instr} (h : Step P host ⟨s, f, vals us ++ [.plain (.tryTable bt cs body)]⟩ c) :
    ∃ ws vs t₁ t₂, us = ws ++ vs ∧ f.module.blockType? bt = some (t₁, t₂) ∧
      vs.length = t₁.length ∧
      c = ⟨s, f, vals ws ++
        [.handler t₂.length cs [.label t₂.length [] (vals vs ++ expression body)]]⟩ :=
  Proofs.Inversion.tryTable_vals_inv h rfl

/-- `if` pops its `i32` condition and becomes a `block` of the chosen arm. -/
theorem Step.if_vals_inv {us : List Val} {bt : BlockType} {b₁ b₂ : List Instr}
    (h : Step P host ⟨s, f, vals us ++ [.plain (.if_ bt b₁ b₂)]⟩ c) :
    ∃ ws k, us = ws ++ [.i32 k] ∧
      c = ⟨s, f, vals ws ++ [.plain (.block bt (if k = 0 then b₂ else b₁))]⟩ :=
  Proofs.Inversion.if_vals_inv h rfl

/-- `br l` under values does not step: only an enclosing label or handler removes it. -/
theorem Step.br_vals_stuck {us : List Val} {l : LabelIdx} :
    ¬ Step P host ⟨s, f, vals us ++ [.plain (.br l)]⟩ c :=
  fun h => Proofs.Inversion.br_vals_stuck h rfl

/-- `return` under values does not step: only an enclosing label, handler or frame removes it. -/
theorem Step.return_vals_stuck {us : List Val} :
    ¬ Step P host ⟨s, f, vals us ++ [.plain .return_]⟩ c :=
  fun h => Proofs.Inversion.return_vals_stuck h rfl

/-- `br_if` pops its `i32` condition: it branches when it is nonzero and falls through
otherwise. -/
theorem Step.brIf_vals_inv {us : List Val} {l : LabelIdx}
    (h : Step P host ⟨s, f, vals us ++ [.plain (.brIf l)]⟩ c) :
    ∃ ws k, us = ws ++ [.i32 k] ∧
      c = ⟨s, f, vals ws ++ (if k = 0 then [] else [.plain (.br l)])⟩ :=
  Proofs.Inversion.brIf_vals_inv h rfl

/-- A trap under values only collapses (`trap-instrs`), keeping fewer values. -/
theorem Step.trap_vals_inv {us : List Val} (h : Step P host ⟨s, f, vals us ++ [.trap]⟩ c) :
    ∃ w, c = ⟨s, f, vals w ++ [.trap]⟩ ∧ w.length < us.length :=
  Proofs.Inversion.trap_vals_inv h rfl

/-- A non-control instruction under values steps by one of its family's rules, on its top
operands, under the values below them. -/
theorem Step.noncontrol_vals_inv {us : List Val} {i : Instr}
    (hk : SingleThreaded.Det.famOf (.plain i) ≠ .control)
    (h : Step P host ⟨s, f, vals us ++ [.plain i]⟩ c) :
    ∃ ws vs c₀, us = ws ++ vs ∧ FamStep P ⟨s, f, vals vs ++ [.plain i]⟩ c₀ ∧
      c = ⟨c₀.store, c₀.frame, vals ws ++ c₀.code⟩ :=
  Proofs.Inversion.noncontrol_vals_inv h hk rfl

/-- A data-dependent branch rule is a Core step. -/
theorem BrStep.step {us us' : List Val} {i : Instr} {X : List Admin} (h : BrStep s f us i us' X) :
    Step P host ⟨s, f, vals us ++ [.plain i]⟩ ⟨s, f, vals us' ++ X⟩ :=
  Proofs.Inversion.brStep_step h

/-- A data-dependent branch under values steps by exactly one of its rules (`BrStep`), on its
top operands. -/
theorem Step.brData_vals_inv {vs : List Val} {i : Instr} (hb : i.IsBrData)
    (h : Step P host ⟨s, f, vals vs ++ [.plain i]⟩ c) :
    ∃ ws us us' X, vs = ws ++ us ∧ BrStep s f us i us' X ∧
      c = ⟨s, f, vals ws ++ (vals us' ++ X)⟩ :=
  Proofs.Inversion.brData_vals_inv h hb rfl

/-- `throw x` under values allocates the exception from its top operands and throws it. -/
theorem Step.throw_vals_inv {us : List Val} {x : TagIdx}
    (h : Step P host ⟨s, f, vals us ++ [.plain (.throw x)]⟩ c) :
    ∃ ws vs ta ti ts, us = ws ++ vs ∧ s.tag? f x = some (ta, ti) ∧
      Expand ti.type (.func ts .nil) ∧ vs.length = ts.length ∧
      c = ⟨s.addExn ⟨ta, vs⟩, f, vals ws ++ throwing s.exns.length⟩ :=
  Proofs.Inversion.throw_vals_inv h rfl

/-- `throw_ref` under values: a null reference traps; an exception reference is thrown after
dropping some values below it. -/
theorem Step.throwRef_vals_inv {us : List Val}
    (h : Step P host ⟨s, f, vals us ++ [.plain .throwRef]⟩ c) :
    (∃ ws, us = ws ++ [.ref .null] ∧ c = ⟨s, f, vals ws ++ [.trap]⟩) ∨
      ∃ ws ws' a, us = ws ++ ws' ++ [.ref (.exn a)] ∧ ws' ≠ [] ∧
        c = ⟨s, f, vals ws ++ throwing a⟩ :=
  Proofs.Inversion.throwRef_vals_inv h rfl

/-! ## Contexts -/

/-- A label steps inside (`ctxt-label`) or by an exit rule. -/
theorem Step.label_inv {n : Nat} {cont : List Instr} {is : List Admin}
    (h : Step P host ⟨s, f, [.label n cont is]⟩ c) :
    (∃ s' f' is', Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩ ∧ c = ⟨s', f', [.label n cont is']⟩) ∨
      ∃ out, LabelExit n cont is out ∧ c = ⟨s, f, out⟩ :=
  Proofs.Inversion.label_inv h rfl

/-- A handler steps inside (`ctxt-handler`) or by an exit rule (including catching). -/
theorem Step.handler_inv {n : Nat} {cs : List Catch} {is : List Admin}
    (h : Step P host ⟨s, f, [.handler n cs is]⟩ c) :
    (∃ s' f' is', Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩ ∧ c = ⟨s', f', [.handler n cs is']⟩) ∨
      ∃ out, HandlerExit s f n cs is out ∧ c = ⟨s, f, out⟩ :=
  Proofs.Inversion.handler_inv h rfl

/-- A frame steps inside, in its own frame (`ctxt-frame`), or by an exit rule (values,
`return`, trap, exception, tail call). Neither alternative depends on the outer frame `f`. -/
theorem Step.frame_inv {n : Nat} {fi : Frame} {is : List Admin}
    (h : Step P host ⟨s, f, [.frame n fi is]⟩ c) :
    (∃ s' fi' is', Step P host ⟨s, fi, is⟩ ⟨s', fi', is'⟩ ∧ c = ⟨s', f, [.frame n fi' is']⟩) ∨
      ∃ out, FrameExit s fi n is out ∧ c = ⟨s, f, out⟩ :=
  Proofs.Inversion.frame_inv h rfl

/-- A `LABEL`, `HANDLER` or `FRAME` in the middle of a sequence steps as itself, in place. -/
theorem Step.ctx_in_seq {vs : List Val} {X : Admin} {rest : List Admin} (hX : X.IsCtx)
    (h : Step P host ⟨s, f, vals vs ++ X :: rest⟩ c) :
    ∃ c₀ : Config H, Step P host ⟨s, f, [X]⟩ c₀ ∧
      c = ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩ :=
  Proofs.Inversion.ctx_in_seq hX h

/-- A label around values only leaves with them (`label-vals`). -/
theorem labelExit_of_vals {n : Nat} {cont : List Instr} {ws : List Val} {out : List Admin}
    (h : LabelExit n cont (vals ws) out) : out = vals ws :=
  Proofs.Inversion.labelExit_vals h

/-- `LABEL_n{cont} (br 0)` only branches: `n = 0` and the continuation runs. -/
theorem Step.label_br_zero_inv {n : Nat} {cont : List Instr} {l : LabelIdx} (hl : l.toNat = 0)
    (h : Step P host ⟨s, f, [.label n cont [.plain (.br l)]]⟩ c) :
    n = 0 ∧ c = ⟨s, f, expression cont⟩ :=
  Proofs.Inversion.label_br_zero_inv h hl rfl

/-! ## `loop (br 0)` -/

theorem Step.loopBr0_inv {bt : BlockType} (h : Step P host (loopBr0 s f bt) c) :
    c = labelBr0 s f bt :=
  Proofs.Inversion.loopBr0_inv h

theorem Step.labelBr0_inv {bt : BlockType} (h : Step P host (labelBr0 s f bt) c) :
    c = loopBr0 s f bt :=
  Proofs.Inversion.labelBr0_inv h

theorem Step.loopBr0_step {bt : BlockType} {t₂ : List CValType}
    (hbt : f.module.blockType? bt = some ([], t₂)) :
    Step P host (loopBr0 s f bt) (labelBr0 s f bt) :=
  Proofs.Inversion.loopBr0_step hbt

theorem Step.labelBr0_step {bt : BlockType} : Step P host (labelBr0 s f bt) (loopBr0 s f bt) :=
  Proofs.Inversion.labelBr0_step

/-- Every configuration reachable from `loop bt (br 0)` is one of its two. -/
theorem loopBr0_reach {bt : BlockType} (h : Steps P host (loopBr0 s f bt) c) :
    c = loopBr0 s f bt ∨ c = labelBr0 s f bt :=
  Proofs.Inversion.loopBr0_reach h

theorem loopBr0_diverges {bt : BlockType} {t₂ : List CValType}
    (hbt : f.module.blockType? bt = some ([], t₂)) : Diverges P host (loopBr0 s f bt) :=
  Proofs.Inversion.loopBr0_diverges hbt

/-- `loop bt (br 0)` never reaches a result (values, trap or exception). -/
theorem loopBr0_not_terminal {bt : BlockType} (h : Steps P host (loopBr0 s f bt) c) :
    ¬ c.Terminal :=
  Proofs.Inversion.loopBr0_not_terminal h

end Silmaril.Wasm.Execution.Core
