module

public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Games.Abstract.HostRunInf.Defs
public import Silmaril.Wasm.Abstract.HostClosing.Defs
public import Silmaril.Wasm.Abstract.DivO.Defs
public import Silmaril.Games.Abstract.ModuleDLog.Defs

/-!
# Productive runs of invocations: definitions

The infinite counterpart of `Silmaril.Wasm.Abstract.HostClosing`. `wasmEvFun` and `wasmEvPend`
observe finished behaviours and pending calls; neither can show a productive run (infinitely
many answered host calls). `wasmEvInf P s (a, vs)` is the set of productive runs of an
invocation, host-independently: Core runs under the universal host `anyHost` cut at their host
events (`CoreInf`). Each stream is witnessed by one coherent run, and its finite prefixes are
the actual event logs of that run (`coreInf_prefix`).

**A finite host-event log, then host-free divergence**, natively and host-independently:

* `quietCall`: the oracle answering a call by a behaviour of the closure `Shape.close wasmHOpen`
  with an **empty import log**, read back as a body flow through `exitFlow`/`endOfFlow` as
  `wasmHOpen` does. A host function always logs its import call, so only Wasm callees that make
  no host call (directly or deeper) are answered;
* `LogDiv s f stk es l`: the trees perform the logged open calls `l` (an `EvalL` prefix; the
  constructors are those of `ReachL`) and then diverge within the function, every further call
  answered by `quietCall` (`LocalDivO quietCall`);
* `LogDivOut Q s f stk es cs`: the trees diverge after a prefix resolving to `cs`, within the
  function (`LogDiv`) or in a reached callee whose divergence is given by `Q`;
* `LDLw z u`: the body of the Wasm function called by `z` does so, `u` its log as calls of
  `wasmHOpen`;
* `wasmEvFunD := Shape.closeDLog wasmHOpen LDLw`: `wasmEvFun` with divergence after descent
  paths and infinite descent chains (`Shape.closeD`) and after logged local divergence.

No host semantics occurs in these definitions.

Theorems in `Silmaril.Wasm.Abstract.HostClosingInf.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The universal host: every answer and divergence is allowed. -/
def anyHost : HostSemantics H := fun _ _ _ _ => True

/-- **The productive runs of an invocation**, host-independently: Core runs under the
universal host cut at their host events, one coherent run per stream. -/
def wasmEvInf (P : Numerics.Profile) : PInf (wasmHostSig H) (Store H) (Nat × List Val) :=
  fun s p => {ω | CoreInf P anyHost (invoke s p.1 p.2) ω}

/-! ## A finite host-event log, then host-free divergence -/

open Silmaril.Wasm.Binaryen

/-- **Host-free callees**: a call answered by a behaviour of the closure with an empty import
log, its body flow read through `exitFlow` and `endOfFlow` as in `wasmHOpen`. -/
def quietCall : CallRel H := fun s a us out =>
  ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (fl : Flow),
    s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
    exitFlow rs.length out.2 = some fl ∧ ([], endOfFlow fl out.1) ∈ Shape.close wasmHOpen a s us

/-- **The trees perform the logged calls `l`, then diverge within the function**, every later
call answered by a host-free callee (`quietCall`). The prefix is an `EvalL` prefix; the
constructors are those of `ReachL`, with local divergence in place of the reached call. -/
inductive LogDiv : Store H → Frame → List Val → List BExpr → List (OCall H) → Prop where
  | div {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} :
      LocalDivO quietCall s f stk es → LogDiv s f stk es []
  | args {s : Store H} {f : Frame} {stk : List Val} {i : Instr} {args es : List BExpr}
      {l : List (OCall H)} :
      LogDiv s f stk args l → LogDiv s f stk (.op i args :: es) l
  | callK {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {l₁ l₂ : List (OCall H)}
      (hargs : EvalL s f stk args l₁ (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi))
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      LogDiv s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es l₂ →
      LogDiv s f stk (.op (.call x) args :: es)
        (l₁ ++ OCall.mk a (stk₁.take ps.length).reverse s₁ (.inl ws) s₂ :: l₂)
  | opK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ : List Val} {i : Instr}
      {args es : List BExpr} {l₁ l₂ : List (OCall H)}
      (hi : ∀ x, i ≠ .call x)
      (hargs : EvalL s f stk args l₁ (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂)) :
      LogDiv s₂ f₂ stk₂ es l₂ → LogDiv s f stk (.op i args :: es) (l₁ ++ l₂)
  | block {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} {l : List (OCall H)} (har : arity f bt = some (np, nr)) :
      LogDiv s f (stk.take np) body l → LogDiv s f stk (.block bt body :: es) l
  | blockK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {l₁ l₂ : List (OCall H)}
      (har : arity f bt = some (np, nr)) (hbody : EvalL s f (stk.take np) body l₁ (s₁, f₁, fl))
      (hvs : fl.blockVals = some vs) :
      LogDiv s₁ f₁ (vs.take nr ++ stk.drop np) es l₂ →
      LogDiv s f stk (.block bt body :: es) (l₁ ++ l₂)
  | loop {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} {l : List (OCall H)} (har : arity f bt = some (np, nr)) :
      LogDiv s f (stk.take np) body l → LogDiv s f stk (.loop bt body :: es) l
  | loopK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {l₁ l₂ : List (OCall H)}
      (har : arity f bt = some (np, nr))
      (hbody : EvalL s f (stk.take np) body l₁ (s₁, f₁, .normal vs)) :
      LogDiv s₁ f₁ (vs.take nr ++ stk.drop np) es l₂ →
      LogDiv s f stk (.loop bt body :: es) (l₁ ++ l₂)
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {l₁ l₂ : List (OCall H)}
      (har : arity f bt = some (np, nr))
      (hbody : EvalL s f (stk.take np) body l₁ (s₁, f₁, .brk 0 vs)) :
      LogDiv s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) l₂ →
      LogDiv s f stk (.loop bt body :: es) (l₁ ++ l₂)
  | cond {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {c t el es : List BExpr}
      {l : List (OCall H)} :
      LogDiv s f stk c l → LogDiv s f stk (.if_ bt c t el :: es) l
  | arm {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {l₁ l₂ : List (OCall H)}
      (hc : EvalL s f stk c l₁ (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr)) :
      LogDiv s₁ f₁ (stk₁.take np) (if b then t else el) l₂ →
      LogDiv s f stk (.if_ bt c t el :: es) (l₁ ++ l₂)
  | ifK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      {l₁ l₂ l₃ : List (OCall H)}
      (hc : EvalL s f stk c l₁ (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalL s₁ f₁ (stk₁.take np) (if b then t else el) l₂ (s₂, f₂, fl))
      (hvs : fl.blockVals = some vs) :
      LogDiv s₂ f₂ (vs.take nr ++ stk₁.drop np) es l₃ →
      LogDiv s f stk (.if_ bt c t el :: es) (l₁ ++ l₂ ++ l₃)

/-- **The trees diverge after a logged prefix resolving to the host calls `cs`**: within the
function (`LogDiv`), its calls resolved by the closure to `cs`; or in a callee `y` reached
after a prefix resolving to `q` (`ReachL`), the callee diverging after the rest `q'` as `Q`
says. The one-function step of divergence after a log; `Q` is the callees' divergence. -/
def LogDivOut (Q : (wasmOShape H).self.Op → List (Call (wasmHostSig H)) → Prop) (s : Store H)
    (f : Frame) (stk : List Val) (es : List BExpr) (cs : List (Call (wasmHostSig H))) : Prop :=
  (∃ l, LogDiv s f stk es l ∧ Shape.SubstPre (Shape.close wasmHOpen) (l.map OCall.lift) cs) ∨
    ∃ (l : List (OCall H)) (y : (wasmOShape H).self.Op) (q q' : List (Call (wasmHostSig H))),
      ReachL s f stk es l y ∧ Shape.SubstPre (Shape.close wasmHOpen) (l.map OCall.lift) q ∧
        Q y q' ∧ cs = q ++ q'

/-- **Logged local divergence of a call**: the body of the Wasm function called by `z`
performs the open calls `u` and then diverges within the function, host-free. -/
def LDLw (z : (wasmHShape H).self.Op) (u : List (HCall H)) : Prop :=
  ∃ (fi : FuncInst H) (fn : Func) (l : List (OCall H)), z.2.2.funcs[z.1]? = some fi ∧
    fi.code = .wasm fn ∧
    LogDiv z.2.2 (Frame.forCall fi.module z.2.1 fn.locals) [] (liftInstrs fn.body) l ∧
    u = l.map OCall.lift

/-- **The logged native semantics of an invocation, with divergence**: `wasmEvFun` plus `div`
after descent chains and after logged local divergence (`Shape.closeDLog`). -/
def wasmEvFunD : AFun (wasmHostSig H) (Store H) (Nat × List Val) (List Val ⊕ Nat) :=
  fun s p => Shape.closeDLog wasmHOpen LDLw p.1 s p.2

end Silmaril.Wasm.Abstract
