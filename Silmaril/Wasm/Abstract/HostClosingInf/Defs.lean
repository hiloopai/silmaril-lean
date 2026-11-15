module

public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Games.Abstract.HostRunInf.Defs
public import Silmaril.Wasm.Abstract.HostClosing.Defs
public import Silmaril.Wasm.Abstract.DivO.Defs
public import Silmaril.Games.Abstract.ModuleDLog.Defs
public import Silmaril.Games.Abstract.ModuleInf.Defs

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

**Productive runs, natively and host-independently**:

* `InfL s f stk es ω`: the trees run forever within their function, making the open calls `ω`
  (each with its answer, as in `EvalL`). The constructors are those of `LogDiv`: a finite part
  run by `EvalL` puts its log in front of the stream, a completed call is recorded with its
  answer. The definition is inductive except for `loopInf`, a loop branching back forever, whose
  stream is the concatenation of its iteration logs, of unbounded length; so a loop whose
  iterations make no call claims no stream. Divergence inside a callee is not here;
* `InfLw`: the productive open runs of a Wasm body, as calls of `wasmHOpen` (`OCall.lift`). Host
  calls appear as the internal calls of host functions, which the closure resolves to their
  one import call, as in `wasmHOpen`;
* `wasmEvInfN := Shape.closeInfL wasmHOpen InfLw`: the productive runs through unbounded
  recursion (`Shape.closeInf`), and those of a function's own body after a descent path, its
  open calls resolved by the closure one choice per position (`Shape.SubstInf`).

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

/-! ## Productive runs inside one function, natively -/

open Shape (streamAppend StreamConcat) in
/-- **The trees run forever within the function, making the open calls `ω`.** The constructors
are those of `LogDiv`: finite parts run by `EvalL` put their logs in front of the stream
(`l ++ω ω`), and a completed call is recorded with its answer. The trees are finite and the
only way back into a tree is a loop's back edge, so the definition is inductive except for one
constructor, `loopInf`: a loop iterating forever, the stream the concatenation of the
iteration logs, **of unbounded length**. So every stream is produced: a loop whose iterations
make no call claims no stream (`InfL` has no gfp reading of an empty back edge). Divergence
inside a callee is not here: it is a descent of the module (`Shape.closeInfL`). -/
inductive InfL : Store H → Frame → List Val → List BExpr → (Nat → OCall H) → Prop where
  | args {s : Store H} {f : Frame} {stk : List Val} {i : Instr} {args es : List BExpr}
      {ω : Nat → OCall H} :
      InfL s f stk args ω → InfL s f stk (.op i args :: es) ω
  | callK {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ ws : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {l₁ : List (OCall H)} {ω : Nat → OCall H}
      (hargs : EvalL s f stk args l₁ (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi))
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      InfL s₂ f₁ (ws.reverse ++ stk₁.drop ps.length) es ω →
      InfL s f stk (.op (.call x) args :: es)
        ((l₁ ++ [OCall.mk a (stk₁.take ps.length).reverse s₁ (.inl ws) s₂]) ++ω ω)
  | opK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ : List Val} {i : Instr}
      {args es : List BExpr} {l₁ : List (OCall H)} {ω : Nat → OCall H}
      (hi : ∀ x, i ≠ .call x)
      (hargs : EvalL s f stk args l₁ (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂)) :
      InfL s₂ f₂ stk₂ es ω → InfL s f stk (.op i args :: es) (l₁ ++ω ω)
  | block {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} {ω : Nat → OCall H} (har : arity f bt = some (np, nr)) :
      InfL s f (stk.take np) body ω → InfL s f stk (.block bt body :: es) ω
  | blockK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {l₁ : List (OCall H)}
      {ω : Nat → OCall H}
      (har : arity f bt = some (np, nr)) (hbody : EvalL s f (stk.take np) body l₁ (s₁, f₁, fl))
      (hvs : fl.blockVals = some vs) :
      InfL s₁ f₁ (vs.take nr ++ stk.drop np) es ω →
      InfL s f stk (.block bt body :: es) (l₁ ++ω ω)
  | loop {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} {ω : Nat → OCall H} (har : arity f bt = some (np, nr)) :
      InfL s f (stk.take np) body ω → InfL s f stk (.loop bt body :: es) ω
  | loopK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {l₁ : List (OCall H)} {ω : Nat → OCall H}
      (har : arity f bt = some (np, nr))
      (hbody : EvalL s f (stk.take np) body l₁ (s₁, f₁, .normal vs)) :
      InfL s₁ f₁ (vs.take nr ++ stk.drop np) es ω →
      InfL s f stk (.loop bt body :: es) (l₁ ++ω ω)
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {l₁ : List (OCall H)} {ω : Nat → OCall H}
      (har : arity f bt = some (np, nr))
      (hbody : EvalL s f (stk.take np) body l₁ (s₁, f₁, .brk 0 vs)) :
      InfL s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) ω →
      InfL s f stk (.loop bt body :: es) (l₁ ++ω ω)
  /-- A loop iterating forever: the states `st n` at the loop head, the iteration logs `l n`,
  the stream their concatenation, of unbounded length. -/
  | loopInf {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} {ω : Nat → OCall H} (st : Nat → Store H × Frame × List Val)
      (l : Nat → List (OCall H)) (h0 : st 0 = (s, f, stk))
      (har : ∀ n, arity (st n).2.1 bt = some (np, nr))
      (hit : ∀ n, ∃ vs, EvalL (st n).1 (st n).2.1 ((st n).2.2.take np) body (l n)
          ((st (n + 1)).1, (st (n + 1)).2.1, .brk 0 vs) ∧
        (st (n + 1)).2.2 = vs.take np ++ (st n).2.2.drop np)
      (hω : StreamConcat l ω) :
      InfL s f stk (.loop bt body :: es) ω
  | cond {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {c t el es : List BExpr}
      {ω : Nat → OCall H} :
      InfL s f stk c ω → InfL s f stk (.if_ bt c t el :: es) ω
  | arm {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {l₁ : List (OCall H)}
      {ω : Nat → OCall H}
      (hc : EvalL s f stk c l₁ (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr)) :
      InfL s₁ f₁ (stk₁.take np) (if b then t else el) ω →
      InfL s f stk (.if_ bt c t el :: es) (l₁ ++ω ω)
  | ifK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      {l₁ l₂ : List (OCall H)} {ω : Nat → OCall H}
      (hc : EvalL s f stk c l₁ (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalL s₁ f₁ (stk₁.take np) (if b then t else el) l₂ (s₂, f₂, fl))
      (hvs : fl.blockVals = some vs) :
      InfL s₂ f₂ (vs.take nr ++ stk₁.drop np) es ω →
      InfL s f stk (.if_ bt c t el :: es) ((l₁ ++ l₂) ++ω ω)

/-- **The productive open runs of a Wasm body**: the body of the Wasm function called runs
forever within its function (`InfL`), its open calls lifted to calls of `wasmHOpen`
(`OCall.lift`). A host function has none: its one import call ends it. Host-independent. -/
def InfLw : Shape.OpenInf (wasmHShape H) := fun a s vs =>
  {ν | ∃ (fi : FuncInst H) (fn : Func) (ω : Nat → OCall H), s.funcs[a]? = some fi ∧
    fi.code = .wasm fn ∧ InfL s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) ω ∧
    ν = fun i => (ω i).lift}

/-- **The productive runs of an invocation, natively**: the closure of `wasmHOpen` with
productive runs through unbounded recursion and inside one function after a descent path
(`Shape.closeInfL`). No host semantics occurs. -/
def wasmEvInfN : PInf (wasmHostSig H) (Store H) (Nat × List Val) :=
  fun s p => Shape.closeInfL wasmHOpen InfLw p.1 s p.2

end Silmaril.Wasm.Abstract
