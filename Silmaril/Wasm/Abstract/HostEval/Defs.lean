module

public import Silmaril.Wasm.Abstract.Recursion.Defs
public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Wasm.Interp.Defs
public import Silmaril.Wasm.Abstract.Closing.Defs

/-!
# The native semantics with host calls (stage H2)

`EvalO C` (`Silmaril.Wasm.Abstract.Recursion`) answers every internal call
through an oracle `C`, whatever the callee's code. A host function is
therefore just another oracle answer:

* `resFlow r`: a host result as a callee body flow. Returned values `vs` (Core
  order) are the flow `normal vs.reverse` (top-first); a trap traps; an
  exception throws.
* `hostAns host`: the call of a **host** function at `a` on `args` in `s` may end
  in `(s', resFlow r)` exactly when `host h s args (.returned s' r)`. Host
  divergence and the absence of a host outcome are **not** answers. They are
  the `hostDiv` and `blocked` observations, handled separately
  (`Silmaril.Wasm.Abstract.HostCall`).
* `hostCall host`: the least fixpoint of "run a Wasm callee's body with the
  calls answered by the fixpoint, or answer a host callee by `hostAns`".
* `EvalH host := EvalO (hostCall host)`: terminating native runs with
  internal recursion and host calls, every host answer as the relation allows.

No determinism or totality of `host` is assumed.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- A host result as a callee body flow (values top-first). -/
def resFlow : Result → Flow
  | .values vs => .normal vs.reverse
  | .trap => .trap
  | .throw t => .throw t

/-- Answers of host functions, as the host semantics allows. -/
def hostAns (host : HostSemantics H) : CallRel H := fun s a args out =>
  ∃ (fi : FuncInst H) (h : H) (r : Result), s.funcs[a]? = some fi ∧ fi.code = .host h ∧
    host h s args (.returned out.1 r) ∧ out.2 = resFlow r

/-- One round: Wasm callees by their bodies, host callees by the host. -/
def hostCallOp (host : HostSemantics H) : CallRel H →o CallRel H where
  toFun C := bodyCall C ⊔ hostAns host
  monotone' C C' h s a args out := by
    rintro (h₁ | h₂)
    · exact .inl ((bodyCallOp (H := H)).monotone' h s a args out h₁)
    · exact .inr h₂

/-- **Closing with host calls**: the least fixpoint. -/
def hostCall (host : HostSemantics H) : CallRel H := (hostCallOp host).lfp

/-- **The native semantics with host calls.** -/
abbrev EvalH (host : HostSemantics H) := EvalO (hostCall host)

/-! ## Backward simulation: how a Core run ends -/

/-- **A pending host call with no host outcome** somewhere in the code, under
values and labels or frames: the `blocked` observation, seen in Core. The call
is `ref.func a; call_ref` of a host function on exactly its arguments `us`, and
the host has no outcome for it. -/
inductive Pending (host : HostSemantics H) (s : Store H) : List Admin → Prop where
  | call {ws us : List Val} {a : Nat} {fi : FuncInst H} {hh : H}
      {ps rs : Validation.Ty (.list .val)} {rest : List Admin}
      (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
      (he : Validation.Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
      (hno : ∀ o, ¬ host hh s us o) :
      Pending host s (vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest)
  | label {ws : List Val} {n : Nat} {cont : List Instr} {es rest : List Admin} :
      Pending host s es → Pending host s (vals ws ++ .label n cont es :: rest)
  | frame {ws : List Val} {n : Nat} {F : Frame} {es rest : List Admin} :
      Pending host s es → Pending host s (vals ws ++ .frame n F es :: rest)

/-- A Core configuration ends as the native result `r`: it is a final form whose
outcome matches `r` (`Interp.Match`: same store and frame, matching flow). -/
def EndsAs (r : Store H × Frame × Flow) (c : Config H) : Prop :=
  ∃ o : Logic.Core.Outcome, o.Ends c.code ∧ Interp.Match r c.store c.frame o

/-- **A pending host call the host may diverge on** somewhere in the code, under
values and labels or frames: the `hostDiv` observation, seen in Core. -/
inductive PendingDiv (host : HostSemantics H) (s : Store H) : List Admin → Prop where
  | call {ws us : List Val} {a : Nat} {fi : FuncInst H} {hh : H}
      {ps rs : Validation.Ty (.list .val)} {rest : List Admin}
      (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
      (he : Validation.Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
      (hdiv : host hh s us .diverged) :
      PendingDiv host s (vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest)
  | label {ws : List Val} {n : Nat} {cont : List Instr} {es rest : List Admin} :
      PendingDiv host s es → PendingDiv host s (vals ws ++ .label n cont es :: rest)
  | frame {ws : List Val} {n : Nat} {F : Frame} {es rest : List Admin} :
      PendingDiv host s es → PendingDiv host s (vals ws ++ .frame n F es :: rest)

/-! ## Reaching a call with answered calls -/

/-- **The trees reach the call `y`** (callee address, arguments, store) after a
prefix that terminates in `EvalO C`: the oracle analog of `Decomp.Reach`, every
completed call answered by `C`. -/
inductive ReachO (C : CallRel H) : Store H → Frame → List Val → List BExpr →
    (wasmOShape H).self.Op → Prop where
  | here {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
      (hargs : EvalO C s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi))
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
      ReachO C s f stk (.op (.call x) args :: es) ⟨a, ((stk₁.take ps.length).reverse, s₁)⟩
  | args {s : Store H} {f : Frame} {stk : List Val} {i : Instr} {args es : List BExpr}
      {y : (wasmOShape H).self.Op} :
      ReachO C s f stk args y → ReachO C s f stk (.op i args :: es) y
  | callK {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val} {x : FuncIdx}
      {args es : List BExpr} {a : Nat} {fi : FuncInst H}
      {ps rs : List Validation.CValType} {fl : Flow} {y : (wasmOShape H).self.Op}
      (hargs : EvalO C s f stk args (s₁, f₁, .normal stk₁))
      (hfi : s₁.func? f₁ x = some (a, fi))
      (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
      (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, fl))
      (hvs : fl.retVals = some vs) :
      ReachO C s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es y →
      ReachO C s f stk (.op (.call x) args :: es) y
  | opK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ : List Val} {i : Instr}
      {args es : List BExpr} {y : (wasmOShape H).self.Op} (hi : ∀ x, i ≠ .call x)
      (hargs : EvalO C s f stk args (s₁, f₁, .normal stk₁))
      (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂)) :
      ReachO C s₂ f₂ stk₂ es y → ReachO C s f stk (.op i args :: es) y
  | block {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} {y : (wasmOShape H).self.Op} (har : arity f bt = some (np, nr)) :
      ReachO C s f (stk.take np) body y → ReachO C s f stk (.block bt body :: es) y
  | blockK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {fl : Flow} {y : (wasmOShape H).self.Op}
      (har : arity f bt = some (np, nr)) (hbody : EvalO C s f (stk.take np) body (s₁, f₁, fl))
      (hvs : fl.blockVals = some vs) :
      ReachO C s₁ f₁ (vs.take nr ++ stk.drop np) es y → ReachO C s f stk (.block bt body :: es) y
  | loop {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
      {np nr : Nat} {y : (wasmOShape H).self.Op} (har : arity f bt = some (np, nr)) :
      ReachO C s f (stk.take np) body y → ReachO C s f stk (.loop bt body :: es) y
  | loopK {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {y : (wasmOShape H).self.Op}
      (har : arity f bt = some (np, nr))
      (hbody : EvalO C s f (stk.take np) body (s₁, f₁, .normal vs)) :
      ReachO C s₁ f₁ (vs.take nr ++ stk.drop np) es y → ReachO C s f stk (.loop bt body :: es) y
  | loopBack {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
      {body es : List BExpr} {np nr : Nat} {y : (wasmOShape H).self.Op}
      (har : arity f bt = some (np, nr))
      (hbody : EvalO C s f (stk.take np) body (s₁, f₁, .brk 0 vs)) :
      ReachO C s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) y →
      ReachO C s f stk (.loop bt body :: es) y
  | cond {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {c t el es : List BExpr}
      {y : (wasmOShape H).self.Op} :
      ReachO C s f stk c y → ReachO C s f stk (.if_ bt c t el :: es) y
  | arm {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {y : (wasmOShape H).self.Op}
      (hc : EvalO C s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr)) :
      ReachO C s₁ f₁ (stk₁.take np) (if b then t else el) y →
      ReachO C s f stk (.if_ bt c t el :: es) y
  | ifK {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ vs : List Val} {cv : Val} {b : Bool}
      {bt : BlockType} {c t el es : List BExpr} {np nr : Nat} {fl : Flow}
      {y : (wasmOShape H).self.Op}
      (hc : EvalO C s f stk c (s₁, f₁, .normal (cv :: stk₁))) (hb : truthy cv = some b)
      (har : arity f₁ bt = some (np, nr))
      (harm : EvalO C s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
      (hvs : fl.blockVals = some vs) :
      ReachO C s₂ f₂ (vs.take nr ++ stk₁.drop np) es y → ReachO C s f stk (.if_ bt c t el :: es) y

/-- **A pending call of an invocation** `x`: the call `y` is reached in the body of
`x`, or of a Wasm function the body reaches, finitely deep. -/
inductive PendO (C : CallRel H) : (wasmOShape H).self.Op → (wasmOShape H).self.Op → Prop where
  | body {x y : (wasmOShape H).self.Op} {fi : FuncInst H} {fn : Func}
      (hf : x.2.2.funcs[x.1]? = some fi) (hcode : fi.code = .wasm fn)
      (hr : ReachO C x.2.2 (Frame.forCall fi.module x.2.1 fn.locals) [] (liftInstrs fn.body) y) :
      PendO C x y
  | desc {x z y : (wasmOShape H).self.Op} {fi : FuncInst H} {fn : Func}
      (hf : x.2.2.funcs[x.1]? = some fi) (hcode : fi.code = .wasm fn)
      (hr : ReachO C x.2.2 (Frame.forCall fi.module x.2.1 fn.locals) [] (liftInstrs fn.body) z) :
      PendO C z y → PendO C x y

/-- **At the call `a` on `us`** in store `s`: the code is `vals us ++ [ref.func a,
call_ref]` (with the function's type), under values and labels or frames. -/
inductive AtCall (s : Store H) (a : Nat) (us : List Val) : List Admin → Prop where
  | here {ws : List Val} {fi : FuncInst H} {rest : List Admin} (hf : s.funcs[a]? = some fi) :
      AtCall s a us (vals ws ++ vals us ++ .ref (.func a) :: .callRefType fi.type :: rest)
  | label {ws : List Val} {n : Nat} {cont : List Instr} {es rest : List Admin} :
      AtCall s a us es → AtCall s a us (vals ws ++ .label n cont es :: rest)
  | frame {ws : List Val} {n : Nat} {F : Frame} {es rest : List Admin} :
      AtCall s a us es → AtCall s a us (vals ws ++ .frame n F es :: rest)

/-- The call `y` is reached from the trees, directly or through callee bodies. -/
def ReachP (C : CallRel H) (s : Store H) (f : Frame) (stk : List Val) (es : List BExpr)
    (y : (wasmOShape H).self.Op) : Prop :=
  ReachO C s f stk es y ∨ ∃ z, ReachO C s f stk es z ∧ PendO C z y

/-- `c` is blocked at the host call `y`: `y`'s store is `c`'s, `y` is a host function with no
host outcome on its arguments, and `c`'s code is at that call. -/
def BlockedAt (host : HostSemantics H) (c : Config H) (y : (wasmOShape H).self.Op) : Prop :=
  ∃ (fi : FuncInst H) (hh : H), y.2.2 = c.store ∧ c.store.funcs[y.1]? = some fi ∧
    fi.code = .host hh ∧ (∀ o, ¬ host hh c.store y.2.1 o) ∧ AtCall c.store y.1 y.2.1 c.code

/-- The trees reach, directly or through callee bodies, a host call the host may diverge on. -/
def HostDivReach (host : HostSemantics H) (s : Store H) (f : Frame) (stk : List Val)
    (es : List BExpr) : Prop :=
  ∃ (y : (wasmOShape H).self.Op) (fi : FuncInst H) (hh : H),
    ReachP (hostCall host) s f stk es y ∧ y.2.2.funcs[y.1]? = some fi ∧ fi.code = .host hh ∧
      host hh y.2.2 y.2.1 .diverged

/-! ## Backward simulation: the conclusion -/

/-- **The backward conclusion**: a stuck end `c` of a Core run of the lowered
trees `es` on `stk` is the end of a native run with host calls (`EvalH`), or is
blocked at a host call with no outcome (`Pending`), together with **reach
evidence**: a host call `y` the native semantics reaches from the trees, through
answered calls and Wasm callee bodies (`ReachP (hostCall host)`), at which `c` is
blocked (`BlockedAt`). -/
def BackOut (host : HostSemantics H) (s : Store H) (f : Frame) (stk : List Val)
    (es : List BExpr) (c : Config H) : Prop :=
  (∃ r, EvalH host s f stk es r ∧ EndsAs r c) ∨
    (Pending host c.store c.code ∧ ∃ y, ReachP (hostCall host) s f stk es y ∧ BlockedAt host c y)

end Silmaril.Wasm.Abstract
