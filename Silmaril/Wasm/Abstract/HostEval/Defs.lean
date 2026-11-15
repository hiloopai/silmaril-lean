module

public import Silmaril.Wasm.Abstract.Recursion.Defs
public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Wasm.Interp.Defs

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

/-- **The backward conclusion**: a stuck end `c` of a Core run of the lowered
trees `es` on `stk` is the end of a native run with host calls (`EvalH`), or is
blocked at a host call with no outcome. -/
def BackOut (host : HostSemantics H) (s : Store H) (f : Frame) (stk : List Val)
    (es : List BExpr) (c : Config H) : Prop :=
  (∃ r, EvalH host s f stk es r ∧ EndsAs r c) ∨ Pending host c.store c.code

end Silmaril.Wasm.Abstract
