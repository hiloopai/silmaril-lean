module

public import Silmaril.Wasm.Abstract.HostEval.Defs
public import Silmaril.Wasm.Abstract.HostCall.Thms
public import Silmaril.Wasm.Logic.Core.Thms
public import Silmaril.Wasm.Interp.Thms
import Silmaril.Proofs.Wasm.Abstract.HostEval.Basic
import Silmaril.Proofs.Wasm.Abstract.HostEval.Backward

/-!
# The native semantics with host calls: theorems (stage H2)

* `hostCall_fixpoint`: the closure answers Wasm callees by their bodies and
  host callees by the host.
* `hostCall_closedHost`: with the closed host it is `closedCall`. So `EvalH
  closedHost` is the closed native semantics of `Silmaril.Wasm.Abstract.Recursion`,
  and every closed-host result applies to it.

**First forward-simulation cases**, any frame, every profile and host:

* `wp_host_callOk`: a native call of a host function answered `values vs`
  (with the declared result arity) continues in Core at exactly the native
  continuation stack `vs.reverse ++ stk₁.drop ps.length`, in the store the host
  returned;
* `steps_host_callTrap`: an answer `trap` is a Core run to `[trap]` in the
  host's store.

**The whole forward simulation** is `Interp.evalH_good`
(`Silmaril.Wasm.Interp.Thms`): every `EvalH host` run of arity-checked code is a
Core 3.0 run with the same host, for hosts in `Interp.NativeHostSlice`. Those
hosts extend the store's functions as Core's `Extend` does, with appended
functions native and passing the arity check (`Interp.FuncsGood`), answer values
at the declared result arity, and never throw. Not covered: hosts that append
non-native or unchecked functions, and host exceptions.

**Backward simulation, first cases** (`BackOut`: a stuck end of a Core run of
the lowered trees is the end of an `EvalH` run, `EndsAs`, or is blocked at a host
call with no outcome, `Pending`), any profile and host:

* `Pending.append`, `Pending.ne_vals`, `Pending.ne_trap`, `Pending.ne_throwing`;
* `back_nil`: the empty tree list;
* `back_op_args`: an operator tree, through its arguments. An abrupt or blocked
  end of the arguments ends the whole run (`argsAbort`); a normal end on `stk₁`
  hands the remaining run from `vals stk₁ ++ i :: es` to the instruction's case.

* `back_flat` (deterministic profile, any host): a native flat instruction
  (not a call, passing the check) stepping to `(s₂, f₂, fl)` is followed by every
  Core run to a stuck end: after it, the run continues from `vals stk₂ ++ rest` in
  at most as many steps when `fl` is normal, and otherwise ends as the native
  abrupt result. Through `HostCall.stepsN_through_steps`: the native step predicts a
  host-free Core run, and the actual run, whatever its host answers, passes
  through it. With typed code the native step exists in any store
  (`Interp.evalFlat_progressH`).

* `back_op_flat`: an operator tree other than a call, composed from
  `back_op_args`, `back_flat` and the case of the following trees. The native
  step after the arguments and its check are hypotheses (`hflat`), to be
  discharged from typing (`ContextTyped.steps_typed` with `HostTyped`,
  `Interp.evalFlat_progressH`) and the forward arity invariants.

The flat and composed cases are stated for the deterministic profile
`SingleThreaded.profile o` (they follow host-free steps through
`stepsN_through`); nothing is claimed here for other profiles.

* `back_call_host`, `back_op_call_host`: a direct call of a host function. After
  `call x` (host-free) the run is at the host call on the top `ps.length` values:
  it is blocked there (`Pending`), or the host gave an answer that `hostCall`
  takes, values (the run continues from the native continuation stack in fewer
  steps) or a trap. Result arity and no exceptions are hypotheses (the host
  slice, `Interp.NativeHostSlice`).

**Not yet proved.** Discharging the hypotheses in the whole theorem, calls of
Wasm functions, blocks, loops and `if`,
hence the whole backward simulation, and the decomposition of divergence with
host calls.
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core

variable {H : Type}

theorem hostCall_fixpoint (host : HostSemantics H) :
    hostCall host = bodyCall (hostCall host) ⊔ hostAns host :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.hostCall_fixpoint host

/-- With the closed host, closing with host calls is plain closing. -/
theorem hostCall_closedHost : hostCall (closedHost : HostSemantics H) = closedCall :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.hostCall_closedHost

variable {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- **Host call answered with values**: the native continuation is the Core one. -/
theorem wp_host_callOk {s₁ s₂ : Store H} {f₁ : Frame} {stk₁ : List Val} {x : Silmaril.Wasm.FuncIdx}
    {a : Nat} {fi : FuncInst H} {h : H} {ps rs : Ty (.list .val)} {vs : List Val}
    {rest : List Admin} {Q : Post H}
    (hx : f₁.module.funcs[x.toNat]? = some a) (hf : s₁.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hcode : fi.code = .host h)
    (hlen : ps.length ≤ stk₁.length) (hres : vs.length = rs.length)
    (hans : host h s₁ (stk₁.take ps.length).reverse (.returned s₂ (.values vs)))
    (hk : WP P host s₂ f₁
      (vals ((vs.reverse.take rs.length) ++ stk₁.drop ps.length).reverse ++ rest) Q) :
    WP P host s₁ f₁ (vals stk₁.reverse ++ .plain (.call x) :: rest) Q :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.wp_host_callOk hx hf he hcode hlen hres hans hk

/-- **Host call answered with a trap.** -/
theorem steps_host_callTrap {s₁ s₂ : Store H} {f₁ : Frame} {stk₁ : List Val}
    {x : Silmaril.Wasm.FuncIdx} {a : Nat} {fi : FuncInst H} {h : H} {ps rs : Ty (.list .val)}
    {rest : List Admin}
    (hx : f₁.module.funcs[x.toNat]? = some a) (hf : s₁.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hcode : fi.code = .host h)
    (hlen : ps.length ≤ stk₁.length)
    (hans : host h s₁ (stk₁.take ps.length).reverse (.returned s₂ .trap)) :
    Steps P host ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩ ⟨s₂, f₁, [.trap]⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.steps_host_callTrap hx hf he hcode hlen hans

theorem Pending.append {s : Store H} {es : List Admin} (h : Pending host s es) (rest : List Admin) :
    Pending host s (es ++ rest) :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.pending_append h rest

theorem Pending.ne_vals {s : Store H} {es : List Admin} (h : Pending host s es) (ws : List Val) :
    es ≠ vals ws :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.pending_ne_vals h ws

theorem Pending.ne_trap {s : Store H} {es : List Admin} (h : Pending host s es) : es ≠ [.trap] :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.pending_ne_trap h

theorem Pending.ne_throwing {s : Store H} {es : List Admin} (h : Pending host s es) (x : Nat) :
    es ≠ throwing x :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.pending_ne_throwing h x

/-- **The empty tree list**: its run ends as the native `nil`. -/
theorem back_nil {n : Nat} {s : Store H} {f : Frame} {stk : List Val} {c : Config H}
    (hrun : StepsN P host n ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList [])⟩ c) :
    BackOut host s f stk [] c :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.back_nil hrun

/-- **An operator tree, through its arguments.** -/
theorem back_op_args {n : Nat} {s : Store H} {f : Frame} {stk : List Val} {i : Instr}
    {args es : List Binaryen.BExpr} {c : Config H}
    (hrun : StepsN P host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.op i args :: es))⟩ c)
    (hend : ∀ c', ¬ Step P host c c')
    (ihargs : ∀ m ≤ n, ∀ c₁, StepsN P host m
        ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args)⟩ c₁ →
      (∀ c', ¬ Step P host c₁ c') → BackOut host s f stk args c₁)
    (hk : ∀ s₁ f₁ stk₁ m, m ≤ n → EvalH host s f stk args (s₁, f₁, .normal stk₁) →
      StepsN P host m ⟨s₁, f₁, vals stk₁.reverse ++ .plain i ::
        expression (Binaryen.BExpr.lowerList es)⟩ c →
      BackOut host s f stk (.op i args :: es) c) :
    BackOut host s f stk (.op i args :: es) c :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.back_op_args hrun hend ihargs hk

/-- **The backward case of a flat instruction.** -/
theorem back_flat {o : SingleThreaded.GrowOracle} {n : Nat} {s₁ s₂ : Store H} {f₁ f₂ : Frame}
    {stk₁ : List Val} {i : Instr} {fl : Binaryen.Flow} {rest : List Admin} {c : Config H}
    {F : List (FuncInst H)} {mi : ModuleInst} {ret : Nat} {labels : List Nat} {h₀ : Nat}
    {o₁ : Option Nat} (hi : ∀ x, i ≠ .call x)
    (hc : Interp.flatChk F mi f₁.locals.length ret labels h₀ i = some o₁)
    (hflat : Binaryen.evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, fl))
    (hrun : StepsN (SingleThreaded.profile o) host n ⟨s₁, f₁, vals stk₁.reverse ++ .plain i :: rest⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c') :
    (∀ stk₂, fl = .normal stk₂ →
        ∃ m ≤ n, StepsN (SingleThreaded.profile o) host m ⟨s₂, f₂, vals stk₂.reverse ++ rest⟩ c) ∧
      (¬ fl.IsNormal → EndsAs (s₂, f₂, fl) c) :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.back_flat hi hc hflat hrun hend

/-- **An operator tree other than a call** (deterministic profile, any host). -/
theorem back_op_flat {o : SingleThreaded.GrowOracle} {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {i : Instr} {args es : List Binaryen.BExpr} {c : Config H}
    (hi : ∀ x, i ≠ .call x)
    (hrun : StepsN (SingleThreaded.profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.op i args :: es))⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c')
    (ihargs : ∀ m ≤ n, ∀ c₁, StepsN (SingleThreaded.profile o) host m
        ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args)⟩ c₁ →
      (∀ c', ¬ Step (SingleThreaded.profile o) host c₁ c') → BackOut host s f stk args c₁)
    (hflat : ∀ s₁ f₁ stk₁, EvalH host s f stk args (s₁, f₁, .normal stk₁) →
      (∃ r, Binaryen.evalFlat s₁ f₁ stk₁ i = some r) ∧
      ∃ (F : List (FuncInst H)) (mi : ModuleInst) (ret : Nat) (labels : List Nat) (h₀ : Nat)
        (o₁ : Option Nat), Interp.flatChk F mi f₁.locals.length ret labels h₀ i = some o₁)
    (ihes : ∀ s₁ f₁ stk₁ s₂ f₂ stk₂ m, m ≤ n → EvalH host s f stk args (s₁, f₁, .normal stk₁) →
      Binaryen.evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂) →
      StepsN (SingleThreaded.profile o) host m
        ⟨s₂, f₂, vals stk₂.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ c →
      BackOut host s₂ f₂ stk₂ es c) :
    BackOut host s f stk (.op i args :: es) c :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.back_op_flat hi hrun hend ihargs hflat ihes

/-- **A direct call of a host function** (deterministic profile). -/
theorem back_call_host {o : SingleThreaded.GrowOracle} {n : Nat} {s₁ : Store H} {f₁ : Frame}
    {stk₁ : List Val} {x : FuncIdx} {a : Nat} {fi : FuncInst H} {hh : H}
    {ps rs : List Validation.CValType} {rest : List Admin} {c : Config H}
    (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .host hh)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hp : ps.length ≤ stk₁.length)
    (harity : ∀ s' ws, host hh s₁ (stk₁.take ps.length).reverse (.returned s' (.values ws)) →
      ws.length = rs.length)
    (hnothrow : ∀ s' t, ¬ host hh s₁ (stk₁.take ps.length).reverse (.returned s' (.throw t)))
    (hrun : StepsN (SingleThreaded.profile o) host n
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c') :
    Pending host c.store c.code ∨
      ∃ s₂ fl, hostCall host s₁ a (stk₁.take ps.length).reverse (s₂, fl) ∧
        ((∃ vs m, m < n ∧ fl.retVals = some vs ∧
            StepsN (SingleThreaded.profile o) host m
              ⟨s₂, f₁, vals (vs.take rs.length ++ stk₁.drop ps.length).reverse ++ rest⟩ c) ∨
          (fl = .trap ∧ EndsAs (s₂, f₁, .trap) c)) :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.back_call_host hfi hcode hty hp harity hnothrow hrun hend

/-- **A direct call of a host function, as a tree** (deterministic profile). -/
theorem back_op_call_host {o : SingleThreaded.GrowOracle} {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {x : FuncIdx} {args es : List Binaryen.BExpr} {c : Config H}
    (hrun : StepsN (SingleThreaded.profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.op (.call x) args :: es))⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c')
    (ihargs : ∀ m ≤ n, ∀ c₁, StepsN (SingleThreaded.profile o) host m
        ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args)⟩ c₁ →
      (∀ c', ¬ Step (SingleThreaded.profile o) host c₁ c') → BackOut host s f stk args c₁)
    (hcallee : ∀ s₁ f₁ stk₁, EvalH host s f stk args (s₁, f₁, .normal stk₁) →
      ∃ (a : Nat) (fi : FuncInst H) (hh : H) (ps rs : List Validation.CValType),
        s₁.func? f₁ x = some (a, fi) ∧ fi.code = .host hh ∧
        Validation.DefType.funcType? fi.type = some (ps, rs) ∧ ps.length ≤ stk₁.length ∧
        (∀ s' ws, host hh s₁ (stk₁.take ps.length).reverse (.returned s' (.values ws)) →
          ws.length = rs.length) ∧
        ∀ s' t, ¬ host hh s₁ (stk₁.take ps.length).reverse (.returned s' (.throw t)))
    (ihes : ∀ s₂ f₁ stk₂ m, m ≤ n →
      StepsN (SingleThreaded.profile o) host m
        ⟨s₂, f₁, vals stk₂.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ c →
      BackOut host s₂ f₁ stk₂ es c) :
    BackOut host s f stk (.op (.call x) args :: es) c :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.back_op_call_host hrun hend ihargs hcallee ihes

end Silmaril.Wasm.Abstract
