module

public import Silmaril.Wasm.Abstract.HostEval.Defs
public import Silmaril.Wasm.Abstract.HostCall.Thms
public import Silmaril.Wasm.Logic.Core.Thms
public import Silmaril.Wasm.Interp.Thms
import Silmaril.Proofs.Wasm.Abstract.HostEval.Basic
import Silmaril.Proofs.Wasm.Abstract.HostEval.Backward
import Silmaril.Proofs.Wasm.Abstract.HostEval.CallWasm
import Silmaril.Proofs.Wasm.Abstract.HostEval.Whole
import Silmaril.Proofs.Wasm.Abstract.HostEval.Obs
import Silmaril.Proofs.Wasm.Abstract.HostEval.Invoke
import Silmaril.Proofs.Wasm.Abstract.HostEval.Reach
import Silmaril.Proofs.Wasm.Abstract.HostEval.PendO
import Silmaril.Proofs.Wasm.Abstract.HostEval.Profile

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

* `back_block`, `back_block_tree`: a block. Entering it is host-free; the body runs
  in its label to a stuck end (`HostCall.stepsN_label_seq_split`), given by the
  body's case on a no longer run; a blocked body blocks the block (a pending call
  is no label exit form); otherwise the label is left by host-free steps as the
  native block is left (`blockOk`, `blockBrk`, `blockEsc`). The block arity of the
  body's results is a hypothesis (`hblk`, from the forward arity invariants).

* `back_loop`, `back_loop_tree`: a loop. Entering is the loop's only step
  (`loop_step_unique`, `stepsN_unique`), so a re-entry runs strictly shorter; the
  body as for blocks; falling through continues after the loop (`loopOk`), a branch
  to the loop re-enters it (`loopBack`, by `ihloop` on a strictly shorter run),
  other abrupt ends leave it (`loopBrk`, `loopEsc`). The loop arity of the body's
  results is a hypothesis (`hlp`).

* `back_prefix`: a run of trees followed by more code (blocked, abrupt, or normal
  with the rest of the run); `back_if_tree`: an `if`, its condition by
  `back_prefix`, the host-free `if` step to the chosen arm's block
  (`Interp.step_if_arm`), the arm by `back_block` (`ifOk`, `ifBrk`, `ifEsc`,
  `ifAbort`). The condition being an `i32` and the arm's block arity are the
  hypothesis `hcond`.

* `back_call_wasm`: a direct call of a Wasm function. `call x` and `call_ref` are
  the only steps into the callee (`call_step_unique`, `callRef_wasm_step_unique`),
  so its body runs strictly shorter than the whole run, in its frame and label
  (`HostCall.stepsN_frame_seq_split`), as the body's case says; a blocked body
  blocks the call; otherwise the native `bodyCall` (hence `hostCall`) answers, and
  the frame is left by host-free steps (`frame_ends`, or a trap). The callee's
  result arity is the hypothesis `hret`.
* `back_op_call`: a direct call as a tree, for any callee, from `back_op_args`, a
  call case (`back_call_host` or `back_call_wasm`) and the following trees.

**The whole-run backward simulation** (`back_whole`, `back_whole_steps`),
deterministic profile `SingleThreaded.profile o`: for a host whose answers are
typed (`HostCall.HostTyped`, no outcome required) in the native host slice
(`Interp.NativeHostSlice`), every Core run of lowered trees that pass the arity
check, in a store whose functions pass it (`Interp.StoreChk`), from a typed
configuration (`Sim.ContextTyped`), to a stuck end, is the end of an `EvalH` run
(`EndsAs`) or blocked at a host call with no outcome (`Pending`). Proof: a
well-founded induction on the run length, then the tree size, over the cases
above, their hypotheses discharged from the forward simulation
(`Interp.evalH_good`: `FlowOk`, `EvalInv`, and Core runs carrying typing), typed
native progress and the host slice. Nothing is claimed for other profiles.

**The host observations in Core.** `pending_stuck`: a configuration at a blocked
host call (`Pending`) has no step, in any frame and profile, so `blocked` is Core
stuckness. `stuck_iff` (deterministic profile): for typed native code, the stuck
ends of a Core run are exactly the ends of `EvalH` runs and the blocked host calls.
`pendingDiv_diverges`: at a pending call the host may diverge on (`PendingDiv`),
Core diverges by stuttering at the call, in any frame and profile, so `hostDiv` is
Core divergence.

**Invocations** (`back_invoke`, deterministic profile): a Core run of a typed
invocation `invoke s a vs` (`StoreOk`, `InvokeOk`, functions passing the check)
to a stuck end is blocked at a host call, or ends exactly as a native answer
`hostCall host s a vs (s₂, fl)` does: the callee's results, or a trap, in `s₂`.

**Every profile** (`back_invoke_profile`, `back_invoke_steps_profile`): the same at
every profile `P`, under two explicit native-profile side conditions: the store's Wasm
functions are native-profile code (`Interp.NativeWasmFuncs`, not implied by `StoreChk`)
and the host satisfies `Interp.HostNative` (its answers keep that, and never throw).
Native configurations step alike at every profile (`Interp.step_profile`), so the run
and its stuck end are a run and a stuck end at the deterministic profile. Hosts that
allocate non-native Wasm functions are not covered.

**Forward reachability of pending calls**, every profile: `reach_atCall`: a reach
of a call after answered calls (`ReachO (hostCall host)`, the oracle analog of
`Decomp.Reach`) of arity-checked trees, for a host in the native host slice, is a
Core run to a configuration at that call (`AtCall`), in the call's store. At a
host function, `atCall_pending` (no outcome: `Pending`, so Core is blocked) and
`atCall_pendingDiv` (the host may diverge: `PendingDiv`, so Core diverges).

**Pending calls of an invocation** (`PendO`, reached through Wasm callee bodies),
every profile: `invoke_pendO_atCall` (reached in Core, under the callee frames and
labels entered on the way), `invoke_pendO_blocked` (a host call with no outcome is
a reachable stuck `Pending` configuration), `invoke_pendO_diverges` (a host call
the host may diverge on makes the invocation diverge in Core).

**Not yet proved.** The commuting square with `HostRun.hostObs` (once the logged
packaging exists), and the backward direction in other profiles.-/

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

/-- **A block tree** (deterministic profile). -/
theorem back_block_tree {o : SingleThreaded.GrowOracle} {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {bt : BlockType} {body es : List Binaryen.BExpr} {np nr : Nat} {c : Config H}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hrun : StepsN (SingleThreaded.profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.block bt body :: es))⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c')
    (ihbody : ∀ m ≤ n, ∀ cb, StepsN (SingleThreaded.profile o) host m
        ⟨s, f, vals (stk.take np).reverse ++ expression (Binaryen.BExpr.lowerList body)⟩ cb →
      (∀ c', ¬ Step (SingleThreaded.profile o) host cb c') →
      BackOut host s f (stk.take np) body cb)
    (hblk : ∀ r, EvalH host s f (stk.take np) body r → ∀ vs, r.2.2.blockVals = some vs →
      nr ≤ vs.length ∧ ∀ ws, r.2.2 = .normal ws → ws.length = nr)
    (ihes : ∀ s₁ f₁ fl vs m, m ≤ n → EvalH host s f (stk.take np) body (s₁, f₁, fl) →
      fl.blockVals = some vs →
      StepsN (SingleThreaded.profile o) host m
        ⟨s₁, f₁, vals (vs.take nr ++ stk.drop np).reverse ++
          expression (Binaryen.BExpr.lowerList es)⟩ c →
      BackOut host s₁ f₁ (vs.take nr ++ stk.drop np) es c) :
    BackOut host s f stk (.block bt body :: es) c :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.back_block_tree har hp hrun hend ihbody hblk ihes

/-- **A loop tree** (deterministic profile). -/
theorem back_loop_tree {o : SingleThreaded.GrowOracle} {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {bt : BlockType} {body es : List Binaryen.BExpr} {np nr : Nat} {c : Config H}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hrun : StepsN (SingleThreaded.profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.loop bt body :: es))⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c')
    (ihbody : ∀ m < n, ∀ cb, StepsN (SingleThreaded.profile o) host m
        ⟨s, f, vals (stk.take np).reverse ++ expression (Binaryen.BExpr.lowerList body)⟩ cb →
      (∀ c', ¬ Step (SingleThreaded.profile o) host cb c') →
      BackOut host s f (stk.take np) body cb)
    (hlp : ∀ r, EvalH host s f (stk.take np) body r →
      (∀ ws, r.2.2 = .normal ws → ws.length = nr) ∧ ∀ vs, r.2.2 = .brk 0 vs → np ≤ vs.length)
    (ihes : ∀ s₁ f₁ vs m, m < n → EvalH host s f (stk.take np) body (s₁, f₁, .normal vs) →
      StepsN (SingleThreaded.profile o) host m
        ⟨s₁, f₁, vals (vs.take nr ++ stk.drop np).reverse ++
          expression (Binaryen.BExpr.lowerList es)⟩ c →
      BackOut host s₁ f₁ (vs.take nr ++ stk.drop np) es c)
    (ihloop : ∀ s₁ f₁ vs m, m < n → EvalH host s f (stk.take np) body (s₁, f₁, .brk 0 vs) →
      StepsN (SingleThreaded.profile o) host m
        ⟨s₁, f₁, vals (vs.take np ++ stk.drop np).reverse ++
          expression (Binaryen.BExpr.lowerList (.loop bt body :: es))⟩ c →
      BackOut host s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) c) :
    BackOut host s f stk (.loop bt body :: es) c :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.back_loop_tree har hp hrun hend ihbody hlp ihes ihloop

/-- **An `if` tree** (deterministic profile). -/
theorem back_if_tree {o : SingleThreaded.GrowOracle} {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {bt : BlockType} {cnd t el es : List Binaryen.BExpr} {c : Config H}
    (hrun : StepsN (SingleThreaded.profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.if_ bt cnd t el :: es))⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c')
    (ihcond : ∀ m ≤ n, ∀ c₁, StepsN (SingleThreaded.profile o) host m
        ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList cnd)⟩ c₁ →
      (∀ c', ¬ Step (SingleThreaded.profile o) host c₁ c') → BackOut host s f stk cnd c₁)
    (hcond : ∀ s₁ f₁ stk', EvalH host s f stk cnd (s₁, f₁, .normal stk') →
      ∃ cv stk₁ b np nr, stk' = cv :: stk₁ ∧ Binaryen.truthy cv = some b ∧
        Binaryen.arity f₁ bt = some (np, nr) ∧ np ≤ stk₁.length ∧
        (∀ r, EvalH host s₁ f₁ (stk₁.take np) (if b then t else el) r →
          ∀ vs, r.2.2.blockVals = some vs → nr ≤ vs.length ∧
            ∀ ws, r.2.2 = .normal ws → ws.length = nr))
    (iharm : ∀ (s₁ : Store H) (f₁ : Frame) (cv : Val) (stk₁ : List Val) (b : Bool) (np nr : Nat)
      (m : Nat), m ≤ n → EvalH host s f stk cnd (s₁, f₁, .normal (cv :: stk₁)) →
      Binaryen.truthy cv = some b → Binaryen.arity f₁ bt = some (np, nr) → ∀ cb,
      StepsN (SingleThreaded.profile o) host m
        ⟨s₁, f₁, vals (stk₁.take np).reverse ++
          expression (Binaryen.BExpr.lowerList (if b then t else el))⟩ cb →
      (∀ c', ¬ Step (SingleThreaded.profile o) host cb c') →
      BackOut host s₁ f₁ (stk₁.take np) (if b then t else el) cb)
    (ihes : ∀ (s₁ : Store H) (f₁ : Frame) (cv : Val) (stk₁ : List Val) (b : Bool) (np nr : Nat)
      (s₂ : Store H) (f₂ : Frame) (fl : Binaryen.Flow) (vs : List Val) (m : Nat), m ≤ n →
      EvalH host s f stk cnd (s₁, f₁, .normal (cv :: stk₁)) → Binaryen.truthy cv = some b →
      Binaryen.arity f₁ bt = some (np, nr) →
      EvalH host s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl) →
      fl.blockVals = some vs →
      StepsN (SingleThreaded.profile o) host m
        ⟨s₂, f₂, vals (vs.take nr ++ stk₁.drop np).reverse ++
          expression (Binaryen.BExpr.lowerList es)⟩ c →
      BackOut host s₂ f₂ (vs.take nr ++ stk₁.drop np) es c) :
    BackOut host s f stk (.if_ bt cnd t el :: es) c :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.back_if_tree hrun hend ihcond hcond iharm ihes

/-- **A direct call of a Wasm function** (deterministic profile). -/
theorem back_call_wasm {o : SingleThreaded.GrowOracle} {n : Nat} {s₁ : Store H} {f₁ : Frame}
    {stk₁ : List Val} {x : FuncIdx} {a : Nat} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} {rest : List Admin} {c : Config H}
    (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hp : ps.length ≤ stk₁.length)
    (hrun : StepsN (SingleThreaded.profile o) host n
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: rest⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c')
    (ihbody : ∀ m < n, ∀ cb, StepsN (SingleThreaded.profile o) host m
        ⟨s₁, Interp.calleeFrame fi fn stk₁ ps.length,
          vals ([] : List Val).reverse ++
            expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body))⟩ cb →
      (∀ c', ¬ Step (SingleThreaded.profile o) host cb c') →
      BackOut host s₁ (Interp.calleeFrame fi fn stk₁ ps.length) [] (Binaryen.liftInstrs fn.body) cb)
    (hret : ∀ r, EvalH host s₁ (Interp.calleeFrame fi fn stk₁ ps.length) []
        (Binaryen.liftInstrs fn.body) r →
      (∀ vs, r.2.2.retVals = some vs →
        rs.length ≤ vs.length ∧ ∀ ws, r.2.2 = .normal ws → ws.length = rs.length) ∧
      (r.2.2.retVals = none → r.2.2 = .trap)) :
    Pending host c.store c.code ∨
      ∃ s₂ fl, hostCall host s₁ a (stk₁.take ps.length).reverse (s₂, fl) ∧
        ((∃ vs m, m < n ∧ fl.retVals = some vs ∧
            StepsN (SingleThreaded.profile o) host m
              ⟨s₂, f₁, vals (vs.take rs.length ++ stk₁.drop ps.length).reverse ++ rest⟩ c) ∨
          (fl = .trap ∧ EndsAs (s₂, f₁, .trap) c)) :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.back_call_wasm hfi hcode hty hp hrun hend ihbody hret

/-- **A direct call as a tree**, for any callee (deterministic profile). -/
theorem back_op_call {o : SingleThreaded.GrowOracle} {n : Nat} {s : Store H} {f : Frame}
    {stk : List Val} {x : FuncIdx} {args es : List Binaryen.BExpr} {c : Config H}
    (hrun : StepsN (SingleThreaded.profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.op (.call x) args :: es))⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c')
    (ihargs : ∀ m ≤ n, ∀ c₁, StepsN (SingleThreaded.profile o) host m
        ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args)⟩ c₁ →
      (∀ c', ¬ Step (SingleThreaded.profile o) host c₁ c') → BackOut host s f stk args c₁)
    (hcase : ∀ s₁ f₁ stk₁ m, m ≤ n → EvalH host s f stk args (s₁, f₁, .normal stk₁) →
      StepsN (SingleThreaded.profile o) host m
        ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: expression (Binaryen.BExpr.lowerList es)⟩ c →
      Pending host c.store c.code ∨
        ∃ (a : Nat) (fi : FuncInst H) (ps rs : List Validation.CValType) (s₂ : Store H)
          (fl : Binaryen.Flow), s₁.func? f₁ x = some (a, fi) ∧
          Validation.DefType.funcType? fi.type = some (ps, rs) ∧
          hostCall host s₁ a (stk₁.take ps.length).reverse (s₂, fl) ∧
          ((∃ vs m', m' ≤ n ∧ fl.retVals = some vs ∧
              StepsN (SingleThreaded.profile o) host m'
                ⟨s₂, f₁, vals (vs.take rs.length ++ stk₁.drop ps.length).reverse ++
                  expression (Binaryen.BExpr.lowerList es)⟩ c) ∨
            (fl = .trap ∧ EndsAs (s₂, f₁, .trap) c)))
    (ihes : ∀ (s₁ : Store H) (f₁ : Frame) (stk₁ : List Val) (a : Nat) (fi : FuncInst H)
      (ps rs : List Validation.CValType) (s₂ : Store H) (fl : Binaryen.Flow) (vs : List Val)
      (m : Nat), m ≤ n → EvalH host s f stk args (s₁, f₁, .normal stk₁) →
      s₁.func? f₁ x = some (a, fi) → Validation.DefType.funcType? fi.type = some (ps, rs) →
      hostCall host s₁ a (stk₁.take ps.length).reverse (s₂, fl) → fl.retVals = some vs →
      StepsN (SingleThreaded.profile o) host m
        ⟨s₂, f₁, vals (vs.take rs.length ++ stk₁.drop ps.length).reverse ++
          expression (Binaryen.BExpr.lowerList es)⟩ c →
      BackOut host s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es c) :
    BackOut host s f stk (.op (.call x) args :: es) c :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.back_op_call hrun hend ihargs hcase ihes

/-- **The whole-run backward simulation with host calls** (deterministic profile
`profile o`). -/
theorem back_whole {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {n : Nat} {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {labels : List Nat} {ret : Nat} {out : Option Nat} {c : Config H}
    (hS : Interp.StoreChk s.funcs)
    (hc : Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out)
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩)
    (hrun : StepsN (SingleThreaded.profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c') :
    BackOut host s f stk es c :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.back_whole hT hH n es s f stk labels ret out c hS hc ht
    hrun hend

/-- `back_whole` for an uncounted Core run. -/
theorem back_whole_steps {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {labels : List Nat} {ret : Nat} {out : Option Nat} {c : Config H}
    (hS : Interp.StoreChk s.funcs)
    (hc : Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out)
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩)
    (hrun : Steps (SingleThreaded.profile o) host
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c') :
    BackOut host s f stk es c := by
  obtain ⟨n, hn⟩ := stepsN_of_steps hrun
  exact back_whole hT hH hS hc ht hn hend

/-- **A blocked host call is stuck**, in any frame and profile. -/
theorem pending_stuck {P : Silmaril.Wasm.Numerics.Profile} {s : Store H} {es : List Admin}
    (hp : Pending host s es) (f : Frame) (c : Config H) : ¬ Step P host ⟨s, f, es⟩ c :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.pending_stuck hp f c

/-- **A host call the host may diverge on makes Core diverge**, in any frame and profile. -/
theorem pendingDiv_diverges {P : Silmaril.Wasm.Numerics.Profile} {s : Store H} {f : Frame}
    {es : List Admin} (hp : PendingDiv host s es) : Diverges P host ⟨s, f, es⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.pendingDiv_diverges hp

/-- The end of a native run is stuck. -/
theorem endsAs_stuck {P : Silmaril.Wasm.Numerics.Profile} {r : Store H × Frame × Binaryen.Flow}
    {c : Config H} (h : EndsAs r c) : ∀ c', ¬ Step P host c c' :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.endsAs_stuck h

/-- **The stuck ends of a Core run of typed native code** (deterministic profile):
exactly the ends of `EvalH` runs and the blocked host calls. -/
theorem stuck_iff {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {n : Nat} {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {labels : List Nat} {ret : Nat} {out : Option Nat} {c : Config H}
    (hS : Interp.StoreChk s.funcs)
    (hc : Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out)
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩)
    (hrun : StepsN (SingleThreaded.profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ c) :
    (∀ c', ¬ Step (SingleThreaded.profile o) host c c') ↔ BackOut host s f stk es c :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.stuck_iff hT hH hS hc ht hrun

/-- **The backward simulation of an invocation** (deterministic profile). -/
theorem back_invoke {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {n : Nat} {s : Store H} {a : Nat} {vs : List Val}
    {c : Config H} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hrun : StepsN (SingleThreaded.profile o) host n (invoke s a vs) c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c') :
    Pending host c.store c.code ∨
      ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (s₂ : Store H) (fl : Binaryen.Flow),
        s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        hostCall host s a vs (s₂, fl) ∧
        ((∃ ws, fl.retVals = some ws ∧ c = ⟨s₂, {}, vals (ws.take rs.length).reverse⟩) ∨
          (fl = .trap ∧ c = ⟨s₂, {}, [.trap]⟩)) :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.back_invoke hT hH hs hS hok hrun hend

/-- **The backward simulation of an invocation, every profile**, for native-profile Wasm
functions and a host satisfying `Interp.HostNative`. -/
theorem back_invoke_profile {P : Silmaril.Wasm.Numerics.Profile} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) (hN : Interp.HostNative host) {n : Nat} {s : Store H}
    {a : Nat} {vs : List Val} {c : Config H} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hW : Interp.NativeWasmFuncs s.funcs) (hok : InvokeOk s a vs)
    (hrun : StepsN P host n (invoke s a vs) c) (hend : ∀ c', ¬ Step P host c c') :
    Pending host c.store c.code ∨
      ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (s₂ : Store H) (fl : Binaryen.Flow),
        s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        hostCall host s a vs (s₂, fl) ∧
        ((∃ ws, fl.retVals = some ws ∧ c = ⟨s₂, {}, vals (ws.take rs.length).reverse⟩) ∨
          (fl = .trap ∧ c = ⟨s₂, {}, [.trap]⟩)) :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.back_invoke_profile hT hH hN hs hS hW hok hrun hend

/-- `back_invoke_profile` for an uncounted run. -/
theorem back_invoke_steps_profile {P : Silmaril.Wasm.Numerics.Profile} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) (hN : Interp.HostNative host) {s : Store H}
    {a : Nat} {vs : List Val} {c : Config H} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hW : Interp.NativeWasmFuncs s.funcs) (hok : InvokeOk s a vs)
    (hrun : Steps P host (invoke s a vs) c) (hend : ∀ c', ¬ Step P host c c') :
    Pending host c.store c.code ∨
      ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (s₂ : Store H) (fl : Binaryen.Flow),
        s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        hostCall host s a vs (s₂, fl) ∧
        ((∃ ws, fl.retVals = some ws ∧ c = ⟨s₂, {}, vals (ws.take rs.length).reverse⟩) ∨
          (fl = .trap ∧ c = ⟨s₂, {}, [.trap]⟩)) :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.back_invoke_steps_profile hT hH hN hs hS hW hok hrun hend

/-- **At a host call with no outcome, Core is blocked.** -/
theorem atCall_pending {s : Store H} {a : Nat} {us : List Val} {es : List Admin}
    {fi : FuncInst H} {hh : H} {ps rs : Validation.Ty (.list .val)}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (he : Validation.Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (hno : ∀ o, ¬ host hh s us o) (h : AtCall s a us es) : Pending host s es :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.atCall_pending hf hcode he hn hno h

/-- **At a host call the host may diverge on, Core diverges.** -/
theorem atCall_pendingDiv {s : Store H} {a : Nat} {us : List Val} {es : List Admin}
    {fi : FuncInst H} {hh : H} {ps rs : Validation.Ty (.list .val)}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (he : Validation.Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (hdiv : host hh s us .diverged) (h : AtCall s a us es) : PendingDiv host s es :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.atCall_pendingDiv hf hcode he hn hdiv h

/-- **Forward reachability of a call**, every profile. -/
theorem reach_atCall {P : Silmaril.Wasm.Numerics.Profile} (hH : Interp.NativeHostSlice host)
    {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {y : (wasmOShape H).self.Op} {labels : List Nat} {ret : Nat} {out : Option Nat}
    (hr : ReachO (hostCall host) s f stk es y) (hS : Interp.StoreChk s.funcs)
    (hc : Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out) :
    ∃ (f' : Frame) (c : List Admin),
      Steps P host ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩
        ⟨y.2.2, f', c⟩ ∧ AtCall y.2.2 y.1 y.2.1 c :=
  let ⟨f', c, h, hat, _⟩ := Silmaril.Proofs.Wasm.Abstract.HostEval.reach_atCall (P := P) hH hr hS hc
  ⟨f', c, h, hat⟩

/-- **A pending call of an invocation is reached in Core**, every profile. -/
theorem invoke_pendO_atCall {P : Silmaril.Wasm.Numerics.Profile} (hH : Interp.NativeHostSlice host)
    {s : Store H} {a : Nat} {vs : List Val} {y : (wasmOShape H).self.Op}
    (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hp : PendO (hostCall host) ⟨a, (vs, s)⟩ y) :
    ∃ (f' : Frame) (c : List Admin),
      Steps P host (invoke s a vs) ⟨y.2.2, f', c⟩ ∧ AtCall y.2.2 y.1 y.2.1 c :=
  let ⟨f', c, h, hat, _⟩ :=
    Silmaril.Proofs.Wasm.Abstract.HostEval.invoke_pendO_atCall (P := P) hH hS hok hp
  ⟨f', c, h, hat⟩

/-- **A pending host call with no outcome is a reachable blocked configuration**,
every profile. -/
theorem invoke_pendO_blocked {P : Silmaril.Wasm.Numerics.Profile} (hH : Interp.NativeHostSlice host)
    {s : Store H} {a : Nat} {vs : List Val} {y : (wasmOShape H).self.Op}
    (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hp : PendO (hostCall host) ⟨a, (vs, s)⟩ y) {fi : FuncInst H} {hh : H}
    (hf : y.2.2.funcs[y.1]? = some fi) (hcode : fi.code = .host hh)
    (hno : ∀ o, ¬ host hh y.2.2 y.2.1 o) :
    ∃ c : Config H, Steps P host (invoke s a vs) c ∧ Pending host c.store c.code ∧
      ∀ c', ¬ Step P host c c' :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.invoke_pendO_blocked hH hS hok hp hf hcode hno

/-- **A pending host call the host may diverge on makes the invocation diverge**,
every profile. -/
theorem invoke_pendO_diverges {P : Silmaril.Wasm.Numerics.Profile} (hH : Interp.NativeHostSlice host)
    {s : Store H} {a : Nat} {vs : List Val} {y : (wasmOShape H).self.Op}
    (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    (hp : PendO (hostCall host) ⟨a, (vs, s)⟩ y) {fi : FuncInst H} {hh : H}
    (hf : y.2.2.funcs[y.1]? = some fi) (hcode : fi.code = .host hh)
    (hdiv : host hh y.2.2 y.2.1 .diverged) : Diverges P host (invoke s a vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostEval.invoke_pendO_diverges hH hS hok hp hf hcode hdiv

end Silmaril.Wasm.Abstract
