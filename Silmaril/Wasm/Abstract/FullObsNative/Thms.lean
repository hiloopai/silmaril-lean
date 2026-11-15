module

public import Silmaril.Wasm.Abstract.FullObsNative.Defs
public import Silmaril.Wasm.Abstract.StoreCall.Thms
public import Silmaril.Wasm.Abstract.DivO.Thms
public import Silmaril.Wasm.Abstract.HostEval.Thms
import Silmaril.Proofs.Wasm.Abstract.FullObsNative.Obs

/-!
# Full observations of the exposed native body, filtered by an oracle: theorems

`obsC C es f stk` (Defs) is `FullObs.toFull` of the exposed native body `StoreCall.denListE es f stk`,
both parts filtered by the oracle `C`. For **any** oracle `C` (no functionality or totality):

* **Finite part.** `obsC_ret_iff`, `obsC_trap_iff`: the filtered finished behaviours are exactly the
  `EvalO C` outcomes (`StoreCall.evalO_iff`, `StoreCall.evalO_trap_iff`, read through
  `BodyTrace.toAFun`: paths lifted by `liftCall`/`endOf`). `mem_obsC_fin`, `mem_obsC_inf`,
  `obsC_div_iff`, `obsC_inf_iff` read `obsC` as answered paths and runs of the tree.
* **Local divergence.** `exposed_of_localDivO`: a problem that diverges within its function
  (`LocalDivO C`, every call it makes answered by `C`) has a silent path after `C`-answered calls
  (`.div`) or an infinite `C`-answered run (`InfPath`). The proof follows the witness of
  `LocalDivO` (the oracle may be nondeterministic, so `StoreCall`'s closed-oracle argument does
  not apply); a loop iterating silently forever runs to `diverge` by Elgot uniformity.
  `localDivO_of_infPath`: conversely, an infinite `C`-answered run is local divergence.
  In observation form: `localDivO_obsC`, `localDivO_of_obsC_inf`.
* **The silent half is not exact.** A `.div` path of `denListE` is silent divergence *or* a stuck
  configuration (`stuck` is `diverge`: an operand `evalFlat` rejects, an unresolved callee, an
  answer with no return values, `try_table`, a missing arity). So `.div` paths are not
  `LocalDivO C` in general: `tryTable_silent` is a counterexample at every oracle and state. The
  exact statement is therefore: local divergence ⇒ silent or productive (`exposed_of_localDivO`),
  productive ⇒ local divergence (`localDivO_of_infPath`), and `localDivO_iff_of_silent`: wherever
  the silent paths are local divergence, `LocalDivO C` is exactly "silent or productive".
* **Calls.** `localCallDivO_obsC`, `localCallDivO_of_obsC`: `LocalCallDivO C` on the filtered
  observation of the callee's body.

**H2** (`C = hostCall host`, the native semantics with host calls; no coincidence with the
EH/pending-tail `denXP`/`EvalOXP` is assumed or used):

* `evalH_iff_obs`, `evalH_trap_iff_obs`: the finite part is the H2 native semantics `EvalH host`;
* `localDivO_host_obsC`, `localDivO_host_of_obsC_inf`: local divergence `LocalDivO (hostCall host)`;
* invocation bodies: `hostCall_wasm_iff`, `hostCall_iff_obs`, `hostCall_trap_iff_obs` (the H2
  callee relation on a Wasm function is its filtered body observation, as `EvalH`), and
  `localCallDivO_host_obsC`, `localCallDivO_host_of_obsC` (the `LocalCallDivO (hostCall host)`
  targets of `HostEval.invoke_div_decomp`).
-/

public section

namespace Silmaril.Wasm.Abstract.FullObsNative

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall

variable {H : Type}

/-! ## Reading the observation -/

/-- Filtered finished behaviours are answered finished paths. -/
theorem mem_obsC_fin {C : CallRel H} {es : List BExpr} {f : Frame} {stk : List Val} {s : Store H}
    {x : CallBeh (liftSig (CallSig H)) (St H) Res} :
    x ∈ (obsC C es f stk).1 ⟨s⟩ ⟨⟩ ↔
      ∃ cs r, Answered C cs ∧ Path (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) cs r ∧
        x = (cs.map liftCall, endOf r) :=
  Silmaril.Proofs.Wasm.Abstract.FullObsNative.mem_obsC_fin

/-- Filtered productive runs are answered infinite runs. -/
theorem mem_obsC_inf {C : CallRel H} {es : List BExpr} {f : Frame} {stk : List Val} {s : Store H}
    {ω : Nat → Call (liftSig (CallSig H))} :
    ω ∈ (obsC C es f stk).2 ⟨s⟩ ⟨⟩ ↔
      ∃ ω', AnsweredS C ω' ∧ InfPath (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) ω' ∧
        ω = liftCall ∘ ω' :=
  Silmaril.Proofs.Wasm.Abstract.FullObsNative.mem_obsC_inf

/-- Filtered silent ends are answered silent paths. -/
theorem obsC_div_iff {C : CallRel H} {es : List BExpr} {f : Frame} {stk : List Val} {s : Store H} :
    (∃ c, (c, End.div) ∈ (obsC C es f stk).1 ⟨s⟩ ⟨⟩) ↔
      ∃ cs, Answered C cs ∧ Path (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) cs .div :=
  Silmaril.Proofs.Wasm.Abstract.FullObsNative.obsC_div_iff

/-- The filtered observation is productive exactly when the tree has an answered infinite run. -/
theorem obsC_inf_iff {C : CallRel H} {es : List BExpr} {f : Frame} {stk : List Val} {s : Store H} :
    (∃ ω, ω ∈ (obsC C es f stk).2 ⟨s⟩ ⟨⟩) ↔
      ∃ ω, AnsweredS C ω ∧ InfPath (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) ω :=
  Silmaril.Proofs.Wasm.Abstract.FullObsNative.obsC_inf_iff

/-! ## The finite part -/

/-- **Finite part, values.** The filtered finished behaviours ending in a non-trap flow are
exactly the `EvalO C` outcomes, final store and frame included. -/
theorem obsC_ret_iff {C : CallRel H} {es : List BExpr} {f : Frame} {stk : List Val} {s s' : Store H}
    {f' : Frame} {fl : Flow} (hfl : fl ≠ .trap) :
    (∃ c, (c, End.ret ⟨(f', fl)⟩ ⟨s'⟩) ∈ (obsC C es f stk).1 ⟨s⟩ ⟨⟩) ↔
      EvalO C s f stk es (s', f', fl) :=
  Silmaril.Proofs.Wasm.Abstract.FullObsNative.obsC_ret_iff hfl

/-- **Finite part, traps.** -/
theorem obsC_trap_iff {C : CallRel H} {es : List BExpr} {f : Frame} {stk : List Val} {s : Store H} :
    (∃ c, (c, End.trap) ∈ (obsC C es f stk).1 ⟨s⟩ ⟨⟩) ↔
      ∃ s' f', EvalO C s f stk es (s', f', .trap) :=
  Silmaril.Proofs.Wasm.Abstract.FullObsNative.obsC_trap_iff

/-! ## Local divergence -/

/-- **Local divergence is silent divergence after answered calls, or an infinite answered run**,
any oracle. -/
theorem exposed_of_localDivO {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} (h : LocalDivO C s f stk es) :
    (∃ cs, Answered C cs ∧ Path (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) cs .div) ∨
      ∃ ω, AnsweredS C ω ∧ InfPath (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) ω :=
  Silmaril.Proofs.Wasm.Abstract.FullObsNative.exposed_of_localDivO h

/-- **Productive local divergence**, any oracle: an infinite run with every call answered by `C`
is local divergence. -/
theorem localDivO_of_infPath {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {ω : Nat → Call (CallSig H)} (hA : AnsweredS C ω)
    (h : InfPath (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) ω) :
    LocalDivO C s f stk es :=
  Silmaril.Proofs.Wasm.Abstract.FullObsNative.localDivO_of_prod ⟨ω, hA, h⟩

/-- **Silent paths are not local divergence in general**: `try_table` is stuck (`diverge`), at
every oracle, store, frame and stack. -/
theorem tryTable_silent {C : CallRel H} (bt : BlockType) (cs : List Catch) (body : List BExpr)
    (s : Store H) (f : Frame) (stk : List Val) :
    Path (((denListE [.tryTable bt cs body] f stk : M (CallSig H) H Res).run ⟨s⟩).run) [] .div ∧
      ¬ LocalDivO C s f stk [.tryTable bt cs body] :=
  Silmaril.Proofs.Wasm.Abstract.FullObsNative.tryTable_silent bt cs body s f stk

/-- **Exactness where silent paths diverge.** If every answered silent path of the problem is
local divergence (e.g. no stuck configuration is reachable), local divergence is exactly silent
divergence after answered calls or an infinite answered run. -/
theorem localDivO_iff_of_silent {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr}
    (hsil : (∃ cs, Answered C cs ∧
      Path (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) cs .div) →
        LocalDivO C s f stk es) :
    LocalDivO C s f stk es ↔
      (∃ cs, Answered C cs ∧ Path (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) cs .div) ∨
        ∃ ω, AnsweredS C ω ∧ InfPath (((denListE es f stk : M (CallSig H) H Res).run ⟨s⟩).run) ω :=
  ⟨exposed_of_localDivO, fun h => h.elim hsil fun ⟨_, hA, hp⟩ => localDivO_of_infPath hA hp⟩

/-- Local divergence on the filtered observation: a silent end or a productive run. -/
theorem localDivO_obsC {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    (h : LocalDivO C s f stk es) :
    (∃ c, (c, End.div) ∈ (obsC C es f stk).1 ⟨s⟩ ⟨⟩) ∨ ∃ ω, ω ∈ (obsC C es f stk).2 ⟨s⟩ ⟨⟩ :=
  (exposed_of_localDivO h).imp obsC_div_iff.2 obsC_inf_iff.2

/-- A productive filtered run is local divergence. -/
theorem localDivO_of_obsC_inf {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {ω : Nat → Call (liftSig (CallSig H))} (h : ω ∈ (obsC C es f stk).2 ⟨s⟩ ⟨⟩) :
    LocalDivO C s f stk es :=
  let ⟨_, hA, hp, _⟩ := mem_obsC_inf.1 h; localDivO_of_infPath hA hp

/-- **Local divergence of a call**, on the filtered observation of its body. -/
theorem localCallDivO_obsC {C : CallRel H} {z : (wasmOShape H).self.Op} (h : LocalCallDivO C z) :
    ∃ (fi : FuncInst H) (fn : Func), z.2.2.funcs[z.1]? = some fi ∧ fi.code = .wasm fn ∧
      ((∃ c, (c, End.div) ∈
          (obsC C (liftInstrs fn.body) (Frame.forCall fi.module z.2.1 fn.locals) []).1 ⟨z.2.2⟩ ⟨⟩) ∨
        ∃ ω, ω ∈
          (obsC C (liftInstrs fn.body) (Frame.forCall fi.module z.2.1 fn.locals) []).2 ⟨z.2.2⟩ ⟨⟩) :=
  Silmaril.Proofs.Wasm.Abstract.FullObsNative.localCallDivO_obsC h

/-- A productive filtered run of a Wasm callee's body is local divergence of the call. -/
theorem localCallDivO_of_obsC {C : CallRel H} {z : (wasmOShape H).self.Op}
    (h : ∃ (fi : FuncInst H) (fn : Func), z.2.2.funcs[z.1]? = some fi ∧ fi.code = .wasm fn ∧
      ∃ ω, ω ∈
        (obsC C (liftInstrs fn.body) (Frame.forCall fi.module z.2.1 fn.locals) []).2 ⟨z.2.2⟩ ⟨⟩) :
    LocalCallDivO C z :=
  Silmaril.Proofs.Wasm.Abstract.FullObsNative.localCallDivO_of_obsC h

/-! ## H2: the native semantics with host calls -/

/-- **H2, values**: the finite part at the H2 oracle is `EvalH host`. -/
theorem evalH_iff_obs {host : HostSemantics H} {es : List BExpr} {f : Frame} {stk : List Val}
    {s s' : Store H} {f' : Frame} {fl : Flow} (hfl : fl ≠ .trap) :
    EvalH host s f stk es (s', f', fl) ↔
      ∃ c, (c, End.ret ⟨(f', fl)⟩ ⟨s'⟩) ∈ (obsC (hostCall host) es f stk).1 ⟨s⟩ ⟨⟩ :=
  (obsC_ret_iff hfl).symm

/-- **H2, traps.** -/
theorem evalH_trap_iff_obs {host : HostSemantics H} {es : List BExpr} {f : Frame} {stk : List Val}
    {s : Store H} :
    (∃ s' f', EvalH host s f stk es (s', f', .trap)) ↔
      ∃ c, (c, End.trap) ∈ (obsC (hostCall host) es f stk).1 ⟨s⟩ ⟨⟩ :=
  obsC_trap_iff.symm

/-- **H2 local divergence**: a silent end or a productive run of the filtered observation. -/
theorem localDivO_host_obsC {host : HostSemantics H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} (h : LocalDivO (hostCall host) s f stk es) :
    (∃ c, (c, End.div) ∈ (obsC (hostCall host) es f stk).1 ⟨s⟩ ⟨⟩) ∨
      ∃ ω, ω ∈ (obsC (hostCall host) es f stk).2 ⟨s⟩ ⟨⟩ :=
  localDivO_obsC h

/-- **H2 productive local divergence.** -/
theorem localDivO_host_of_obsC_inf {host : HostSemantics H} {s : Store H} {f : Frame}
    {stk : List Val} {es : List BExpr} {ω : Nat → Call (liftSig (CallSig H))}
    (h : ω ∈ (obsC (hostCall host) es f stk).2 ⟨s⟩ ⟨⟩) : LocalDivO (hostCall host) s f stk es :=
  localDivO_of_obsC_inf h

/-- The H2 callee relation on a Wasm function: its body, run by `EvalH`. -/
theorem hostCall_wasm_iff {host : HostSemantics H} {s : Store H} {a : Nat} {us : List Val}
    {fi : FuncInst H} {fn : Func} (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    {out : Store H × Flow} :
    hostCall host s a us out ↔
      ∃ ps rs f₂, Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        EvalH host s (Frame.forCall fi.module us fn.locals) [] (liftInstrs fn.body)
          (out.1, f₂, out.2) :=
  Silmaril.Proofs.Wasm.Abstract.FullObsNative.hostCall_wasm_iff hfi hcode

/-- **H2 invocation bodies, values**: the H2 callee relation on a Wasm function is the filtered
observation of its body. -/
theorem hostCall_iff_obs {host : HostSemantics H} {s : Store H} {a : Nat} {us : List Val}
    {fi : FuncInst H} {fn : Func} (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    {s' : Store H} {fl : Flow} (hfl : fl ≠ .trap) :
    hostCall host s a us (s', fl) ↔
      ∃ ps rs f₂, Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        ∃ c, (c, End.ret ⟨(f₂, fl)⟩ ⟨s'⟩) ∈
          (obsC (hostCall host) (liftInstrs fn.body) (Frame.forCall fi.module us fn.locals) []).1
            ⟨s⟩ ⟨⟩ :=
  Silmaril.Proofs.Wasm.Abstract.FullObsNative.hostCall_iff_obs hfi hcode hfl

/-- **H2 invocation bodies, traps.** -/
theorem hostCall_trap_iff_obs {host : HostSemantics H} {s : Store H} {a : Nat} {us : List Val}
    {fi : FuncInst H} {fn : Func} (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn) :
    (∃ s', hostCall host s a us (s', .trap)) ↔
      ∃ ps rs, Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        ∃ c, (c, End.trap) ∈
          (obsC (hostCall host) (liftInstrs fn.body) (Frame.forCall fi.module us fn.locals) []).1
            ⟨s⟩ ⟨⟩ :=
  Silmaril.Proofs.Wasm.Abstract.FullObsNative.hostCall_trap_iff_obs hfi hcode

/-- **H2 invocation bodies, local divergence**: the `LocalCallDivO (hostCall host)` targets of
`HostEval.invoke_div_decomp`, on the filtered observation of the callee's body. -/
theorem localCallDivO_host_obsC {host : HostSemantics H} {z : (wasmOShape H).self.Op}
    (h : LocalCallDivO (hostCall host) z) :
    ∃ (fi : FuncInst H) (fn : Func), z.2.2.funcs[z.1]? = some fi ∧ fi.code = .wasm fn ∧
      ((∃ c, (c, End.div) ∈ (obsC (hostCall host) (liftInstrs fn.body)
          (Frame.forCall fi.module z.2.1 fn.locals) []).1 ⟨z.2.2⟩ ⟨⟩) ∨
        ∃ ω, ω ∈ (obsC (hostCall host) (liftInstrs fn.body)
          (Frame.forCall fi.module z.2.1 fn.locals) []).2 ⟨z.2.2⟩ ⟨⟩) :=
  localCallDivO_obsC h

/-- **H2 invocation bodies, productive local divergence.** -/
theorem localCallDivO_host_of_obsC {host : HostSemantics H} {z : (wasmOShape H).self.Op}
    (h : ∃ (fi : FuncInst H) (fn : Func), z.2.2.funcs[z.1]? = some fi ∧ fi.code = .wasm fn ∧
      ∃ ω, ω ∈ (obsC (hostCall host) (liftInstrs fn.body)
        (Frame.forCall fi.module z.2.1 fn.locals) []).2 ⟨z.2.2⟩ ⟨⟩) :
    LocalCallDivO (hostCall host) z :=
  localCallDivO_of_obsC h

end Silmaril.Wasm.Abstract.FullObsNative
