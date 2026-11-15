module

public import Silmaril.Wasm.Interp.Defs
public import Silmaril.Proofs.Wasm.Interp.Straight
public import Silmaril.Proofs.Wasm.Interp.Trap
public import Silmaril.Proofs.Wasm.Interp.Div
public import Silmaril.Proofs.Wasm.Interp.Check
public import Silmaril.Proofs.Wasm.Interp.Replace
public import Silmaril.Proofs.Wasm.Interp.Store
public import Silmaril.Proofs.Wasm.Interp.CallFrame
public import Silmaril.Proofs.Wasm.Interp.HostOracle
public import Silmaril.Proofs.Wasm.Interp.FuncsExt
public import Silmaril.Proofs.Wasm.Interp.Tail
public import Silmaril.Proofs.Wasm.Interp.ProfileHost

@[expose] public section

/-!
# The native Binaryen interpreter against Core 3.0: results

**Checked flat instructions** (`flat_core_normal`, `flat_core_abrupt`): public forms of
`steps_flat_normal`/`wp_flat_abrupt` for clients outside `Interp`.

Proofs in `Silmaril.Proofs.Wasm.Interp.{Straight,Trap,Profile,Arity,Control,Invoke,Obligations,Lag,
Termination,Progress,Total,Div,Check,Replace}`.

**Forward simulation for straight-line integer code, every profile and host.** For trees of
straight-line integer instructions with in-range local writes (`BExpr.straightList`):

* `exec_of_eval`: a normal native evaluation (`Binaryen.Eval`) is the straight-line Core
  evaluation `Silmaril.Wasm.Logic.Core.exec` of the lowering;
* `steps_of_eval`, `steps_of_run`: a normal native evaluation, or a terminating run of the fuel
  interpreter `Binaryen.run`, is a Core 3.0 run `Steps P host` of the lowered code, from the
  same store and frame, for **every** profile `P` and host `host`, the native top-first stack
  being the reversed Core operand stack;
* `steps_trap_of_eval`, `steps_trap_of_run`: a native evaluation or run ending in a trap
  (division/remainder by zero, signed overflow) is a Core 3.0 run of the lowered code, in any
  code context `rest`, to `[trap]`, every profile and host.

**Pending tail calls** (`Silmaril.Proofs.Wasm.Interp.Tail`, checker step 4). `MatchT P host n r`
is `Match r`, a pending tail call `.tail vs a c` that ends as `r` does (`TailRun`: in every
outer frame the callee returns `r`'s top `n` return values, or traps, in `r`'s store), or a
pending tail call of a null reference `.tailNull vs c`, which traps at the frame
(`return_call_ref-frame-null`, `frame_tailNull`), so ends as a trapping `r` in the same store. The
invariant `CoreGoodQ ext P host M` takes the postcondition per return arity; `CoreGoodE` is
`M = Match` (unchanged), `CoreGoodT` is `M = MatchT`. On results that neither return nor trap
the two agree (`matchT_eq_match`, `core_of_coreT`); the continuation cases (`core_opOk`,
`core_callOk`, `core_blockOk`, `core_loopOk`, `core_loopBack`, `core_ifOk`) hold for any `M`;
the abrupt cases have `MatchT` versions (`coreT_argsAbort`, `coreT_blockAbrupt`,
`coreT_loopAbrupt`, `coreT_ifAbrupt`, `coreT_ifAbort`), a pending tail leaving labels by
`return_call_ref-label`; and calls whose callee body ends in a tail call (`coreT_callOk`,
`coreT_callTrap`, through `funcPost_of_tailRun` and `frame_ends`). The tail rules of a
derivation (producing `TailRun`) are not here.

**Call oracles and host calls** (`Silmaril.Proofs.Wasm.Interp.OracleSim`, `HostOracle`).
`evalO_good`: with a sound oracle (`OracleSound`: answers keep the store's functions, return at
the callee's arity, and are Core runs of `call_ref` in any frame), every
`Abstract.EvalO C` run of arity-checked code is a Core 3.0 run. `hostCall_sound`,
`evalH_good`: the host-call oracle `Abstract.hostCall host` is sound for hosts in the
**native host slice** `NativeHostSlice`, so every `Abstract.EvalH host` run is a Core run with
that host, every profile. The slice: answers extend the functions as Core's `Extend` does
(`FuncsGood`: existing addresses keep their functions, appended ones are native and pass the
check), values at the declared result arity, no exceptions. The native arity invariant
`EvalInv` is stated up to this extension (`chk_inv`, `storeChk_inv`, `nativeFuncsOk_inv`).

**Checker extensions** (`Silmaril.Wasm.Interp.Defs`: `ExtArity`, `chkE`; proofs in `Arity`,
`Control`, `OracleSim`). The arity and Core-run invariants and their case lemmas hold for every
extension `ext` that is stable under function extension (`ExtStable`): `ArityGoodE ext`,
`CoreGoodE ext`, the `arity_*`/`core_*`/`arityO_*`/`coreO_*` lemmas, and `evalO_goodE`. The
native forms (`ArityGood`, `CoreGood`, `evalO_good`) are the `noExt` instances.
`chkE_of_chk`: the native check implies every extended check. `flatChkE_eq_flatChk`: off the
five non-native call forms, every extension is the native check.

**Memory** (`Silmaril.Proofs.Wasm.Interp.Memory`). Native unpacked integer `load`/`store`
are Core 3.0 `MemoryStep`s, through silmaril-lean's executable `Exec.Mem.loadInt`/`storeInt`
(`load_exec`, `store_exec`): normal results with the same store update (`steps_mem_normal`),
and traps exactly out of bounds (`steps_mem_abrupt`). Typed progress covers them
(`interp_load`, `interp_store`). So every theorem below holds with memory accesses in the
native profile; `Silmaril.Wasm.Interp.MemExample` checks the hypotheses on a module with a
memory.

**Profile independence** (`Silmaril.Proofs.Wasm.Interp.Profile`). `NAdmins` (native-profile code:
silmaril-lean's `instrInNativeProfile` instructions, constants of any type, references and traps,
through labels, handlers and frames) with `Binaryen.NativeFuncsOk` on the store is closed under
Core steps of every profile and host, and the store's functions never change
(`nAdmins_step`, `NConfig.steps`). On such configurations a step at one profile is a step at
every other (`step_profile`): only the numeric, vector, table and memory rules mention the
profile, and the integer `NumericStep` rules have no profile premise. Hence runs, divergence,
normal forms and behaviours are profile-independent (`steps_profile_iff`,
`diverges_profile_iff`, `core_behaviours_profile`), and closed-host normal forms reachable from a
native configuration are unique at every profile (`eq_of_steps_nf`, transferred from
silmaril-lean's deterministic-profile `eq_of_steps_of_nf`).

**Profile independence with host functions** (`Silmaril.Proofs.Wasm.Interp.ProfileHost`). The
store may contain host functions when its Wasm functions are native-profile code
(`NativeWasmFuncs`; `StoreChk` does not imply it) and the host satisfies the explicit side
condition `HostNative` (answers keep `NativeWasmFuncs` and never throw). Then `NHConfig` is closed
under Core steps of every profile (`nAdmins_stepH`, `NHConfig.steps`), and with `step_profile`
runs and divergence are the same at every profile (`steps_profileH`, `diverges_profileH`).

**Forward simulation with structured control and calls, every profile and host.** For trees
of straight-line integer operators, `select`, `unreachable`, blocks, loops, `if`, `br`, `br_if`,
`br_table`, `return` and direct calls that pass the arity check `chk`, in a store whose
functions all pass it (`StoreChk`):

* `flowOk_of_eval`: the check is sound for native evaluation (heights of normal results,
  branch and return arities, no throws, invariants);
* `native_wp` (`wp_of_eval`): a native evaluation is matched by a Core run of the lowering,
  `Silmaril.Wasm.Logic.Core.WP P host … (Match r)`: same store and frame, equal normal results,
  same branch target or `return` with the native values on top, or a trap;
* `native_fwdSim` (`fwdSim_of_storeChk`): silmaril-lean's `Binaryen.FwdSim` at every profile,
  for arguments of the function's parameter types (`InvokeOk`).

**`NoDivOfTerm`** (`Silmaril.Proofs.Wasm.Interp.{Lag,Termination}`). `typed_noDivOfTerm`: a typed
invocation that reaches a result has no infinite trace, at every deterministic profile, for any
code: silmaril-lean's interpreter step `stepI` is maximal, and every other successor is reached
by a bubbling step that shrinks the code (`stepI_lag_typed`), so the pair (distance to the
normal form, size of the code) decreases lexicographically along every step
(`no_infinite_of_lag`). `native_noDivOfTerm`: at every profile on native stores.

**The backward direction, reduced** (`Silmaril.Proofs.Wasm.Interp.Obligations`). On native stores,
`FwdSim`, `BwdSim`, `NoDivOfTerm` and `DivSim` are profile-independent; `native_bwdSim`:
`BwdSim` at every profile from `DivSim` at any one profile; `native_behaviours_eq`: then the
Core behaviours of the invocation at every profile are the native ones (`nbeh`).

**`DivSim` and adequacy** (`Silmaril.Proofs.Wasm.Interp.{Progress,Total,Div}`). `native_divSim`:
if no fuel suffices, Core diverges — otherwise the invocation has no infinite trace and
`term_of_acc` (induction on descent under a reachable configuration, then structural size)
gives a native evaluation; native stuckness is excluded by typed Core progress at the focus
(`evalFlat_progress`, `truthy_progress`). **`native_adequacy`**: Core behaviours at every
profile equal the native ones for typed invocations of native, arity-checked stores.

**Executable hypotheses.** `storeChk_of_check`, `nativeFuncsOk_of_check`: the Boolean checks
`storeChkB`, `nativeFuncsB` imply `StoreChk` and `Binaryen.NativeFuncsOk`. `chk_of_free`: a check
passing against the empty store and instance passes against every store and instance;
`storeChk_modify`: replacing the code of one function by code passing it keeps `StoreChk`
(`Silmaril.Proofs.Wasm.Interp.Replace`). Non-vacuity: `Silmaril.Wasm.Interp.Example` (a validated
module with `select` and `br_table`, all hypotheses discharged, behaviours computed).

The Core-level certification of the lambda-SSA optimiser built on `native_adequacy` is
`Silmaril.Wasm.SSA.CoreCert`.
-/

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Logic.Core

variable {H : Type} {P : Profile} {host : HostSemantics H} {s s' : Store H} {f f' : Frame}
  {stk stk' : List Val} {es : List Binaryen.BExpr}

/-- **Native straight-line evaluation is a Core 3.0 run**, every profile and host. -/
theorem steps_of_eval (h : Binaryen.Eval s f stk es (s', f', .normal stk'))
    (hst : BExpr.straightList f.locals.length es = true) (rest : List Admin) :
    Steps P host ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es) ++ rest⟩
      ⟨s', f', vals stk'.reverse ++ rest⟩ :=
  exec_sound rest (exec_of_eval h rfl hst).1

/-- **A terminating native run of straight-line code is a Core 3.0 run**, every profile and
host. -/
theorem steps_of_run {n : Nat} (h : Binaryen.run n s f stk es = some (s', f', .normal stk'))
    (hst : BExpr.straightList f.locals.length es = true) (rest : List Admin) :
    Steps P host ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es) ++ rest⟩
      ⟨s', f', vals stk'.reverse ++ rest⟩ :=
  steps_of_eval (Binaryen.eval_of_run h) hst rest

/-- **A trapping native run of straight-line code is a Core 3.0 run to a trap**, every profile
and host. -/
theorem steps_trap_of_run {n : Nat} (h : Binaryen.run n s f stk es = some (s', f', .trap))
    (hst : BExpr.straightList f.locals.length es = true) (rest : List Admin) :
    Steps P host ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es) ++ rest⟩
      ⟨s', f', [.trap]⟩ :=
  steps_trap_of_eval (Binaryen.eval_of_run h) rfl hst rest

/-- **Core behaviours of native stores do not depend on the profile.** -/
theorem core_behaviours_profile {P' : Profile} {s : Store H} (hF : Binaryen.NativeFuncsOk s.funcs)
    (a : Nat) (vs : List Val) : behaviours P host s a vs = behaviours P' host s a vs :=
  behaviours_profile hF a vs

/-- **Native evaluation of arity-checked trees is a Core 3.0 run**, every profile and host. -/
theorem native_wp {r : Store H × Frame × Binaryen.Flow} {labels : List Nat} {ret : Nat}
    {out : Option Nat} (h : Binaryen.Eval s f stk es r) (hS : StoreChk s.funcs)
    (hc : chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out) :
    WP P host s f (vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)) (Match r) :=
  wp_of_eval h hS hc

/-- **`FwdSim` on arity-checked stores**, every profile. -/
theorem native_fwdSim {s : Store H} {a : Nat} {vs : List Val} (hS : StoreChk s.funcs)
    (hok : InvokeOk s a vs) : Binaryen.FwdSim P s a vs :=
  fwdSim_of_storeChk hS hok

/-- **`NoDivOfTerm` for typed invocations** at every deterministic profile (any code). -/
theorem typed_noDivOfTerm {o : Silmaril.Wasm.SingleThreaded.GrowOracle} {s : Store H} {a : Nat}
    {vs : List Val} (hs : StoreOk s) (hok : InvokeOk s a vs) :
    Binaryen.NoDivOfTerm (Silmaril.Wasm.SingleThreaded.profile o) s a vs :=
  noDivOfTerm_typed hs hok

/-- **`NoDivOfTerm` at every profile** for typed invocations of native-profile stores. -/
theorem native_noDivOfTerm {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : Binaryen.NativeFuncsOk s.funcs) (hok : InvokeOk s a vs) :
    Binaryen.NoDivOfTerm P s a vs :=
  noDivOfTerm_native hs hF hok

/-- **`BwdSim` at every profile**, from `DivSim` at any one profile. -/
theorem native_bwdSim {P' : Profile} {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : Binaryen.NativeFuncsOk s.funcs) (hS : StoreChk s.funcs) (hok : InvokeOk s a vs)
    (div : Binaryen.DivSim P' s a vs) : Binaryen.BwdSim P s a vs :=
  bwdSim_of_divSim hs hF hS hok div

/-- **Native behaviours are Core behaviours at every profile**, from `DivSim` at any one
profile. -/
theorem native_behaviours_eq {P' : Profile} {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hF : Binaryen.NativeFuncsOk s.funcs) (hS : StoreChk s.funcs)
    (hok : InvokeOk s a vs) (div : Binaryen.DivSim P' s a vs) :
    behaviours P Binaryen.closedHost s a vs = Binaryen.nbeh s a vs :=
  behaviours_eq_nbeh_of_divSim hs hF hS hok div

/-- **`DivSim` at every profile** for typed invocations of native, arity-checked stores. -/
theorem native_divSim {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : Binaryen.NativeFuncsOk s.funcs) (hS : StoreChk s.funcs) (hok : InvokeOk s a vs) :
    Binaryen.DivSim P s a vs :=
  divSim_native hs hF hS hok

/-- **Adequacy of silmaril-lean's native interpreter for Core 3.0, at every profile**: on a
typed invocation of a store whose functions are native-profile Wasm code passing the arity
check, the Core behaviours (closed host) are exactly the native interpreter's behaviours,
divergence included. -/
theorem native_adequacy {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : Binaryen.NativeFuncsOk s.funcs) (hS : StoreChk s.funcs) (hok : InvokeOk s a vs) :
    behaviours P Binaryen.closedHost s a vs = Binaryen.nbeh s a vs :=
  behaviours_eq_nbeh_native hs hF hS hok

/-- **The executable arity check is sound.** -/
theorem storeChk_of_check {F : List (FuncInst H)} (h : storeChkB F = true) : StoreChk F :=
  storeChk_of_storeChkB h

/-- **The executable native-profile check is sound.** -/
theorem nativeFuncsOk_of_check {F : List (FuncInst H)} (h : nativeFuncsB F = true) :
    Binaryen.NativeFuncsOk F :=
  nativeFuncsOk_of_nativeFuncsB h

/-! ## Store-level adequacy

`native_adequacy` relates behaviours, which forget the store. The native
interpreter also computes the final store, and it is Core's. Forward
(`fwd_invoke_store`): a terminating native run is a Core run to a result
configuration whose store is the interpreter's. Backward (`bwd_store`, every
profile, from determinism at the closed deterministic profile and the
existing divergence and termination lemmas): every Core run of an invocation
to a result is found by the interpreter with that configuration's store. -/

/-- **Store-level native adequacy**, on typed, native, arity-checked stores at
every profile: the Core 3.0 runs of an invocation to a result are exactly the
native interpreter's terminating runs, final store included. -/
theorem native_store_adequacy {a : Nat} {vs : List Val} (hs : StoreOk s) (hF : Binaryen.NativeFuncsOk s.funcs)
    (hS : StoreChk s.funcs) (hok : InvokeOk s a vs) (P : Profile) (r : Result) (s' : Store H) :
    (∃ c : Config H, Steps P Binaryen.closedHost (invoke s a vs) c ∧ c.code = r.toAdmin ∧
        c.store = s') ↔
      ∃ fuel fl, Binaryen.invokeRun fuel s a vs = some (s', fl) ∧
        Binaryen.flowBeh fl = some r.toBehaviour := by
  constructor
  · rintro ⟨c, hst, hc, rfl⟩
    exact bwd_store hs hF hS hok hst hc
  · rintro ⟨fuel, fl, hrun, hb⟩
    obtain ⟨c, r', hst, hc, hcs, hb'⟩ :=
      fwd_invoke_store (P := P) (host := Binaryen.closedHost) hS hok hrun
    rw [hb, Option.some.injEq] at hb'
    have hr : r = r' := by
      cases r <;> cases r' <;> simp_all [Result.toBehaviour]
    subst hr
    exact ⟨c, hst, hc, hcs⟩

/-! ## Checked flat instructions as Core runs -/

/-- **A checked flat instruction that completes normally is a Core run** (every profile and
host), under any continuation `rest`. Public form of `steps_flat_normal`. -/
theorem flat_core_normal {F : List (FuncInst H)} {mi : ModuleInst} {ret : Nat}
    {labels : List Nat} {stk stk' : List Val} {h₀ : Nat} {o : Option Nat} {i : Instr}
    (hi : ∀ x, i ≠ .call x) (hc : flatChk F mi f.locals.length ret labels h₀ i = some o)
    (h : Binaryen.evalFlat s f stk i = some (s', f', .normal stk')) (rest : List Admin) :
    Steps P host ⟨s, f, vals stk.reverse ++ .plain i :: rest⟩ ⟨s', f', vals stk'.reverse ++ rest⟩ :=
  steps_flat_normal hi hc h rest

/-- **A checked flat instruction that ends abruptly** (branch, `return` or trap) runs in Core
to the matching final form (every profile and host), under any continuation `rest`. Public
form of `wp_flat_abrupt`. -/
theorem flat_core_abrupt {F : List (FuncInst H)} {mi : ModuleInst} {ret : Nat}
    {labels : List Nat} {stk : List Val} {h₀ : Nat} {o : Option Nat} {i : Instr}
    {fl : Binaryen.Flow} (hc : flatChk F mi f.locals.length ret labels h₀ i = some o)
    (h : Binaryen.evalFlat s f stk i = some (s', f', fl)) (hn : ¬ fl.IsNormal)
    (rest : List Admin) :
    WP P host s f (vals stk.reverse ++ .plain i :: rest) (Match (s', f', fl)) :=
  wp_flat_abrupt hc h hn rest

end Silmaril.Wasm.Interp
