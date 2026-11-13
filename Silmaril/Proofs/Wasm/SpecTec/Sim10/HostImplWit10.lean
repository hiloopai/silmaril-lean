module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.HostImplCore10
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.HostStubWit10

/-!
# Runs that call host functions: witnesses and limits

**A run that calls a host function, as a run of the 1.0 script.** Round 6's `hostB` holds the
host function `.host ([] → []) 0` at address `0`. Take the V1 host `noopHost`, which returns at
once with the store unchanged and no result, and its implementation `noopFn = FUNC 0 [] []`.

* `hostImpl_noop`, `implOk_noop`, `hostTyped_hostB`: the hypotheses of the forward theorem.
* `typed10_impl_hostB`, `typed10T_impl_hostB`: the implemented invocation of address `0` is
  IL-typed (kernel evaluation of the type checker at fuel 2000), although without the reading
  no invocation over `hostB` is (`InstWitnessHost10.not_typed10_hostB`).
* `step_noop_hostB`: the V1 invocation of address `0` under `noopHost` **is a host call**
  (`Step.invokeHost`; its redex is a `HostCall`).
* **`wholeRunFwd10ImplRH_hostB`** (and the `simEnv10T` form): every V1 run of that invocation
  under `noopHost` is, read through the implementation, a run of the 1.0 script.
  **`hostCall_run10`**: in particular the one-step host-call run has an IL run between the
  images, from a typed source to a typed target.

**Round 7's stub, now with host calls.** `hostImpl_stub`: round 7's stub `FUNC 0 [] [UNREACHABLE]`
implements every host whose every return is a trap with the store unchanged (if every
signature has at most one result, as V1's `invokeWasm` requires). `implOk_stub`: the stub is
always a valid implementation. So `wholeRunFwd10Stub` extends to runs that call such hosts
(`wholeRunFwd10StubTrap`).

**The limit.** `not_hostImpl_alloc`: a host that appends a function to the store has **no**
implementation, for any `ι` and `σ`, because an implementing run keeps the function list
(`hostImpl_funcs_length`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.HostReadWit

open Silmaril.SpecTec.Sem (Builtins)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step Steps PureStep values
  result expression)
open Silmaril.Wasm.Execution.Runtime (Value FuncInst FuncAddr ModuleInst Frame Result)
open Silmaril.Wasm.Execution.Core (StoreOk FuncInstOk)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.Valid (coreStore10 invokeCfg10 emptyHost10 frame0)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10.Whole (fwdB10)
open Silmaril.Wasm.SpecTec.Sim10.InstWitness10 (addModule0)
open Silmaril.Wasm.SpecTec.Sim10.InstWitnessHost10 (hostBase hostB hostBMod reachH_hostB
  storeOk_hostBase storeWF_hostBase not_typed10_hostB)
open Silmaril.Wasm.SpecTec.Sim10.HostStub (stubFn stubMod stubF stubS stubC stubCtx moduleOk_stub
  funcInstOk_stubC HostCall)
open Silmaril.Wasm.SpecTec.Sim10.HostRead
open Silmaril.Wasm.SpecTec.Sim10 (Typed10 configV simEnv10)

/-! ## A host that returns at once, and its implementation -/

/-- The V1 host that returns at once, with the store unchanged and no result. -/
def noopHost : HostSemantics Nat := fun _ s args o => args = [] ∧ o = .returned s (.values [])

/-- Every host code has the signature `[] → []`. -/
def sig0 : Nat → V1.FuncType := fun _ => ⟨[], []⟩

/-- The implementation `FUNC 0 [] []`. -/
def noopFn : V1.Func := ⟨⟨0⟩, [], []⟩

/-- Every host code is implemented by `noopFn`. -/
def impl0 : Nat → V1.Func := fun _ => noopFn

/-- **`noopFn` is a valid Core function instance of type `[] → []`.** -/
theorem implOk_noop : ImplOk impl0 sig0 := by
  intro h S
  have hdt : TyOk {} (sig0 h).toDefType := Lime1.Validation.tyOk_toDefType _ _
  have he := Expand.iff.mpr (V1.FuncType.toDefType_expand (sig0 h))
  exact .wasm hdt (moduleOk_stub S _ hdt) rfl (.mk rfl he .nil .nil)
    (Sub.refl (k := .def) _ trivial _)

/-- **`noopFn` implements `noopHost`**: the implementing run enters the function, leaves the
empty block and returns. -/
theorem hostImpl_noop : HostImpl impl0 sig0 noopHost := by
  intro s s' f a h args r ht found arity hb
  obtain ⟨rfl, he⟩ := hb
  cases he
  refine ⟨ht, ?_⟩
  have found' : (implS impl0 s).funcs[a.value]? = some (.wasm (sig0 h) (stubMod (sig0 h)) noopFn) :=
    by simp [implS_funcs, found, implF, impl0]
  have s₁ := Step.invokeWasm (host := emptyHost10) (implS impl0 s) f a (sig0 h) _ _ [] found'
    rfl (Nat.zero_le 1)
  have s₂ := Step.frame (host := emptyHost10)
    (Step.pure (implS impl0 s) ⟨[], stubMod (sig0 h)⟩ (PureStep.labelDone 0 [] [])) 0 f
  have s₃ := Step.pure (host := emptyHost10) (implS impl0 s) f
    (PureStep.frameDone 0 ⟨[], stubMod (sig0 h)⟩ [] rfl)
  exact .head s₁ (.head s₂ (.single s₃))

/-! ## The witness at `hostB` -/

theorem hostB_funcs : hostB.funcs =
    [.host ⟨[], []⟩ 0, .wasm Silmaril.Wasm.V1.Validation.Examples.addType hostBMod
      ⟨⟨0⟩, [], Silmaril.Wasm.V1.Validation.Examples.addBody⟩] := rfl

/-- The host function of `hostB` has the signature `sig0 0`. -/
theorem hostTyped_hostB : HostTyped sig0 hostB.funcs := by
  intro a t h e
  rw [hostB_funcs] at e
  match a, e with
  | 0, e =>
    simp only [List.getElem?_cons_zero, Option.some.injEq, FuncInst.host.injEq] at e
    exact e.1.symm
  | 1, e => simp at e
  | n + 2, e => simp at e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The implemented invocation of the host function is IL-typed** (`simEnv10`). -/
theorem typed10_impl_hostB (B : Builtins) (hn : Nat → String) :
    Typed10 (simEnv10 B) hn (invokeCfg10 (implS impl0 hostB) [] ⟨0⟩) :=
  ⟨2000, by with_unfolding_all rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The same in `simEnv10T`.** -/
theorem typed10T_impl_hostB (B : Builtins) (hn : Nat → String) :
    Typed10 (simEnv10T B) hn (invokeCfg10 (implS impl0 hostB) [] ⟨0⟩) :=
  ⟨2000, by with_unfolding_all rfl⟩

/-- **The invocation of address `0` under `noopHost` is a host call.** -/
theorem step_noop_hostB :
    Step noopHost (invokeCfg10 hostB [] ⟨0⟩) ⟨hostB, frame0, []⟩ ∧
      HostCall (invokeCfg10 hostB [] ⟨0⟩) :=
  ⟨.invokeHost hostB hostB frame0 ⟨0⟩ ⟨[], []⟩ 0 [] (.values []) rfl rfl ⟨rfl, rfl⟩,
    .here [] rfl⟩

/-- **The forward run at `hostB` under `noopHost`, host calls included**: every V1 run of the
invocation of the host function is, read through `noopFn`, a run of the 1.0 script. -/
theorem wholeRunFwd10ImplRH_hostB (hn : Nat → String) (nd : Bool) (r : RelaxedChoice)
    {c' : Config Nat} (h : Steps noopHost (invokeCfg10 hostB [] ⟨0⟩) c') :
    Typed10 (simEnv10 (fwdB10 nd r)) hn (implC impl0 c') ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV hn (implC impl0 (invokeCfg10 hostB [] ⟨0⟩))) (configV hn (implC impl0 c')) :=
  wholeRunFwd10ImplRH (fi := .host ⟨[], []⟩ 0) reachH_hostB storeOk_hostBase storeWF_hostBase
    hostImpl_noop implOk_noop hostTyped_hostB (typed10_impl_hostB _ hn) rfl rfl h

/-- **The same in `simEnv10T`.** -/
theorem wholeRunFwd10ImplRHT_hostB (hn : Nat → String) (nd : Bool) (r : RelaxedChoice)
    {c' : Config Nat} (h : Steps noopHost (invokeCfg10 hostB [] ⟨0⟩) c') :
    Typed10 (simEnv10T (fwdB10 nd r)) hn (implC impl0 c') ∧
      Relation.ReflTransGen (SStepB (simEnv10T (fwdB10 nd r)))
        (configV hn (implC impl0 (invokeCfg10 hostB [] ⟨0⟩))) (configV hn (implC impl0 c')) :=
  wholeRunFwd10ImplRHT (fi := .host ⟨[], []⟩ 0) reachH_hostB storeOk_hostBase storeWF_hostBase
    hostImpl_noop implOk_noop hostTyped_hostB (typed10T_impl_hostB _ hn) rfl rfl h

/-- **A host-call run of V1 is a run of the 1.0 script.** Without the reading the source image
is not typed; with it, the one-step V1 run that calls the host function has an IL run between
typed images. -/
theorem hostCall_run10 (B : Builtins) (hn : Nat → String) (nd : Bool) (r : RelaxedChoice) :
    ¬ Typed10 (simEnv10 B) hn (invokeCfg10 hostB [] ⟨0⟩) ∧
      HostCall (invokeCfg10 hostB [] ⟨0⟩) ∧
      Step noopHost (invokeCfg10 hostB [] ⟨0⟩) ⟨hostB, frame0, []⟩ ∧
      Typed10 (simEnv10 (fwdB10 nd r)) hn (implC impl0 (invokeCfg10 hostB [] ⟨0⟩)) ∧
      Typed10 (simEnv10 (fwdB10 nd r)) hn (implC impl0 ⟨hostB, frame0, []⟩) ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV hn (implC impl0 (invokeCfg10 hostB [] ⟨0⟩)))
        (configV hn (implC impl0 ⟨hostB, frame0, []⟩)) := by
  have hrun := wholeRunFwd10ImplRH_hostB hn nd r (.single step_noop_hostB.1)
  exact ⟨(not_typed10_hostB hn B [] ⟨0⟩).1, step_noop_hostB.2, step_noop_hostB.1,
    typed10_impl_hostB _ hn, hrun.1, hrun.2⟩

/-! ## Round 7's stub implements the trapping hosts -/

/-- **The stub is a valid implementation of every signature.** -/
theorem implOk_stub {H : Type} (σ : H → V1.FuncType) : ImplOk (fun _ => stubFn) σ := by
  intro h S
  exact funcInstOk_stubC S (σ h) h (Lime1.Validation.tyOk_toDefType _ _)
    (Expand.iff.mpr (V1.FuncType.toDefType_expand (σ h)))

/-- **Round 7's stub implements every host that only traps**, leaving the store unchanged
(signatures with at most one result). -/
theorem hostImpl_stub {H : Type} {σ : H → V1.FuncType} {host : HostSemantics H}
    (hσ : ∀ h, (σ h).results.length ≤ 1)
    (htrap : ∀ h s args o, host h s args o → o = .returned s .trap) :
    HostImpl (fun _ => stubFn) σ host := by
  intro s s' f a h args r ht found arity hb
  cases htrap _ _ _ _ hb
  refine ⟨ht, ?_⟩
  let S := implS (fun _ => stubFn) s
  let n := (σ h).results.length
  let F : Frame := ⟨args ++ [], stubMod (σ h)⟩
  have found' : S.funcs[a.value]? = some (.wasm (σ h) (stubMod (σ h)) stubFn) := by
    simp [S, implS_funcs, found, implF]
  have s₁ := Step.invokeWasm (host := emptyHost10) S f a (σ h) _ _ args found' arity (hσ h)
  have s₂ := Step.frame (host := emptyHost10)
    (Step.label (Step.pure S F PureStep.unreachable) n []) n f
  have s₃ := Step.frame (host := emptyHost10) (Step.pure S F (PureStep.labelTrap n [])) n f
  have s₄ := Step.pure (host := emptyHost10) S f (PureStep.frameTrap n F)
  exact .head s₁ (.head s₂ (.head s₃ (.single s₄)))

/-- **Round 7's `wholeRunFwd10Stub` for runs that call trapping hosts.** -/
theorem wholeRunFwd10StubTrap {H : Type} {σ : H → V1.FuncType} {host : HostSemantics H}
    {hn : H → String} {nd : Bool} {r : RelaxedChoice} {s : Store H} {args : List Value}
    {a : FuncAddr} {c' : Config H} (hσ : ∀ h, (σ h).results.length ≤ 1)
    (htrap : ∀ h s args o, host h s args o → o = .returned s .trap)
    (ht : HostTyped σ s.funcs)
    (hc : Typed10 (simEnv10 (fwdB10 nd r)) hn (invokeCfg10 (stubS s) args a))
    (hs : StoreOk (coreStore10 s))
    (hinv : Execution.Core.InvokeOk (coreStore10 s) a.value (args.map Value.toCore))
    (hwf : Lime1.Execution.StoreWF (s.mapCode V1.Func.toLime))
    (h : Steps host (invokeCfg10 s args a) c') :
    Typed10 (simEnv10 (fwdB10 nd r)) hn (stubC c') ∧
      Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r)))
        (configV hn (stubC (invokeCfg10 s args a))) (configV hn (stubC c')) := by
  rw [stubC_eq_implC, stubC_eq_implC]
  rw [stubS_eq_implS] at hc
  exact wholeRunFwd10Impl (hostImpl_stub hσ htrap) (implOk_stub σ) ht hc hs hinv hwf h

/-! ## The limit: hosts that allocate -/

/-- The V1 host that appends a host function to the store and returns no result. -/
def allocHost : HostSemantics Nat := fun _ s _ o =>
  o = .returned { s with funcs := s.funcs ++ [.host ⟨[], []⟩ 0] } (.values [])

/-- **A host that allocates a function has no implementation**, whatever the implementations
and signatures: an implementing run keeps the number of functions. -/
theorem not_hostImpl_alloc (ι : Nat → V1.Func) (σ : Nat → V1.FuncType) :
    ¬ HostImpl ι σ allocHost := by
  intro hH
  let s : Store Nat := { funcs := [.host (σ 0) 0] }
  have ht : HostTyped σ s.funcs := by
    intro a t h e
    match a, e with
    | 0, e =>
      simp only [s, List.getElem?_cons_zero, Option.some.injEq, FuncInst.host.injEq] at e
      rw [← e.1, e.2]
    | n + 1, e => simp [s] at e
  have hl := hostImpl_funcs_length hH frame0 (a := ⟨0⟩) (args := (σ 0).params.map Value.zero)
    ht rfl (by simp) rfl
  simp [s] at hl

end Silmaril.Wasm.SpecTec.Sim10.HostReadWit
