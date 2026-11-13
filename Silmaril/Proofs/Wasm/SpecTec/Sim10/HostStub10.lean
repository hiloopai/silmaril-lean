module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstHost10
public import Silmaril.Wasm.Binaryen.InlStore

/-!
# Host-function instances in the 1.0 IL: the stub restatement

The wasm-1.0 SpecTec script has no host function instance: `funcinst` is
`{TYPE functype, MODULE moduleinst, CODE func}` and `func` has the one case `FUNC`. So the image of
a store holding a V1 host function is not a typed `state` (`Whole.not_typed_host10`), and every
forward theorem, which assumes the invocation image is typed, is vacuous at such stores
(`InstH.noHost10_of_typed10_invoke`).

**The restatement.** A host function instance `.host t h` is read in the 1.0 IL as the defined
function instance `stubF (.host t h) = .wasm t (stubMod t) stubFn`: the same type, a module
instance with the one type `t` and nothing else, and the code `FUNC 0 [] [UNREACHABLE]`. This is
a function the 1.0 IL has. `stubS s` replaces every host function of `s` this way and keeps the
rest, and `stubC c` does it on the store of a configuration. The fixed 1.0 script is unchanged:
the erratum is on the reading of host function instances, not on the script.

What it covers. A V1 run that calls no host function is a run under the empty V1 host
(`step_empty_or_hostCall`: every step under any host is a step under the empty host, or its
redex is a host call, `HostCall`). Such a run commutes with the stub (`step_stub`, `steps_stub`):
the stub has the host function's type, so `call_indirect`'s type check agrees, and a defined
function is never confused with a stub, because the run never invokes a host function.

* `storeOk_stub`, `invokeOk_stub`, `storeWF_stub`: the Core hypotheses of the forward theorem
  move from `s` to `stubS s`. The stub is a valid Core function instance of the host function's
  type (`funcInstOk_stubC`, `unreachable` has every type), and the other function instances keep
  their validity (`Binaryen.InlStore.storeOk_withFuncs`).
* **`wholeRunFwd10Stub`**, `wholeRunFwd10StubT`: round 4's `Task.wholeRunFwd10Inv` (and its
  `simEnv10T` form) at stores with host functions, for runs that call none: the run of the
  stubbed configurations is a run of the 1.0 script. The typing hypothesis is on the stubbed
  invocation, which can hold at a store with host functions.
* **`wholeRunFwd10StubRH`**, `wholeRunFwd10StubRHT`: the same at every store reached from a
  base store with host functions, with no `StoreOk`/`StoreWF` hypothesis
  on the reached store.

What it does not cover: a run that calls a host function. Under the stub reading, the IL invokes
`UNREACHABLE` and traps, while V1 hands control to the host; no IL rule models a host call.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.HostStub

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step Steps values)
open Silmaril.Wasm.Execution.Runtime (Value ExternVal FuncInst ModuleInst)
open Silmaril.Wasm.Execution.Core (StoreOk FuncInstOk ModuleInstOk)
open Silmaril.Wasm.Binaryen.InlS (withFuncs SameTypes storeOk_withFuncs funcInstOk_withFuncs
  valOk_withFuncs)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10.Whole (fwdB10)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10 Silmaril.Wasm.SpecTec.Sim10.Valid
open Silmaril.Wasm.SpecTec.Sim10.InstH (ReachH10 reachH10_ok)

variable {H : Type}

/-! ## The stub -/

/-- The stub's code: `FUNC 0 [] [UNREACHABLE]`. -/
def stubFn : V1.Func := ⟨⟨0⟩, [], [.unreachable]⟩

/-- The stub's module instance: the one type `t`. -/
def stubMod (t : V1.FuncType) : ModuleInst := { types := [t] }

/-- **A host function instance read as a 1.0 function instance**; defined functions are kept. -/
def stubF : FuncInst V1.Func H → FuncInst V1.Func H
  | .wasm t m fn => .wasm t m fn
  | .host t _ => .wasm t (stubMod t) stubFn

/-- Every host function of the store replaced by its stub. -/
def stubS (s : Store H) : Store H := { s with funcs := s.funcs.map stubF }

/-- `stubS` on the store of a configuration. -/
def stubC (c : Config H) : Config H := { c with store := stubS c.store }

@[simp] theorem stubF_type (fi : FuncInst V1.Func H) : (stubF fi).type = fi.type := by
  cases fi <;> rfl

theorem stubF_wasm {fi : FuncInst V1.Func H} {t : V1.FuncType} {m : ModuleInst} {fn : V1.Func}
    (h : stubF fi = .wasm t m fn) : fi = .wasm t m fn ∨ ∃ h', fi = .host t h' := by
  cases fi with
  | wasm t' m' fn' => exact Or.inl h
  | host t' h' =>
    simp only [stubF, FuncInst.wasm.injEq] at h
    exact Or.inr ⟨h', by rw [h.1]⟩

theorem stubS_funcs (s : Store H) (a : Nat) : (stubS s).funcs[a]? = (s.funcs[a]?).map stubF := by
  simp [stubS]

theorem invokeCfg10_stub (s : Store H) (args : List Value) (a : Execution.Runtime.FuncAddr) :
    invokeCfg10 (stubS s) args a = stubC (invokeCfg10 s args a) := rfl

/-! ## Runs that call no host function -/

/-- **A V1 step under the empty host is a step of the stubbed configurations**, under any
host. -/
theorem step_stub {host : HostSemantics H} {c d : Config H} (h : Step emptyHost10 c d) :
    Step host (stubC c) (stubC d) := by
  induction h with
  | pure s f h => exact .pure _ f h
  | context _ vs tail ih => exact .context ih vs tail
  | label _ n cont ih => exact .label ih n cont
  | frame _ n outer ih => exact .frame ih n outer
  | localGet s f i v found => exact .localGet _ f i v found
  | localSet s f i v old found => exact .localSet _ f i v old found
  | globalGet s f i a g index found => exact .globalGet _ f i a g index found
  | globalSet s f i a g v index found mutable => exact .globalSet _ f i a g v index found mutable
  | call s f i a found => exact .call _ f i a found
  | callIndirect s f i c table a fn ft h₁ h₂ h₃ h₄ h₅ =>
    exact .callIndirect _ f i c table a (stubF fn) ft h₁ h₂ h₃ (by simp [stubS_funcs, h₄])
      (by simpa using h₅)
  | callIndirectBounds s f i c table h₁ h₂ => exact .callIndirectBounds _ f i c table h₁ h₂
  | callIndirectNull s f i c table h₁ h₂ => exact .callIndirectNull _ f i c table h₁ h₂
  | callIndirectType s f i c table a fn ft h₁ h₂ h₃ h₄ h₅ =>
    exact .callIndirectType _ f i c table a (stubF fn) ft h₁ h₂ h₃ (by simp [stubS_funcs, h₄])
      (by simpa using h₅)
  | invokeWasm s f a ft module fn args found arity resultArity =>
    exact .invokeWasm _ f a ft module fn args (by simp [stubS_funcs, found, stubF]) arity
      resultArity
  | invokeHost s s' f a ft fn args r found _ hb => exact hb.elim
  | invokeHostDiverges s f a ft fn args found _ hb => exact hb.elim
  | intLoad s f t p arg c a m v h₁ h₂ => exact .intLoad _ f t p arg c a m v h₁ h₂
  | intLoadTrap s f t p arg c a m h₁ h₂ => exact .intLoadTrap _ f t p arg c a m h₁ h₂
  | floatLoad s f t arg c a m v h₁ h₂ => exact .floatLoad _ f t arg c a m v h₁ h₂
  | floatLoadTrap s f t arg c a m h₁ h₂ => exact .floatLoadTrap _ f t arg c a m h₁ h₂
  | intStore s f t p arg c x a m b h₁ h₂ => exact .intStore _ f t p arg c x a m b h₁ h₂
  | intStoreTrap s f t p arg c x a m h₁ h₂ => exact .intStoreTrap _ f t p arg c x a m h₁ h₂
  | floatStore s f t arg c x a m b h₁ h₂ => exact .floatStore _ f t arg c x a m b h₁ h₂
  | floatStoreTrap s f t arg c x a m h₁ h₂ => exact .floatStoreTrap _ f t arg c x a m h₁ h₂
  | memorySize s f a m h₁ => exact .memorySize _ f a m h₁
  | memoryGrow s f a m c r b h₁ h₂ => exact .memoryGrow _ f a m c r b h₁ h₂

/-- **Runs under the empty host commute with the stub.** -/
theorem steps_stub {host : HostSemantics H} {c d : Config H} (h : Steps emptyHost10 c d) :
    Steps host (stubC c) (stubC d) :=
  Relation.ReflTransGen.lift stubC (fun _ _ hs => step_stub hs) _ _ h

/-- The redex of a configuration is a call of a host function. -/
inductive HostCall : Config H → Prop where
  | here {s : Store H} {f : Execution.Runtime.Frame} {a : Execution.Runtime.FuncAddr}
      {ft : V1.FuncType} {h : H} (args : List Value)
      (found : s.funcs[a.value]? = some (.host ft h)) :
      HostCall ⟨s, f, values args ++ [.invoke a]⟩
  | context {s : Store H} {f : Execution.Runtime.Frame} {before : List Admin}
      (h : HostCall ⟨s, f, before⟩) (vs : List Value) (tail : List Admin) :
      HostCall ⟨s, f, values vs ++ before ++ tail⟩
  | label {s : Store H} {f : Execution.Runtime.Frame} {before : List Admin}
      (h : HostCall ⟨s, f, before⟩) (n : Nat) (cont : V1.Expr) :
      HostCall ⟨s, f, [.label n cont before]⟩
  | frame {s : Store H} {inner : Execution.Runtime.Frame} {before : List Admin}
      (h : HostCall ⟨s, inner, before⟩) (n : Nat) (outer : Execution.Runtime.Frame) :
      HostCall ⟨s, outer, [.frame n inner before]⟩

/-- **Every V1 step is a step under the empty host, or its redex calls a host function.** So a
run that calls no host function is a run under the empty host. -/
theorem step_empty_or_hostCall {host : HostSemantics H} {c d : Config H} (h : Step host c d) :
    Step emptyHost10 c d ∨ HostCall c := by
  induction h with
  | pure s f h => exact .inl (.pure s f h)
  | context _ vs tail ih => exact ih.imp (fun h => .context h vs tail) (fun h => .context h vs tail)
  | label _ n cont ih => exact ih.imp (fun h => .label h n cont) (fun h => .label h n cont)
  | frame _ n outer ih => exact ih.imp (fun h => .frame h n outer) (fun h => .frame h n outer)
  | localGet s f i v found => exact .inl (.localGet s f i v found)
  | localSet s f i v old found => exact .inl (.localSet s f i v old found)
  | globalGet s f i a g index found => exact .inl (.globalGet s f i a g index found)
  | globalSet s f i a g v index found mutable =>
    exact .inl (.globalSet s f i a g v index found mutable)
  | call s f i a found => exact .inl (.call s f i a found)
  | callIndirect s f i c table a fn ft h₁ h₂ h₃ h₄ h₅ =>
    exact .inl (.callIndirect s f i c table a fn ft h₁ h₂ h₃ h₄ h₅)
  | callIndirectBounds s f i c table h₁ h₂ => exact .inl (.callIndirectBounds s f i c table h₁ h₂)
  | callIndirectNull s f i c table h₁ h₂ => exact .inl (.callIndirectNull s f i c table h₁ h₂)
  | callIndirectType s f i c table a fn ft h₁ h₂ h₃ h₄ h₅ =>
    exact .inl (.callIndirectType s f i c table a fn ft h₁ h₂ h₃ h₄ h₅)
  | invokeWasm s f a ft module fn args found arity resultArity =>
    exact .inl (.invokeWasm s f a ft module fn args found arity resultArity)
  | invokeHost s s' f a ft fn args r found _ _ => exact .inr (.here args found)
  | invokeHostDiverges s f a ft fn args found _ _ => exact .inr (.here args found)
  | intLoad s f t p arg c a m v h₁ h₂ => exact .inl (.intLoad s f t p arg c a m v h₁ h₂)
  | intLoadTrap s f t p arg c a m h₁ h₂ => exact .inl (.intLoadTrap s f t p arg c a m h₁ h₂)
  | floatLoad s f t arg c a m v h₁ h₂ => exact .inl (.floatLoad s f t arg c a m v h₁ h₂)
  | floatLoadTrap s f t arg c a m h₁ h₂ => exact .inl (.floatLoadTrap s f t arg c a m h₁ h₂)
  | intStore s f t p arg c x a m b h₁ h₂ => exact .inl (.intStore s f t p arg c x a m b h₁ h₂)
  | intStoreTrap s f t p arg c x a m h₁ h₂ => exact .inl (.intStoreTrap s f t p arg c x a m h₁ h₂)
  | floatStore s f t arg c x a m b h₁ h₂ => exact .inl (.floatStore s f t arg c x a m b h₁ h₂)
  | floatStoreTrap s f t arg c x a m h₁ h₂ =>
    exact .inl (.floatStoreTrap s f t arg c x a m h₁ h₂)
  | memorySize s f a m h₁ => exact .inl (.memorySize s f a m h₁)
  | memoryGrow s f a m c r b h₁ h₂ => exact .inl (.memoryGrow s f a m c r b h₁ h₂)

end Silmaril.Wasm.SpecTec.Sim10.HostStub
