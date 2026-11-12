module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.HostStubCore10
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstInvoke10

/-!
# Runs that call host functions: host functions read as their 1.0 implementations

Round 7's stub restatement (`HostStub10`) reads a host function instance `.host t h` in the 1.0
IL as `FUNC 0 [] [UNREACHABLE]`, and covers only V1 runs that call no host function. Here a run
may call host functions. The reading is generalised from the one stub to a per-host-code
**implementation** `ι : H → V1.Func`:

* `implF ι (.host t h) = .wasm t (stubMod t) (ι h)`: the host function is read as a defined 1.0
  function of the same type, with body `ι h`, in a closed module instance (the one type `t`,
  no function, table, memory or global). Defined functions are kept. Round 7's `stubF` is
  `implF (fun _ => stubFn)` (`stubF_eq_implF`).
* `HostTyped σ`: every host function of the store with code `h` has the signature `σ h`.
* **`HostImpl ι σ host`**: every return of the V1 host on a call of a host function of the
  store is matched by a V1 run under the **empty** host of the implementing code, from the
  implemented call configuration to the implemented result configuration (and keeps
  `HostTyped σ`). This is an obligation on V1 runs, not on the IL.

**`steps_impl`**: under `HostImpl`, every V1 run under `host` from a `HostTyped σ` store, host
calls included, is a V1 run under the empty host between the implemented configurations. A host
call step is replaced by the implementation's run (`HostImpl`); a host divergence step is a
self-loop and is dropped; every other step is kept (`step_implE`).

**What the reading cannot cover (`hostImpl_funcs`, `hostImpl_funcs_length`).** A run under the
empty host from a store with no host function keeps the function list (`steps_funcs10`), and an
implemented store has none. So a host that has an implementation never changes the function
list of the store, up to the reading. In particular a host that allocates a function is not
implementable (`HostImplWit10.not_hostImpl_alloc`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.HostRead

open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step Steps values result)
open Silmaril.Wasm.Execution.Runtime (Value FuncInst FuncAddr ModuleInst Frame Result)
open Silmaril.Wasm.SpecTec.Sim10 Silmaril.Wasm.SpecTec.Sim10.Valid
open Silmaril.Wasm.SpecTec.Sim10.Whole (NoHost10)
open Silmaril.Wasm.SpecTec.Sim10.HostStub (stubF stubS stubC stubFn stubMod)

variable {H : Type}

/-! ## The reading -/

/-- **A host function instance read as its implementation**, a defined 1.0 function of the same
type in a closed module instance; defined functions are kept. -/
def implF (ι : H → V1.Func) : FuncInst V1.Func H → FuncInst V1.Func H
  | .wasm t m fn => .wasm t m fn
  | .host t h => .wasm t (stubMod t) (ι h)

/-- Every host function of the store read as its implementation. -/
def implS (ι : H → V1.Func) (s : Store H) : Store H := { s with funcs := s.funcs.map (implF ι) }

/-- `implS` on the store of a configuration. -/
def implC (ι : H → V1.Func) (c : Config H) : Config H := { c with store := implS ι c.store }

@[simp] theorem implF_type (ι : H → V1.Func) (fi : FuncInst V1.Func H) :
    (implF ι fi).type = fi.type := by
  cases fi <;> rfl

theorem implS_funcs (ι : H → V1.Func) (s : Store H) (a : Nat) :
    (implS ι s).funcs[a]? = (s.funcs[a]?).map (implF ι) := by
  simp [implS]

theorem invokeCfg10_impl (ι : H → V1.Func) (s : Store H) (args : List Value) (a : FuncAddr) :
    invokeCfg10 (implS ι s) args a = implC ι (invokeCfg10 s args a) := rfl

/-- **Round 7's stub is the constant implementation `FUNC 0 [] [UNREACHABLE]`.** -/
theorem stubF_eq_implF : (stubF : FuncInst V1.Func H → FuncInst V1.Func H) =
    implF (fun _ => stubFn) := by
  funext fi
  cases fi <;> rfl

theorem stubS_eq_implS (s : Store H) : stubS s = implS (fun _ => stubFn) s := by
  simp only [stubS, implS, stubF_eq_implF]

theorem stubC_eq_implC (c : Config H) : stubC c = implC (fun _ => stubFn) c := by
  simp only [stubC, implC, stubS_eq_implS]

/-- An implemented store has no host function. -/
theorem noHost10_implS (ι : H → V1.Func) (s : Store H) : NoHost10 (implS ι s) := by
  intro i ft h e
  rw [implS_funcs] at e
  obtain ⟨fi, -, he⟩ := Option.map_eq_some_iff.mp e
  cases fi <;> simp [implF] at he

/-! ## Host signatures and the implementation obligation -/

/-- **Host signatures**: every host function of the list with code `h` has the type `σ h`. -/
def HostTyped (σ : H → V1.FuncType) (fs : List (FuncInst V1.Func H)) : Prop :=
  ∀ (a : Nat) (t : V1.FuncType) (h : H), fs[a]? = some (.host t h) → t = σ h

/-- **The implementation obligation**: every return of `host` on a call of a host function of a
`HostTyped σ` store keeps `HostTyped σ` and is matched by a V1 run under the empty host of the
implementing code, between the implemented configurations. -/
def HostImpl (ι : H → V1.Func) (σ : H → V1.FuncType) (host : HostSemantics H) : Prop :=
  ∀ (s s' : Store H) (f : Frame) (a : FuncAddr) (h : H) (args : List Value) (r : Result),
    HostTyped σ s.funcs → s.funcs[a.value]? = some (.host (σ h) h) →
    args.length = (σ h).params.length → host h s args (.returned s' r) →
    HostTyped σ s'.funcs ∧
      Steps emptyHost10 (implC ι ⟨s, f, values args ++ [.invoke a]⟩) (implC ι ⟨s', f, result r⟩)

/-! ## Steps under the empty host commute with the reading -/

/-- **A V1 step under the empty host is a step of the implemented configurations**, under any
host. -/
theorem step_implE (ι : H → V1.Func) {host : HostSemantics H} {c d : Config H}
    (h : Step emptyHost10 c d) : Step host (implC ι c) (implC ι d) := by
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
    exact .callIndirect _ f i c table a (implF ι fn) ft h₁ h₂ h₃ (by simp [implS_funcs, h₄])
      (by simpa using h₅)
  | callIndirectBounds s f i c table h₁ h₂ => exact .callIndirectBounds _ f i c table h₁ h₂
  | callIndirectNull s f i c table h₁ h₂ => exact .callIndirectNull _ f i c table h₁ h₂
  | callIndirectType s f i c table a fn ft h₁ h₂ h₃ h₄ h₅ =>
    exact .callIndirectType _ f i c table a (implF ι fn) ft h₁ h₂ h₃ (by simp [implS_funcs, h₄])
      (by simpa using h₅)
  | invokeWasm s f a ft module fn args found arity resultArity =>
    exact .invokeWasm _ f a ft module fn args (by simp [implS_funcs, found, implF]) arity
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

/-- The same along runs. -/
theorem steps_implE (ι : H → V1.Func) {host : HostSemantics H} {c d : Config H}
    (h : Steps emptyHost10 c d) : Steps host (implC ι c) (implC ι d) :=
  Relation.ReflTransGen.lift (implC ι) (fun _ _ hs => step_implE ι hs) _ _ h

/-- An empty-host step, lifted, with `HostTyped` kept. -/
theorem keep {ι : H → V1.Func} {σ : H → V1.FuncType} {c d : Config H}
    (h : Step emptyHost10 c d) (he : d.store.funcs = c.store.funcs)
    (ht : HostTyped σ c.store.funcs) :
    HostTyped σ d.store.funcs ∧ Steps emptyHost10 (implC ι c) (implC ι d) :=
  ⟨he ▸ ht, .single (step_implE ι h)⟩

/-! ## Runs that call host functions -/

/-- **A V1 step under any host with an implementation is a run under the empty host between the
implemented configurations**, and keeps `HostTyped σ`. -/
theorem step_impl {ι : H → V1.Func} {σ : H → V1.FuncType} {host : HostSemantics H}
    (hH : HostImpl ι σ host) {c d : Config H} (h : Step host c d)
    (ht : HostTyped σ c.store.funcs) :
    HostTyped σ d.store.funcs ∧ Steps emptyHost10 (implC ι c) (implC ι d) := by
  induction h with
  | pure s f h => exact keep (.pure s f h) rfl ht
  | context _ vs tail ih =>
    obtain ⟨ht', hs⟩ := ih ht
    exact ⟨ht', hs.context vs tail⟩
  | label _ n cont ih =>
    obtain ⟨ht', hs⟩ := ih ht
    exact ⟨ht', hs.label n cont⟩
  | frame _ n outer ih =>
    obtain ⟨ht', hs⟩ := ih ht
    exact ⟨ht', hs.frame n outer⟩
  | localGet s f i v found => exact keep (.localGet s f i v found) rfl ht
  | localSet s f i v old found => exact keep (.localSet s f i v old found) rfl ht
  | globalGet s f i a g index found => exact keep (.globalGet s f i a g index found) rfl ht
  | globalSet s f i a g v index found mutable =>
    exact keep (.globalSet s f i a g v index found mutable) rfl ht
  | call s f i a found => exact keep (.call s f i a found) rfl ht
  | callIndirect s f i c table a fn ft h₁ h₂ h₃ h₄ h₅ =>
    exact keep (.callIndirect s f i c table a fn ft h₁ h₂ h₃ h₄ h₅) rfl ht
  | callIndirectBounds s f i c table h₁ h₂ =>
    exact keep (.callIndirectBounds s f i c table h₁ h₂) rfl ht
  | callIndirectNull s f i c table h₁ h₂ => exact keep (.callIndirectNull s f i c table h₁ h₂) rfl ht
  | callIndirectType s f i c table a fn ft h₁ h₂ h₃ h₄ h₅ =>
    exact keep (.callIndirectType s f i c table a fn ft h₁ h₂ h₃ h₄ h₅) rfl ht
  | invokeWasm s f a ft module fn args found arity resultArity =>
    exact keep (.invokeWasm s f a ft module fn args found arity resultArity) rfl ht
  | invokeHost s s' f a ft fn args r found arity hb =>
    have e : ft = σ fn := ht _ _ _ found
    subst e
    exact hH s s' f a fn args r ht found arity hb
  | invokeHostDiverges s f a ft fn args found _ _ => exact ⟨ht, .refl⟩
  | intLoad s f t p arg c a m v h₁ h₂ => exact keep (.intLoad s f t p arg c a m v h₁ h₂) rfl ht
  | intLoadTrap s f t p arg c a m h₁ h₂ => exact keep (.intLoadTrap s f t p arg c a m h₁ h₂) rfl ht
  | floatLoad s f t arg c a m v h₁ h₂ => exact keep (.floatLoad s f t arg c a m v h₁ h₂) rfl ht
  | floatLoadTrap s f t arg c a m h₁ h₂ =>
    exact keep (.floatLoadTrap s f t arg c a m h₁ h₂) rfl ht
  | intStore s f t p arg c x a m b h₁ h₂ =>
    exact keep (.intStore s f t p arg c x a m b h₁ h₂) rfl ht
  | intStoreTrap s f t p arg c x a m h₁ h₂ =>
    exact keep (.intStoreTrap s f t p arg c x a m h₁ h₂) rfl ht
  | floatStore s f t arg c x a m b h₁ h₂ =>
    exact keep (.floatStore s f t arg c x a m b h₁ h₂) rfl ht
  | floatStoreTrap s f t arg c x a m h₁ h₂ =>
    exact keep (.floatStoreTrap s f t arg c x a m h₁ h₂) rfl ht
  | memorySize s f a m h₁ => exact keep (.memorySize s f a m h₁) rfl ht
  | memoryGrow s f a m c r b h₁ h₂ => exact keep (.memoryGrow s f a m c r b h₁ h₂) rfl ht

/-- **Runs that call host functions, read through an implementation, are runs under the empty
host.** -/
theorem steps_impl {ι : H → V1.Func} {σ : H → V1.FuncType} {host : HostSemantics H}
    (hH : HostImpl ι σ host) {c d : Config H} (h : Steps host c d)
    (ht : HostTyped σ c.store.funcs) :
    HostTyped σ d.store.funcs ∧ Steps emptyHost10 (implC ι c) (implC ι d) := by
  induction h with
  | refl => exact ⟨ht, .refl⟩
  | tail _ hs ih =>
    obtain ⟨ht₁, h₁⟩ := ih
    obtain ⟨ht₂, h₂⟩ := step_impl hH hs ht₁
    exact ⟨ht₂, h₁.trans h₂⟩

/-! ## What an implementation cannot do -/

/-- **A host with an implementation keeps the function list**, up to the reading: the
implementing run is under the empty host from a store with no host function. -/
theorem hostImpl_funcs {ι : H → V1.Func} {σ : H → V1.FuncType} {host : HostSemantics H}
    (hH : HostImpl ι σ host) {s s' : Store H} (f : Frame) {a : FuncAddr} {h : H}
    {args : List Value} {r : Result} (ht : HostTyped σ s.funcs)
    (found : s.funcs[a.value]? = some (.host (σ h) h)) (arity : args.length = (σ h).params.length)
    (hb : host h s args (.returned s' r)) :
    s'.funcs.map (implF ι) = s.funcs.map (implF ι) :=
  InstInvoke.steps_funcs10 (hH s s' f a h args r ht found arity hb).2 (noHost10_implS ι s)

/-- In particular the number of functions is kept. -/
theorem hostImpl_funcs_length {ι : H → V1.Func} {σ : H → V1.FuncType} {host : HostSemantics H}
    (hH : HostImpl ι σ host) {s s' : Store H} (f : Frame) {a : FuncAddr} {h : H}
    {args : List Value} {r : Result} (ht : HostTyped σ s.funcs)
    (found : s.funcs[a.value]? = some (.host (σ h) h)) (arity : args.length = (σ h).params.length)
    (hb : host h s args (.returned s' r)) : s'.funcs.length = s.funcs.length := by
  have e := congrArg List.length (hostImpl_funcs hH f ht found arity hb)
  simpa using e

end Silmaril.Wasm.SpecTec.Sim10.HostRead
