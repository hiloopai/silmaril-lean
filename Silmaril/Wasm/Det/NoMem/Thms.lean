module

public import Silmaril.Wasm.Det.NoMem.Defs
public import Silmaril.Proofs.Wasm.Det.NoMem.Main

/-!
# The memory-free, float-free subset is deterministic modulo traps and imports

Every statement holds at an **arbitrary** profile `P` (any NaN policy, relaxed-SIMD choice,
`$ND` and grow policy); nothing assumes a deterministic profile.

**The invariant** (`Silmaril.Wasm.Det.NoMem.Inv q ind`: subset code, and subset bodies for every
function that may be entered):

* `inv_closed`: closed under host-free steps and under resuming an import call with **any**
  answer (`Silmaril.Wasm.Det.Core.Closed`);
* `step_transfer`: on subset code, a Core step at `P` is a step at every profile; in particular
  every step is a step of the deterministic profile `profile o` (`inv_detUpTo`);
* `detCfg_of_inv`: **every `Inv` configuration is deterministic modulo traps and imports**
  (`DetCfg P c`). The proof goes through `Silmaril.Wasm.Det.Core.detCfg_of_detUpTo` (uniqueness of
  normal forms at deterministic profiles, silmaril-lean), so trap and exception bubbling are
  covered.

No profile choice is left in the subset: the profile-dependent rules are excluded syntactically
(floats, vectors, memory, `table.grow`), and silmaril-lean's GC rules have no allocation failure.

**Per function, per module, per instance** (executable checks, kernel-evaluable):

* `detFn_of_storeB`, `detModule_of_storeB`: a store all of whose functions are in the subset
  (`storeB`, indirect calls allowed) is deterministic, every function and every module over it;
* `detFn_of_closB`, `detModule_of_closB`, `detFn_of_detFnB`, `detCall_of_detFnB`: **direct
  mode**: a set of functions closed under direct calls, without indirect calls (`closB`), is
  deterministic even when the rest of the store (the module) is not in the subset;
* `detInst_of_storeB`: with an instantiation configuration of the subset, the instance
  (`Silmaril.Wasm.Det.Core.DetInst`).

**Tactic** `wasm_det`: closes `DetFn P s a`, `DetCall P s a vs`, `DetModule P Entry s` (full
mode) and `DetModule P (· ∈ A) s` (direct mode) for concrete stores by kernel evaluation of
`detFnB`, `storeB` or `closB`.

Proofs: `Silmaril.Proofs.Wasm.Det.NoMem.{Basic,Transfer,Preserve,Step,Main}`. New.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.NoMem

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Det.Core
open Silmaril.Wasm.Numerics (Profile)

/-! ## The invariant -/

/-- **Profile transfer**: on subset code, a Core step at profile `P` is a step at every profile
`P'`. -/
theorem step_transfer {H : Type} {q : Nat → Bool} {ind : Bool} {P P' : Profile}
    {host : HostSemantics H} {c c' : Config H} (h : Step P host c c') {p : Prop}
    (hN : Seq q ind c.frame.module.funcs p c.code) : Step P' host c c' :=
  Silmaril.Proofs.Wasm.Det.NoMem.step_transfer h hN

/-- **Closure** of the invariant under host-free steps and resumptions with any answer. -/
theorem inv_closed {q : Nat → Bool} {ind : Bool} (P : Profile) : Closed P (Inv q ind) :=
  Silmaril.Proofs.Wasm.Det.NoMem.inv_closed P

/-- Every host-free step from an `Inv` configuration is a step of the deterministic profile. -/
theorem inv_detUpTo {q : Nat → Bool} {ind : Bool} {P : Profile} (o : GrowOracle)
    {c : Config Nat} (hc : Inv q ind c) : DetUpTo P o c :=
  Silmaril.Proofs.Wasm.Det.NoMem.inv_detUpTo o hc

/-- **Subset configurations are deterministic modulo traps and imports**, at every profile. -/
theorem detCfg_of_inv {q : Nat → Bool} {ind : Bool} {P : Profile} {c : Config Nat}
    (hc : Inv q ind c) : DetCfg P c :=
  Silmaril.Proofs.Wasm.Det.NoMem.detCfg_of_inv hc

/-! ## Functions, modules, instances -/

/-- **Full mode**: every function of a store passing `storeB` is deterministic, every
profile. -/
theorem detFn_of_storeB {P : Profile} {s : Store Nat} (h : storeB s = true) (a : Nat) :
    DetFn P s a :=
  Silmaril.Proofs.Wasm.Det.NoMem.detFn_of_storeB h a

/-- **Direct mode**: the functions of a list `A` passing `closB` are deterministic, every
profile, whatever the other functions of the store do. -/
theorem detFn_of_closB {P : Profile} {s : Store Nat} {A : List Nat} (h : closB s A = true)
    {a : Nat} (ha : a ∈ A) : DetFn P s a :=
  Silmaril.Proofs.Wasm.Det.NoMem.detFn_of_closB h ha

/-- **The per-function check** `detFnB` (direct mode on the computed direct-call closure). -/
theorem detFn_of_detFnB {P : Profile} {s : Store Nat} {a : Nat} (h : detFnB s a = true) :
    DetFn P s a :=
  Silmaril.Proofs.Wasm.Det.NoMem.detFn_of_detFnB h

/-- The per-function check gives determinism of every invocation, typed or not. -/
theorem detCall_of_detFnB {P : Profile} {s : Store Nat} {a : Nat} (h : detFnB s a = true)
    (vs : List Val) : DetCall P s a vs := by
  simp only [detFnB, Bool.and_eq_true] at h
  exact detCfg_of_inv (Silmaril.Proofs.Wasm.Det.NoMem.inv_invoke vs
    (Silmaril.Proofs.Wasm.Det.NoMem.mode_direct _) (Silmaril.Proofs.Wasm.Det.NoMem.funOk_of_closB h.2)
    h.1)

/-- **Per module, full mode**: a store passing `storeB` is a deterministic module for every set
of entries, every profile. -/
theorem detModule_of_storeB {P : Profile} {Entry : Nat → Prop} {s₀ : Store Nat}
    (h : storeB s₀ = true) : DetModule P Entry s₀ :=
  Silmaril.Proofs.Wasm.Det.NoMem.detModule_of_storeB h

/-- **Per module, direct mode**: with entries `A`, a store passing `closB s₀ A` is a
deterministic module, every profile. -/
theorem detModule_of_closB {P : Profile} {s₀ : Store Nat} {A : List Nat}
    (h : closB s₀ A = true) : DetModule P (· ∈ A) s₀ :=
  Silmaril.Proofs.Wasm.Det.NoMem.detModule_of_closB h

/-- **Per instance**: an instantiation configuration of the subset over a store passing
`storeB` is a deterministic instance. -/
theorem detInst_of_storeB {P : Profile} {c₀ : Config Nat} {Entry : Nat → Prop}
    (h : storeB c₀.store = true)
    (hc : Seq (fun _ => true) true c₀.frame.module.funcs False c₀.code) : DetInst P c₀ Entry :=
  Silmaril.Proofs.Wasm.Det.NoMem.detInst_of_storeB h hc

/-- The checks only read the function instances. -/
theorem storeB_congr {s t : Store Nat} (h : s.funcs = t.funcs) : storeB s = storeB t :=
  Silmaril.Proofs.Wasm.Det.NoMem.storeB_congr h

theorem closB_congr {s t : Store Nat} (h : s.funcs = t.funcs) (A : List Nat) :
    closB s A = closB t A :=
  Silmaril.Proofs.Wasm.Det.NoMem.closB_congr h A

/-- Closes `DetFn P s a`, `DetCall P s a vs`, `DetModule P Entry s` or `DetModule P (· ∈ A) s`
for a concrete store whose relevant functions are in the memory-free, float-free subset, by
kernel evaluation of `detFnB`, `storeB` or `closB`. -/
macro "wasm_det" : tactic => `(tactic| first
  | exact Silmaril.Wasm.Det.NoMem.detFn_of_detFnB (by decide +kernel)
  | exact Silmaril.Wasm.Det.NoMem.detCall_of_detFnB (by decide +kernel) _
  | exact Silmaril.Wasm.Det.NoMem.detFn_of_storeB (by decide +kernel) _
  | exact Silmaril.Wasm.Det.NoMem.detModule_of_storeB (by decide +kernel)
  | exact Silmaril.Wasm.Det.NoMem.detModule_of_closB (by decide +kernel))

end Silmaril.Wasm.Det.NoMem
