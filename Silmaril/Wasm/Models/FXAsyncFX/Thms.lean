module

public import Silmaril.Proofs.Wasm.Models.FXAsyncFX.Example
public import Silmaril.Wasm.Models.FXAsyncPC.Thms

/-!
# The asyncify handler kernel as a fragment of `StepFX'`: results

The header of `Defs`. For a setting `S` (`Setup`) and a kernel program `W` over Core values,
with `Ok S W` (every kernel function is an FX function of the store whose body encodes it,
`EncI`; the root frame is of module `M`; tag addresses are distinct):

* **`sim_step`**: from related configurations (`Rel`), a kernel step in the fragment (`fine`)
  is matched by a positive `StepFX'` run to related configurations, or, when the kernel stops,
  by the `StepFX'` result (`Matched`). One `StepFX'` step per `push` (its `nop`), `prim`, `drop`;
  two for `contNew` and a suspension (the capture and `br 0`); `1 + 1 + np` for a call (`call`,
  `invoke`, the prologue), two more for `cond`; three or four for `resume` (two block entries,
  `resume`, and `invoke` for a fresh continuation); one to five for a return.
* **`kernel_in_fx`**: when every configuration of the kernel run from `x` is in the fragment
  (`Supported`), every behaviour of the kernel from `x` (returned values, divergence) is a
  `StepFX'` behaviour of the related FX configuration, and (`kernel_no_trap`) the kernel does
  not trap.
* **`lower_in_fx`**: composed with `FXAsync.lower_correct_init`, every behaviour of the
  asyncify target `tstep (compP W)` called on `f` is a `StepFX'` behaviour of the WasmFX
  program `fxInit S f args`; **`pc_in_fx`**: the same for the first-order machine `fstep`
  (`FXAsyncPC.kernel_pc_correct`).

* **`ex_end_to_end`** (non-vacuity): a generator `exW` (yield `1`, return `2`; the handler
  resumes it under a second handler and adds) satisfies every hypothesis in a concrete setting
  `exS P host` (for every profile and host): its asyncify target returns `[3]`, and the WasmFX
  program `fxInit (exS P host) 1 []` returns `[3]` under `StepFX'`.

What this does **not** say: only inclusion is proved (`StepFX'` is not shown deterministic on
the fragment, so the WasmFX program could have further behaviours); traps are outside the
fragment; the fragment is one-clause, argument-less `resume`, inlined (non-recursive) handlers,
fixed payload arities, one-result functions and `i32` operators; and nothing here is Core 3.0
`Step`: the asyncify target is still an abstract machine. See "Stretch, fxasync" in
`docs/projects/wasm-wasi.md`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXAsyncFX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncPC
open Silmaril.Proofs.Wasm.Models.FXAsyncFX (Matched)

variable {H : Type} (S : Setup H) {W : Prog (Ins Val)}

/-- **The simulation step.** -/
theorem sim_step (hok : Ok S W) {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c)
    (hf : fine W x = true) : Matched S W c (sstep W i32Test x) :=
  Silmaril.Proofs.Wasm.Models.FXAsyncFX.sim_step S hok hR hf

/-- **Every kernel behaviour in the fragment is a `StepFX'` behaviour.** -/
theorem kernel_in_fx (hok : Ok S W) {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c)
    (hsup : Supported W x) :
    ∀ b ∈ beh (sstep W i32Test) x, obsB b ∈ behavioursFX' S.P S.host S.fx c :=
  Silmaril.Proofs.Wasm.Models.FXAsyncFX.beh_in_fx S hok hR hsup

/-- In the fragment the kernel does not trap. -/
theorem kernel_no_trap (hok : Ok S W) {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c)
    (hsup : Supported W x) : Obs.trap ∉ beh (sstep W i32Test) x :=
  Silmaril.Proofs.Wasm.Models.FXAsyncFX.trap_not_beh S hok hR hsup

/-- The kernel's call of `f` and the WasmFX program `fxInit S f args` are related. -/
theorem rel_init (f : Nat) (args : List Val) :
    Rel S W (sInit f (args.map .val)) (fxInit S f args) :=
  Silmaril.Proofs.Wasm.Models.FXAsyncFX.rel_init S f args

/-- **The asyncify lowering is sound for WasmFX on the fragment**: every behaviour of the
compiled program `tstep (compP W)` called on `f` is a `StepFX'` behaviour of the WasmFX program
`fxInit S f args`. -/
theorem lower_in_fx (hok : Ok S W) (f : Nat) (args : List Val)
    (hsup : Supported W (sInit f (args.map .val))) :
    ∀ b ∈ beh (tstep (compP W) i32Test) (tInit f (args.map .val)),
      obsB b ∈ behavioursFX' S.P S.host S.fx (fxInit S f args) := by
  rw [← lower_correct_init]
  exact kernel_in_fx S hok (rel_init S f args) hsup

/-- The same for the first-order asyncify machine `fstep`. -/
theorem pc_in_fx (hok : Ok S W) (f : Nat) (args : List Val)
    (hsup : Supported W (sInit f (args.map .val))) :
    ∀ b ∈ beh (fstep (annP (compP W)) (bodies (compP W) (rootCode f)) i32Test)
        (fInit f (args.map .val)),
      obsB b ∈ behavioursFX' S.P S.host S.fx (fxInit S f args) := by
  rw [← kernel_pc_correct]
  exact kernel_in_fx S hok (rel_init S f args) hsup

/-- **A generator end to end**: the asyncify target of `exW` returns `[3]` (a closed run), and
the WasmFX program returns `[3]` under `StepFX'`, through `lower_in_fx`'s hypotheses, all
discharged. -/
theorem ex_end_to_end (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics Nat) :
    Obs.done [.val (Val.i32 3)] ∈ beh (tstep (compP Silmaril.Proofs.Wasm.Models.FXAsyncFX.exW)
      i32Test) (tInit 1 []) ∧
    Behaviour.returns [Val.i32 3] ∈ behavioursFX' P host Silmaril.Proofs.Wasm.Models.FXAsyncFX.exFx
      (fxInit (Silmaril.Proofs.Wasm.Models.FXAsyncFX.exS P host) 1 []) := by
  have ht : Obs.done [.val (Val.i32 3)] ∈ beh (tstep (compP Silmaril.Proofs.Wasm.Models.FXAsyncFX.exW)
      i32Test) (tInit 1 (([] : List Val).map .val)) :=
    Or.inl ⟨80, _, Silmaril.Proofs.Wasm.Models.FXAsyncFX.ex_tgt_run, rfl⟩
  exact ⟨ht, lower_in_fx _ (Silmaril.Proofs.Wasm.Models.FXAsyncFX.exOk P host) 1 []
    Silmaril.Proofs.Wasm.Models.FXAsyncFX.exSupported _ ht⟩

/-- info: 'Silmaril.Wasm.Models.FXAsyncFX.ex_end_to_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ex_end_to_end

/-- info: 'Silmaril.Wasm.Models.FXAsyncFX.lower_in_fx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lower_in_fx

/-- info: 'Silmaril.Wasm.Models.FXAsyncFX.pc_in_fx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pc_in_fx

end Silmaril.Wasm.Models.FXAsyncFX
