module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.MemSizeRefute
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdAlign

/-!
# The forward 1.0 whole step on the documented fragment (round 4)

With the successful loads (`FwdLoadVal`), every obligation of round 3's assembly is discharged at
the byte-answering builtins `bytesB10 (Profile.spec nd r)`. This module states the result as a
frozen target and proves it.

* **`Task.wholeStepFwd10`** (proved, `wholeStepFwd10`): every V1 step from a configuration whose
  image is typed, whose code is `Plain10`, which satisfies `GSetOk` and whose memories are aligned
  (`MemsAligned10`) is a step of the wasm-1.0 script between the images, and the successor's
  image is typed.
* **`Task.wholeRunFwd10`** (proved, `wholeRunFwd10`): the same along a V1 run, given `GSetOk` at
  every configuration of the run. `Plain10` (round 3's `plain10_steps`) and `MemsAligned10`
  (`memsAligned10_steps`; a typed store has no host function) are invariants, and the image stays
  typed (`typed10_step'`). `Plain10` holds at every invocation (`plain10_invoke`).
* **The alignment hypothesis cannot be dropped** (`not_wholeStepFwd10_unaligned`): without
  `MemsAligned10`, the statement fails at every builtins, at `memory.size` over a one-byte memory
  (`MemSizeRefute`).

The fragment is everything V1 does except what the hypotheses exclude. `GSetOk` is what V1
validation guarantees and V1 does not check (a `global.set` writes a value of the global's type);
it is assumed, not derived from validation. Stores are matched vacuously: no typed image contains
a `STORE` (round 2's `STORE` erratum), so a storing program is not covered.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step Steps)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10 (GSetOk ActiveF)

/-- The builtins of the forward 1.0 half: the spec's numerics, with `$bytes_`, `$ibytes_` and
`$growmemory` answered as V1 does. -/
noncomputable abbrev fwdB10 (nd : Bool) (r : RelaxedChoice) : Builtins :=
  bytesB10 (Profile.spec nd r)

/-! ## The step -/

/-- **The forward 1.0 whole step on the documented fragment** (frozen; proved below). -/
def Task.wholeStepFwd10 : Prop :=
  ∀ (H : Type) (hn : H → String) (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice)
    (c c' : Config H), Typed10 (simEnv10 (fwdB10 nd r)) hn c → Plain10 c.code →
    GSetOk c.store c.frame c.code → MemsAligned10 c.store → Step host c c' →
      Typed10 (simEnv10 (fwdB10 nd r)) hn c' ∧
        SStepB (simEnv10 (fwdB10 nd r)) (configV hn c) (configV hn c')

/-- **`Task.wholeStepFwd10` holds.** -/
theorem wholeStepFwd10 : Task.wholeStepFwd10 :=
  fun _ _ _ _ _ _ _ hc hpl hg hal h =>
    ⟨typed10_step' h hc hg, wholeStepFwd10_bytesB10'' hc hpl hg hal h⟩

/-! ## The run -/

/-- **The forward 1.0 half along a V1 run** (frozen; proved below): from a configuration whose
image is typed, whose code is `Plain10` and whose memories are aligned, every V1 run along which
`GSetOk` holds is a run of the wasm-1.0 script between the images. -/
def Task.wholeRunFwd10 : Prop :=
  ∀ (H : Type) (hn : H → String) (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice)
    (c c' : Config H), Typed10 (simEnv10 (fwdB10 nd r)) hn c → Plain10 c.code →
    MemsAligned10 c.store → (∀ d, Steps host c d → GSetOk d.store d.frame d.code) →
    Steps host c c' →
      Typed10 (simEnv10 (fwdB10 nd r)) hn c' ∧
        Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r))) (configV hn c) (configV hn c')

/-- **`Task.wholeRunFwd10` holds.** -/
theorem wholeRunFwd10 : Task.wholeRunFwd10 := by
  intro H hn host nd r c c' hc hpl hal hg h
  induction h with
  | refl => exact ⟨hc, .refl⟩
  | @tail b d hcb hbd ih =>
    have hb : Typed10 (simEnv10 (fwdB10 nd r)) hn b ∧
        Relation.ReflTransGen (SStepB (simEnv10 (fwdB10 nd r))) (configV hn c) (configV hn b) :=
      ih
    have hnh : NoHost10 c.store := noHost10_of_typed (typedV_state_of_typed10 hc)
    have hal' : MemsAligned10 b.store := (memsAligned10_steps hcb hnh hal).2
    have hpl' : Plain10 b.code := plain10_steps hcb hpl
    have hstep := wholeStepFwd10 H hn host nd r b d hb.1 hpl' (hg b hcb) hal' hbd
    exact ⟨hstep.1, hb.2.tail hstep.2⟩

/-! ## The alignment hypothesis is needed -/

/-- Nothing active in `memory.size` is a `global.set` redex. -/
theorem gsetOk_memorySize {H : Type} (s : Store H) (f : Frame) :
    GSetOk s f [.source .memorySize] := by
  intro f' v x a g hact
  generalize hcode : ([.source .memorySize] : List Admin) = code at hact
  cases hact with
  | piece =>
    have hl := congrArg List.length hcode
    simp only [List.length_append, List.length_cons, List.length_nil] at hl
    omega
  | label hm _ => simp [← hcode] at hm
  | frame hm _ => simp [← hcode] at hm

/-- **Without `MemsAligned10` the forward step fails**, at every builtins: at `memory.size` over a
one-byte memory the configuration is typed, `Plain10` and `GSetOk`, V1 steps, and the 1.0 script
is stuck. -/
theorem not_wholeStepFwd10_unaligned (B : Builtins) {H : Type} (hn : H → String)
    (host : HostSemantics H) :
    ¬ ∀ c c' : Config H, Typed10 (simEnv10 B) hn c → Plain10 c.code →
      GSetOk c.store c.frame c.code → Step host c c' →
        SStepB (simEnv10 B) (configV hn c) (configV hn c') := by
  intro F
  have hpl : Plain10 (memSizeCfg10 H).code := plain10_vals_sources [] [.memorySize]
  have h := F (memSizeCfg10 H) (memSizeCfg10' H) (typed10_memSize B hn) hpl
    (gsetOk_memorySize _ _) (step_memSize10 host)
  exact stuck10_memorySize B (frameMemory_memSize10 H) (by decide) _ h

end Silmaril.Wasm.SpecTec.Sim10.Whole
