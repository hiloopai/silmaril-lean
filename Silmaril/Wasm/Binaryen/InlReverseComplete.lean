module

public import Silmaril.Wasm.Binaryen.InlReverseGeneric
public import Silmaril.Wasm.Binaryen.InlReverseCallerStep
public import Silmaril.Wasm.Binaryen.InlReverseCalleeStep

@[expose] public section

/-! # Complete chosen reverse inlining at every numerical profile

The generic, changed-caller and relocated-callee proofs recurse together on the
size of the actual target code. Runtime control and activation bodies are
strictly smaller; pending initialization and administrative suffix reductions
are handled separately by the decreasing checkpoint measure.

Every selected target execution is matched using its own outcomes. No numeric
determinism, unique terminal result, or termination-excludes-divergence argument
is used. The resulting law supplies the existing finite-run and divergence
transport for the full checkpoint relation.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Execution.Core.Sim Numerics SingleThreaded

variable {H : Type} {p : Prm} {P : Profile}

/-- Close all three reverse runtime modes by induction on the target code. -/
theorem reverseIH (parameters : PrmOk p) (initialization : PrmC p)
    (functionIndex : p.mi.funcs[p.fx.toNat]? = some p.af) :
    ∀ limit : Nat, ReverseIH p P H limit := by
  intro limit
  induction limit with
  | zero =>
    exact {
      generic := by intro original target next impossible; omega
      caller := by intro original target next impossible; omega
      callee := by intro d locals original target next impossible; omega }
  | succ limit ih =>
    exact {
      generic := reverse_generic_step parameters ih
      caller := reverse_caller_step parameters initialization functionIndex ih
      callee := reverse_callee_step parameters ih }

/-- The actual complete chosen reverse law required by the checkpoint
simulation, for any numerical profile and any related well-typed source. -/
theorem chosenReverseStep (parameters : PrmOk p) (initialization : PrmC p)
    (functionIndex : p.mi.funcs[p.fx.toNat]? = some p.af) :
    ChosenReverseStep p P H := by
  intro original target next typed runtime stores selected
  exact (reverseIH parameters initialization functionIndex (sizeOf target.code + 1)).generic
    (Nat.lt_succ_self _) typed runtime stores selected

/-- Every existing good inlining instance supplies the complete law; no new
restriction on the body, numerical profile or selected execution is added. -/
theorem chosenReverseStep_of_good (good : Good p) : ChosenReverseStep p P H := by
  obtain ⟨initialization⟩ := good.callee
  exact chosenReverseStep good.ok initialization good.fx

/-- The full inlining checkpoint simulation is now unconditional on an
external reverse-step oracle. -/
def completeReverseSim (good : Good p) :
    ConfigSim P Det.noHost (ReverseCheckpoint (H := H) p) :=
  reverseCheckpointSim (chosenReverseStep_of_good good)

end Silmaril.Wasm.Binaryen.InlR
