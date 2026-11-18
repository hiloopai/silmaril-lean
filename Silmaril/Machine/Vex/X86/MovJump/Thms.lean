module

public import Silmaril.Machine.Vex.X86.MovJump.Defs
public import Silmaril.Machine.Vex.Validate.Semantics.Defs
import Silmaril.Proofs.Machine.Vex.X86.MovJump

public section

namespace Silmaril.Machine.Vex.AMD64Scalar.MovJump

open Silmaril.Semantics.Region
open Silmaril.X86 (MState)
open Silmaril.Machine.Region.X86 (system)

theorem Fragment.decode_code (fragment : Fragment) : fragment.code.decode? 2 = some fragment.listing :=
  Proofs.decode fragment

theorem Fragment.decode_scalar (fragment : Fragment) :
    X86.decode fragment.base fragment.bytes = .ok fragment.block := Proofs.scalarDecode fragment

/-- Composable model map with real loaded memory as an invariant. -/
def Fragment.realization (fragment : Fragment) (guard : fragment.Guard) (completion : Bool) (ret : Word) :
    Realizes fragment.simple (system ret) := Proofs.realizes fragment guard completion ret

theorem Fragment.realization_relates (fragment : Fragment) (guard : fragment.Guard) (completion : Bool) (ret : Word)
    (input : Input) (full : MState) :
    (fragment.realization guard completion ret).relates input full ↔ fragment.Related completion input full := Iff.rfl

/-- The simple model has a normal exit, not UB or a missing behavior. -/
theorem Fragment.simple_exit (fragment : Fragment) (guard : fragment.Guard) {input : Input}
    (entry : input.rip = fragment.base) :
    ExitsNormally fragment.simple fragment.support input [] (fragment.block.run input) :=
  Proofs.smallGuard fragment guard entry

/-- Compute the Region WP at the supported scalar entry using the block evaluator. -/
theorem Fragment.entryWP_iff (fragment : Fragment) (guard : fragment.Guard) (Q : Nat → List Empty → Input → Prop)
    (input : Input) : fragment.entryWP Q input ↔
    input.rip = fragment.base ∧ Q fragment.target.toNat [] (fragment.block.run input) :=
  Proofs.entryWP fragment guard Q input

/-- All admitted scalar executions are non-UB. The scalar adapter has no
events or halt codes; this safety theorem does not require the exit guard. -/
theorem Fragment.wp_noUB (fragment : Fragment) (Q : Nat → List Empty → Input → Prop) :
    NoUB fragment.simple (fragment.entryWP Q) fragment.support (fun _ => False) (fun _ => False) :=
  Proofs.wpNoUB fragment Q

/-- The guard upgrades the partial WP to a total scalar contract. -/
theorem Fragment.wp_contract (fragment : Fragment) (guard : fragment.Guard) (Q : Nat → List Empty → Input → Prop) :
    TotalHoare fragment.simple (fragment.entryWP Q) fragment.support Q (fun _ _ _ => False) :=
  Proofs.wpContract fragment guard Q

/-- Transfer the proved scalar WP contract through the model morphism.
The full admitted domain is abstract: it need only supply executable loaded
bytes via the current memory API and a projected scalar entry satisfying WP. -/
theorem Fragment.transfer_wp (fragment : Fragment) (guard : fragment.Guard) (completion : Bool) (ret : Word)
    (Q : Nat → List Empty → Input → Prop) {admit : MState → Prop}
    {ubStop : Silmaril.X86.Ext.Outcome → Prop}
    (initial : ∀ full, admit full → fragment.code.LoadedIn full.memory ∧ fragment.entryWP Q (project completion full)) :
    NoUB (system ret) admit fragment.support (fun _ => False) ubStop ∧
    TotalHoare (system ret) admit fragment.support (fun label es full => Q label es (project completion full))
      (fun stop _ _ => ubStop stop) := Proofs.transferWP fragment guard completion ret Q initial

/-- The full machine retires through the cut to a unique normal exit. The
output relation is a projection and a loading invariant, not a state frame. -/
theorem Fragment.full_exit (fragment : Fragment) (guard : fragment.Guard) (completion : Bool) (ret : Word)
    {input : Input} {initial : MState} (entry : input.rip = fragment.base)
    (related : fragment.Related completion input initial) :
    ∃ final, ExitsNormally (system ret) fragment.support initial [] final ∧
      fragment.Related completion (fragment.block.run input) final :=
  Proofs.fullExit fragment guard completion ret entry related

/-- Lift a scalar postcondition to every full first exit, with separate
progress, termination and absence of a fault or other halt inside the cut. -/
theorem Fragment.lift_postcondition (fragment : Fragment) (guard : fragment.Guard) (completion : Bool) (ret : Word)
    {input : Input} {initial : MState} (entry : input.rip = fragment.base)
    (related : fragment.Related completion input initial) (property : List Empty → Input → Prop)
    (proved : property [] (fragment.block.run input)) :
    (∃ final, ExitsNormally (system ret) fragment.support initial [] final) ∧
    ∀ trace final, FirstExit (system ret) fragment.support initial trace final →
      property trace (project completion final) :=
  Proofs.postcondition fragment guard completion ret entry related property proved

theorem Fragment.region_sound (fragment : Fragment) (guard : fragment.Guard) (ret : Word) :
    Sound (system ret) (fun initial => initial.core.rip = fragment.base ∧ fragment.code.LoadedIn initial.memory)
      fragment.support (· = fragment.target.toNat) := Proofs.regionSound fragment guard ret

/-- Checker acceptances for these bytes compose with the real-model bridge.
The full first exit is guaranteed independently of target execution. -/
theorem Fragment.validated_exit (fragment : Fragment) (guard : fragment.Guard) (completion : Bool) (ret : Word)
    {raw : Raw.Block} {pair : Pair} (accepted : validate fragment.base fragment.bytes raw = .ok pair)
    {initial : MState} (entry : initial.core.rip = fragment.base) (loaded : fragment.code.LoadedIn initial.memory) :
    ∃ final, ExitsNormally (system ret) fragment.support initial [] final ∧
      pair.target.run (project completion initial) = .ok (project completion final) :=
  Proofs.validatedExit fragment guard completion ret accepted entry loaded

/-- Agreement at these two named roots: every first exit of the existing x86
system has the projected state returned by every VEX boundary behavior, and
both roots have an execution. This is not an intersection of reference models. -/
theorem Fragment.validated_beh (fragment : Fragment) (guard : fragment.Guard) (completion : Bool) (ret : Word)
    {raw : Raw.Block} {pair : Pair} (accepted : validate fragment.base fragment.bytes raw = .ok pair)
    {initial : MState} (entry : initial.core.rip = fragment.base) (loaded : fragment.code.LoadedIn initial.memory) :
    ∃ final, ExitsNormally (system ret) fragment.support initial [] final ∧
      ∀ outcome, (targetSem pair.target).Beh (project completion initial) outcome ↔
        outcome = .returned (project completion final) :=
  Proofs.validatedBeh fragment guard completion ret accepted entry loaded

end Silmaril.Machine.Vex.AMD64Scalar.MovJump
