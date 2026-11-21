module

public import Silmaril.X86.Open.Thms
public import Silmaril.Proofs.Process.LpsBridge.Syscall

/-!
# Proofs: the launch side of the open-machine/LPS bridge

* `init_aligned`: the launched configuration (`X86Launch.init`) is aligned with
  `launchState` (by definition: LPS's x86 initial state is an open-machine state).
* `init_model`: its model is LPS's initial model, alive and without lazy reservations.
* **`processSafe_of_launch`**: process safety of a launch from a `SafeN` run of the launch
  state to `Q`, and process safety of every aligned configuration with the initial model at a
  `Q` state. This is the whole-process theorem schema, for every image and every input.
-/

@[expose] public section

namespace Silmaril.Proofs.Process.LpsBridge

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Process.LpsBridge
open Silmaril.X86.Safe (SafeN)

/-- The launched configuration holds `launchState`. -/
theorem init_aligned (oracle : Oracle) (snapshot : X86Launch.Snapshot) (en : ExecEntry)
    (limit : Int) (inp : ProcInput) :
    Aligned (X86Launch.init (machine oracle) snapshot en limit inp)
      (launchState snapshot en inp) :=
  ⟨rfl, rfl, rfl⟩

/-- **The whole-process schema.** -/
theorem processSafe_of_launch {snapshot : X86Launch.Snapshot} {refusals : SpuriousCfg}
    {limit : Int} {en : ExecEntry} {inp : ProcInput} {Allowed : List Event → Prop}
    {Q : MState → Prop} (hA : Allowed [])
    (hrun : ∀ n, SafeN Silmaril.X86.Open.isa Q n (launchState snapshot en inp))
    (hQ : ∀ oracle (c : Config (machine oracle)) m, Aligned c m →
      c.model = (X86Launch.init (machine oracle) snapshot en limit inp).model → Q m →
      PSafe snapshot.image.segments (NativeX86.defaultRefusalFilter refusals) Allowed c) :
    ProcessSafe snapshot refusals limit en inp Allowed := fun oracle =>
  psafe_of_safeN hA (hQ oracle) (init_aligned oracle snapshot en limit inp) rfl hrun

end Silmaril.Proofs.Process.LpsBridge
