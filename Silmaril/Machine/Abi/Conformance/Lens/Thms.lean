module

public import Silmaril.Machine.Abi.Conformance.Lens.Defs
public import Silmaril.Machine.Abi.Conformance.Thms
import Silmaril.Proofs.Machine.Abi.Conformance.Lens

/-! # The machine lens: the #994 review's gaps, closed

PROVED (standard axioms), proofs in `Silmaril.Proofs.Machine.Abi.Conformance.Lens`:

* **No laundering.** `launder_not_store`: the laundering store of the review (`launder`: clear
  the direction flag and set x87 mode whenever the machine state changed) is the store of no
  `Mach`, through any map of integer states into its states: it violates put-put
  (`Mach.store_store`), which every `Mach.store` satisfies. `launder_direction`: it does change
  the direction flag. `models_eq_machine`: a machine whose state is fixed by its core and memory
  (an integer machine) models no FFI field but `.machine`, so its store carries the direction
  flag, x87 mode, MXCSR, x87 control word, vectors and thread pointer
  (`store_carried_of_determined`): a return obligation about them holds on such a machine only
  because the entry state met it.
* **Hidden state a step reads.** `tsc` holds a time-stamp value the FFI state does not
  determine and reads it into `rax` (`tsc_reads_hidden`: two completions of one FFI state step
  to different FFI states). No deterministic reference is faithful to it
  (`tsc_not_faithful_ofFun`), which is why `Ref` is a relation; `tsc_faithful`: it is faithful
  to `tscRef`, which may return any value. So `Faithful` is satisfiable for a machine with
  hidden state, and `Conforms.onRef` reads its rows on `tscRef`.
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance.Lens

open Silmaril.Machine.SystemV.Abi
open Silmaril.X86 (MState)

theorem launder_direction : (launder { blank with direction := true }
    ⟨{ blank.machine.core with rip := 1 }, blank.machine.memory⟩).direction ≠ true :=
  Silmaril.Proofs.Machine.Abi.Conformance.Lens.launder_direction

theorem launder_not_store (M : Mach) (e : MState → M.σ) :
    ¬ ∀ s y, M.store s (e y) = launder s y :=
  Silmaril.Proofs.Machine.Abi.Conformance.Lens.launder_not_store M e

theorem models_eq_machine (M : Mach)
    (hdet : ∀ x x', M.isa.core x = M.isa.core x' → M.isa.mem x = M.isa.mem x' → x = x')
    {f : FfiField} (hf : M.models f = true) : f = .machine :=
  Silmaril.Proofs.Machine.Abi.Conformance.Lens.models_eq_machine M hdet hf

theorem store_carried_of_determined (M : Mach)
    (hdet : ∀ x x', M.isa.core x = M.isa.core x' → M.isa.mem x = M.isa.mem x' → x = x')
    {f : FfiField} (hf : f ≠ .machine) (s : Ffi.State) (y : M.σ) : f.Agree (M.store s y) s :=
  Silmaril.Proofs.Machine.Abi.Conformance.Lens.store_carried_of_determined M hdet hf s y

theorem tsc_reads_hidden : ∃ s x x', tsc.Fills s x ∧ tsc.Fills s x' ∧ ∃ y y',
    tsc.isa.step x = some y ∧ tsc.isa.step x' = some y' ∧ tsc.store s y ≠ tsc.store s y' :=
  Silmaril.Proofs.Machine.Abi.Conformance.Lens.tsc_reads_hidden

theorem tsc_not_faithful_ofFun (r : Ffi.State → Option Ffi.State) :
    ¬ Faithful (Ref.ofFun r) tsc :=
  Silmaril.Proofs.Machine.Abi.Conformance.Lens.tsc_not_faithful_ofFun r

/-- Every hidden time-stamp value completes an FFI state. -/
theorem tsc_fillsAll : tsc.FillsAll := fun _ _ h => h .machine rfl

theorem tsc_faithful : Faithful tscRef tsc :=
  Silmaril.Proofs.Machine.Abi.Conformance.Lens.tsc_faithful

end Silmaril.Machine.Abi.Conformance.Lens

end
