module

public import Silmaril.Wasm.KernelEval.Defs
import Silmaril.Proofs.Wasm.KernelEval.Basic

@[expose] public section

/-!
# Kernel evaluation of a small Wasm subset: results

Proofs in `Silmaril.Proofs.Wasm.KernelEval.Basic`.

* `runRec_eq_run`: the recursor-driven run is the reference run;
* `run_add`, `run_add_of_running`: runs compose, so a long run can be checked in chunks against intermediate
  configurations (piecewise checking);
* `step_mapMem`, `run_mapMem`: a memory simulation (`MemSim`) commutes with steps and runs;
* **`memSim_toNatMem`**: packing a list memory into one number is a memory simulation, so
  **`returns_toNatMem`**: a check evaluated on the packed memory is the check on the list
  memory; `zeros_eq`: the packed zero memory is the packed list of zeros;
* `run_of_returns`: what a successful check means for the reference run.
-/

namespace Silmaril.Wasm.KernelEval

variable {M : Type} [MemOps M]

theorem runRec_eq_run (n : Nat) (c : Config M) : runRec n c = run n c :=
  Proofs.Wasm.KernelEval.runRec_eq_run n c

theorem run_add (a b : Nat) (c : Config M) : run (a + b) c = (run a c).andThen (run b) :=
  Proofs.Wasm.KernelEval.run_add a b c

/-- One chunk of a piecewise check: a run that stops at a checked intermediate configuration. -/
theorem run_add_of_running {a b : Nat} {c c' : Config M} (h : run a c = .running c') :
    run (a + b) c = run b c' := by
  rw [run_add, h]; rfl

theorem step_mapMem {N : Type} [MemOps N] {g : M → N} (h : MemSim g) (c : Config M) :
    step (c.mapMem g) = (step c).mapMem g :=
  Proofs.Wasm.KernelEval.step_mapMem h c

theorem run_mapMem {N : Type} [MemOps N] {g : M → N} (h : MemSim g) (n : Nat) (c : Config M) :
    run n (c.mapMem g) = (run n c).mapMem g :=
  Proofs.Wasm.KernelEval.run_mapMem h n c

theorem memSim_toNatMem : MemSim ListMem.toNatMem :=
  Proofs.Wasm.KernelEval.memSim_toNatMem

theorem zeros_eq (n : Nat) : (⟨List.replicate n 0⟩ : ListMem).toNatMem = NatMem.zeros n :=
  Proofs.Wasm.KernelEval.zeros_eq n

theorem returns_toNatMem (fuel : Nat) (body : List Instr) (locals : List (BitVec 32))
    (m : ListMem) (v : BitVec 32) :
    returns fuel body locals m.toNatMem v = returns fuel body locals m v :=
  Proofs.Wasm.KernelEval.returns_toNatMem fuel body locals m v

theorem run_of_returns {fuel : Nat} {body : List Instr} {locals : List (BitVec 32)} {m : M}
    {v : BitVec 32} (h : returns fuel body locals m v = true) :
    ∃ s ls m', run fuel (Config.init body locals m) = .done (v :: s) ls m' :=
  Proofs.Wasm.KernelEval.run_of_returns h

end Silmaril.Wasm.KernelEval
