module

public import Silmaril.Proofs.Wasm.Logic.V1.Examples.Straightline
public import Silmaril.Proofs.Wasm.Logic.V1.Examples.ArrayLemmas
public import Silmaril.Wasm.Logic.V1.Soundness.Thms

/-!
# Wasm Logic case studies

Ported so far (proofs in `Silmaril.Proofs.Wasm.Logic.V1.Examples.*`):

* the abstract predicates of §4 and Appendix B of Watt et al. (array segments,
  bounded and ordered arrays, B-tree pages), in `Silmaril.Wasm.Logic.V1.Examples.Defs`;
* their algebra (`Aseg_append`, `BA_push`, `Ordered_insert`, `Nodup_insert`, …);
* the straight-line examples of §3.3: `addConsts_spec`, `addLocal_spec`,
  `swapLocals01_spec`, `bumpCell_spec` (load, add, store on one owned cell).

`bumpCell_valid` below runs one of them through the soundness theorem, so the
derived triple becomes a statement about every big-step execution of the code.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1.Examples

open Silmaril.Wasm.V1 Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Runtime
  Silmaril.Wasm.V1.Execution Silmaril.Wasm.Logic.V1

/-- **The `bumpCell` example, end to end.** In a context with no assumed
function specifications, every execution of `bumpCell` (of derivation height at
most `n`, for any `n` and any host) from a state owning the cell at `a` with
contents `v` leaves that cell holding `v + 1`, does not trap, and preserves every
variable it does not modify. -/
theorem bumpCell_valid {H : Type*} (host : HostSemantics H) (n : Nat) (F : List FuncDef)
    (a : Term Nat) (v : Term (BitVec 32))
    (addr : ∀ ρ, ρ (.loc 0) = Value.int .i32 (BitVec.ofNat 32 (a ρ)))
    (inBounds : ∀ ρ, a ρ < 2 ^ 32) :
    Valid host n F [] none (Assert.mk [] (cell32 a v)) bumpCell
      (Assert.mk [] (cell32 a fun ρ => v ρ + 1)) :=
  (bumpCell_spec (Γ := ⟨F, fun _ _ _ => False, [], none⟩) a v addr inBounds).sound host n
    fun _ _ _ h => h.elim

end Silmaril.Wasm.Logic.V1.Examples
