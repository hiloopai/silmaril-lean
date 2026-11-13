module

public import Silmaril.Wasm.Wac.Seq.Defs
public import Silmaril.Wasm.Wac.Graph.Thms
public import Silmaril.Proofs.Wasm.Wac.Seq

/-!
# Sequential composition: theorems

Proofs in `Silmaril.Proofs.Wasm.Wac.Seq`:

* `seq_assoc : (g₁.seq S g₂).seq S g₃ = g₁.seq S (g₂.seq S g₃)`: **associativity**,
  syntactically; `toComp_seq_assoc`: hence the composed components are equal;
* `plugSrc_seq`: plugging into a sequential composition is plugging twice;
* `explicate_mapSrc_explicate`: substitution keeps explicit instances explicit.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

open Silmaril.Wasm.Component

/-- **Associativity of plugging**, on composed components. -/
theorem toComp_seq_assoc {M : Type} (P : Nat → Comp M) (g₁ g₂ g₃ : Graph) :
    ((g₁.seq (fun k => sigOf (P k)) g₂).seq (fun k => sigOf (P k)) g₃).toComp P =
      (g₁.seq (fun k => sigOf (P k)) (g₂.seq (fun k => sigOf (P k)) g₃)).toComp P := by
  rw [seq_assoc]

end Silmaril.Wasm.Wac
