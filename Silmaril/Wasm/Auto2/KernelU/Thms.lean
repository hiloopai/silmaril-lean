module

public import Silmaril.Wasm.Auto2.KernelU.Defs
public import Silmaril.Proofs.Wasm.Auto2.KernelU.Eq

@[expose] public section

/-!
# The chunk checks of the function summaries over `instK?`: results

Proofs in `Silmaril.Proofs.Wasm.Auto2.KernelU.Eq`.

* `sumCheckUK_eq : sumCheckUK = Silmaril.Wasm.Auto2.Summ.sumCheckU`;
* **`checkAmongU_eq_K`**, **`checkAmongC_eq_K`**: given `(validate? m₁).isSome` and
  `(validate? m₂).isSome`, the `equivu` and `equivc` chunk checks are `checkAmongUK` and
  `checkAmongCK` (no validation, closed-form data segments, memories compared by list
  recursion).

A certificate's `chunkU_c`/`chunkC_c` theorem rewrites with these and decides the `K` form by
`decide +kernel`, reusing the `validA`/`validB` theorems proved once.
-/
