module

public import Silmaril.Wasm.Auto2.Link.Defs
public import Silmaril.Proofs.Wasm.Auto2.Link.Trans

@[expose] public section

/-!
# Composing module equivalences: results

Proofs in `Silmaril.Proofs.Wasm.Auto2.Link.Trans`.

* `modEquiv_trans`: `Rel.eq` equivalences compose when the middle module accepts the outer ones'
  arguments (`InvokeImp`); `modEquiv_symm`;
* `invokeOk_transfer`, **`invokeImp_of_sigOkK`**: the same defined type at export `j` with number
  or vector parameters (`sigOkK`, kernel-decided over `instK?`) gives `InvokeImp` both ways;
* **`modEquiv_link`**: a link `m₁ ≈ m₂` and a certificate `m₂ ≈ m₃` give `m₁ ≈ m₃` under
  `sigOkK` (used by `wasm-check pass --link-equiv`).
-/
