module

@[expose] public section

/-! The shared policy names, without importing semantic proofs into native tools. -/

namespace Silmaril.Wasm.Optimization

inductive Mode where
  | equivalence
  | refinement
  | trapInsertion
  deriving DecidableEq, Repr

end Silmaril.Wasm.Optimization
