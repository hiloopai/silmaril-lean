module

public import Silmaril.Wasm.Cfg.BlockTree.Defs
import Silmaril.Proofs.Wasm.Cfg.BlockTree

@[expose] public section

/-!
# Basic blocks of a function body: theorems

The blocks `blocks` lists in the body's own sequence (path `[]`) are exactly the body's
canonical segmentation (`Silmaril.Wasm.Cfg.Block.Thms`), numbered in order; every block of a
nested sequence carries a strictly longer path that extends its parent's.
-/

namespace Silmaril.Wasm.Cfg

/-- Every block `walk` lists lies at or below its sequence path. -/
theorem walk_prefix (path : List SeqStep) (k : Nat) (acc is : List Instr) :
    ∀ x ∈ walk path k acc is, path <+: x.1.seq :=
  Proofs.BlockTree.walk_prefix path k acc is

/-- The blocks of the sequences a terminator opens lie strictly below the opening sequence. -/
theorem nested_prefix (path : List SeqStep) (k : Nat) (i : Instr) :
    ∀ x ∈ nested path k i, ∃ s, path ++ [s] <+: x.1.seq :=
  Proofs.BlockTree.nested_prefix path k i

/-- **The body's own blocks are its canonical segmentation**, numbered in order. -/
theorem blocks_top (body : Expr) :
    (blocks body).filter (fun x => x.1.seq == []) =
      (segment body).mapIdx fun j s => (⟨[], j⟩, s) := by
  simpa [blocks, segment] using Proofs.BlockTree.walk_top [] body 0 []

end Silmaril.Wasm.Cfg
