module

public import Silmaril.Wasm.Cfg.Block.Defs

@[expose] public section

/-!
# Basic blocks of a function body: the block tree and canonical block identities

Every sequence of a function body is segmented (`Silmaril.Wasm.Cfg.Block.Defs`). A sequence is
identified by its **sequence path** from the body: a list of steps `(segment, arm)`, where
`segment` is the position (in the parent's segmentation) of the segment whose terminator opens
the nested sequence, and `arm` is `0` for the body of `block`, `loop` and `try_table` and for
the then-arm of `if`, and `1` for the else-arm. A **block** is identified by `BlockId`: its
sequence path and its position in that sequence's segmentation. `blocks body` lists every block
of a body with its identity, sequences in pre-order and blocks in order.

This is the node set of the basic-block CFG relation (roadmap, layer 2); the edge relation over
these identities is next.
-/

namespace Silmaril.Wasm.Cfg

/-- A step into a nested sequence: the opening segment's position and the arm. -/
abbrev SeqStep := Nat × Nat

/-- A basic block's identity: its sequence path and its position in the segmentation. -/
structure BlockId where
  seq : List SeqStep
  idx : Nat
  deriving DecidableEq, Repr

mutual
/-- The blocks of a sequence at `path`, from block position `k`, with the simple instructions
`acc` (reversed) of the current block; nested sequences in pre-order. On every sequence this
computes `segment` (the canonical segmentation; to be proved with the edge relation). -/
def walk (path : List SeqStep) (k : Nat) (acc : List Instr) : List Instr → List (BlockId × Segment)
  | [] => if acc.isEmpty then [] else [(⟨path, k⟩, ⟨acc.reverse, none⟩)]
  | i :: is =>
    if isTerminator i then
      (⟨path, k⟩, ⟨acc.reverse, some i⟩) :: (nested path k i ++ walk path (k + 1) [] is)
    else walk path k (i :: acc) is
/-- The blocks of the sequences that the terminator of block `k` opens. -/
def nested (path : List SeqStep) (k : Nat) : Instr → List (BlockId × Segment)
  | .block _ b | .loop _ b | .tryTable _ _ b => walk (path ++ [(k, 0)]) 0 [] b
  | .if_ _ t e => walk (path ++ [(k, 0)]) 0 [] t ++ walk (path ++ [(k, 1)]) 0 [] e
  | _ => []
end

/-- The basic blocks of a function body. -/
def blocks (body : Expr) : List (BlockId × Segment) := walk [] 0 [] body

end Silmaril.Wasm.Cfg
