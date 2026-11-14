module

public import Silmaril.Wasm.Cfg.Defs

@[expose] public section

/-!
# Basic blocks of Wasm instruction sequences: the canonical segmentation

The first layer of the basic-block CFG relation (see `docs/projects/wasm-cfg.md`, "Roadmap").

**Convention.** An instruction is a *terminator* when it can transfer control elsewhere than the
next instruction of its sequence or opens nested sequences: the structured instructions
(`block`, `loop`, `if`, `try_table`), the branches (`br`, `br_if`, `br_table`, `br_on_*`),
`return` and the tail calls, `unreachable`, `throw` and `throw_ref`. Every other instruction is
*simple* (calls are simple: control returns to the next instruction, or the callee traps or
throws, which the CFG marks separately).

A **segment** (basic block) of a sequence is a run of simple instructions followed by at most one
terminator. A **segmentation** of a sequence `is` is a list of nonempty segments whose
instructions concatenate to `is`, in which only the last segment may lack a terminator.

**Existence and uniqueness** (`Thms`): every sequence has exactly one segmentation, and
`segment` computes it (`segment_isSegmentation`, `isSegmentation_unique`). So the partition of a
sequence into basic blocks is a *function* of the sequence, determined by the relation
`IsSegmentation` rather than by the executable `segment`: a block's identity is its sequence and
its position in the segmentation.

Segments of nested sequences, the edges between segments, and the byte encodings of blocks and
functions are the next layers (roadmap).
-/

namespace Silmaril.Wasm.Cfg

/-- Terminators: instructions that may not continue to the next instruction of their sequence,
or that open nested sequences. -/
def isTerminator : Instr → Bool
  | .block .. | .loop .. | .if_ .. | .tryTable .. => true
  | .br _ | .brIf _ | .brTable .. | .brOnNull _ | .brOnNonNull _ | .brOnCast .. | .brOnCastFail .. => true
  | .return_ | .returnCall _ | .returnCallRef _ | .returnCallIndirect .. => true
  | .unreachable | .throw _ | .throwRef => true
  | _ => false

/-- A basic block of a sequence: simple instructions, then at most one terminator. -/
structure Segment where
  body : List Instr
  term : Option Instr
  deriving Repr

/-- The instructions of a segment, in order. -/
def Segment.instrs (s : Segment) : List Instr := s.body ++ s.term.toList

/-- A segment is well formed: its body is simple and its terminator a terminator. -/
def Segment.WellFormed (s : Segment) : Prop :=
  (∀ i ∈ s.body, isTerminator i = false) ∧ ∀ t ∈ s.term, isTerminator t = true

/-- **The canonical segmentation of a sequence**: nonempty well-formed segments covering the
sequence in order, every one but the last ending with a terminator. -/
def IsSegmentation (is : List Instr) (segs : List Segment) : Prop :=
  segs.flatMap Segment.instrs = is ∧ (∀ s ∈ segs, s.WellFormed) ∧
    (∀ s ∈ segs.dropLast, s.term.isSome) ∧ ∀ s ∈ segs, s.instrs ≠ []

/-- The executable segmentation: accumulate simple instructions until a terminator. -/
def segmentAux : List Instr → List Instr → List Segment
  | acc, [] => if acc.isEmpty then [] else [⟨acc.reverse, none⟩]
  | acc, i :: is =>
    if isTerminator i then ⟨acc.reverse, some i⟩ :: segmentAux [] is
    else segmentAux (i :: acc) is

/-- The segmentation of a sequence. -/
def segment (is : List Instr) : List Segment := segmentAux [] is

end Silmaril.Wasm.Cfg
