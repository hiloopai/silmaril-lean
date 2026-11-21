module

public import Silmaril.Parse.DecodeGraph.Defs

/-! # Block boundaries and observable rebasing -/

@[expose] public section

namespace Silmaril.Machine.DecodeGraph

open scoped SetRel
open Silmaril.Parse.DecodeGraph

variable {Context Buffer Source Block : Type*}

/-- A block construction/checking relation, separate from decoding and boundary
selection. A relation can check contextual typing and need not return a list. -/
abbrev IsBasicBlock (Context Source Block : Type*) := Context → List Source → Block → Prop

def IsBasicBlock.contextFree (rel : List Source → Block → Prop) : IsBasicBlock Context Source Block :=
  fun _ => rel

section Blocks

variable (decoder : Graph Context Buffer Source) (ends : Context → Nat → Source → Prop)

/-- Decode until the first terminator (inclusive), keeping the original buffer
and upper bound. Each step strictly advances inside the window. Fuel counts
instructions; undecodable bytes, EOF or exhausted fuel before a terminator give
no path. Neither the cursors nor `ends` compute an architectural successor PC. -/
inductive Path : Nat → Input Context Buffer → List Source → Nat → Prop
  | last {fuel input instr endPos}
      (decoded : (input, (instr, endPos)) ∈ decoder)
      (advance : input.pos < endPos) (inside : endPos ≤ input.stop)
      (endsHere : ends input.context input.pos instr) :
      Path (fuel + 1) input [instr] endPos
  | next {fuel input instr nextPos rest endPos}
      (decoded : (input, (instr, nextPos)) ∈ decoder)
      (advance : input.pos < nextPos) (inside : nextPos ≤ input.stop)
      (continues : ¬ ends input.context input.pos instr)
      (tail : Path fuel (input.atPos nextPos) rest endPos) :
      Path (fuel + 1) input (instr :: rest) endPos

def blocks (fuel : Nat) : Graph Context Buffer (List Source) :=
  {(input, result) | Path decoder ends fuel input result.1 result.2}

end Blocks

/-- Check or assemble a decoded listing without changing its end cursor. -/
def assembleBlocks (listings : Graph Context Buffer (List Source)) (assemble : IsBasicBlock Context Source Block) :
    Graph Context Buffer Block :=
  {(input, result) | ∃ listing, (input, (listing, result.2)) ∈ listings ∧ assemble input.context listing result.1}

/-- A typed variant with a distinguished final token, rather than a predicate
classifying a homogeneous instruction type. -/
structure TerminatedBlock (Source Terminator : Type*) where
  body : List Source
  exit : Terminator

def TerminatedBlock.tokens {Terminator : Type*} (block : TerminatedBlock Source Terminator) :
    List (Source ⊕ Terminator) := block.body.map Sum.inl ++ [.inr block.exit]

def TerminatedBlock.Assembles {Terminator : Type*} :
    IsBasicBlock Context (Source ⊕ Terminator) (TerminatedBlock Source Terminator) :=
  IsBasicBlock.contextFree fun tokens block => tokens = block.tokens

/-- A machine described by its observable executions at each input. Input may
include an initial state; an observation is opaque to rebasing. -/
abbrev Observed (Input Observation : Type*) := SetRel Input Observation

/-- An observation is admitted if some related base input admits it. No input
witness gives no observation; different witnesses contribute their union. -/
abbrev rebase {Input Base Observation : Type*} (adapter : SetRel Input Base)
    (machine : Observed Base Observation) : Observed Input Observation := adapter ○ machine

end Silmaril.Machine.DecodeGraph
