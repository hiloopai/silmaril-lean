module

public import Silmaril.X86.Decompile.Cfg

/-!
# Proposing a control-flow graph

**Nothing in this file is trusted.** `ofFunction` is the textbook leader
algorithm, and `Decompile.checkCfg` is the judge; the soundness theorems depend
on the checker alone. Nothing is proved about the proposal beyond the fact that
it is a total function.

The leaders of a function are its entry, every jump and branch target, and
every instruction immediately after a control transfer. A block runs from a
leader to the instruction before the next leader, and its edges are the
intraprocedural successors of its terminator.

An instruction after a *call* is a leader too: `retiring` is false for `call`,
so the checker requires a call to be the terminator of its block. This is the
one place where the usual textbook freedom — treating a call as an ordinary
instruction inside a block — is not available, and it is the right choice
anyway, since the call is where the function's reasoning hands off to another.

Leaders are read off the function's own listing rather than sorted into place:
`List.mergeSort` is defined by well-founded recursion and does not reduce in
the kernel, so filtering the body's addresses by membership in the seed set
produces the leaders already in increasing order and already free of
duplicates. That is what lets `recover_cfg` close a goal about this proposer by
kernel reduction rather than by compiled evaluation.
-/

@[expose] public section

namespace Silmaril.X86.Decompile.CfgPropose

open Silmaril.X86.Decompile

/-- The addresses that seed a block: the function's entry, every jump or branch
target, and the fall-through address of every instruction that does not retire.
The list is unsorted and may contain addresses that are not instructions of the
function; `leaders` filters it. -/
def leaderSeeds (body : List Decoded) (f : FunctionSpec) : List Nat :=
  f.entry :: body.flatMap fun d =>
    (d.edges.filterMap fun e =>
      match e with
      | .jump t => some t
      | .branch t => some t
      | _ => none) ++ (if retiring d.instr then [] else [d.next])

/-- The leaders of a function: the seed addresses that are addresses of its own
instructions, in increasing address order. -/
def leaders (body : List Decoded) (f : FunctionSpec) : List Nat :=
  let seeds := leaderSeeds body f
  (body.map Decoded.addr).filter fun a => decide (a ∈ seeds)

/-- The blocks of a run of leaders: each one runs from its leader to the last
instruction before the next leader, or to the last instruction of the function
for the final leader. A leader with no instruction of its own contributes no
block, which cannot happen for a leader produced by `leaders`. -/
def blocksOf (body : List Decoded) : List Nat → List BlockSpec
  | [] => []
  | [a] =>
    match (body.filter fun d => decide (a ≤ d.addr)).getLast? with
    | some d => [{ start := a, terminator := d.addr }]
    | none => []
  | a :: b :: rest =>
    (match (body.filter fun d => decide (a ≤ d.addr ∧ d.addr < b)).getLast? with
      | some d => [{ start := a, terminator := d.addr }]
      | none => []) ++ blocksOf body (b :: rest)

/-- The edges of a proposed set of blocks: the intraprocedural successors of
each block's terminator, paired with the block's start. -/
def edgesOf (body : List Decoded) (blocks : List BlockSpec) : List (Nat × Nat) :=
  blocks.flatMap fun b => (cfgTargetsAt body b.terminator).map fun t => (b.start, t)

/-- Propose a control-flow graph for one function of an accepted partition. -/
def ofFunction (acc : Accepted) (f : FunctionSpec) : CfgSpec :=
  let body := acc.body f
  let blocks := blocksOf body (leaders body f)
  { func := f, blocks := blocks, edges := edgesOf body blocks }

end Silmaril.X86.Decompile.CfgPropose
