module

public import Silmaril.Machine.CBackend.Lift.Abstraction.Defs
public import Silmaril.Machine.CBackend.Lift.Loops.Defs
/-!
# Untrusted proposers

**Nothing in this file is trusted, and nothing in it is proved.** These are
heuristics that guess a proposal; the checkers of `Lift/Abstraction.lean`,
`Lift/Ssa.lean` and `Lift/Loops.lean` decide whether the guess is right. A bug
here produces a rejected proposal, never an unsound theorem. That is the whole
point of the arrangement: the search is allowed to be a heuristic because the
result is checked.

## What is here, and what is not

* `proposeLoops` is a complete loop-nest proposer: it enumerates the back edges,
  groups them by header, and computes each header's loop as the union of the
  natural loops of its back edges. It proposes exactly what `checkLoops`
  computes, so `checkLoops g (proposeLoops g)` fails only when the graph is not
  pruned or not reducible — which is information about the graph, not about the
  proposer.
* `proposeAlloc` is a register allocator of the crudest possible kind: it homes
  the pseudo-registers in the physical registers it is given, in order, and
  spills the rest to consecutive slots. It makes no attempt at liveness,
  colouring or coalescing.
* `proposeFrame` reads a frame proposal off an allocation: a frame large enough
  for the slots the allocation uses, at the backend's slot size, and the
  callee-saved registers it writes.

**There is no SSA-construction proposer.** Placing block arguments correctly is
dominance-frontier computation and a renaming pass — a real compiler pass, not a
heuristic — and this PR does not contain one. The SSA proposal comes from the
agent, and `checkSsa` is what makes that safe. Writing a proposer is a separate
piece of work whose only consequence for soundness is how often the checker
accepts.
-/

@[expose] public section

namespace Silmaril.Machine.Lift

open Silmaril.Machine.Graph (Digraph)
open Silmaril.Machine (CallingConvention)

/-! ## Loop nests -/

/-- The headers of the graph's back edges, without repetition, in increasing
order of their first appearance. -/
def proposedHeaders (g : Digraph) : List Nat := ((allBackEdges g).map Prod.snd).dedup

/-- **Propose the loop nest of a graph**: one entry per back-edge target, with
all the tails that reach it and the union of their natural loops. Untrusted;
`checkLoops` decides. -/
def proposeLoops (g : Digraph) : LoopSpec where
  loops := (proposedHeaders g).map fun h =>
    { header := h, tails := g.backEdgeTails h, body := canonicalBody g h (g.backEdgeTails h) }

/-! ## Allocations -/

/-- **Propose an allocation**: home the pseudo-registers `0 … regs.length - 1`
in the given physical registers, in order, and spill the pseudo-registers
`regs.length … count - 1` to consecutive slots. Untrusted; `checkAlloc` decides,
and `checkAbstraction` decides whether the whole proposal recompiles. -/
def proposeAlloc {P : Type} (regs : List P) (count : Nat) (scratch₀ scratch₁ : P) :
    TableAlloc P where
  table := regs.map Lir.Alloc.Home.reg ++
    (List.range (count - regs.length)).map Lir.Alloc.Home.spill
  scratch₀ := scratch₀
  scratch₁ := scratch₁

/-- **Propose a frame**: large enough for every slot the allocation uses, and
declaring saved every callee-saved register it writes. Untrusted; `checkFrame`
decides. -/
def proposeFrame {P : Type} [DecidableEq P] (cc : CallingConvention P) (slotSize : SlotSize)
    (a : TableAlloc P) : FrameSpec P where
  cc := cc
  frame := (2 * a.slotCeiling) * slotSize - cc.redZone
  saved := (a.regs ++ [a.scratch₀, a.scratch₁]).filter fun p => decide (p ∈ cc.calleeSaved)

end Silmaril.Machine.Lift
