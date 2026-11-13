module

public import Silmaril.Wasm.Execution.Core.Step

/-!
# The `br_table` dispatch prologue of a rewound function, in Core 3.0

The first-order asyncify machine (`Silmaril.Wasm.Models.FXAsyncPC`) re-enters a saved frame by
dispatching on its resume index (`disp`). In Wasm this is the prologue of an asyncified
function: nested `block`s around a `br_table` on the saved index, so that branching to label
`i` leaves the `i + 1` innermost blocks and falls through into the code from resume point `i`
on. This module states that prologue in Core 3.0 syntax:

* the body of the function is cut at its resume points into segments `seg₀, …, segₙ₋₁`;
* `nest segs inner` puts `inner` in the innermost `block`, with `seg₀` after it, the two in the
  next block, with `seg₁` after it, and so on; `segₙ₋₁` follows the outermost block;
* `prologue g segs`: the innermost block reads the resume index from global `g` and runs
  `br_table [0, …, n-1] (n-1)`;
* `resumeAt segs i`: the same function as it would be written to start at resume point `i`:
  `segᵢ` in the innermost block, then the segments after it;
* `check m save`: the call-site check of an asyncified call, on the mode register `m`;
* `wrap segs X`: the run-time form, administrative code `X` inside the labels of the blocks
  around it, each followed by its segment.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXDispatch

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- Label index `j` (modulo `2 ^ 32`). -/
def lab (j : Nat) : LabelIdx := ⟨⟨j % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩

/-- The dispatch table over `n` resume points: index `j` branches to label `j`. -/
def table (n : Nat) : Instr := .brTable ((List.range n).map lab) (lab (n - 1))

/-- Nest `inner` in one empty-typed `block` per segment, each block followed by its segment. -/
def nest : List (List Instr) → List Instr → List Instr
  | [], inner => inner
  | seg :: segs, inner => nest segs (.block .empty inner :: seg)

/-- **The dispatch prologue**: read the resume index from global `g`, then `br_table`. -/
def prologue (g : GlobalIdx) (segs : List (List Instr)) : List Instr :=
  nest segs [.globalGet g, table segs.length]

/-- The code from resume point `i` on, with the block structure of the segments after it. -/
def resumeAt (segs : List (List Instr)) (i : Nat) : List Instr :=
  nest (segs.drop (i + 1)) (segs[i]?.getD [])

/-- Administrative code `X` inside the labels of the blocks around it. -/
def wrap : List (List Instr) → List Admin → List Admin
  | [], X => X
  | seg :: segs, X => wrap segs (.label 0 [] X :: expression seg)

/-- **The call-site check on the mode register** `m`: in normal mode (`0`) do nothing; otherwise
run the code `save` (which saves the frame and returns). -/
def check (m : GlobalIdx) (save : List Instr) : List Instr := [.globalGet m, .if_ .empty save []]

end Silmaril.Wasm.Models.FXDispatch
