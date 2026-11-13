module

public import Silmaril.Project.CompilesTo.Defs
public import Silmaril.Compiler.CompilesTo.Sim.Thms
public import Silmaril.Proofs.Project.CompilesTo.Compose
public import Silmaril.Proofs.Project.CompilesTo.Epilogue
public import Silmaril.Proofs.Project.CompilesTo.O0Machine
public import Silmaril.Proofs.Project.CompilesTo.O0Core
public import Silmaril.Proofs.Project.CompilesTo.O0Segments
public import Silmaril.Proofs.Project.CompilesTo.O0Entry
public import Silmaril.Proofs.Project.CompilesTo.Params
public import Silmaril.Proofs.Project.CompilesTo.Inhabit
public import Silmaril.Proofs.Project.CompilesTo.O2Run

/-!
# "This C compiles to this x86 code", segment by segment: theorems

This header re-exports the topic's proof modules, as the ported Cerberus topics do; the
theorems a row uses are listed here, each with the module that proves it.

* `FnData.whole_of_segments`: every segment simulated ⇒ the whole run simulated (`Compose`,
  from `Silmaril.Compiler.CompilesTo.Corr.whole_of_segments`).
* `FnData.segment_ret`: the return-label segment of every gcc `-O0` leaf (`pop %rbp; ret`) is
  simulated, given decidable facts about the `FnData` (`Epilogue`).
* The machine side of gcc `-O0` bodies, one instruction at a time (`step_store32`,
  `step_load32`, `step_add32`, `step_cmp32_mem`, `step_jcc8`, `step_jmp8`, `Frame0.store`,
  `FnData.notCut`: `O0Machine`), and the Core side of their statements from the verified Core
  library (`create_extends`, `init_next`, `ret_jumps`: `O0Core`).
* Generic `-O0` segment theorems, every hypothesis a decidable fact about the `FnData`:
  `FnData.segment_entry` (prologue, argument spills, the block's `int` locals: `O0Entry`),
  `FnData.segment_init_add` (`int x = y + z;`), `FnData.segment_if_gt` (`if (y > z) A else B`)
  and `FnData.segment_return` (`return v;` to the return label, with `retRun_load` /
  `retRun_load_jmp`) (`O0Segments`); `segment_none` past the last point.
* Function granularity (`-O2`, one point): `FnData.segment_call` (the segment from the call to
  the return), `FnData.core_straight` (the Core run of a straight-line body
  `int x = y + z; …; return v;`, every hypothesis decidable: `straightIs`, `definedAlong`; the
  value `valsAfter`) and the machine step `step_lea32` (`O2Run`).
* Core entries: `Params.ArgsMem` and `Params.inv_params` (the parameters' objects under the
  verified library's invariant, `Params`); `argAlloc`, `argsMem_alloc` (allocating them);
  `forcedRun`, `forcedRun_sound` and `safe_of_forced` (a forced Core run to a normal end makes
  its entry safe, checked by evaluation) (`Inhabit`).
-/
