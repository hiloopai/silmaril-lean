module

public import Silmaril.Wasm.Models.Features.Defs

/-!
# Feature sets of the determinism subsets

The syntactic subsets of `Silmaril.Wasm.Det` placed in the feature lattice (`Thms`: their flat
instructions are runtime instructions of these sets, `Rt.instrB`):

* `noMemS` (`Det.NoMem`): control, integers (with sign extension), direct, indirect and tail
  calls, tables, globals, reference types, typed function references, mutable GC, exceptions
  and the table bulk operations; no memory, no floats, no SIMD;
* `statelessS` (`Det.Stateless`): control, integers, direct calls and globals;
* `growTrapS` (`Det.GrowTrap`): control, integers, direct calls, globals, `throw_ref`, and
  integer memory (with bulk operations and several memories).

None of these subsets is exactly a feature set: `Det.NoMem` drops `table.grow`, `Det.GrowTrap`
requires a guard after every `memory.grow`, and `Det.Stateless` restricts which globals are
read and written. The placement is the inclusion "subset ⊆ feature set".

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models

open FeatureSet

/-- The feature set of the memory-free, float-free subset `Det.NoMem`. -/
def noMemS : FeatureSet :=
  ofList [.control, .intNum, .signExt, .directCall, .callIndirect, .table, .globals, .mutGlobal,
    .refTypes, .typedFuncRef, .gcImm, .gcMut, .exn, .tailCall, .bulkMemory, .multiValue]

/-- The feature set of the stateless subset `Det.Stateless`. -/
def statelessS : FeatureSet :=
  ofList [.control, .intNum, .signExt, .directCall, .globals, .mutGlobal]

/-- The feature set of the grow-trap subset `Det.GrowTrap`. -/
def growTrapS : FeatureSet :=
  ofList [.control, .intNum, .signExt, .directCall, .globals, .mutGlobal, .exn, .memory,
    .multiMemory, .bulkMemory, .bulkMemoryOpt]

end Silmaril.Wasm.Models
