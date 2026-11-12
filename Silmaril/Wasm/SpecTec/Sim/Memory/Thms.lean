module

public import Silmaril.Wasm.SpecTec.Sim.Memory.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.TableFwd
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.MemoryFwd
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.Boundary
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.Wrap
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.Loads
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.Grow
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.TableAll
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.LoadFloat

/-!
# SpecTec ↔ Core 3.0, track memory: what is proved

Core → SpecTec, at `simEnv B`, under `TypingFacts`, `State.StateTyping` and (for the `size`
rules) `MemTyping`; each has the type of the matching case of `Forward.table` or
`Forward.memory`, plus an explicit no-wrap hypothesis `hw` where Core's bit-vector arithmetic
could wrap (gap G1):

* tables: `fwd_tableSize`, `fwd_tableFillZero`, `fwd_tableFillSucc`, `fwd_tableCopyOob`,
  `fwd_tableCopyZero`, `fwd_tableCopyLe`, `fwd_tableCopyGt`, `fwd_tableInitOob`,
  `fwd_tableInitZero`, `fwd_tableInitSucc` (`Step_read` 27, 29–37), via the value-level rule
  constructions `sread_table*`; the `otherwise` premises are discharged by opcode with the
  earlier rules of the same instruction refuted from their premises (`not_table*`).
* memories: `fwd_memorySize`, `fwd_memoryFillOob`, `fwd_memoryFillZero`, `fwd_memoryFillSucc`,
  `fwd_memoryCopyOob`, `fwd_memoryCopyZero`, `fwd_memoryCopyLe`, `fwd_memoryCopyGt`,
  `fwd_memoryInitOob`, `fwd_memoryInitZero`, `fwd_memoryInitSucc` (`Step_read` 52–62), via
  `sread_memory*`; `$memarg0` and `$Ki` are evaluated by their clauses (`memarg0Ok_simEnv`,
  `kiOk_simEnv`). `fwd_memorySize` also needs the memory to be a whole number of pages.

* integer loads and stores that trap: `fwd_loadIntOob`, `fwd_loadPackOob` (`Step_read` 38, 40),
  `fwd_storeIntOob`, `fwd_storePackOob` (`Step` 18, 20), with the access width `$size(nt) / 8`
  evaluated through ℚ (`evalExp_div8`, `evalExp_widthInt`); `fwd_loadFloatOob` (`Step_read` 38
  for floats, through `$size`'s float clauses, `sizeDefs_simEnv`).

* growth succeeding: `fwd_tableGrowSucceed` (`Step` 15), `fwd_memoryGrowSucceed` (`Step` 26), in
  any profile, under `GrowFuns` (what `B` must supply for `$growtable`/`$growmem`, gap G3) and
  `InstTyping` (grown instances are typed); `$with_tableinst`/`$with_meminst` are evaluated by
  their clauses (`withInstDefs_simEnv`).

* `fwd_table_bounded`: `Forward.table` for every `TableStep` constructor (with family M's
  `get`, `set`, `fill-oob`, `grow-fail`, `elem.drop`), from a store whose tables and element
  segments have fewer than `2 ^ 32` entries (`TablesBounded`).

Obstruction 2 (the load boundary), resolved by the corrected slice bound (upstream item U2):
`slice?_bytesL` and `setSlice_bytesL` show that slicing the encoded memory is Core's `readBytes`
and `writeBytes` at every address, boundary included, both ways; `loadBoundary` shows that at an
`i32.load` whose four bytes end at the end of memory, Core reads `r`, `load-num-oob` has no
instance at the image (`not_loadNumOob_boundary`), and `load-num-val`'s slice is the image of
`r` (`evalExp_loadNumValSlice` at the rule's bindings).

The wrap at a full-size memory (gap G1): `grow_full` (an `i32` memory of `2 ^ 32` bytes is
reachable by `memory.grow`), `fillSucc_full` (Core's `memory.fill` steps at its last byte) and
`fillSucc_full_ne` (Core's successor operand `% 0` is not SpecTec's `% 2 ^ 32`).

Coverage and gaps are tracked in `docs/projects/spectec/README.md`, track memory.
-/
