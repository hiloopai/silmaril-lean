module

public import Silmaril.Raw.Project.WasmComponents.Kernel.CodeSections
public import Silmaril.Project.WasmComponents.Thms

/-!
# The framing determines the code: `Task.parse_codeSections`

**PROVED** (proofs in `Silmaril.Raw.Project.WasmComponents.Kernel.CodeSections`):

* `parse_codeSections : Task.parse_codeSections`. Two component binaries that parse and have
  the same framed non-custom sections (`codeSections`: ids and raw bodies, in order) have the
  same code (`CodeEq`). The proof does not evaluate anything:
  * a parse is a grammar derivation at depth `size + 1` (`Binary.parse_sound`);
  * the derivation's sections are exactly `codeSections`' frames (`sections_of_seq`, through
    `leb_of_U32`: the grammar's `u32` read back by the pilot's `leb 4`);
  * a section's value depends on its id and body only (`section_shape`), and it is a custom
    section exactly when its id is `0`;
  * the grammar at depth `k` is contained in the grammar at every `k' ≥ k`
    (`defTypeG_mono`, `componentG_mono`, `sectionG_le`), so two files of different sizes can be
    compared at one depth, where the grammar is unambiguous (`Grammar.functional`).

With it, the pass-1 theorems `io_same_world_of` and `io_behaviourEq_of` hold from the two
`wasi:io@0.2.12` parses alone (`io_same_world_of_parses`); `Kernel.Io0212.Thms` proves the same
rows without it, from the two ASTs.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmComponents.Kernel

open Silmaril.Wasm.Component.Binary (Ast)

/-- **One world** for the two `wasi:io@0.2.12` files from their parses and the projection
(an earlier `io_same_world_of`, its `Task` discharged). -/
theorem io_same_world_of_parses {a b : Ast}
    (ha : silmaril.wasm_components.wasi.io.v0_2_12.oci.Is a)
    (hb : silmaril.wasm_components.wasi.io.v0_2_12.fixture.Is b)
    (hw : (Silmaril.Wasm.Wit.Project.projectX a).isSome) :
    silmaril.wasm_components.wasi.io.v0_2_12.same_world :=
  io_same_world_of parse_codeSections ha hb hw

end Silmaril.Project.WasmComponents.Kernel

end
