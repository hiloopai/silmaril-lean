module

public import Silmaril.Project.WasmComponents.Kernel.Io0212.Oci.Thms
public import Silmaril.Project.WasmComponents.Kernel.Io0212.Fixture.Thms

/-!
# `wasi:io@0.2.12`: the two files parse, with one world and one behaviour

**PROVED** (kernel; `Kernel.is_of_ast`: Silmaril's list encoder writes the registered bytes from
the AST, so the verified parser reads them back):

* `oci_is`, `fixture_is` (`….Io0212.{Oci,Fixture}.Thms`, about 13 s each): the published
  file and the `tests/wat` fixture parse to `io0212OciAst` and `io0212FixtureAst`;
* `codeEq`: the two ASTs have the same code (`CodeEq`, they differ only in trailing custom
  sections), by evaluation;
* `oci_projects`: the WIT projection of the published file is defined;
* hence **`same_world`** and **`behaviour_eq`** (under every core semantics and names) of the two
  files, without `Task.parse_codeSections`.

A Silmaril addition.
-/

open Silmaril.Project (Value)

@[expose] public section

namespace Silmaril.Project.WasmComponents.Kernel

open Silmaril.Wasm.Component.Binary (Ast)
open Silmaril.Project.Shapes.Component

/-- The two ASTs have the same code: they differ only in their trailing custom sections. -/
theorem codeEq : CodeEq io0212OciAst io0212FixtureAst := rfl

/-- The WIT projection of the published file is defined. -/
theorem oci_projects : (Silmaril.Wasm.Wit.Project.projectX io0212OciAst).isSome = true := by
  decide +kernel

/-- **One world** for the two `wasi:io@0.2.12` files (unconditional). -/
@[answers "silmaril.wasm_components.wasi.io.v0_2_12.same_world" thm]
theorem io_same_world : silmaril.wasm_components.wasi.io.v0_2_12.same_world :=
  ⟨_, oci_is, _, fixture_is, oci_projects, projectX_eq_of_codeEq codeEq⟩

/-- **One behaviour** for the two files under every core semantics and names (unconditional). -/
theorem io_behaviourEq (C : Silmaril.Wasm.Component.CoreSem Silmaril.Wasm.Component.Binary.CoreMod)
    (L : Silmaril.Wasi.Layout) :
    DigestBehaviourEq (irDen C L) silmaril.wasm_components.wasi.io.v0_2_12.oci
      silmaril.wasm_components.wasi.io.v0_2_12.fixture :=
  digestBehaviourEq_of_codeEq (irDen_stripCustom C L) oci_is fixture_is codeEq

@[answers "silmaril.wasm_components.wasi.io.v0_2_12.behaviour_eq" thm]
theorem io_behaviourEq_row : silmaril.wasm_components.wasi.io.v0_2_12.behaviour_eq :=
  io_behaviourEq topSem typesLayout

end Silmaril.Project.WasmComponents.Kernel

end
