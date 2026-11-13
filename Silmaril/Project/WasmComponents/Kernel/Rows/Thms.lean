module

public import Silmaril.Project.WasmComponents.Kernel.Io0212.Thms
public import Silmaril.Project.WasmComponents.Kernel.Io0212.Package.Thms
public import Silmaril.Project.WasmComponents.Kernel.Io0212.FixturePackage.Thms
public import Silmaril.Project.WasmComponents.Kernel.Io026.Thms
public import Silmaril.Project.WasmComponents.Kernel.Reactor.Thms
public import Silmaril.Project.WasmComponents.Kernel.Command.Thms
public import Silmaril.Project.WasmComponents.Kernel.CodeSections.Thms

/-!
# Kernel decoders: the rows they settle

Every module of `Silmaril.Project.WasmComponents.Kernel`, and the answers that need several of them.

**PROVED** (from the kernel decodings, no `Task` left):

* `io_upgrade`: `wasi:io@0.2.12` is a `wit_upgrade` of `wasi:io@0.2.6`
  (`silmaril.wasm_components.wasi.io.upgrade_0_2_6_to_0_2_12`, THM);
* `io_not_downgrade`: and not conversely (`…upgrade_0_2_12_to_0_2_6`, UNS).

Solved in the imported modules: the `parses` of `wasi.io.v0_2_12.{oci,fixture}` and their
`….package`, of `wasi.io.v0_2_6.oci` and of `adapter.{reactor,command}.world`; the rows
`wasi.io.v0_2_12.{same_world,behaviour_eq}`; and four of the six frozen `Task`s 
(`silmaril.wasm_components.versions.{io_0_2_6_summary, io_0_2_12_summary, reactor_world,
command_world}`).

**OPEN**: the `Task`s `silmaril.wasm_components.versions.{reactor,command}_imports` and the
adapters' `parses` under `wasm.module.core3`. They need silmaril's Core 3.0 decoder
(`Binary.Core.decode?`) in the kernel on the 51 KB modules, mostly a 24 KB code section, and
that decoder reads the input by position (see `docs/projects/wasm-wasi.md`). So the rows
`adapter.{reactor,command}.{imports_via,implements_via}` stay conditional on those two `Task`s
(their world halves are now proved).

A Silmaril addition.
-/

open Silmaril.Project (Value)

@[expose] public section

namespace Silmaril.Project.WasmComponents.Kernel

open Silmaril.Project.WasmComponents.Versions

/-- **`wasi:io@0.2.12` upgrades `wasi:io@0.2.6`** (unconditional). -/
@[answers "silmaril.wasm_components.wasi.io.upgrade_0_2_6_to_0_2_12" thm]
theorem io_upgrade : silmaril.wasm_components.wasi.io.upgrade_0_2_6_to_0_2_12 :=
  io_upgrade_of io026_summary io0212_summary

/-- **And `wasi:io@0.2.6` does not upgrade `wasi:io@0.2.12`** (unconditional). -/
@[answers "silmaril.wasm_components.wasi.io.upgrade_0_2_12_to_0_2_6" uns]
theorem io_not_downgrade : ¬ silmaril.wasm_components.wasi.io.upgrade_0_2_12_to_0_2_6 :=
  io_not_downgrade_of io026_summary io0212_summary

/-- The reactor's imports are on the `0.2` track, given only the open decoding of its core
imports (its world is now proved). -/
theorem reactor_importsVia_of_imports
    (hm : Task.silmaril.wasm_components.versions.reactor_imports) :
    silmaril.wasm_components.adapter.reactor.imports_via :=
  reactor_importsVia_of reactor_world hm

theorem command_importsVia_of_imports
    (hm : Task.silmaril.wasm_components.versions.command_imports) :
    silmaril.wasm_components.adapter.command.imports_via :=
  command_importsVia_of command_world hm

theorem reactor_implementsVia_of_imports
    (hm : Task.silmaril.wasm_components.versions.reactor_imports) :
    silmaril.wasm_components.adapter.reactor.implements_via :=
  reactor_implementsVia_of reactor_world hm

theorem command_implementsVia_of_imports
    (hm : Task.silmaril.wasm_components.versions.command_imports) :
    silmaril.wasm_components.adapter.command.implements_via :=
  command_implementsVia_of command_world hm

end Silmaril.Project.WasmComponents.Kernel

end

namespace Silmaril.Project.WasmComponents.Kernel

silmaril decomposition := Silmaril.Project.WasmComponents.Kernel.reactor_importsVia_of_imports
silmaril decomposition := Silmaril.Project.WasmComponents.Kernel.command_importsVia_of_imports
silmaril decomposition := Silmaril.Project.WasmComponents.Kernel.reactor_implementsVia_of_imports
silmaril decomposition := Silmaril.Project.WasmComponents.Kernel.command_implementsVia_of_imports

end Silmaril.Project.WasmComponents.Kernel
