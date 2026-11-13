module

public import Silmaril.Project.WasmP3Rust.CommandWorld.Defs
public import Silmaril.Project.WasmP3Rust.TasksP3.Thms
public import Silmaril.Wasm.Component.BinaryP3.WorldSub.Thms

/-!
# The examples target the whole `wasi:cli/command@0.3.0`

**PROVED** (kernel evaluation of `BinaryP3.World.targets` on the ASTs of the files, read by the
chunked certificates):

* `command_resolves`: the generated world resolves to a closed component type;
* `<n>_hasWorldFull : HasWorld3 <N>.File.bytes command` for `hello`, `echo`, `cat`, `cat-debug`:
  the component targets the whole world (with `wasi:clocks`, `wasi:filesystem`,
  `wasi:sockets`, `wasi:random`), not only its `wasi:cli` part (`Cli.command`);
* `<n>_csub`: by `targets_sound`, the component's closed type is a Component Model subtype
  (`CSub`) of the world's;
* `cli_csub`: the `wasi:cli` part `Cli.command` is a subtype of the whole world
  (it imports less and exports the same), so every component of `Cli.command` is one of
  `command` (`CSub.trans`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmP3Rust.CommandWorld

open Silmaril.Wasm.Component.BinaryP3.World

/-- The whole world resolves. -/
theorem command_resolves : (resolveWorld command).isSome = true := by decide +kernel

/-- **`hello` targets the whole `wasi:cli/command@0.3.0`.** -/
theorem hello_hasWorldFull : HasWorld3 Hello.File.bytes command :=
  ⟨_, Hello.P3.parse_eq, by decide +kernel⟩

/-- **`echo` targets the whole `wasi:cli/command@0.3.0`.** -/
theorem echo_hasWorldFull : HasWorld3 Echo.File.bytes command :=
  ⟨_, Echo.P3.parse_eq, by decide +kernel⟩

/-- **`cat` targets the whole `wasi:cli/command@0.3.0`.** -/
theorem cat_hasWorldFull : HasWorld3 Cat.File.bytes command :=
  ⟨_, Cat.P3.parse_eq, by decide +kernel⟩

/-- **`cat-debug` targets the whole `wasi:cli/command@0.3.0`.** -/
theorem catDebug_hasWorldFull : HasWorld3 CatDebug.File.bytes command :=
  ⟨_, CatDebug.P3.parse_eq, by decide +kernel⟩

/-- `HasWorld3` gives a Component Model subtype. -/
theorem csub_of_hasWorld {b : List UInt8} {W : Silmaril.Wasm.Wit.Project.WorldType}
    (h : HasWorld3 b W) : ∃ c tc tw, Silmaril.Wasm.Component.BinaryP3.parse (arrOf b) = .ok c ∧
      resolveAst c = some tc ∧ resolveWorld W = some tw ∧ CSub tc tw := by
  obtain ⟨c, hp, ht⟩ := h
  obtain ⟨tc, tw, h1, h2, h3⟩ := targets_sound ht
  exact ⟨c, tc, tw, hp, h1, h2, h3⟩

/-- The `wasi:cli` part of the world provides what the whole world needs of it. -/
theorem cli_targets_imports :
    ∃ ci ce wi we, resolveWorld Cli.command = some (.comp ci ce) ∧
      resolveWorld command = some (.comp wi we) ∧
      provides wi.toList ci.toList = true ∧ provides ce.toList we.toList = true := by
  refine ⟨_, _, _, _, rfl, rfl, ?_, ?_⟩ <;> decide +kernel

/-- **`Cli.command` is a subtype of the whole world.** -/
theorem cli_csub : ∃ a b, resolveWorld Cli.command = some a ∧ resolveWorld command = some b ∧
    CSub a b := by
  obtain ⟨ci, ce, wi, we, h1, h2, h3, h4⟩ := cli_targets_imports
  exact ⟨_, _, h1, h2, csub_comp_of (provides_sound h3) (provides_sound h4)⟩

end Silmaril.Project.WasmP3Rust.CommandWorld

end
