module

public import Silmaril.Wasm.JcoTool.KTee.Defs
public import Silmaril.Wasm.JcoTool.KCoreEmit.Defs

/-!
# The generated tee as a Core 3.0 module: bytes and text

`KCoreEmit.toModule` lays out the generated stream modules (imports, two pages of memory, nine
`i32` globals, `cabi_realloc`, the lift and the callback). The tee (`KTee.genT`) uses the same
layout; only its `task.return` differs: it returns **two** readable ends, so it is imported with
the type `[i32, i32] → []` (type `4` of `KCoreEmit.types`, the type of `waitable.join`).

* `toModuleT N name`: `toModule (genT N) name` with that import;
* `wasmOfT N name`: its bytes, by silmaril's verified encoder (`KTeeEmit.Thms`,
  `wasmOfT_encodes`);
* `watOfT N name`: its text, by silmaril's checked printer (`watOfT_encodes`).

`wasm-jco ktee NAME N [-o OUT.wasm]` prints `watOfT` or writes `wasmOfT`; the component's WIT is
`tee: async func(in: stream<u8>) -> tuple<stream<u8>, stream<u8>>` (as `wasm-streams-gen teewit`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KTeeEmit

open Silmaril.Wasm
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KCoreEmit

/-- The imports of the tee: `KCoreEmit.imports` with `task.return` of two `i32`s. -/
def importsT (name : String) : List Import :=
  imp "[export]$root" s!"[task-return]{name}" 4 :: (imports name).tail

/-- **The generated tee as a Core 3.0 module.** -/
def toModuleT (N : Nat) (name : String) : Module :=
  { toModule (Silmaril.Wasm.JcoTool.KTee.genT N) name with imports := importsT name }

/-- The bytes of a module, by silmaril's verified encoder. -/
def wasmOfM (m : Module) : Except String ByteArray :=
  (fun bs => ⟨bs.toArray⟩) <$> Silmaril.Wasm.Binaryen.Exe.encodeModule? m

/-- The text of a module, by silmaril's checked printer. -/
def watOfM (m : Module) : Except String String :=
  match Silmaril.Wasm.Binaryen.Toolkit.Wat.moduleSyntax? m with
  | none => .error "ktee: the module is outside the printer's fragment"
  | some x =>
    match Silmaril.Wasm.Binaryen.Toolkit.renderWatDocument? x with
    | none => .error "ktee: the module's text does not render"
    | some t => .ok t

/-- **The bytes** of the tee. -/
def wasmOfT (N : Nat) (name : String) : Except String ByteArray := wasmOfM (toModuleT N name)

/-- **The text** of the tee. -/
def watOfT (N : Nat) (name : String) : Except String String := watOfM (toModuleT N name)

/-- The WIT world of the tee component. -/
def teeWit (name : String) : String :=
  s!"package silmaril:streams;\n\nworld {name} \{\n  export {name}: async func(in: stream<u8>) -> tuple<stream<u8>, stream<u8>>;\n}\n"

end Silmaril.Wasm.JcoTool.KTeeEmit
