import Silmaril.Wasm.Wit.Text.Parse.Defs
import Silmaril.Wasm.Wit.Elab.Defs
import Silmaril.Wasm.Wit.Binary.Custom.Defs
import Silmaril.Wasm.Wit.Binary.Embed.Defs
import Silmaril.Wasm.Component.Binary.Example.Defs
import Silmaril.Project.Formats.Wit.Defs

/-!
Writes the component fixtures of `examples/project-formats/` with Silmaril's own encoders
(run from the repository root: `lake env lean --run examples/project-formats/gen-components.lean`):

* `hello-wit.wasm`: `hello.wit` parsed (`Wit.Text.parse`), elaborated (`Wit.Elab.elaborate`)
  and encoded (`Wit.Binary.encodePackage`), the type-only component wit-component writes;
* `component-run.wasm`: `Component.Binary.Example.compB` (import `get`, lower it into a core
  module, lift and export `run`) with the export ascribed its type `(func (type 0))`, as
  wit-component writes exports, encoded by `Component.Binary.encode`;
* `module-getter.wasm`: the core module `Component.Binary.Example.producer` with the world
  `getter` of `hello.wit` embedded as a `component-type` custom section
  (`Wit.Binary.encodeWorldType`, `Wit.Binary.embedPayload`).
-/

open Silmaril.Wasm

def orFail {α ε} [ToString ε] (what : String) : Except ε α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{what}: {e}")

/-- `compB` with its export ascribed the function type 0. -/
def runAst : Component.Binary.Ast :=
  match Component.Binary.Example.compB with
  | .mk ss => .mk (ss.dropLast ++ [.exports [⟨↑"run", ⟨.func, 1⟩, some (.func 0)⟩]])

def main : IO Unit := do
  let dir : System.FilePath := "examples/project-formats"
  let text ← IO.FS.readFile (dir / "hello.wit")
  let some d := Wit.Text.parse text | throw (IO.userError "hello.wit does not parse")
  let (P, env) ← orFail "elaborate" (Wit.Elab.elaborate d.packages d.main.name [])
  let pkg ← orFail "encodePackage" (Wit.Binary.encodePackage env P)
  IO.FS.writeBinFile (dir / "hello-wit.wasm") pkg
  let some comp := Component.Binary.encode runAst
    | throw (IO.userError "compB does not encode")
  IO.FS.writeBinFile (dir / "component-run.wasm") comp
  let some w := P.worlds.lookup "getter" | throw (IO.userError "no world getter")
  let payload ← orFail "encodeWorldType" (Wit.Binary.encodeWorldType env P.name "getter" w .utf8)
  let m ← orFail "embedPayload" (Wit.Binary.embedPayload Component.Binary.Example.producer payload)
  IO.FS.writeBinFile (dir / "module-getter.wasm") m
  -- compiled checks of the formats on the files (not kernel facts)
  let check (what : String) (ok : Bool) : IO Unit :=
    unless ok do throw (IO.userError s!"check failed: {what}")
  let f (bs : ByteArray) : Silmaril.Formats.Bytes := ⟨bs⟩
  check "component-run.wasm: wasm.component.ir" (Silmaril.Project.Formats.wasmComponentIR.parse (f comp)).isSome
  check "component-run.wasm: wasm.component.world" (Silmaril.Project.Formats.wasmComponentWorld.parse (f comp)).isSome
  check "hello-wit.wasm: wit.binary" (Silmaril.Project.Formats.witBinary.parse (f pkg) == some P.canon)
  check "module-getter.wasm: wasm.module.world" (Silmaril.Project.Formats.wasmModuleWorld.parse (f m)).isSome
  check "hello.wit: wit.package" (Silmaril.Project.Formats.witPackage.parse (f text.toUTF8)).isSome
  IO.println s!"hello-wit.wasm {pkg.size} B, component-run.wasm {comp.size} B, module-getter.wasm {m.size} B"
