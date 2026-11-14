import Silmaril.Wasm.Verify.Check.Defs
import Silmaril.Wasm.Verify.From.Defs
import Silmaril.Wasm.Binaryen.Exe.CompactInput

/-! `wasm-verify`: decode a Core 3.0 binary module with silmaril-lean's decoder and run the
verified checker `Silmaril.Wasm.Verify.check` (or, per export, `Silmaril.Wasm.Verify.checkFrom`) on a
property given on the command line, printing the JSON report (`Report.toJson`). The soundness
theorems of the verdicts are in `Silmaril.Wasm.Verify.Check.Thms` (`check_sound`,
`check_assert_sound`, `check_refuted_sound`, `check_assert_refuted_sound`, `check_start_sound`)
and `Silmaril.Wasm.Verify.From.Thms` (`checkFrom_sound`, `checkFrom_refuted_sound`); see
`docs/projects/wasm-wasi.md`.

```
wasm-verify FILE.wasm never-call IMPORT
wasm-verify FILE.wasm assert-never-false IMPORT
wasm-verify FILE.wasm never-call-from IMPORT EXPORT
wasm-verify FILE.wasm imports
wasm-verify FILE.wasm exports
```

`IMPORT` is an import index or `module.name`; `EXPORT` is an index into the function exports or
an export name. Exit code `0` when a report is printed (whatever the verdict), `2` on a usage,
input or decoding error. -/

namespace Silmaril.Wasm.Verify.Cli

open Silmaril.Wasm

/-- The usage message. -/
def usage : String :=
  "usage: wasm-verify FILE.wasm (never-call|assert-never-false) IMPORT\n" ++
  "       wasm-verify FILE.wasm never-call-from IMPORT EXPORT\n" ++
  "       wasm-verify FILE.wasm (imports|exports)\n" ++
  "IMPORT is an import index or module.name, EXPORT an index into the function exports or an\n" ++
  "export name; prints the JSON report of the verified checker."

/-- Escape a string for JSON. -/
def jsonStr (s : String) : String :=
  "\"" ++ (s.toList.map fun c =>
    if c == '"' then "\\\"" else if c == '\\' then "\\\\" else if c == '\n' then "\\n"
    else c.toString).foldl (· ++ ·) "" ++ "\""

/-- The kind of an import, as a string. -/
def externKind : ExternType → String
  | .func _ => "func"
  | .table _ => "table"
  | .memory _ => "memory"
  | .global _ => "global"
  | .tag _ => "tag"

/-- The imports of a module, as JSON. -/
def importsJson (m : Module) : String :=
  "{\"imports\":[" ++ ",".intercalate ((List.range m.imports.length).zip m.imports |>.map
    fun (k, im) => "{\"index\":" ++ toString k ++ ",\"module\":" ++ jsonStr im.moduleName ++
      ",\"name\":" ++ jsonStr im.name ++ ",\"kind\":" ++ jsonStr (externKind im.type) ++ "}") ++
    "]}"

/-- The function exports of a module (name, function index), in order: the export indices of
`checkFrom`. -/
def funcExports (m : Module) : List (String × Nat) :=
  m.exports.filterMap fun x => match x.index with
    | .func y => some (x.name, y.toNat)
    | _ => none

/-- The function exports of a module, as JSON. -/
def exportsJson (m : Module) : String :=
  let fx := funcExports m
  "{\"exports\":[" ++ ",".intercalate ((List.range fx.length).zip fx |>.map
    fun (k, (n, y)) => "{\"index\":" ++ toString k ++ ",\"name\":" ++ jsonStr n ++
      ",\"func\":" ++ toString y ++ "}") ++ "]}"

/-- Resolve a function export given as an index or as a name. -/
def resolveExport (m : Module) (arg : String) : Option Nat :=
  match arg.toNat? with
  | some k => some k
  | none =>
    let fx := funcExports m
    ((List.range fx.length).zip fx).findSome? fun (k, (n, _)) => if n == arg then some k else none

/-- Resolve an import given as an index or as `module.name`. -/
def resolveImport (m : Module) (arg : String) : Option Nat :=
  match arg.toNat? with
  | some k => some k
  | none => ((List.range m.imports.length).zip m.imports).findSome? fun (k, im) =>
      if im.moduleName ++ "." ++ im.name == arg then some k else none

/-- Parse a property name. -/
def parseProperty (name : String) (i : Nat) : Option Property :=
  match name with
  | "never-call" | "neverCall" => some (.neverCall i)
  | "assert-never-false" | "assertNeverFalse" => some (.assertNeverFalse i)
  | _ => none

/-- Decode a binary module (standard, or with compact imports). -/
def decode (bytes : ByteArray) : Except String Module :=
  (Silmaril.Wasm.Binaryen.Exe.CompactInput.prepare bytes).map (·.source)

/-- The command line. -/
def run (args : List String) : IO UInt32 := do
  let readModule (path : String) : IO (Option Module) := do
    let bytes ← IO.FS.readBinFile path
    match decode bytes with
    | .ok m => return some m
    | .error e =>
      IO.eprintln s!"wasm-verify: cannot decode {path}: {e}"
      return none
  try
    match args with
    | [path, "imports"] =>
      let some m ← readModule path | return 2
      IO.println (importsJson m)
      return 0
    | [path, "exports"] =>
      let some m ← readModule path | return 2
      IO.println (exportsJson m)
      return 0
    | [path, "never-call-from", imp, exp] | [path, "neverCallFrom", imp, exp] =>
      let some m ← readModule path | return 2
      let some i := resolveImport m imp | do
        IO.eprintln s!"wasm-verify: no import {imp}\n{usage}"
        return 2
      let some e := resolveExport m exp | do
        IO.eprintln s!"wasm-verify: no function export {exp}\n{usage}"
        return 2
      IO.println (checkFrom m i e).toJson
      return 0
    | [path, prop, imp] =>
      let some m ← readModule path | return 2
      let some i := resolveImport m imp | do
        IO.eprintln s!"wasm-verify: no import {imp}\n{usage}"
        return 2
      let some φ := parseProperty prop i | do
        IO.eprintln s!"wasm-verify: unknown property {prop}\n{usage}"
        return 2
      IO.println (check m φ).toJson
      return 0
    | _ =>
      IO.eprintln usage
      return 2
  catch e =>
    IO.eprintln s!"wasm-verify: {e}"
    return 2

end Silmaril.Wasm.Verify.Cli

/-- The `wasm-verify` entry point. -/
def main (args : List String) : IO UInt32 :=
  Silmaril.Wasm.Verify.Cli.run args
