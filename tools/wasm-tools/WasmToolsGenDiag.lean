import Silmaril.Wasm.Tools.Gen.Cmd.Model.Defs
import Silmaril.Wasm.Perf.ValidateR.Defs
import Silmaril.Wasm.Models.Syntax.Defs
import Silmaril.Wasm.Perf.CoreDecode.Defs
import Silmaril.Wasm.Binary.Core.Decode
import Silmaril.Wasm.Binaryen.Toolkit.WatSource
import Silmaril.Formats.SExp.EncodingWatFullLexer
import Silmaril.Wasm.Tools.Gen.Cmd.WatLex.Defs
import Silmaril.Wasm.Tools.Gen.Cmd.Smith.Defs
import Silmaril.Wasm.Tools.Gen.Cmd.WatFast.Defs

/-!
# `wasm-tools-gen-diag`: why a module is rejected (test tool of the gentool track)

`wasm-tools-gen-diag FILE…` prints, per file, one line: `decode` (the fast verified decoder
and silmaril's error message), `valid` (the validator `validateR`), and the components of
`Module.inFeatB` at the default model of `smith`/`mutate`/`shrink` that fail. `wasm-tools-gen-diag --smith-raw SEED OUT` writes the raw (unchecked) module `smith` draws from
SEED at the default model and prints whether the validator and the feature check accept it, so
that a fallback can be classified (generator or validator) by upstream `validate` of OUT.
`wasm-tools-gen-diag --wat-phases FILE` times each stage of silmaril's certified WAT reader
(the three lexers, the bracket matcher, the canonical and the source elaborator) on a text
file, the measurement behind the `Input` fast path (`docs/projects/wasm-wasi.md`). The differential
fuzzer (`tools/wasm-tools/tests/gen/fuzz.sh`) uses it to classify disagreements with upstream.
-/

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Tools.Gen.Cmd

def featParts (S : FeatureSet) (m : Module) : List String :=
  (if m.types.all (RecType.inFeatB S) then [] else ["types"]) ++
  (if m.imports.all (fun i => ExternType.inFeatB S i.type) then [] else ["imports"]) ++
  (if m.tags.isEmpty || S.has .exn then [] else ["tags"]) ++
  (if m.globals.all (Global.inFeatB S) then [] else ["globals"]) ++
  (if m.memories.all (MemoryType.inFeatB S) then [] else ["memories"]) ++
  (if m.tables.all (Table.inFeatB S) then [] else ["tables"]) ++
  (if m.funcs.all (Func.inFeatB S) then [] else ["funcs"]) ++
  (if m.elems.all (Elem.inFeatB S) then [] else ["elems"]) ++
  (if m.data.all (Data.inFeatB S) then [] else ["data"]) ++
  (if decide (m.memories.length + (m.imports.filter Import.isMemory).length ≤ 1) ||
      S.has .multiMemory then [] else ["multi-memory"]) ++
  (if decide (m.tables.length + (m.imports.filter Import.isTable).length ≤ 1) ||
      S.has .refTypes then [] else ["multi-table"])

open Silmaril.Formats.SExpEncoding.Wat in
/-- Time the stages of silmaril's WAT reader on one text file. -/
def watPhases (f : String) : IO UInt32 := do
  let s ← IO.FS.readFile f
  let cs := s.toList
  let time {α : Type} (name : String) (x : Unit → α) (show? : α → String) : IO α := do
    let t0 ← IO.monoMsNow
    let r := x ()
    let msg := show? r
    let t1 ← IO.monoMsNow
    IO.println s!"{name}: {t1 - t0} ms ({msg})"
    return r
  let n ← time "chars" (fun _ => cs.length) toString
  let _ ← time "lexExec (original)" (fun _ => lexExec? .core3 cs) (fun r => toString r.isSome)
  let _ ← time "lexGoBytes" (fun _ => lexGoBytes .core3 (n + 1) cs) (fun r => toString r.isSome)
  let _ ← time "lexF (linear fast path)" (fun _ => Silmaril.Wasm.Tools.Gen.Cmd.WatLex.lexF .core3 (n + 1) (n + 1) cs)
    (fun r => toString r.isSome)
  let toks ← time "lexGoFull" (fun _ => lexGoFull .core3 (n + 1) cs) (fun r => toString r.isSome)
  let tree ← time "bracketExec" (fun _ => toks.bind bracketExec?) (fun r => toString r.isSome)
  match tree with
  | none => return 1
  | some t =>
    let _ ← time "parseCanonical" (fun _ => Silmaril.Wasm.Binaryen.Toolkit.Wat.parseCanonical? t)
      (fun r => toString r.isSome)
    let _ ← time "Source.module" (fun _ => Silmaril.Wasm.Binaryen.Toolkit.Wat.Source.module? t)
      (fun r => toString r.isSome)
    let _ ← time "WatFast.moduleF? (fast path)" (fun _ => Silmaril.Wasm.Tools.Gen.Cmd.WatFast.moduleF? t)
      (fun r => toString r.isSome)
    return 0

/-- The raw module of a `smith` seed, encoded, with the checks' verdicts. -/
def smithRaw (seedFile out : String) : IO UInt32 := do
  let seed ← IO.FS.readBinFile seedFile
  let m := Smith.rawModule Model.default {} seed
  let v := (Silmaril.Wasm.Perf.ValidateR.validateR m).isSome
  let parts := featParts Model.default (wnorm m)
  IO.println s!"validateR {v}, features {if parts.isEmpty then "ok" else ", ".intercalate parts}"
  match Silmaril.Wasm.Binaryen.Exe.encodeModuleWith? true m with
  | .ok bs => IO.FS.writeBinFile out ⟨bs.toArray⟩; return 0
  | .error e => IO.println s!"encode: {e}"; return 1

def main (args : List String) : IO UInt32 := do
  if let ["--wat-phases", f] := args then return ← watPhases f
  if let ["--smith-raw", s, o] := args then return ← smithRaw s o
  let mut bad := 0
  for f in args do
    let b ← IO.FS.readBinFile f
    match Silmaril.Wasm.Perf.CoreDecode.decodeF b with
    | none =>
      let msg := match Binary.Core.Decode.decodeModule b with
        | .error e => e
        | .ok _ => "?"
      IO.println s!"{f}: decode failed: {msg}"; bad := bad + 1
    | some m =>
      let v := (Silmaril.Wasm.Perf.ValidateR.validateR m).isSome
      let parts := featParts Model.default m
      IO.println s!"{f}: decode ok, valid {v}, features {if parts.isEmpty then "ok" else ", ".intercalate parts}"
      if !v || !parts.isEmpty then bad := bad + 1
  return if bad == 0 then 0 else 1
