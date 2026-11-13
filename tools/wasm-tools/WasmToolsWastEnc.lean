import Silmaril.Wasm.Tools.Wast.Backend.Defs

/-!
# `wasm-tools-wastenc`: the `wast` crate encoder transcription alone (a test driver)

`wasm-tools-wastenc IN.wat OUT.wasm` encodes the core module text `IN.wat` with
`Silmaril.Wasm.Tools.WastEnc.encodeModule` only (no certified `parse` path first), so that
`tools/wasm-tools/tests/wast/wastenc.sh` can compare it byte for byte with the pinned
`wasm-tools parse` on every module of a corpus. `wasm-tools-wastenc --check IN.wat` prints
how `Silmaril.Wasm.Tools.Wast.checkedCore` treats the text: `accepted` (the certified pipeline
agrees with the transcription's bytes), `fallback` (it does not: the `parse` bytes are used),
`unchecked` (outside the certified fragment) or `error`. Exit status 0 on success, 1 on an
encoding error (the message on stderr), 2 on a usage error. `wasm-tools-wastenc --diag IN.wasm`
prints the message `wast` gives for the module (`Silmaril.Wasm.Tools.Wast.validateCoreF` with the
default features: `valid`, or the decoder's or the diagnosis' message).
-/

open Silmaril Silmaril.Wasm in
def checkClass (text : String) : String :=
  match Silmaril.Wasm.Tools.Text.textTree? text with
  | .error _ => "unchecked"
  | .ok (_, m) =>
    let dc := Binaryen.Exe.usesDataIdx m
    match Binaryen.Exe.encodeModuleWith? dc m, Silmaril.Wasm.Tools.Wast.wastEncText text with
    | .ok canon, .ok c =>
      if Silmaril.Wasm.Tools.Layout.accepts dc canon c.data.toList then "accepted"
      else if Silmaril.Wasm.Tools.Wast.acceptsNorm dc m c.data.toList then "accepted-norm"
      else "fallback"
    | .error _, _ => "unchecked"
    | _, .error _ => "error"

/-- Time one step (forcing its result through `toString` of a summary). -/
def timeStep {α : Type} (name : String) (f : Unit → α) (summary : α → String) : IO α := do
  let t0 ← IO.monoMsNow
  let a ← IO.lazyPure f
  let s ← IO.lazyPure fun _ => summary a
  let t1 ← IO.monoMsNow
  IO.println s!"{name}\t{t1 - t0} ms\t{s}"
  return a

def exceptSummary {α : Type} (sz : α → Nat) : Except String α → String
  | .ok a => s!"ok {sz a}"
  | .error e => s!"error {e}"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--time", inp] =>
    let text ← IO.FS.readFile inp
    let open_ := Silmaril.Wasm.Tools.Wast.checkedCore text (Silmaril.Wasm.Tools.Wast.wastEncText text)
    let _ ← timeStep "wastEnc" (fun _ => Silmaril.Wasm.Tools.Wast.wastEncText text) (exceptSummary ByteArray.size)
    let _ ← timeStep "textToBinary" (fun _ => Silmaril.Wasm.Tools.Text.textToBinary text) (exceptSummary ByteArray.size)
    let b ← timeStep "checkedCore" (fun _ => open_) (exceptSummary ByteArray.size)
    match b with
    | .ok b =>
      let _ ← timeStep "validate" (fun _ => Silmaril.Wasm.Tools.Wast.validateCoreF Silmaril.Wasm.Tools.Features.WFeatures.dflt b) (exceptSummary fun _ => 0)
      let t ← timeStep "print" (fun _ => Silmaril.Wasm.Tools.Wast.printAny b) (exceptSummary String.length)
      let _ ← timeStep "printFolded" (fun _ => Silmaril.Wasm.Tools.Wast.printFoldedAny b) (exceptSummary String.length)
      match t with
      | .ok t =>
        let b2 ← timeStep "parse" (fun _ => Silmaril.Wasm.Tools.Wast.parseAny t) (exceptSummary ByteArray.size)
        match b2 with
        | .ok b2 => let _ ← timeStep "print2" (fun _ => Silmaril.Wasm.Tools.Wast.printAny b2) (exceptSummary String.length)
        | .error _ => pure ()
      | .error _ => pure ()
      let _ ← timeStep "reencode" (fun _ => Silmaril.Wasm.Tools.Wast.reencodeAny b) (exceptSummary ByteArray.size)
    | .error _ => pure ()
    return 0
  | ["--diag", inp] =>
    let b ← IO.FS.readBinFile inp
    match Silmaril.Wasm.Tools.Wast.validateCoreF Silmaril.Wasm.Tools.Features.WFeatures.dflt b with
    | .ok () => IO.println "valid"
    | .error e => IO.println e
    return 0
  | ["--check", inp] =>
    IO.println (checkClass (← IO.FS.readFile inp))
    return 0
  | [inp, out] =>
    let text ← IO.FS.readFile inp
    match Silmaril.Wasm.Tools.Wast.wastEncText text with
    | .ok b => IO.FS.writeBinFile out b; return 0
    | .error e => IO.eprintln s!"error: {e}"; return 1
  | _ =>
    IO.eprintln "usage: wasm-tools-wastenc IN.wat OUT.wasm | --check IN.wat"
    return 2
