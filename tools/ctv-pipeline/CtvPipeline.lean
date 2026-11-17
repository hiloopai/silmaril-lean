import Silmaril.Cerberus.TV.Validate.Defs
import Silmaril.Cerberus.Elaboration.Functions.Defs
import Silmaril.Cerberus.Ail.Codec.Defs
import Silmaril.Cerberus.Codec.WellFormed.Defs
import Silmaril.Cerberus.Spec.Check.Defs
import Silmaril.Cerberus.Elab.Translate.Defs
import Silmaril.Compiler.Native.TargetCoherence.Defs

/-! # `ctv-pipeline`: typed Ail → Core → whole-program validation (docs/projects/c-tv.md)

```
ctv-pipeline elaborate RUNTIME FRESH TAIL OUT     elaborate one typed-Ail document to a Core document
ctv-pipeline run RUNTIME FRESH OUTDIR [--depth N] [--budget N] [--observe NAME TERM STDOUT]...
                 NAME=TAIL...                      (TERM: an exit status, `signal:N` or `abort`)                      elaborate each route, explore, cross-validate
```

`RUNTIME` is a genuine Cerberus Core document whose runtime maps (`stdlib`, `impl`) and the
runtime alias map next to it (`ailnames.sexp`) are the elaborator's runtime inputs
(benchmarks/cerberus-elaboration/oracle). `FRESH` is the first fresh symbol number (above every
symbol of the typed Ail). The elaborator runs with the target configuration
`TargetCoherence.linuxLP64` and no enum registrations.

`run` writes `OUTDIR/<NAME>.core.sexp` for every route the elaborator accepts and prints one JSON
report: per route the elaboration result and the exploration of its Core (endings, `limited`,
`stuck`, gaps, undefined behaviour), per ordered pair of routes the validator's verdict
(`Silmaril.Cerberus.TV.validate`), and per observation (`--observe NAME STATUS STDOUT`: an exit
status and a file with the stdout of a native run) the verdict of `Spec.check` on every route.

**Evidence kind**: everything here is computed by the compiled Lean code (`compiled` in
`TV.Provenance`). A verdict is backed by the validator's soundness theorems
(`TV.validate_sound`, `TV.validate_refuted`, `Spec.check_sound`, `Spec.check_complete`) only up to
the faithfulness of the compiler and runtime that computed it; a kernel-checked instance needs
the verdict computed in the kernel.

Exit status: 0 report written; 2 usage or I/O error; 3 an input does not decode.
-/

open Silmaril.Cerberus Silmaril.Cerberus.TV Silmaril.Cerberus.Elaboration
open Lean (Json)

def checked {α : Type} (context : String) : Except String α → IO α
  | .ok v => pure v
  | .error e => throw <| IO.userError s!"{context}: {e}"

def readText (path : String) : IO String := do
  if path.endsWith ".gz" then
    let r ← IO.Process.output { cmd := "gzip", args := #["-dc", path] }
    unless r.exitCode == 0 do throw <| IO.userError s!"{path}: gzip: {r.stderr}"
    pure r.stdout
  else IO.FS.readFile path

def readAliases (path : System.FilePath) : IO (List (String × Sym)) := do
  let text ← IO.FS.readFile path
  let some tree := Silmaril.Formats.SExpEncoding.parseTagged? text
    | throw <| IO.userError s!"{path}: invalid tagged runtime alias map"
  let codec := Silmaril.TaggedCodec.Codec.map Silmaril.TaggedCodec.Codec.str Codec.sym
  match codec.decode tree with
  | .ok aliases => pure aliases
  | .error why => throw <| IO.userError s!"{path}: runtime alias decoding: {repr why}"

def readRuntime (path : String) : IO Functions.RuntimeInputs := do
  let doc ← match Codec.WellFormed.parseDocument (← readText path) with
    | .ok d => pure d
    | .error e => throw <| IO.userError s!"{path}: Core decoding: {repr e}"
  let dir := (System.FilePath.mk path).parent.getD "."
  let aliasPath := dir.parent.getD "." / "shared" / "runtime" / "ailnames.sexp"
  let aliases ← readAliases aliasPath
  pure { stdlib := doc.bindings.stdlib, impl := doc.bindings.impl, aliases }

inductive Elaborated where
  | ok (b : Codec.FileBindings)
  | rejected (stage why : String)

def elaborateTail (runtime : Functions.RuntimeInputs) (fresh : Nat) (text : String) :
    Except String Elaborated := do
  match ← Ail.Codec.readTailDocument text with
  | .reject _ _ stage _ msg => pure (.rejected stage msg)
  | .document _ _ prog =>
    let (result, _) := Functions.elaborate Silmaril.Compiler.Native.TargetCoherence.linuxLP64
      Target.emptyEnvironment runtime prog ⟨⟨[]⟩, fresh, fresh + 100000000⟩
    match result with
    | .ok b => pure (.ok b)
    | .error e => pure (.rejected "elaborate" (reprStr e))

def outcomeJson : Core.Dynamics.Outcome → Json
  | .defined v => Json.mkObj [("kind", "defined"), ("exit", match Spec.exitValue v with
      | .int n => Json.num n | .unspecified => "unspecified" | .other => "other")]
  | .ub _ u => Json.mkObj [("kind", "ub"), ("ub", reprStr u)]
  | .error e => Json.mkObj [("kind", "error"), ("why", e)]
  | .unsupported e => Json.mkObj [("kind", "unsupported"), ("why", e)]
  | .aborted => Json.mkObj [("kind", "aborted")]

def leavesJson (L : Leaves) : Json :=
  let ends := (L.ends.take 32).map fun (o, out) => Json.mkObj [("outcome", outcomeJson o), ("stdout", out)]
  Json.mkObj [("endings", L.ends.length), ("sample", Json.arr ends.toArray), ("limited", L.limited),
    ("stuck", L.stuck), ("gap", L.gap), ("ub", L.ub), ("steps", L.steps)]

def verdictString : Verdict → String
  | .validated => "validated" | .refuted => "refuted" | .unsupported => "unsupported" | .unknown => "unknown"

def checkVerdict : Spec.Verdict → String
  | .admitted => "admitted" | .rejected => "rejected" | .unknown => "unknown"

structure Opts where
  depth : Nat := 100000
  budget : Nat := 2000000
  observe : List (String × Spec.Termination × String) := []
  routes : List (String × String) := []

partial def parseOpts : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--depth" :: n :: rest, o => do parseOpts rest { o with depth := ← (n.toNat?.elim (.error "depth") .ok) }
  | "--budget" :: n :: rest, o => do parseOpts rest { o with budget := ← (n.toNat?.elim (.error "budget") .ok) }
  | "--observe" :: name :: st :: file :: rest, o => do
      let t ← match st.splitOn ":" with
        | ["signal", n] => n.toNat?.elim (.error "signal") (fun n => .ok (.signal n))
        | ["abort"] => .ok .abort
        | _ => st.toNat?.elim (.error "status") (fun n => .ok (.exit n))
      parseOpts rest { o with observe := o.observe ++ [(name, t, file)] }
  | r :: rest, o => match r.splitOn "=" with
      | [name, path] => parseOpts rest { o with routes := o.routes ++ [(name, path)] }
      | _ => .error s!"unexpected argument {r}"

def run (runtimePath : String) (fresh : Nat) (outDir : String) (o : Opts) : IO UInt32 := do
  let runtime ← readRuntime runtimePath
  IO.FS.createDirAll outDir
  let bounds : Bounds := { depth := o.depth, budget := o.budget }
  let mut routes : Array (String × Json) := #[]
  let mut programs : Array (String × Closed) := #[]
  for (name, path) in o.routes do
    let text ← readText path
    match elaborateTail runtime fresh text with
    | .error e => routes := routes.push (name, Json.mkObj [("status", "undecodable"), ("why", e)])
    | .ok (.rejected stage why) =>
        routes := routes.push (name, Json.mkObj [("status", "rejected"), ("stage", stage), ("why", why)])
    | .ok (.ok b) =>
        let doc := Elab.printDocument b
        IO.FS.writeFile (System.FilePath.mk outDir / s!"{name}.core.sexp") doc
        let P : Closed := ⟨b.toFile, ∅, []⟩
        let L := P.explore bounds
        programs := programs.push (name, P)
        routes := routes.push (name, Json.mkObj [("status", "elaborated"),
          ("core", s!"{name}.core.sexp"), ("explore", leavesJson L)])
  let mut pairs : Array Json := #[]
  for (a, A) in programs do
    for (b, B) in programs do
      if a != b then
        let r := validate Spec.Impl.lp64 A B bounds
        pairs := pairs.push (Json.mkObj [("source", a), ("target", b),
          ("verdict", verdictString r.verdict), ("coveredOnlyByUB", r.coveredOnlyByUB),
          ("uncovered", r.uncovered.length)])
  let mut observations : Array Json := #[]
  for (name, status, file) in o.observe do
    let out ← IO.FS.readBinFile file
    let obs : Spec.Obs := ⟨status, out.toList.map (·.toNat)⟩
    let mut per : Array (String × Json) := #[]
    for (p, P) in programs do
      let r := Spec.check Spec.Impl.lp64 P.file P.enums P.args [obs] { depth := o.depth, budget := o.budget }
      per := per.push (p, Json.str (checkVerdict (r.verdict obs)))
    let term := match status with
      | .exit n => s!"exit {n}" | .abort => "abort" | .signal n => s!"signal {n}"
    observations := observations.push (Json.mkObj [("name", name), ("termination", term),
      ("stdoutBytes", out.size), ("check", Json.mkObj per.toList)])
  let report := Json.mkObj [("schema", "silmaril.c-tv.pipeline.v1"), ("profile", "linuxX86_64"),
    ("elaborator", "Silmaril.Cerberus.Elaboration.Functions.elaborate, TargetCoherence.linuxLP64"),
    ("runtime", runtimePath), ("fresh", fresh), ("bounds", Json.mkObj [("depth", o.depth), ("budget", o.budget)]),
    ("evidence", "compiled"), ("routes", Json.mkObj routes.toList), ("pairs", Json.arr pairs),
    ("observations", Json.arr observations)]
  IO.println report.pretty
  return 0

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["elaborate", runtimePath, fresh, tail, out] =>
        let runtime ← readRuntime runtimePath
        let some n := fresh.toNat? | IO.eprintln "FRESH must be a number"; return 2
        match elaborateTail runtime n (← readText tail) with
        | .error e => IO.eprintln s!"ctv-pipeline: {tail}: {e}"; return 3
        | .ok (.rejected stage why) => IO.eprintln s!"ctv-pipeline: {tail}: rejected ({stage}): {why}"; return 1
        | .ok (.ok b) => IO.FS.writeFile out (Elab.printDocument b); return 0
    | "run" :: runtimePath :: fresh :: outDir :: rest =>
        let some n := fresh.toNat? | IO.eprintln "FRESH must be a number"; return 2
        match parseOpts rest {} with
        | .error e => IO.eprintln s!"ctv-pipeline: {e}"; return 2
        | .ok o => run runtimePath n outDir o
    | _ =>
        IO.eprintln "usage: ctv-pipeline elaborate RUNTIME FRESH TAIL OUT\n       ctv-pipeline run RUNTIME FRESH OUTDIR [--depth N] [--budget N] [--observe NAME STATUS STDOUT]... NAME=TAIL..."
        return 2
  catch e =>
    IO.eprintln s!"ctv-pipeline: {e}"; return 2
