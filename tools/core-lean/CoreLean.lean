
import Silmaril.Cerberus.Core.Outcome.Defs
import Silmaril.Cerberus.Codec.WellFormed.Defs
import Silmaril.Compiler.Core.Reader.Defs
import Silmaril.Compiler.Core.Backend.Defs
import Silmaril.Compiler.Core.Emit.Defs
import Silmaril.Compiler.Core.Verified.LoopFallthrough.Defs
import Silmaril.Compiler.Core.Verified.Cfg.Defs

/-! # `core-lean`: Cerberus Core documents in Lean

```
core-lean read FILE...                  decode each `cerb-oracle --level core` document with
                                        `Compile.Core.Reader.read`, proved equal to the checked
                                        codec `Codec.WellFormed.parseDocument` (`read_eq`); one line
                                        per file: `ok BYTES SECS` or `error MESSAGE`
core-lean compare FILE...               decode with both and print both times and whether they agree
core-lean run FILE [FUEL] [CHOICE] [ARG...]
                                        run the bounded Core dynamics (`Core.Run.runWith`) and print
                                        one JSON observation: status, value, raw stdout
core-lean loop-shape FILE                inspect the proved mutable-loop boundary recognizers;
                                        report saved-header continuations without compiling
core-lean cfg-shape FILE                 print the trees of `Cfg.recognizeBody` with the file's
                                        string literals (print nodes enabled), without compiling
```

Exit status 0 when every document decodes (read) or the run produced an observation (run).
-/

open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics

open Silmaril.Compile.Core.Verified in
private def loopLocals : EE → List Sym
  | .mk _ (.sseq (.mk _ (.base (some x, _))) cr rest) =>
      (if Locals.createInt cr then [x] else []) ++ loopLocals rest
  | .mk _ (.sseq _ a b) => loopLocals a ++ loopLocals b
  | _ => []

open Silmaril.Compile.Core.Verified in
private def loopTerm : StateExpr.Term → String
  | .lit n => toString n
  | .var q => s!"local#{q.2}"
  | .bin op a b => s!"({repr op} {loopTerm a} {loopTerm b})"
  | .cmp r a b x y => s!"({repr r} {a} {b} {loopTerm x} {loopTerm y})"
  | .cond c a b => s!"(if {loopTerm c} {loopTerm a} {loopTerm b})"
  | .un .neg a => s!"(- {loopTerm a})"
  | .un .compl a => s!"(~ {loopTerm a})"
  | .bit .and a b => s!"(& {loopTerm a} {loopTerm b})"
  | .bit .or a b => s!"(| {loopTerm a} {loopTerm b})"
  | .bit .xor a b => s!"(^ {loopTerm a} {loopTerm b})"
  | .divpos .quot d a => s!"(/ {loopTerm a} {d.val})"
  | .divpos .rem d a => s!"(% {loopTerm a} {d.val})"

open Silmaril.Compile.Core.Verified in
private def loopBodyView : LoopFallthrough.Stmt → String
  | .skip => "unit"
  | .assign x t => s!"(assign local#{x.number} {loopTerm t})"
  | .seq a b => s!"(seq {loopBodyView a} {loopBodyView b})"
  | .save x b => s!"(save local#{x.number} {loopBodyView b})"

open Silmaril.Compile.Core.Verified in
private def loopRawShape (xs : List Sym) : EE → Option (EE × EE × EE)
  | .mk _ (.sseq (.mk _ (.base (some c, _))) (.mk _ (.bound ec))
      (.mk _ (.sseq (.mk _ (.base (some b, _))) cb
        (.mk _ (.if_ (.mk _ () (.sym b')) yes no))))) =>
      if b'.key = b.key ∧ StmtIf.boolSource c cb = true ∧
          StateStmt.isFresh xs c = true ∧ StateStmt.isFresh xs b = true then some (ec, yes, no) else none
  | _ => none

private def hasEffectfulGuard : EE → Bool
  | .mk _ (.wseq _ (.mk _ (.unseq [_, _])) (.mk _ (.case_ _ _))) => true
  | .mk _ (.wseq _ (.mk _ (.unseq [a, b])) _) => hasEffectfulGuard a || hasEffectfulGuard b
  | _ => false

open Silmaril.Compile.Core.Verified in
private def wrappedTestDepth (file : Program) (xs : List Sym) (e : EE) : Option Nat :=
  if (loopRawShape xs e).isSome then some 0 else
    match e with
    | .mk _ (.sseq _ a _) | .mk _ (.wseq _ a _) => (wrappedTestDepth file xs a).map (· + 1)
    | _ => none
termination_by sizeOf e

open Silmaril.Compile.Core.Verified in
private def loopShapes (file : Program) (xs : List Sym) (labels : Labels) : EE → List Lean.Json
  | e@(.mk _ node) =>
    let here := match loopRawShape xs e with
      | none => []
      | some (sourceTest, yes, no) =>
        let recognizedTest := LoopCondition.recognize file xs e
        let body := match yes with
          | .mk _ (.sseq (.mk _ (.base (none, _))) a (.mk _ (.run () s [_]))) =>
              let recognized := LoopFallthrough.recognize file a
              [("backedge", Lean.toJson s.number),
                ("body_recognized", Lean.toJson recognized.isSome),
                ("body", Lean.toJson (recognized.map loopBodyView)),
                ("saved_header_depth", Lean.toJson
                  ((labels.lookup s).bind fun (_, b) => wrappedTestDepth file xs b))]
          | _ => [("body_recognized", Lean.toJson false)]
        [Lean.Json.mkObj ([("condition", Lean.toJson (recognizedTest.map fun (t, _, _) => loopTerm t)),
          ("test_recognized", Lean.toJson recognizedTest.isSome),
          ("effectful_case_guard", Lean.toJson (hasEffectfulGuard sourceTest)),
          ("false_recognized", Lean.toJson (LoopFallthrough.recognize file no).isSome)] ++ body)]
    here ++ match node with
      | .sseq _ a b | .wseq _ a b | .if_ _ a b => loopShapes file xs labels a ++ loopShapes file xs labels b
      | .save _ _ b | .bound b | .let_ _ _ b => loopShapes file xs labels b
      | _ => []
termination_by e => sizeOf e

/-- Inspect real Core syntax against the proved loop boundary recognizers.
This command does not emit an artifact or claim compiler acceptance. -/
def loopShapeOne (path : String) : IO UInt32 := do
  let text ← IO.FS.readFile path
  let .ok doc := Silmaril.Compile.Core.Reader.read text | do
    IO.eprintln "decode error"; return 1
  let some main := doc.file.main | return 1
  let some (.procedure _ _ _ _ body) := doc.file.funs.lookup main | return 1
  let xs := loopLocals body
  let saved := saves body
  IO.println (Lean.Json.mkObj [("locals", Lean.toJson (xs.map (·.number))),
    ("unique_label_keys", Lean.toJson (decide (saved.map (fun x => x.1.key)).Nodup)),
    ("conditions", Lean.toJson (loopShapes doc.file xs (Map.ofList saved) body))]).compress
  return 0

open Silmaril.Compile.Core.Verified in
private def cfgCode : Cfg.Code → String
  | .atom (.set q t) c => s!"local#{q.2} := {loopTerm t}; {cfgCode c}"
  | .atom (.clear q) c => s!"clear local#{q.2}; {cfgCode c}"
  | .print pre suf t c => s!"print {repr (String.ofList pre)} {loopTerm t} {repr (String.ofList suf)}; {cfgCode c}"
  | .test d t y n => s!"test{if d then "(do)" else ""} {loopTerm t} [yes: {cfgCode y}] [no: {cfgCode n}]"
  | .goto l => s!"goto label#{l.2}"
  | .ret t => s!"ret {loopTerm t}"
  | .abort => "abort"

open Silmaril.Compile.Core.Verified in
def cfgShapeOne (path : String) : IO UInt32 := do
  let text ← IO.FS.readFile path
  let .ok doc := Silmaril.Compile.Core.Reader.read text | do
    IO.eprintln "decode error"; return 1
  let some main := doc.file.main | return 1
  let some (.procedure _ _ _ [] body) := doc.file.funs.lookup main | do
    IO.println "main has parameters"; return 1
  let lits := StrLit.litsOf doc.file
  IO.println s!"literals: {(lits.getD []).map fun z => (z.1.number, z.2)}"
  match Cfg.recognizeBody doc.file body [] lits with
  | none => IO.println "not recognised"; return 1
  | some P =>
    IO.println s!"locals: {P.xs.map (·.number)}"
    IO.println s!"entry: {cfgCode P.entry}"
    for (l, c) in P.codes do
      IO.println s!"label#{l.2}: {cfgCode c}"
    return 0

def pinsOk (doc : Codec.Document) : Bool :=
  doc.commit == "b3e11ea334e95359907d4abf9194f0e7fedc6c6a" &&
    doc.implementation == "gcc_4.9.0_x86_64-apple-darwin10.8.0"

def readOne (path : String) : IO Bool := do
  let text ← IO.FS.readFile path
  let t0 ← IO.monoNanosNow
  let r := Silmaril.Compile.Core.Reader.read text
  let ok ← match r with
    | .ok doc => pure (some doc.commit.length)
    | .error e => do IO.println s!"error {path} {repr e.path} {e.message}"; pure none
  let t1 ← IO.monoNanosNow
  if let some _ := ok then
    IO.println s!"ok {path} {text.utf8ByteSize} {(Float.ofNat (t1 - t0)) / 1e9}"
  return ok.isSome

/-- Time `Reader.read` against `Codec.WellFormed.parseDocument` on one document. -/
def compareOne (path : String) : IO Bool := do
  let text ← IO.FS.readFile path
  let t0 ← IO.monoNanosNow
  let fast ← IO.lazyPure fun _ => Silmaril.Compile.Core.Reader.read text
  let t1 ← IO.monoNanosNow
  let checked ← IO.lazyPure fun _ => Codec.WellFormed.parseDocument text
  let t2 ← IO.monoNanosNow
  let same := match fast, checked with
    | .ok a, .ok b => a.commit == b.commit && a.implementation == b.implementation &&
        a.bindings.funs.length == b.bindings.funs.length
    | .error a, .error b => a == b
    | _, _ => false
  let secs (a b : Nat) : Float := (Float.ofNat (b - a)) / 1e9
  IO.println s!"{if same then "same" else "DIFFERENT"} {path} {text.utf8ByteSize} read {secs t0 t1} parseDocument {secs t1 t2}"
  return same

def runOne (path : String) (fuel choice : Nat) (args : List String) : IO UInt32 := do
  let text ← IO.FS.readFile path
  let .ok doc := Silmaril.Compile.Core.Reader.read text | do
    IO.println (Lean.Json.mkObj [("status", .str "DecodeError")]).compress; return 1
  if !pinsOk doc then
    IO.println (Lean.Json.mkObj [("status", .str "Pins")]).compress; return 1
  let (obs, out) := match initial doc.file (Map.ofList (doc.enumBindings.getD []))
      (Startup.execArguments args) with
    | .error o => (observation (some o), "")
    | .ok (state, labels) =>
      let r := runWith choice doc.file labels fuel state
      (runObservation r, r.finalState.memory.stdout)
  let value : Lean.Json := match obs.value with
    | some v => .num (Lean.JsonNumber.fromInt v)
    | none => .null
  IO.println (Lean.Json.mkObj [("status", .str obs.status), ("value", value),
    ("printed", match obs.printedValue with | some s => .str s | none => .null),
    ("ub", .str obs.ub), ("reason", .str obs.reason), ("stdout", .str out)]).compress
  return 0

/-- Test of the trusted artifact path: `main` returning `n`, through the proved backend,
`Core.Backend.artifactOf` and the frozen `Core.Emit.object`; writes the object `obj`. -/
def emitTest (obj : String) (n : Int) : IO UInt32 := do
  let mainF : Silmaril.Compile.Mir.Func :=
    { name := "main", params := [], results := 1,
      blocks := #[⟨#[.op (.const 0 (BitVec.ofInt 64 n))], .ret [.reg 0]⟩] }
  let units := #[Silmaril.Compile.Forks.CoreComp.Target.unit 0 1, { funcs := #[mainF] }]
  match Silmaril.Compile.Mir.link Silmaril.Compile.Forks.CoreComp.Target.layout units with
  | .error e => IO.eprintln e.message; return 1
  | .ok l =>
    match Silmaril.Compile.Core.Backend.artifactOf l with
    | .error e => IO.eprintln e; return 1
    | .ok a =>
      IO.FS.writeBinFile obj (Silmaril.Compile.Core.Emit.object a)
      IO.println s!"{(Silmaril.Compile.Core.Emit.ldArgs a "OUT" obj "CRT0").toList}"
      return 0

/-- Test of the argument path: `main(argc, argv)` returning `argc + argv[1][0]` (or `argc` alone
when `argc = 1`), through the proved backend, `Core.Backend.artifactOf` and `Core.Emit.object`. -/
def emitArgvTest (obj : String) : IO UInt32 := do
  let mainF : Silmaril.Compile.Mir.Func :=
    { name := "main", params := [2, 3], results := 1,
      blocks := #[⟨#[.op (.const 4 1), .op (.binary (.cmp .eq) 5 2 4)], .branch 5 1 2⟩,
                  ⟨#[], .ret [.reg 2]⟩,
                  ⟨#[.op (.load .b8 .zero 6 3 8), .op (.load .b1 .zero 7 6 0), .op (.binary .add 8 2 7)],
                    .ret [.reg 8]⟩] }
  let units := #[Silmaril.Compile.Forks.CoreComp.Target.unit 2 1, { funcs := #[mainF] }]
  match Silmaril.Compile.Mir.link Silmaril.Compile.Forks.CoreComp.Target.layout units with
  | .error e => IO.eprintln e.message; return 1
  | .ok l =>
    match Silmaril.Compile.Core.Backend.artifactOf l with
    | .error e => IO.eprintln e; return 1
    | .ok a =>
      IO.FS.writeBinFile obj (Silmaril.Compile.Core.Emit.object a)
      IO.println s!"{(Silmaril.Compile.Core.Emit.ldArgs a "OUT" obj "CRT0").toList}"
      return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["loop-shape", file] => loopShapeOne file
  | ["cfg-shape", file] => cfgShapeOne file
  | "read" :: files =>
    let mut ok := true
    for f in files do
      ok := (← readOne f) && ok
    return if ok then 0 else 1
  | "compare" :: files =>
    let mut ok := true
    for f in files do
      ok := (← compareOne f) && ok
    return if ok then 0 else 1
  | "run" :: file :: rest =>
    let fuel := (rest[0]?.bind String.toNat?).getD 1000000
    let choice := (rest[1]?.bind String.toNat?).getD 0
    runOne file fuel choice (rest.drop 2)
  | ["emit-test", obj, n] => emitTest obj (n.toInt?.getD 42)
  | ["emit-argv-test", obj] => emitArgvTest obj
  | _ =>
    IO.eprintln "usage: core-lean read FILE... | core-lean compare FILE... | core-lean run FILE [FUEL] [CHOICE] [ARG...] | core-lean loop-shape FILE"
    return 2
