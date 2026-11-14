import WasmTools.Wast

/-!
# `wasm-tools-wast-bench`: phase timings of `json-from-wast` and `wast`

`wasm-tools-wast-bench FILE.wast…` prints, per file, the milliseconds spent in each phase:
positioned lexing (`lexBytes`, `bracket`), the check against the verified lexer
(`readCheck`), the script reader (`Script.ofSExps?`), the JSON lowering (`scriptJson`),
the JSON printing, and the `wast` check (`checkScript`). Used by
`tools/wasm-tools/tests/wast/bench.sh` as a regression benchmark. `wasm-tools-wast-bench --full
FILE` times every directive with the backend of `wasm-tools wast` and the phases of the first
module (encoding, validation, the round trip and its steps).
-/

open Silmaril.Wasm.Tools.Wast

def timeIt {α : Type} (f : Unit → IO α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let a ← f ()
  let t1 ← IO.monoNanosNow
  return (a, (t1 - t0) / 1000000)

/-- All bare tokens of positioned trees. -/
partial def syms : PNode → List String
  | .atom _ (.sym t) => [t]
  | .atom .. => []
  | .list _ _ xs => xs.flatMap syms

/-- `--check-floats FILE…`: the fast float reader agrees with the specification's candidate
search on every bare token (as `f32` and as `f64`). -/
def checkFloats (args : List String) : IO UInt32 := do
  let mut n := 0
  let mut bad := 0
  for path in args do
    let text ← IO.FS.readFile path
    let some ps := (lexBytes text.toUTF8 >>= bracket).toOption | continue
    for t in ps.flatMap syms do
      n := n + 1
      if floatLit? .f32 t != floatLitFast? .f32 t || floatLit? .f64 t != floatLitFast? .f64 t then
        bad := bad + 1
        IO.println s!"DISAGREE {path}: {t}"
  IO.println s!"floats: {n} tokens, {bad} disagreements"
  return (if bad == 0 then 0 else 1)

/-- `--full FILE`: the `wast` check with the backend of `wasm-tools wast` (`fullBackend` with
the default features), timing every directive; prints the slowest ten. -/
def fullTimes (path : String) : IO UInt32 := do
  let text ← IO.FS.readFile path
  let b := text.toUTF8
  let some (ps, _) := (read text).toOption | IO.eprintln "unreadable"; return 1
  let some (.directives ds) := Script.ofSExps? (ps.map PNode.erase) | IO.eprintln "not a script"; return 1
  let be := fullBackend Silmaril.Wasm.Tools.Features.WFeatures.dflt
  let mut times : Array (Nat × Nat) := #[]
  let mut fails := 0
  for ((d, p), i) in (ds.zip ps).zipIdx do
    let t0 ← IO.monoMsNow
    let r ← IO.lazyPure fun _ => Id.run (checkDirective be {} noSnap path b i d p).run
    match r with
    | .ok () => pure ()
    | .error _ => fails := fails + 1
    let t1 ← IO.monoMsNow
    times := times.push (t1 - t0, p.pos)
  -- the phases of the first module directive
  match ds.zip ps with
  | (.module q, p) :: _ =>
    let src := modSrc b p (.module q)
    let t0 ← IO.monoMsNow
    let e ← IO.lazyPure fun _ => encodeQW be.enc src q
    let t1 ← IO.monoMsNow
    IO.println s!"encode {t1 - t0} ms {(e.toOption.map ByteArray.size)}"
    if let .ok bytes := e then
      let v ← IO.lazyPure fun _ => be.validate bytes
      let t2 ← IO.monoMsNow
      IO.println s!"validate {t2 - t1} ms {v.toBool}"
      if let some rt := be.roundtrip then
        let ta ← IO.monoMsNow
        let t1' ← IO.lazyPure fun _ => rt.print bytes
        let tb ← IO.monoMsNow
        IO.println s!"  print {tb - ta} ms {t1'.toOption.map String.length}"
        if let .ok txt := t1' then
          let b2 ← IO.lazyPure fun _ => rt.parse txt
          let tc ← IO.monoMsNow
          IO.println s!"  parse {tc - tb} ms {b2.toOption.map ByteArray.size}"
          let re ← IO.lazyPure fun _ => rt.reencode bytes
          let td ← IO.monoMsNow
          IO.println s!"  reencode {td - tc} ms {re.toOption.map ByteArray.size}"
          if let .ok b2 := b2 then
            let c ← IO.lazyPure fun _ => binaryCompare b2 bytes
            let te ← IO.monoMsNow
            IO.println s!"  binaryCompare {te - td} ms {c.toBool}"
            let t2' ← IO.lazyPure fun _ => rt.print b2
            let tf ← IO.monoMsNow
            IO.println s!"  print2 {tf - te} ms"
            let eq ← IO.lazyPure fun _ => (t2'.toOption.getD "") != txt
            let tg ← IO.monoMsNow
            IO.println s!"  neq {tg - tf} ms {eq}"
            let x1 ← IO.lazyPure fun _ => Id.run (foldedPrint {} noSnap path rt bytes true).run
            let th ← IO.monoMsNow
            IO.println s!"  foldedPrint {th - tg} ms {x1.toBool}"
            let x2 ← IO.lazyPure fun _ => Id.run (foldedRoundtrip rt bytes true txt "").run
            let ti ← IO.monoMsNow
            IO.println s!"  foldedRoundtrip-construct-and-run {ti - th} ms {x2.toBool}"
            let x3 ← IO.lazyPure fun _ => Id.run (reencodeCheck rt bytes).run
            let tj ← IO.monoMsNow
            IO.println s!"  reencodeCheck {tj - ti} ms {x3.toBool}"
            let x4 ← IO.lazyPure fun _ => Id.run (roundtripWith {} noSnap rt path bytes false false).run
            let tk ← IO.monoMsNow
            IO.println s!"  roundtripWith ff {tk - tj} ms {x4.toBool}"
      let t2 ← IO.monoMsNow
      let r ← IO.lazyPure fun _ => Id.run (testRoundtrip be {} noSnap path bytes true true).run
      let t3 ← IO.monoMsNow
      IO.println s!"roundtrip {t3 - t2} ms {r.toBool}"
  | _ => pure ()
  let total := times.foldl (· + ·.1) 0
  IO.println s!"total {total} ms over {times.size} directives, {fails} failing"
  for (t, pos) in (times.qsort (fun a b => a.1 > b.1)).toList.take 10 do
    IO.println s!"{t} ms\tline {lineOf (lineStarts b) pos}"
  return 0

def main (args : List String) : IO UInt32 := do
  if args.head? == some "--check-floats" then return ← checkFloats args.tail
  if let ["--full", f] := args then return ← fullTimes f
  IO.println "file\tbytes\tlex\tread\tscript\tlower\tprint\twast"
  for path in args do
    let text ← IO.FS.readFile path
    let b := text.toUTF8
    let (ps, tLex) ← timeIt fun _ => do
      match lexBytes b >>= bracket with
      | .ok ps => pure ps
      | .error e => throw (IO.userError s!"{path}: {e.msg}")
    let (ok, tCheck) ← timeIt fun _ => pure (match read text with | .ok _ => true | .error _ => false)
    let (sc, tScript) ← timeIt fun _ => pure (Script.ofSExps? (ps.map PNode.erase))
    let some sc := sc | IO.eprintln s!"{path}: not a script"; continue
    let c : LowerCtx := { stem := fileStem path, source := b, lines := lineStarts b,
                          enc := defaultEncoder }
    let (j, tLower) ← timeIt fun _ => pure (scriptJson c path sc ps)
    let (n, tPrint) ← timeIt fun _ => pure (match j with | .ok (j, _) => j.compactFast.length | .error _ => 0)
    let (w, tWast) ← timeIt fun _ => pure (checkScriptPure defaultBackend {} path b sc ps).length
    IO.println s!"{path}\t{b.size}\t{tLex}\t{tCheck}\t{tScript}\t{tLower}\t{tPrint}\t{tWast}\t(check={ok}, json={n}, wastFailures={w})"
  return 0
