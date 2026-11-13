module

public import Silmaril.Cerberus.Frontend.Parse.Defs
public import Silmaril.Cerberus.Frontend.Desugar.Defs
public import Silmaril.Cerberus.Frontend.Typing.Defs
public import Silmaril.Cerberus.Ail.Canonical.Defs

/-! # `cerb-lean`: the driver

```
cerb-lean parse [--level cabs|ail|tail] [--time] FILE.i    print the document of FILE.i, or its reject
cerb-lean parse [--level cabs|ail|tail] --batch LIST       the same for every path listed in LIST, framed
cerb-lean read [--level cabs|ail|tail] [--time] FILE.sexp  decode an oracle document and print it again
cerb-lean read [--level cabs|ail|tail] --batch LIST
cerb-lean typecheck [--time] FILE.sexp                     type an oracle Ail document, print typed Ail
cerb-lean typecheck --batch LIST
cerb-lean digest [--batch LIST | FILE]                     the MD5 digest the symbols of FILE carry
```

`parse` reads the file, drops its final newline (Cerberus's `Pipeline.cpp` joins the
lines of the cpp output with `"\n"`), runs `Silmaril.Cerberus.Frontend.parse` and, at the
levels `ail` and `tail`, `Frontend.desugar` (under the MD5 `Ail.fileDigest` of the whole
file) and `Frontend.typecheck`. It prints the result exactly as `cerb-oracle --level
cabs|ail|tail` prints it: Ail documents go through `Ail.Canonical.renumber`, which replaces
every symbol number, loop id and marker id by its rank, as the oracle does. The default
level is `cabs`. `read` decodes with `Codec.readCabsDocument`, `readAilDocument` or
`readTailDocument`, which do not compare layout, and prints with the same printer as
`parse` (renumbering included), so a byte-exact round trip checks the types, the codec
and the canonical renumbering. `typecheck` reads an oracle Ail document and runs
`Frontend.typecheck` on its program (a reject passes through), so the typing port can be
measured on Cerberus's own Ail.

Single-file exit status: 0 for a document, 1 for a reject, 3 when a `read` input does
not decode (the message goes to stderr), 2 for a usage or I/O error. `--time` prints
`time read|parse|print|total <seconds>` to stderr. `parse` times only the frontend
(`Frontend.parse`, the digest, `desugar`, `typecheck`), as the oracle's `parse`,
`desugar` and `typing` phases time only Cerberus's.

In batch mode LIST holds one path per line. For the `i`-th path (from 0) the output
is one header line and then the payload:

```
@@cerb-lean <i> <document|reject|error> <payload bytes> <parse ns> <print ns>
```

followed by exactly `<payload bytes>` bytes: the printed document, or the error
message. Inputs are processed in order and stdout is flushed after each, so a caller
can stream, time out and restart at any input.

This file is the trusted glue of the frontend; the frontend is `Frontend.parse`,
`Frontend.desugar` and `Frontend.typecheck`.
-/

@[expose] public section

namespace Silmaril.Cerberus.Cabs.Main

open Silmaril.Cerberus Cabs.Codec

/-- What Cerberus's parser sees: the text without its final newline. -/
def cppText (b : ByteArray) : ByteArray :=
  if b.size > 0 && b[b.size - 1]! == '\n'.toUInt8 then b.extract 0 (b.size - 1) else b

/-- One result: the status word, the payload, and the parse and print times in ns. -/
structure Result where
  status : String
  payload : String
  parseNs : Nat
  printNs : Nat

/-- Evaluate `f ()` between two clock readings. Storing the value in a reference
forces it before the second reading. -/
def timed {α : Type} (f : Unit → α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let cell ← IO.mkRef (f ())
  let t1 ← IO.monoNanosNow
  return (← cell.get, t1 - t0)

def secs (ns : Nat) : String :=
  let us := ns / 1000
  s!"{us / 1000000}.{(toString (us % 1000000 + 1000000)).drop 1}"

/-- The frontend at a level, timed, and its printed output. -/
def frontend (level : String) (bytes : ByteArray) : IO Result := do
  let input := cppText bytes
  let ail : Unit → Except Ail.Reject (Ail.Program Unit) := fun _ => do
    let unit ← (Frontend.parse input).mapError Ail.Reject.ofCabs
    Frontend.desugar (Ail.fileDigest bytes) unit
  let digest := fun _ : Unit => hex ⟨(Ail.fileDigest bytes).bytes.toArray⟩
  match level with
  | "ail" =>
    let (r, parseNs) ← timed ail
    let (text, printNs) ← timed fun _ => match r with
      | .ok prog => Ail.Canonical.renumber (some (digest ()))
          (Ail.Codec.printAilDocument (.document cerberusCommit cerberusImpl prog))
      | .error e => Ail.Codec.printAilDocument (.reject cerberusCommit cerberusImpl e.stage e.loc e.message)
    return ⟨if r matches .ok _ then "document" else "reject", text, parseNs, printNs⟩
  | "tail" =>
    let (r, parseNs) ← timed fun _ => ail () >>= Frontend.typecheck
    let (text, printNs) ← timed fun _ => match r with
      | .ok prog => Ail.Canonical.renumber (some (digest ()))
          (Ail.Codec.printTailDocument (.document cerberusCommit cerberusImpl prog))
      | .error e => Ail.Codec.printTailDocument (.reject cerberusCommit cerberusImpl e.stage e.loc e.message)
    return ⟨if r matches .ok _ then "document" else "reject", text, parseNs, printNs⟩
  | _ =>
    let (r, parseNs) ← timed fun _ => Frontend.parse input
    let out := match r with
      | .ok unit => Output.document cerberusCommit cerberusImpl unit
      | .error rej => Output.reject cerberusCommit cerberusImpl rej
    let (text, printNs) ← timed fun _ => printCabsDocument out
    return ⟨if r matches .ok _ then "document" else "reject", text, parseNs, printNs⟩

def parseFile (level : String) (path : String) : IO Result := do
  frontend level (← IO.FS.readBinFile path)

/-- Decode with `dec`, print with `pr`; `status` tells a document from a reject. -/
def roundTrip {α : Type} (dec : String → Except String α) (pr : α → String) (isDoc : α → Bool)
    (text : String) : IO Result := do
  let (r, parseNs) ← timed fun _ => dec text
  match r with
  | .error e => return ⟨"error", e, parseNs, 0⟩
  | .ok out =>
    let (text, printNs) ← timed fun _ => pr out
    return ⟨if isDoc out then "document" else "reject", text, parseNs, printNs⟩

def isCabsDoc : Output → Bool | .document .. => true | .reject .. => false
def isAilDoc : Ail.Codec.AilOutput → Bool | .document .. => true | .reject .. => false
def isTailDoc : Ail.Codec.TailOutput → Bool | .document .. => true | .reject .. => false

def readFile (level : String) (path : String) : IO Result := do
  let bytes ← IO.FS.readBinFile path
  let some text := String.fromUTF8? bytes
    | return ⟨"error", "input is not valid UTF-8", 0, 0⟩
  match level with
  | "ail" =>
    roundTrip Ail.Codec.readAilDocument
      (fun x => Ail.Canonical.renumber none (Ail.Codec.printAilDocument x)) isAilDoc text
  | "tail" =>
    roundTrip Ail.Codec.readTailDocument
      (fun x => Ail.Canonical.renumber none (Ail.Codec.printTailDocument x)) isTailDoc text
  | _ => roundTrip readCabsDocument printCabsDocument isCabsDoc text

/-- Type the program of an oracle Ail document. -/
def typecheckFile (path : String) : IO Result := do
  let bytes ← IO.FS.readBinFile path
  let some text := String.fromUTF8? bytes
    | return ⟨"error", "input is not valid UTF-8", 0, 0⟩
  match Ail.Codec.readAilDocument text with
  | .error e => return ⟨"error", e, 0, 0⟩
  | .ok (.reject c i stage loc msg) =>
    return ⟨"reject", Ail.Codec.printTailDocument (.reject c i stage loc msg), 0, 0⟩
  | .ok (.document c i prog) =>
    let (r, parseNs) ← timed fun _ => Frontend.typecheck prog
    let (text, printNs) ← timed fun _ => match r with
      | .ok tprog => Ail.Canonical.renumber none (Ail.Codec.printTailDocument (.document c i tprog))
      | .error e => Ail.Codec.printTailDocument (.reject c i e.stage e.loc e.message)
    return ⟨if r matches .ok _ then "document" else "reject", text, parseNs, printNs⟩

/-- The lowercase hex MD5 of a file, as `Ail.fileDigest` computes it. -/
def digestFile (path : String) : IO Result := do
  let bytes ← IO.FS.readBinFile path
  let (h, ns) ← timed fun _ => hex ⟨(Ail.fileDigest bytes).bytes.toArray⟩
  return ⟨"document", h, ns, 0⟩

def single (mode : String → IO Result) (path : String) (time : Bool) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let r ← mode path
  let stdout ← IO.getStdout
  if r.status == "error" then
    IO.eprintln s!"cerb-lean: {path}: {r.payload}"
  else
    stdout.putStr r.payload
    stdout.flush
  if time then
    let total := (← IO.monoNanosNow) - t0
    IO.eprintln s!"time parse {secs r.parseNs}"
    IO.eprintln s!"time print {secs r.printNs}"
    IO.eprintln s!"time read {secs (total - r.parseNs - r.printNs)}"
    IO.eprintln s!"time total {secs total}"
  return match r.status with | "document" => 0 | "reject" => 1 | _ => 3

def batch (mode : String → IO Result) (list : String) : IO UInt32 := do
  let paths := (← IO.FS.lines list).filter (· ≠ "")
  let stdout ← IO.getStdout
  for (path, i) in paths.toList.zipIdx do
    let r ← try mode path catch e => pure ⟨"error", toString e, 0, 0⟩
    stdout.putStr s!"@@cerb-lean {i} {r.status} {r.payload.utf8ByteSize} {r.parseNs} {r.printNs}\n"
    stdout.putStr r.payload
    stdout.flush
  return 0

def usage : String :=
  "usage: cerb-lean parse|read [--level cabs|ail|tail] [--time] FILE\n" ++
  "       cerb-lean parse|read [--level cabs|ail|tail] --batch LIST\n" ++
  "       cerb-lean typecheck|digest [--time] FILE\n       cerb-lean typecheck|digest --batch LIST"

def run (args : List String) : IO UInt32 := do
  let (level, rest) := match args.tail with
    | "--level" :: l :: rest => (l, rest)
    | rest => ("cabs", rest)
  unless ["cabs", "ail", "tail"].contains level do IO.eprintln usage; return 2
  let mode : Option (String → IO Result) := match args.head? with
    | some "parse" => some (parseFile level)
    | some "read" => some (readFile level)
    | some "typecheck" => some typecheckFile
    | some "digest" => some digestFile
    | _ => none
  let some mode := mode | do IO.eprintln usage; return 2
  try
    match rest with
    | ["--batch", list] => batch mode list
    | ["--time", path] => single mode path true
    | [path] => single mode path false
    | _ => do IO.eprintln usage; return 2
  catch e => do
    IO.eprintln s!"cerb-lean: {e}"
    return 2

end Silmaril.Cerberus.Cabs.Main
