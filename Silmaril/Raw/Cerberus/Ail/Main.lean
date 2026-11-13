module

public import Silmaril.Cerberus.Ail.Codec.Defs

/-! # `ail-lean`: the driver

```
ail-lean read [--time] FILE.sexp      decode a typed-Ail oracle document and print it again
ail-lean read --batch LIST            the same for every path listed in LIST, framed
```

`read` decodes with `Codec.readTailDocument`, which does not compare layout, and prints with
`Codec.printTailDocument`, so a byte-exact round trip against `cerb-oracle --level tail`
checks the types and the codec.

Single-file exit status: 0 for a document, 1 for a reject, 3 when the input does not decode
(the message goes to stderr), 2 for a usage or I/O error. `--time` prints
`time read|parse|print|total <seconds>` to stderr (`parse` is the decoding).

In batch mode LIST holds one path per line. For the `i`-th path (from 0) the output is one
header line and then the payload:

```
@@ail-lean <i> <document|reject|error> <payload bytes> <parse ns> <print ns>
```

followed by exactly `<payload bytes>` bytes: the printed document, or the error message.
Inputs are processed in order and stdout is flushed after each, so a caller can stream, time
out and restart at any input.
-/

@[expose] public section

namespace Silmaril.Cerberus.Ail.Main

open Silmaril.Cerberus Ail.Codec

/-- One result: the status word, the payload, and the decode and print times in ns. -/
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

def readFile (path : String) : IO Result := do
  let bytes ← IO.FS.readBinFile path
  let some text := String.fromUTF8? bytes
    | return ⟨"error", "input is not valid UTF-8", 0, 0⟩
  let (r, parseNs) ← timed fun _ => readTailDocument text
  match r with
  | .error e => return ⟨"error", e, parseNs, 0⟩
  | .ok out =>
    let (text, printNs) ← timed fun _ => printTailDocument out
    let status := match out with | .document .. => "document" | .reject .. => "reject"
    return ⟨status, text, parseNs, printNs⟩

def single (path : String) (time : Bool) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let r ← readFile path
  let stdout ← IO.getStdout
  if r.status == "error" then
    IO.eprintln s!"ail-lean: {path}: {r.payload}"
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

def batch (list : String) : IO UInt32 := do
  let paths := (← IO.FS.lines list).filter (· ≠ "")
  let stdout ← IO.getStdout
  for (path, i) in paths.toList.zipIdx do
    let r ← try readFile path catch e => pure ⟨"error", toString e, 0, 0⟩
    stdout.putStr s!"@@ail-lean {i} {r.status} {r.payload.utf8ByteSize} {r.parseNs} {r.printNs}\n"
    stdout.putStr r.payload
    stdout.flush
  return 0

def usage : String :=
  "usage: ail-lean read [--time] FILE\n       ail-lean read --batch LIST"

def run (args : List String) : IO UInt32 := do
  unless args.head? == some "read" do
    IO.eprintln usage
    return 2
  try
    match args.tail with
    | ["--batch", list] => batch list
    | ["--time", path] => single path true
    | [path] => single path false
    | _ => do IO.eprintln usage; return 2
  catch e => do
    IO.eprintln s!"ail-lean: {e}"
    return 2

end Silmaril.Cerberus.Ail.Main
