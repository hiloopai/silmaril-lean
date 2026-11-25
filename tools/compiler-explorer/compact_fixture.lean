module

import Silmaril.Compiler.C.Compact.Codec
meta import Silmaril.Compiler.C.Compact.Codec

open Silmaril.Cerberus.Ail.Codec
open Silmaril.Cerberus.Cabs.Wire
open Silmaril.Compiler.C.Compact
open Silmaril.Compile.C.Sem

def readAil (input : String) : IO Silmaril.Cerberus.Ail.TypedProgram := do
  let bytes ← IO.FS.readBinFile input
  match (read bytes).bind (decodeProgram decodeGenTypeCategory) with
  | .ok ail => return ail
  | .error reason => throw (IO.userError reason)

def checked (ail : Silmaril.Cerberus.Ail.TypedProgram) : IO Projection :=
  match project ail with
  | .ok packed => pure packed
  | .error reason => throw (IO.userError reason)

def timed (count : Nat) (run : Nat → Option Int) : IO (Nat × Int) := do
  let start ← IO.monoNanosNow
  let mut checksum := 0
  for index in [0:count] do
    let some value := run index | throw (IO.userError "benchmark evaluation stopped")
    checksum := checksum + value
  return ((← IO.monoNanosNow) - start, checksum)

def bench (input : String) (count : Nat) : IO Unit := do
  let ail ← readAil input
  let start ← IO.monoNanosNow
  let packed ← checked ail
  let projectNs := (← IO.monoNanosNow) - start
  let [(symbol, _)] := ail.2.functionDefinitions | throw (IO.userError "expected one Ail definition")
  let args := fun index => (List.range packed.fn.arity).map fun parameter =>
    (if index % 2 = 0 then Int.ofNat parameter else -Int.ofNat parameter) + Int.ofNat (index % 31)
  let start ← IO.monoNanosNow
  let prepared := C0.prepare ail
  unless prepared.funcs.contains symbol.number do throw (IO.userError "missing C0 function")
  let prepareNs := (← IO.monoNanosNow) - start
  for index in [0:count] do
    let actual := (C0.callFn prepared 80 symbol (args index) {}).toOption.map Prod.fst
    unless actual == (packed.fn.run (args index).toArray).toOption && actual.isSome do
      throw (IO.userError "benchmark models disagree")
  let (ailNs, ailSum) ← timed count (fun index => (C0.callFn prepared 80 symbol (args index) {}).toOption.map Prod.fst)
  let (compactNs, compactSum) ← timed count (fun index => (packed.fn.run (args index).toArray).toOption)
  IO.println s!"{input}: calls={count} project_ns={projectNs} c0_prepare_ns={prepareNs} c0_ns={ailNs} compact_ns={compactNs} checksums={ailSum}/{compactSum}"

public def main : List String → IO Unit
  | ["bench", input, iterations] => do
    let some count := iterations.toNat? | throw (IO.userError "expected an iteration count")
    if count == 0 || count > 100000 then throw (IO.userError "expected 1–100000 calls")
    bench input count
  | [input, tree, origins] => do
    let packed ← checked (← readAil input)
    IO.FS.writeFile tree packed.fn.encode
    IO.FS.writeFile origins packed.originText
  | _ => throw (IO.userError "usage: compact_fixture <typed-ail.sexp> <compact.sexp> <compact-origins.sexp>")
