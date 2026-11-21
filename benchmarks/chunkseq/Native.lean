module

import Silmaril.Prelude.ChunkSeq.Balanced.Thms

open Silmaril.ChunkSeq.Balanced

def measurePhase {β : Type} (variant phase : String) (size : Nat) (work : Unit → β) : IO β := do
  let start ← IO.monoNanosNow
  let result := work ()
  let elapsed := (← IO.monoNanosNow) - start
  IO.println s!"{variant},{size},{phase},{elapsed}"
  return result

def checks (get : Nat → Option Nat) (count : Nat) : Nat := Id.run do
  let mut sum := 0
  let mut index := 0
  for _ in [:100000] do
    index := (index * 17 + 31) % count
    sum := sum + (get index).getD count
  return sum

def seqBench (items : List Nat) (count : Nat) : IO Unit := do
  let seq ← measurePhase "node" "build" count (fun _ => Seq.ofList .left items)
  let more ← measurePhase "node" "insert1000" count (fun _ =>
    (List.range 1000).foldl (fun state index => state.insert (count + index)) seq)
  let total ← measurePhase "node" "lookup100000" count (fun _ => checks more.get? more.size)
  IO.eprintln s!"checksum {total}"

def chunkBench (items : List Nat) (count width : Nat) : IO Unit := do
  let tag := s!"chunk{width + 1}"
  let seq ← measurePhase tag "build" count (fun _ => Chunked.ofList .left width items)
  let more ← measurePhase tag "insert1000" count (fun _ =>
    (List.range 1000).foldl (fun state index => state.insert (count + index)) seq)
  let total ← measurePhase tag "lookup100000" count (fun _ => checks more.get? more.size)
  IO.eprintln s!"checksum {total}"

public def main (arguments : List String) : IO Unit := do
  let [variant, count] := arguments | throw (IO.userError "expected node|chunk1|chunk32 and count")
  let some count := count.toNat? | throw (IO.userError "invalid count")
  let items := List.range count
  match variant with
  | "node" => seqBench items count
  | "chunk1" => chunkBench items count 0
  | "chunk32" => chunkBench items count 31
  | _ => throw (IO.userError "unknown variant")
