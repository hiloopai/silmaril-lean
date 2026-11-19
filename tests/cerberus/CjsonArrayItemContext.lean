module
public meta import Silmaril.Elf.Corpus.CjsonArrayItem.Context.Defs
public meta import Silmaril.Cerberus.Core.Outcome.Defs
public meta import tests.cerberus.RuntimeShard
public meta section
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Elf.Corpus.CjsonArrayItem
private def sample (n : Fin 65) (index : Int) (seed : Fin 3) (isNull : Bool) : Context.Input where
  isNull := isNull
  length := n
  index := BitVec.ofInt 32 index
  base := 1048576+65536*seed.val
  payload off := BitVec.ofNat 8 (off*31+seed.val*17)
  aligned := by omega
  lower := by omega
  upper := by have := seed.isLt; omega
public def main (args : List String) : IO Unit := do
  let seeds ← Cerberus.RuntimeShard.seeds args
  let mut cases := 0
  let F := Source.Elaboration.function
  unless reprStr Source.Elaboration.core.funs == reprStr Source.programDocument.bindings.funs &&
      reprStr Source.Elaboration.core.funInfo == reprStr Source.programDocument.bindings.funInfo do
    throw <| IO.userError "actual source Core/metadata differ from saved source-backed closure"
  let lengths : List (Fin 65) := [⟨0,by decide⟩,⟨1,by decide⟩,⟨8,by decide⟩,⟨64,by decide⟩]
  for n in lengths do
    for index in ([-1,0,1,4,8,64,2147483647] : List Int) do
      for seed in seeds do
        for isNull in [false,true] do
          let input := sample n index seed isNull
          let before ← match Context.prepare input with
            | .ok value => pure value
            | .error why => throw <| IO.userError why
          let result := run F.file ∅ 2000000 before
          let expected := if isNull || index < 0 || index >= (n.val : Int) then 0
            else Context.heap input (index.toNat+1)
          match result.ending with
          | some (.defined value) =>
            unless Context.pointerWord input value == some (BitVec.ofNat 64 expected) do
              throw <| IO.userError s!"wrong actual caller pointer n={n.val},index={index},null={isNull}"
            match value with
            | .loaded (.specified (.pointer (.allocated id address))) =>
              unless id == index+3 && address == (expected : Int) do
                throw <| IO.userError "actual pointer allocation provenance/address mismatch"
            | .loaded (.specified (.pointer (.null _))) =>
              unless expected == 0 do throw <| IO.userError "unexpected null pointer"
            | _ => throw <| IO.userError "actual source returned nonpointer"
          | ending => throw <| IO.userError s!"actual caller execution:{(observation ending).json.compress}"
          let after := result.finalState.memory
          unless after.enumTypes == before.memory.enumTypes && after.functions == before.memory.functions &&
              after.stdout == before.memory.stdout do throw <| IO.userError "caller registration/stdout changed"
          for id in List.range (n.val+4) do
            unless reprStr (after.allocations.lookup (Int.ofNat id)) == reprStr (before.memory.allocations.lookup (Int.ofNat id)) &&
                after.dead.contains (Int.ofNat id) == before.memory.dead.contains (Int.ofNat id) do
              throw <| IO.userError "caller allocation/lifetime changed"
          for address in (List.range ((n.val+2)*64)).map (input.base+·) ++ (List.range 12).map (4096+·) do
            unless after.bytes.lookup (Int.ofNat address) == before.memory.bytes.lookup (Int.ofNat address) &&
                after.pointerBytes.lookup (Int.ofNat address) == before.memory.pointerBytes.lookup (Int.ofNat address) do
              throw <| IO.userError "original heap/parameter bytes or provenance changed"
          for id in List.range after.nextId.toNat do
            if (Int.ofNat id) >= before.memory.nextId then
              unless after.dead.contains (Int.ofNat id) do throw <| IO.userError "private call/local object remains live"
          if n.val == 1 && index == 1 && !isNull then
            let invalid := {before with memory := {before.memory with allocations := before.memory.allocations.erase 3}}
            match (run F.file ∅ 2000000 invalid).ending with
            | some (.defined _) => throw <| IO.userError "missing caller allocation accepted"
            | none => throw <| IO.userError "invalid entry exhausted fuel"
            | some (.unsupported why) =>
              unless why == "outside allocation lifetime UB mapping" do throw <| IO.userError s!"unexpected Unsupported:{why}"
            | some _ => pure ()
          unless (Context.pointerWord input (.loaded (.specified (.pointer (.allocated 0 input.base))))).isNone &&
              (Context.pointerWord input (.loaded (.specified (.pointer (.allocated 2 (input.base+8)))))).isNone do
            throw <| IO.userError "forged provenance/offset pointer accepted by observation"
          cases := cases + 1
  IO.println s!"PASS{cases} actual registered-candidate caller/helper Core cases: null/list lengths0,1,8,64; seven signed indices; three addresses/payloads; typed readonly caller memory/provenance/lifetimes and private cleanup; missing-allocation/forged-provenance negatives. Finite observations, no semantic/termination proof."
  Cerberus.RuntimeShard.report "core" seeds cases
