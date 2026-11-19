module
public meta import Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Equivalence.Thms
public meta section
open Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Equivalence
open Silmaril.X86
private def leftBytes : List (BitVec 8) := Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Equivalence.left.code
private def rightBytes : List (BitVec 8) := Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Equivalence.right.code
private def sp : Nat := 8388616
private def exit : Nat := 40960
private partial def execute (fuel : Nat) (m : MState) : IO MState := do
  if m.core.rip.toNat == exit then return m
  if fuel == 0 then throw <| IO.userError "machine fuel exhausted"
  match Open.step m with
  | some next => execute (fuel-1) next
  | none => throw <| IO.userError s!"machine stuck at{m.core.rip.toNat}"
private def check (input : Nat) (salt : Nat) (address frame : Nat) : IO (BitVec 32) := do
  let mut bytes : Silmaril.Process.ByteMemory := ∅
  bytes := Silmaril.Process.Memory.install bytes 20542 leftBytes
  bytes := Silmaril.Process.Memory.install bytes 10262 rightBytes
  bytes := Silmaril.Process.Memory.install bytes (sp-128) ((List.range 256).map fun j => BitVec.ofNat 8 (j*31+salt))
  let memory : Silmaril.Process.Memory := ⟨
    [⟨20542,leftBytes.length,⟨true,false,true⟩⟩,⟨10262,rightBytes.length,⟨true,false,true⟩⟩,⟨sp-128,256,⟨true,true,false⟩⟩],bytes⟩
  let some memory := Ext.storeN memory (BitVec.ofNat 64 sp) 8 (BitVec.ofNat 64 exit) | throw <| IO.userError "bad initial stack"
  let core : Silmaril.X86.State := ⟨(fun r => match r with
    | .rdi => BitVec.ofNat 64 (salt*256+input)
    | .rsp => BitVec.ofNat 64 sp
    | _ => BitVec.ofNat 64 (salt+r.toBitVec.toNat+17)), BitVec.ofNat 64 address,
      ⟨some (salt%2==0),some (salt%3==0),some (salt%5==0),some (salt%7==0),some (salt%11==0),some (salt%13==0)⟩,0⟩
  let before : MState := ⟨core,memory⟩
  let after ← execute 64 before
  unless after.core.read .rsp == BitVec.ofNat 64 (sp+8) do throw <| IO.userError "stack mismatch"
  for r in [Reg.rbx,.rbp,.r12,.r13,.r14,.r15] do
    unless after.core.read r == before.core.read r do throw <| IO.userError "callee-saved mutation"
  unless after.memory.regions == before.memory.regions && after.memory.bytes.size == before.memory.bytes.size do
    throw <| IO.userError "mapping/backing keys changed"
  for a in (List.range leftBytes.length).map (20542+·) ++ (List.range rightBytes.length).map (10262+·) ++ (List.range 256).map (sp-128+·) do
    unless sp-frame ≤ a && a < sp do
      unless after.memory.bytes.get? a == before.memory.bytes.get? a do throw <| IO.userError s!"unrelated memory mutation at{a}"
  return (after.core.read .rax).setWidth 32
public def main : IO Unit := do
  for salt in [0,1,0x123456789abcde,0xffffffffffffff] do
    for n in List.range 256 do
      let a ← check n salt 20542 12
      let b ← check n salt 10262 0
      unless a == b do throw <| IO.userError s!"different actual predicate returns at{n}, salt{salt}"
  IO.println "PASS1024 actual shared-initial-memory Open.step byte-predicate pairs: all256 bytes under four upper-register/flags/stack patterns, equal actual EAX, ABI and caller memory/mappings preserved outside exact12/0 frames; UNPROVED, finite observations are not semantic proofs"
