module
public meta import Silmaril.Elf.Corpus.CjsonArrayItem.Context.Defs
public meta import Silmaril.X86.Open.Thms
public meta import tests.cerberus.RuntimeShard
public meta section
open Silmaril.X86
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
private def sp : Nat := 8388616
private def exit : Nat := 40960
private partial def execute (fuel : Nat) (m : MState) : IO MState := do
 if m.core.rip.toNat == exit then return m
 if fuel == 0 then throw <| IO.userError "actual caller/helper machine fuel exhausted"
 match Open.step m with
 | some next => execute (fuel-1) next
 | none => throw <| IO.userError s!"actual caller/helper machine stuck at{m.core.rip.toNat}"
public def main (args : List String) : IO Unit := do
 let seeds ← Cerberus.RuntimeShard.seeds args
 let mut cases := 0
 for n in (List.finRange 9).map (fun n => (⟨n.val,by have := n.isLt; omega⟩ : Fin 65)) ++ [⟨64,by decide⟩] do
  for index in ([-1,0,1,4,8,9,2147483647] : List Int) do
   for seed in seeds do
    for isNull in [false,true] do
     let input := sample n index seed isNull
     let source ← match Context.prepare input with
      | .ok source => pure source
      | .error why => throw <| IO.userError why
     let base := input.base
     let addr := fun (i : Nat) => base+64*i
     let mut bytes : Silmaril.Process.ByteMemory := ∅
     for offset in List.range ((n.val+2)*64) do
      let some (some v) := source.memory.bytes.lookup ((base+offset : Nat) : Int)
       | throw <| IO.userError "actual prepared caller payload unspecified"
      bytes := bytes.insert (base+offset) (BitVec.ofInt 8 v)
     bytes := Silmaril.Process.Memory.install bytes address code
     bytes := Silmaril.Process.Memory.install bytes (sp-128) (List.replicate 256 0x5a)
     let mut mem : Silmaril.Process.Memory := ⟨
       [⟨address,code.length,⟨true,false,true⟩⟩,⟨base,(n.val+2)*64,⟨true,true,false⟩⟩,
         ⟨sp-128,256,⟨true,true,false⟩⟩],bytes⟩
     let some ret := Ext.storeN mem (BitVec.ofNat 64 sp) 8 (BitVec.ofNat 64 exit)
       | throw <| IO.userError "return address store failed"
     mem := {ret with regions := [⟨address,code.length,⟨true,false,true⟩⟩,
       ⟨base,(n.val+2)*64,⟨true,false,false⟩⟩,⟨sp-128,256,⟨true,true,false⟩⟩]}
     let core : Silmaril.X86.State := ⟨(fun r => match r with
       | .rdi => Context.rootWord input
       | .rsi => BitVec.ofNat 64 (0xabcdef0100000000 + seed.val*2^32) ||| ((BitVec.ofInt 32 index).setWidth 64)
       | .rsp => BitVec.ofNat 64 sp
       | _ => BitVec.ofNat 64 (r.toBitVec.toNat+17)),BitVec.ofNat 64 callerAddress,
       ⟨some false,some false,some false,some false,some false,some false⟩,0⟩
     let before : MState := ⟨core,mem⟩
     let after ← execute 2048 before
     let expected := if isNull || index < 0 || index >= (n.val : Int) then 0 else addr (index.toNat+1)
     unless after.core.read .rax == BitVec.ofNat 64 expected && after.core.read .rsp == BitVec.ofNat 64 (sp+8) do
      throw <| IO.userError "actual caller/helper target pointer return/stack mismatch"
     for r in [Reg.rbx,.rbp,.r12,.r13,.r14,.r15] do
      unless after.core.read r == before.core.read r do throw <| IO.userError "callee-saved register changed"
     unless after.memory.regions == before.memory.regions && after.memory.bytes.size == before.memory.bytes.size do
      throw <| IO.userError "mapping or byte-key count changed"
     for a in (List.range ((n.val+2)*64)).map (base+·) ++
         (List.range code.length).map (address+·) ++ (List.range 256).map (sp-128+·) do
      unless sp-72 ≤ a && a < sp do
       unless after.memory.bytes.get? a == before.memory.bytes.get? a do
        throw <| IO.userError "caller/code/other backing bytes changed outside72-byte nested private frame"
     cases := cases + 1
 IO.println s!"PASS{cases} actual context-prepared Open.step caller/helper cases: null/list lengths0..8 and64, three actual source addresses/payloads, readonly caller+unrelated heap preserved, pointer returns, noncanonical high argument bits, SysV callee-saved/stack,72-byte nested private frame and complete mapping/key preservation; finite observations only"
 Cerberus.RuntimeShard.report "machine" seeds cases
