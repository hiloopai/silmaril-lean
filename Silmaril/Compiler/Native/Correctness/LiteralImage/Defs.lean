module

public import Silmaril.Compiler.Native.Correctness.Execution.Defs
/-! One explicit closed-main process image for the actual canonical literal42
83-byte code. The data is shared by assembly and execution certificates. This
header introduces no evaluator, assembler-correctness or general Loaded claim. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.LiteralImage
open Silmaril Silmaril.X86

/-- The exact canonical instruction bytes, also obtained by GNU as2.42 from
actual O0 compiler output; external assembler correctness is separate. -/
def code : List Byte := [0x55, 0x48, 0x89, 0xe5, 0x48, 0x83, 0xec, 0x30, 0x48, 0x83, 0xe4, 0xc0, 0x48, 0x89, 0xe0, 0x48, 0x89, 0x45, 0xf8, 0xeb, 0x0, 0x48, 0xb8, 0x2a, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0x89, 0x45, 0xe8, 0x48, 0x8b, 0x45, 0xe8, 0x48, 0x63, 0xc0, 0x48, 0x89, 0x45, 0xe0, 0x48, 0x8b, 0x45, 0xe0, 0x48, 0x63, 0xc0, 0x48, 0x89, 0x45, 0xd8, 0x48, 0x8b, 0x45, 0xd8, 0xc9, 0xc3, 0x48, 0xb8, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0x89, 0x45, 0xe8, 0x48, 0x8b, 0x45, 0xe8, 0xc9, 0xc3]
def memory : Process.Memory := {
  regions := [⟨0x1000, 0x1000, ⟨true, false, true⟩⟩,
    ⟨0x2000, 0x1000, ⟨true, true, false⟩⟩,
    ⟨0x5000, 0x1000, ⟨true, false, false⟩⟩]
  bytes := Process.Memory.install
    (Process.Memory.install (Process.Memory.install ∅ 0x1000 code)
      0x2ff8 (Machine.LittleEndian.encodeWords [0x4000]))
    0x5000 ((Silmaril.Compile.Core.Spec.argBlock 0x5000 ["a.out"]).map
      fun byte => BitVec.ofNat 8 byte.toNat) }
def core : X86.State := {
  regs := fun r => if r == .rsp then 0x2ff8 else if r == .rdi then 1 else if r == .rsi then 0x5000 else 0
  rip := 0x1000
  flags := ⟨none, none, none, none, none, none⟩ }
def initial : NativeState := ⟨Features.State.ofCore core, memory⟩
def returnedExit? : Features.Outcome → Option Nat
  | .returned final => some ((final.state.core.read .rax).toNat % 256)
  | _ => none
def result : Option Nat :=
  (Features.run Features.FeatureSet.baseline64 [Features.floatExt, Features.Fpu.ext]
    0x4000 17 initial).bind fun mid => returnedExit? (step 0x4000 mid)
def image : Image := ⟨0x1000, code, 0x1000, 0x4000, 0x5000, initial⟩

/-- Actual unbounded observations of this image, without a caller projection. -/
def behaviors : Set Observation := {observation | Realises image.exit image.initial observation}

end Silmaril.Compiler.Native.Correctness.LiteralImage
