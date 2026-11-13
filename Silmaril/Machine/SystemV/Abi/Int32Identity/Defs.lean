module

public import Silmaril.Machine.X86.Decompile.Returns.Defs
public import Silmaril.Machine.SystemV.Abi.Ctypes.Defs
public import Silmaril.Machine.C.Api.SysV.Defs

/-! Real GCC13.3 O2 bytes for int id(int). The input is an actual integer-API
caller plus a real loaded image. Upper argument bits are unconstrained; absent
DF/MMX-mode fields are not supplied or claimed. Compiler correctness is separate. -/
@[expose] public section
namespace Silmaril.Machine.SystemV.Abi.Int32Identity
open Silmaril Silmaril.X86
open Silmaril.X86.Decompile.SemLift

/-- Extracted from GCC13.3.0, Ubuntu13.3.0-6ubuntu2~24.04.1, with explicit
O2/no unwind/stack protector/CET options; see the source/tool receipt. -/
def code : List Byte := [0x89, 0xf8, 0xc3]

def registers : List Reg := [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi,
  .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

def summary : Summary where
  outs := registers.map fun r =>
    (r, if r = .rax then .ext .d (.reg .rdi) else .reg r)
  stores := []
  reads := []
  len := 2
  flags := .unknown

def signature : Silmaril.C.Api.Signature := ⟨[.int32], some .int32⟩
def arguments (value : BitVec 32) : Silmaril.C.Api.Arguments signature.arguments :=
  .cons value .nil

def call (base exit : Word) (initial : Silmaril.X86.Features.MState) : Silmaril.C.Api.SysV.Call :=
  ⟨base, exit, initial.toBase⟩

structure Entry (value : BitVec 32) (base exit : Word) (initial : Silmaril.X86.Features.MState) : Prop where
  caller : Silmaril.C.Api.SysV.Entry signature (arguments value) (call base exit initial)
  loaded : Ext.Loaded initial.memory base code

structure Result (value : BitVec 32) (base exit : Word)
    (initial final : Silmaril.X86.Features.MState) : Prop where
  returned : Silmaril.C.Api.SysV.Return (call base exit initial) final.toBase
  valueAt : Silmaril.C.Api.SysV.ResultAt final.toBase (some .int32) value
  normalized : final.state.core.read .rax = value.setWidth 64
  registers : ∀ r, r ≠ .rax → r ≠ .rsp → final.state.core.read r = initial.state.core.read r
  fsBase : final.state.core.fsBase = initial.state.core.fsBase
  flags : final.state.core.flags = initial.state.core.flags
  vectors : final.state.zmm = initial.state.zmm
  masks : final.state.k = initial.state.k
  mxcsr : final.state.mxcsr = initial.state.mxcsr
  x87 : final.state.x87 = initial.state.x87
  frame : initial.memory.WritesWithin final.memory (fun _ => False)

def intObject : Object := Object.integer 4

def callPlan : CallPlan where
  arguments := [⟨intObject, [⟨0, 4, .gp .rdi⟩], none⟩]
  result := .direct [⟨0, 4, .gp .rax⟩]
  stackSize := 0
  stackAlign := 16
  gpUsed := 1
  vectorUsed := 0
  variadicAL := none

def intType : Silmaril.Cerberus.Ctype := .mk [] (.basic (.integer (.signed .int)))

end Silmaril.Machine.SystemV.Abi.Int32Identity
