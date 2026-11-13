module

public import Silmaril.Machine.X86.Decompile.Lea32.Defs
public import Silmaril.Machine.X86.Decompile.Returns.Defs
public import Silmaril.Machine.SystemV.Abi.Ctypes.Defs
public import Silmaril.Machine.C.Api.SysV.Defs
public import Silmaril.Cerberus.Core.Dynamics.Defs

/-! Real GCC13.3/Clang18.1 bytes for two-int addition. Machine addition wraps
modulo32; correspondence to signed Core addition requires independent sum bounds.
No compiler-emission correctness or full missing-state FFI contract is claimed. -/
@[expose] public section
namespace Silmaril.Machine.SystemV.Abi.Int32Add
open Silmaril Silmaril.X86
open Silmaril.X86.Decompile.SemLift

def code : List Byte := [0x8d, 0x04, 0x37, 0xc3]

def address : Ext.Mem := Ext.Mem.ofReg .rdi (some ⟨.rsi, 0, by decide⟩) 0

def registers : List Reg := [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi,
  .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

def expression : Ex := .alu .d .add (.reg .rdi) (.reg .rsi)

def summary : Summary where
  outs := registers.map fun r => (r, if r = .rax then expression else .reg r)
  stores := []
  reads := []
  len := 3
  flags := .unknown

def signature : Silmaril.C.Api.Signature := ⟨[.int32, .int32], some .int32⟩
def arguments (a b : BitVec 32) : Silmaril.C.Api.Arguments signature.arguments :=
  .cons a (.cons b .nil)

def call (base exit : Word) (initial : Silmaril.X86.Features.MState) : Silmaril.C.Api.SysV.Call :=
  ⟨base, exit, initial.toBase⟩

structure Entry (a b : BitVec 32) (base exit : Word) (initial : Silmaril.X86.Features.MState) : Prop where
  caller : Silmaril.C.Api.SysV.Entry signature (arguments a b) (call base exit initial)
  loaded : Ext.Loaded initial.memory base code

structure Result (a b : BitVec 32) (base exit : Word)
    (initial final : Silmaril.X86.Features.MState) : Prop where
  returned : Silmaril.C.Api.SysV.Return (call base exit initial) final.toBase
  valueAt : Silmaril.C.Api.SysV.ResultAt final.toBase (some .int32) (a + b)
  normalized : final.state.core.read .rax = (a + b).setWidth 64
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
  arguments := [⟨intObject, [⟨0, 4, .gp .rdi⟩], none⟩,
    ⟨intObject, [⟨0, 4, .gp .rsi⟩], none⟩]
  result := .direct [⟨0, 4, .gp .rax⟩]
  stackSize := 0
  stackAlign := 16
  gpUsed := 2
  vectorUsed := 0
  variadicAL := none

def intType : Silmaril.Cerberus.Ctype := .mk [] (.basic (.integer (.signed .int)))

/-- Independent signed-C sum bounds, with no machine execution/result in them. -/
def DefinedSum (a b : BitVec 32) : Prop :=
  -2147483648 ≤ a.toInt + b.toInt ∧ a.toInt + b.toInt ≤ 2147483647

/-- The actual Core signed-int exceptional-condition primitive has the same
integer result as the returned low32 word. This is not a whole-function proof. -/
def CoreResult (a b : BitVec 32) (final : Silmaril.X86.Features.MState) : Prop :=
  Silmaril.Cerberus.Core.Dynamics.primitive (.catchInt (.signed .int) .add)
    [Silmaril.Cerberus.Core.Dynamics.integer a.toInt,
      Silmaril.Cerberus.Core.Dynamics.integer b.toInt] =
    .ok (Silmaril.Cerberus.Core.Dynamics.integer ((final.state.core.read .rax).setWidth 32).toInt)

end Silmaril.Machine.SystemV.Abi.Int32Add
