module

public import Silmaril.Wasm.Binaryen.Exe.Fold

@[expose] public section

/-! Runtime-only growth-wrapper recognition and refinement rewrite.

The original declarations retain their names and behavior. Their module/session
proofs and pass certificates remain in GrowWrapper and GrowWrapperPass.
-/

namespace Silmaril.Wasm.Binaryen.GrowWrapper

def recType (a : AddrType) : RecType :=
  ⟨[⟨true, [], .func ⟨[], [.num (.int a.intType)]⟩⟩]⟩

def func (a : AddrType) (n : BitVec a.intType.width) (failure : Bool) : Func :=
  ⟨⟨0⟩, [], if failure then [.intConst a.intType (BitVec.allOnes _)]
    else [.intConst a.intType n, .memoryGrow ⟨0⟩]⟩

def mod (a : AddrType) (n : BitVec a.intType.width) (failure : Bool) : Module :=
  { types := [recType a], funcs := [func a n failure],
    memories := [⟨a, ⟨0, none⟩⟩],
    exports := [⟨"grow", .func ⟨0⟩⟩, ⟨"memory", .memory ⟨0⟩⟩] }

structure Params where
  address : AddrType
  delta : BitVec address.intType.width

def metadataOk (a : AddrType) (types : List RecType) (mems : List MemoryType)
    (exports : List Export) : Prop :=
  types = [recType a] ∧ mems = [⟨a, ⟨0, none⟩⟩] ∧
    exports = [⟨"grow", .func ⟨0⟩⟩, ⟨"memory", .memory ⟨0⟩⟩]

instance (a : AddrType) (types : List RecType) (mems : List MemoryType)
    (exports : List Export) : Decidable (metadataOk a types mems exports) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- All unrecognized modules are rejected; there is no syntactic equality axiom
or unchecked comparison on arbitrary instruction bodies. -/
def recognize? : Module → Option Params
  | ⟨types, [], [], [], mems, [],
      [⟨⟨0⟩, [], [.intConst .i32 n, .memoryGrow ⟨0⟩]⟩], [], [], none, exports⟩ =>
      if metadataOk .i32 types mems exports then some ⟨.i32, n⟩ else none
  | ⟨types, [], [], [], mems, [],
      [⟨⟨0⟩, [], [.intConst .i64 n, .memoryGrow ⟨0⟩]⟩], [], [], none, exports⟩ =>
      if metadataOk .i64 types mems exports then some ⟨.i64, n⟩ else none
  | _ => none

/-- Select the failure wrapper when recognized; otherwise keep the input. -/
def optimize (m : BModule) : BModule :=
  match recognize? m.lower with
  | some p => BModule.lift (mod p.address p.delta true)
  | none => m

end Silmaril.Wasm.Binaryen.GrowWrapper
