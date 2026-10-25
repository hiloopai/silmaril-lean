module

public import Silmaril.Wasm.Binaryen.GrowOOMRuntime

@[expose] public section

/-! Candidate fatal-OOM guards for arbitrary literal growth amounts.

The existing zero-delta implementation and optimizer remain unchanged. This
additive candidate stores the actual grow result in a fresh local, compares its
failure sentinel, returns that same result on success and traps on failure.
Actual admission and arbitrary-memory shared-store session certificates are
separate in GrowOOMLiteralMode; byte-runner composition is in TrapGrowCleanupSound.
-/

namespace Silmaril.Wasm.Binaryen.GrowOOMLiteral

def func (a : AddrType) (n : BitVec a.intType.width) : Func :=
  ⟨⟨0⟩, [.num (.int a.intType)],
    [.intConst a.intType n, .memoryGrow ⟨0⟩, .localTee ⟨0⟩,
      .intConst a.intType (BitVec.allOnes _), .intRelOp a.intType .eq,
      .if_ (.value (.num (.int a.intType))) [.unreachable] [.localGet ⟨0⟩]]⟩

def mod (a : AddrType) (n : BitVec a.intType.width) : Module :=
  { GrowWrapper.mod a n false with funcs := [func a n] }

/-- A separate candidate, preserving the established zero-wrapper byte output. -/
def optimize (m : BModule) : BModule :=
  match GrowOOM.recognize? m.lower with
  | some a => BModule.lift (GrowOOM.mod a)
  | none =>
    match GrowWrapper.recognize? m.lower with
    | some p => BModule.lift (mod p.address p.delta)
    | none => m

end Silmaril.Wasm.Binaryen.GrowOOMLiteral
