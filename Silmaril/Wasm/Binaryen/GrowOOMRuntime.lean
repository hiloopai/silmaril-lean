module

public import Silmaril.Wasm.Binaryen.GrowWrapperRuntime

@[expose] public section

/-! Runtime candidate for a fatal-OOM policy on zero-delta growth wrappers.

The full source module is recognized, including its memory and exports. The
actual `memory.grow 0` is retained: successful growth returns zero, and its
failure sentinel takes an inserted `unreachable`. Other deltas and all other
module shapes retain identity fallback. Semantic certificates are separate.
-/

namespace Silmaril.Wasm.Binaryen.GrowOOM

def func (a : AddrType) : Func :=
  ⟨⟨0⟩, [], [.intConst a.intType 0, .memoryGrow ⟨0⟩, .intTestOp a.intType .eqz,
    .if_ (.value (.num (.int a.intType))) [.intConst a.intType 0] [.unreachable]]⟩

def mod (a : AddrType) : Module :=
  { GrowWrapper.mod a 0 false with funcs := [func a] }

/-- Recognize only the zero-delta member of the complete growth-wrapper family.
The dependent delta is compared at its actual memory address width. -/
def recognize? (m : Module) : Option AddrType := do
  let p ← GrowWrapper.recognize? m
  if p.delta = 0 then some p.address else none

/-- An additive insertion-only candidate; unsupported modules are unchanged. -/
def optimize (m : BModule) : BModule :=
  match recognize? m.lower with
  | some a => BModule.lift (mod a)
  | none => m

end Silmaril.Wasm.Binaryen.GrowOOM
