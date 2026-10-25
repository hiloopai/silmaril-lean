module

public import Silmaril.Wasm.Binaryen.GrowOOMRuntime

@[expose] public section

/-! Select successful zero-growth execution of the exact fatal-OOM wrapper.

The empty memory and both exports are retained. The runtime candidate has
identity fallback on every other complete module, including deterministic traps.
Its refinement certificate explicitly requires that zero growth may succeed.
-/

namespace Silmaril.Wasm.Binaryen.GrowZeroSuccess

def func (a : AddrType) : Func :=
  ⟨⟨0⟩, [], [.intConst a.intType 0]⟩

def mod (a : AddrType) : Module :=
  { GrowOOM.mod a with funcs := [func a] }

/-- Recognize the entire guarded zero-growth module, not an arbitrary trapping
body or a wrapper whose memory/import/export context differs. -/
def recognize? : Module → Option AddrType
  | ⟨types, [], [], [], [⟨a, limits⟩], [], [⟨⟨0⟩, [], body⟩], [], [], none, exports⟩ =>
      if GrowWrapper.metadataOk a types [⟨a, limits⟩] exports ∧
          Exe.instrsEqb body (GrowOOM.func a).body = true then some a else none
  | _ => none

/-- Select the optional nontrapping outcome, retaining identity elsewhere. -/
def optimize (m : BModule) : BModule :=
  match recognize? m.lower with
  | some a => BModule.lift (mod a)
  | none => m

end Silmaril.Wasm.Binaryen.GrowZeroSuccess
