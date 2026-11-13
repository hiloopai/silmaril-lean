module

public import Silmaril.Wasm.Unified.Versions.Named.Thms

/-!
# A Core 3.0 program outside every version's own syntax

`selAny` is the typed `select` at the 3.0 reference type `anyref` (nullable `any`, a GC heap
type). Its opcode is `select`, which every version has (untyped `select` is 1.0), so its
encoding is code of every version signature (`selCode S h`), but no own instruction of 1.0,
Lime1 or 2.0 translates to it: 1.0 and Lime1 have only untyped `select`, 2.0 types `select` with
2.0 value types only. `Silmaril.Wasm.Unified.Versions.OwnNeq.Thms` uses it to refute the converse
of the own-model refinements.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions.Own

open Silmaril.Wasm Silmaril.Wasm.Unified Silmaril.Wasm.Unified.Core30

/-- The 3.0 value type `anyref`. -/
def anyRef : ValType := .ref ⟨true, .abstract .any⟩

/-- `select (result anyref)`. -/
def selAny : Instr := .select (some [anyRef])

/-- The code of `selAny` in the signature of `S`, given that `S` has the `select` opcode. -/
def selCode (S : Silmaril.Wasm.Models.FeatureSet) (h : head (.select none) ∈ (nsig S).ops) :
    (nsig S).Code :=
  [.op ⟨head (.select none), h⟩ (immsOf selAny) [] []]

end Silmaril.Wasm.Unified.Versions.Own
