module

public import Silmaril.Wasm.SpecTec.Sim.State.Defs

/-!
# SpecTec ↔ Core 3.0, track memory: definitions

The memory track extends family M (`Sim.State`) with the table and memory rules it left open
(`docs/projects/spectec/README.md`, gap 6 and obstruction 2). Declarations live in the namespace
`Silmaril.Wasm.SpecTec.Sim.Memory`.

`MemTyping` collects the typing facts about encoded store components that the rules'
quantifiers need beyond `State.StateTyping`: the components of a table's or memory's type in a
typed state. Like `StateTyping`, they are facts about the encoding (family E's subject); the
per-rule theorems take them as hypotheses.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Memory

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

/-- The IL type `limits`. -/
abbrev limitsT : Typ := .varT "limits" []
/-- The IL type `reftype`. -/
abbrev reftypeT : Typ := .varT "reftype" []

/-- **Typing of store components and memory immediates** (for family E). In a typed state, the
limits and element type of every table, and the limits of every memory, are typed at the IL types
the `table.size` and `memory.size` rules quantify them at; number types, memory arguments,
signedness flags and integer constants are typed at the types the load and store rules quantify
them at. -/
structure MemTyping (env : Env) : Prop where
  /-- The limits and element type of a table of a typed state. -/
  tableType : ∀ {H : Type} (hn : H → String) (s : Store H) (f : Frame) (ti : TableInst),
    ti ∈ s.tables → TypedV env stateT (stateV hn s f) →
      TypedV env limitsT (Encode.toValue ti.type.limits) ∧
        TypedV env reftypeT (Silmaril.SpecTec.Equiv.Validation.tyV ti.type.element)
  /-- The limits of a memory of a typed state. -/
  memType : ∀ {H : Type} (hn : H → String) (s : Store H) (f : Frame) (mi : MemInst),
    mi ∈ s.mems → TypedV env stateT (stateV hn s f) →
      TypedV env limitsT (Encode.toValue mi.type.limits)
  /-- Number types. -/
  numtype : ∀ t : NumType, TypedV env (.varT "numtype" []) (Encode.toValue t)
  /-- Integer number types at `Inn`. -/
  inn : ∀ t : IntType, TypedV env (.varT "Inn" []) (Encode.toValue (NumType.int t))
  /-- Memory arguments. -/
  memarg : ∀ a : MemArg, TypedV env (.varT "memarg" []) (memargV a)
  /-- Signedness flags. -/
  sx : ∀ s : Signedness, TypedV env (.varT "sx" []) (sxV s)
  /-- An integer constant, in a scope binding the number-type variable `y` to its type, has type
  `num_(y)`. -/
  numInt : ∀ (y : IL.Id) (t : IntType) (b : BitVec t.width) (ρ : VarEnv), ValsOnly ρ →
    ρ.findVal? y = some (Encode.toValue (NumType.int t)) →
      HasTyp env ρ (.varT "num_" [.expA (.varE y)]) (State.idxV b.toNat)
  /-- The same, with `y` an `Inn` coerced to `numtype` (`num_(Inn)` in the packed rules). -/
  numInn : ∀ (y : IL.Id) (t : IntType) (b : BitVec t.width) (ρ : VarEnv), ValsOnly ρ →
    ρ.findVal? y = some (Encode.toValue (NumType.int t)) →
      HasTyp env ρ (.varT "num_" [.expA (.subE (.varE y) (.varT "Inn" []) (.varT "numtype" []))])
        (State.idxV b.toNat)

end Silmaril.Wasm.SpecTec.Sim.Memory
