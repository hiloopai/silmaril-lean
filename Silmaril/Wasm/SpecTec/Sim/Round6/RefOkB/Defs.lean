module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.RefOk.Defs

/-!
# SpecTec ↔ Core 3.0, round 6, track refokbb: definitions

Track reading's leaf `Round6.Reading.RefOkBB` asks SpecTec's `Ref_ok`, read by `DDerivesB`, to
be Core's `RefOk` on typed stores and **bounded** reference types. It is false for every `B`
(`Round6.RefOkB.not_refOkBB`): at round 5's nested type `REF NULL D_out`, SpecTec's
`Deftype_ok` (which checks a group under `{RECS st*} ⊕ C`, appending to `C.RECS`) accepts an
inner `REC 1` that Core's `TyOk.defn` (which replaces `RECS`, `TypeCtx.withRecs`) rejects. So
SpecTec types `null` at a type at which Core does not.

The witness is not Core-valid (`Round5.RefOk.not_tyOk_nested`), so it says nothing about
configurations of valid programs, whose cast types are valid. The restatement is `RefOkBV`:
`RefOkBB` restricted to Core-valid stores and Core-valid closed types, `Round5.RefOk.RefOkBV`
over `DDerivesB`. It is **open** (neither proved nor refuted here).

See `docs/projects/spectec/README.md`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

/-- **`RefOkBB` restricted to Core-valid stores and Core-valid closed types**
(`Round5.RefOk.RefOkBV` under `DDerivesB`): on a store that is valid in Core (`StoreOk`) and has
a typed image, and a bounded reference type valid in `{}` (`TyOk {}`), SpecTec's `Ref_ok` under
`DDerivesB` is Core's `RefOk`. Open. -/
structure RefOkBV (env : Env) : Prop where
  /-- On a Core-valid, typed store and a Core-valid, closed, bounded reference type. -/
  refOk : ∀ {H : Type} (hn : H → String) (s : Store H) (rt : CRefType),
    TypedV env storeT (storeV hn s) → StoreOk s → Round4.tyBnd rt = true → TyOk {} rt →
      Reading.RefOkAtB env hn s rt

end Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB
