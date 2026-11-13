module

public import Silmaril.Wasm.Validation.Subtyping.CheckRecs
public import Silmaril.Wasm.Validation.Check.TyOkComplete

/-!
# `Sub.checkR`: the `REC`-aware subtyping checker with the `TyOk.check` oracle

silmaril-lean's `Sub.checkRWith okD` decides subtyping in a context with `RECS`, given an
oracle `okD` for the validity of `_DEF` supertypes of the `RECS` entries. `Sub.checkR` takes
the core type checker `TyOk.check` as the oracle. The theorems are in
`Silmaril.Wasm.Validation.SubCheckR.Thms`.

Ported from an earlier development `Silmaril/Wasm/Validation/Subtyping/CheckRecsTyOk.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.Validation

open Silmaril.Wasm.Validation

/-- The `REC`-aware subtyping checker, with `TyOk.check` deciding the `_DEF` supertypes. -/
def Sub.checkR (Δ : TypeCtx) {k : TKind} (a b : Ty k) : Bool :=
  Sub.checkRWith (fun d => TyOk.check Δ d) Δ a b

end Silmaril.Wasm.Validation
