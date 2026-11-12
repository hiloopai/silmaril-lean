module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.ElseExp.Pairs
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.ElseExp.Inner

/-!
# Round 9, RE: the pairs left are the four `Ref_ok` pairs (unrefined)

`elseBwdBLeft3_of_ref`: `ElseBwdBLeft3` (5 pairs) from `ElseBwdBRef` (the 4 `Ref_ok` pairs),
since `(21, 9)` holds vacuously (`pairReflectB_inner`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp

open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd

variable {B : Silmaril.SpecTec.Sem.Builtins}

/-- **`ElseBwdBLeft3` from the 4 `Ref_ok` pairs.** -/
theorem elseBwdBLeft3_of_ref (hR : ElseBwdBRef (utf8Env B)) : ElseBwdBLeft3 (utf8Env B) := by
  intro p hp
  by_cases h : p ∈ innerPairs
  · exact pairReflectB_inner h
  · exact hR p (by revert hp h; revert p; decide)

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseExp
