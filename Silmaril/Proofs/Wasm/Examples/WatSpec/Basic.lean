module

public import Silmaril.Wasm.Examples.WatSpec.Defs
public import Silmaril.Wasm.WatSpec.Thms
public import Silmaril.Wasm.Examples.Wat.Thms

/-!
# Annotated WAT examples: the verification conditions

`addS_vc`, `squareS_vc`, `maxS_vc`, `countdownS_vc` are closed by `wat_vc` alone; `absS_vc`
needs the value of `(-x).toInt` (`BitVec.toInt_neg_of_ne_intMin`), `sumS_vc` the arithmetic of
one iteration (`Silmaril.Wasm.Examples.Wat.triangle_step`). `addS_export`: every run of `$invoke`
of the instantiated `add` returns `x + y` or can still step.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.WatSpec

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Game Silmaril.Wasm.WatSpec
open Silmaril.Wasm.Examples.Wat (triangle triangle_step tyII_I)

theorem addS_vc : addS.vc := by wat_vc [addS]

theorem squareS_vc : squareS.vc := by wat_vc [squareS]

theorem maxS_vc : maxS.vc := by wat_vc [maxS]

theorem countdownS_vc : countdownS.vc := by wat_vc [countdownS]

theorem absS_vc : absS.vc := by
  wat_vc [absS]
  · rw [BitVec.toInt_neg_of_ne_intMin ‹_›, abs_of_neg ‹_›]
  · rw [abs_of_nonneg ‹_›]

theorem sumS_vc : sumS.vc := by
  wat_vc [sumS, triangle]
  exact ⟨triangle_step _ _ ‹_› ‹_›, by bv_omega⟩

/-- The function of the instantiated `add`. -/
theorem addStore_funcs : ∃ fi : FuncInst Nat, addStore.funcs = [fi] ∧ fi.code = .wasm addS.func ∧
    FnType.ofDefType? fi.type = some tyII_I := by
  have hlen : addStore.funcs.length = 1 := rfl
  obtain ⟨fi, hf⟩ := List.length_eq_one_iff.mp hlen
  have hc : addStore.funcs.map FuncInst.code = [.wasm addS.func] := rfl
  have ht : addStore.funcs.map (fun fi => FnType.ofDefType? fi.type) = [some tyII_I] := by
    decide +kernel
  rw [hf] at hc ht
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hc ht
  exact ⟨fi, hf, hc, ht⟩

variable {P : Profile} {host : HostSemantics Nat}

/-- **The instantiated annotated `add`**: every run of `$invoke` on `x, y` can still step or
has returned `x + y` with the store unchanged; every profile, every host relation. -/
theorem addS_export (x y : BitVec 32) {c' : Config Nat}
    (hs : Steps P host (invoke addStore 0 [.i32 x, .i32 y]) c') :
    (∃ c'', Step P host c' c'') ∨ c' = ⟨addStore, {}, vals [.i32 (x + y)]⟩ := by
  obtain ⟨fi, hf, hc, ht⟩ := addStore_funcs
  have hv : Silmaril.Wasm.Logic.Hoare.FSpecValid P host 0 (addS.spec fi 0) :=
    addS.sound addS_vc hc (FnType.expand_of_ofDefType? ht) rfl rfl
  rcases Annotated.invoke hv (by rw [hf]; rfl) ⟨x, y, rfl, trivial⟩ hs with h | ⟨res, hpost, hc'⟩
  · exact .inl h
  · obtain ⟨r, hr, hrx⟩ := hpost x y rfl
    right
    rw [hc', hr, hrx]

end Silmaril.Wasm.Examples.WatSpec
