module

public import Silmaril.Raw.Wasm.Auto2.VCEquiv.Conds
public import Silmaril.Raw.Wasm.Auto2.VCEquiv.Mod

/-!
# Equivalence through a shared contract: the library (unrefined)

The proved contracts of the two new `sum` programs (`sumO3Entry`, `sumDoWhileEntry`) and the
functional contracts `sumFun` (three program shapes: `Silmaril.WasmSpec.SumTo`'s `block`/`loop`/
`br_if`, Binaryen's `loop`/`if`/`br`, and the guarded `do … while`), `maxFun`, `addFun`,
`div10Fun` (one shape each), collected in `eqFuns`, which `wasm-check` searches.

New definitions and proofs (unrefined).
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCEquiv

open Silmaril.Wasm Silmaril.Wasm.Execution
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Auto2.VCBridge
open Silmaril.Wasm.Auto2.VCLib
open Silmaril.Wasm.Auto.FrontBench (sumRef maxRef addRef div10RefFn)

/-- `sum n = triBV n` (total), proved on Binaryen's `-O3` of `$sum`. -/
def sumO3Entry : VcEntry where
  name := "sum-O3"
  F := sumFns
  S := sumSpec
  fuel := libFuel
  conds := genFunc sumSpec sumO3Func libFuel
  valid := sumO3_vcs
  total := rfl
  calls := rfl
  mem := rfl

/-- `sum n = triBV n` (total), proved on the `do … while` form of `$sum`. -/
def sumDoWhileEntry : VcEntry where
  name := "sum-dowhile"
  F := sumFns
  S := sumDoWhileSpec
  fuel := libFuel
  conds := genFunc sumDoWhileSpec sumDoWhileFunc libFuel
  valid := sumDoWhile_vcs
  total := rfl
  calls := rfl
  mem := rfl

/-- **The triangular numbers**, three program shapes. -/
def sumFun : EqFun where
  name := "sum"
  f := sumRef
  es := [sumEntry, sumO3Entry, sumDoWhileEntry]
  pre := by
    intro e he ρ _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> trivial
  ref := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact sum_ref
    · exact sum_ref
    · exact sum_ref
  tot := by
    intro e he vs htv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;>
    · obtain ⟨x, rfl⟩ := typed1_32 htv
      exact ⟨_, rfl⟩

/-- The signed maximum. -/
def maxFun : EqFun where
  name := "max"
  f := maxRef
  es := [maxEntry]
  pre := by
    intro e he ρ _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    trivial
  ref := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    exact max_ref
  tot := by
    intro e he vs htv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    obtain ⟨x, y, rfl⟩ := typed2_32 htv
    exact ⟨_, rfl⟩

/-- `x + y`. -/
def addFun : EqFun where
  name := "add"
  f := addRef
  es := [addEntry]
  pre := by
    intro e he ρ _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    trivial
  ref := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    exact add_ref
  tot := by
    intro e he vs htv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    obtain ⟨x, y, rfl⟩ := typed2_32 htv
    exact ⟨_, rfl⟩

/-- `x / 10` on `i64`. -/
def div10Fun : EqFun where
  name := "div10"
  f := div10RefFn
  es := [div10Entry]
  pre := by
    intro e he ρ _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    trivial
  ref := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    exact div10_ref
  tot := by
    intro e he vs htv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    obtain ⟨x, rfl⟩ := typed1_64 htv
    exact ⟨_, rfl⟩

/-- **The library of functional contracts** (`wasm-check`'s stage `vcequiv`). -/
def eqFuns : List EqFun := [sumFun, maxFun, addFun, div10Fun]

end Silmaril.Wasm.Auto2.VCEquiv
