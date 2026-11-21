module

public import Silmaril.X86.Concurrency.Bridge.Defs

/-!
# Gap 1 as first stated is false: the counterexample

`not_tsoRunCirAsStated` (header `Silmaril.X86.Concurrency.Bridge.Thms`): a
validated test with no threads whose condition reads the first data byte, which no location
initialises. A test memory may hold `5` there, so the condition holds of the machine's final
state; every CIR behaviour of the (empty) program leaves the byte undefined, so it holds of
none. `Task.tsoRunCir` now assumes `CondInit`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge

open Silmaril.Process (Memory)
open Silmaril.X86.MemoryModel.Litmus (Test Final Atom Cond)
open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Tv (TvTest)
open Silmaril.X86.Concurrency.Bridge

/-- A test with no threads whose condition reads the first data byte, which no location
initialises. -/
def cexTest : Test where
  name := "cex"
  source := ""
  doc := ""
  locs := []
  threads := []
  quant := .exists_
  cond := .atom (.mem Silmaril.X86.Litmus.dataBase 1 5)
  coverage := .tso
  tso := none
  xl := .allowed
  sc := none
  basis := ""

/-- The validated test: no certificates. -/
def cex : TvTest := ⟨cexTest, []⟩

/-- A test memory whose data page holds `5` everywhere. -/
def cexMem : Memory :=
  ⟨Silmaril.X86.Litmus.testRegions 0,
    Memory.install ∅ Silmaril.X86.Litmus.dataBase (List.replicate 4096 5)⟩

theorem cexMem_backed : Backed cexMem := by
  intro a ha
  have hreg : cexMem.regions = Silmaril.X86.Litmus.testRegions 0 := rfl
  have hr : 0x10000 ≤ a ∧ a < 0x10000 + 4096 := by
    simp only [Memory.permits, hreg] at ha
    simp [Silmaril.X86.Litmus.testRegions, Silmaril.Process.Region.Contains,
      Silmaril.X86.Litmus.dataBase, Silmaril.X86.Litmus.dataSize,
      Silmaril.Process.Permissions.allows] at ha
    rcases ha with ha | ha
    · have := of_decide_eq_true ha; omega
    · omega
  have := Memory.install_get ∅ 0x10000 (List.replicate 4096 5) (a - 0x10000)
    (by rw [List.length_replicate]; omega)
  rw [show 0x10000 + (a - 0x10000) = a by omega] at this
  show ((Memory.install ∅ 0x10000 (List.replicate 4096 5)).get? a).isSome = true
  rw [this]
  rfl

theorem cex_tvOk : cex.tvOk = true := by decide

theorem cex_cellsOk : CellsOk cex.test := by
  intro D T hT trs hF
  simp [cex, cexTest, Test.extractOver] at hT
  subst hT
  cases hF
  intro i es h
  simp at h

theorem cex_final : TsoFinal cex.test (poolFinal (testPool cex.test cexMem)) := by
  refine ⟨cexMem, testPool cex.test cexMem, ⟨rfl, ?_, ?_, cexMem_backed⟩, .refl, fun _ => rfl,
    ?_, rfl⟩
  · intro k th h; simp [cex, cexTest] at h
  · intro a b h; simp [cex, cexTest, Test.initMem, Silmaril.X86.MemoryModel.Litmus.initByte] at h
  · intro k s h; simp [testPool, cex, cexTest] at h

theorem cexMem_get : cexMem.bytes.get? Silmaril.X86.Litmus.dataBase = some 5 := by
  have := Memory.install_get ∅ 0x10000 (List.replicate 4096 5) 0
    (by rw [List.length_replicate]; omega)
  show (Memory.install ∅ 0x10000 (List.replicate 4096 5)).get? 0x10000 = some 5
  rw [this]
  rfl

/-- The original gap-1 statement fails on `cex`. -/
theorem not_tsoRunCirAsStated : ¬ tsoRunCirAsStated := by
  intro hT
  obtain ⟨f', ⟨dom, hB⟩, heq⟩ := hT cex cex_tvOk cex_cellsOk _ cex_final
  have hw : cex.test.witness.eval (poolFinal (testPool cex.test cexMem)) = true := by
    simp only [Test.witness, cex, cexTest, Cond.eval, Atom.eval, poolFinal,
      Silmaril.X86.MemoryModel.Litmus.leValue, testPool]
    rw [cexMem_get]
    rfl
  have hw' : cex.test.witness.eval f' = false := by
    obtain ⟨trs, hF, x, hev, -, -, -, -, rfl⟩ := hB
    have htr : trs = [] := by
      simp only [TvTest.prog, Prog.traces, cex, List.map_nil, List.mapIdx_nil] at hF
      cases hF; rfl
    subst htr
    simp [Test.witness, cex, cexTest, Cond.eval, Atom.eval, Silmaril.X86.MemoryModel.Litmus.finalAx,
      Silmaril.X86.MemoryModel.Litmus.finalOf, Silmaril.X86.MemoryModel.Litmus.writtenByte, hev,
      Silmaril.X86.MemoryModel.Litmus.units, Silmaril.X86.MemoryModel.Litmus.accUnits,
      Silmaril.X86.MemoryModel.Litmus.leValue, Prog.memTest, Test.initMem,
      Silmaril.X86.MemoryModel.Litmus.initByte, TvTest.prog]
  rw [heq, hw] at hw'
  cases hw'

end Silmaril.Proofs.X86.Concurrency.Bridge
