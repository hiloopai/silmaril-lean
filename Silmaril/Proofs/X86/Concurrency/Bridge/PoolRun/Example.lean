module

public import Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.Ax
public import Silmaril.X86.MemoryModel.OpAx.Thms
import Silmaril.X86.MemoryModel.Litmus.Models.Thms

/-!
# Non-vacuity of the bridge: store buffering

The traces of SB (`x := 1; r0 := y ∥ y := 1; r1 := x`, both loads returning `0`)
turn, by `traceX`, into the program `OpAx.sbP`. `OpAx` explains its store-buffer run, whose
weak outcome no SC candidate explains (`OpAx.sb_weak_not_sc`), by a TSO candidate with paired
`rmw`s (`OpAx.sb_weak_explained`). The hypotheses of `axReach_of_explains` hold for these
traces and a test with `x` and `y` initially `0`, so the weak outcome is an x86-TSO `AxReach`
final state of that test: `sb_axReach`.

The target stays weak: the same traces have no SC `AxReach` final state at all
(`sb_not_axReach_sc`, by the litmus exact enumerator `axJudge_spec`: the only well-formed candidate
of these traces is TSO- but not SC-consistent).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.Example

open Silmaril.X86 (State)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.MemoryModel.Litmus (XAct XTrace Test traceX AxReach finalOf Byte)
open Silmaril.X86.Concurrency.Bridge.PoolRun

/-- A one-byte action. -/
def act1 (k : MemEvent.Kind) (a : Nat) (rd wr : List Byte) : XAct := ⟨⟨k, a, 1, false⟩, .plain, rd, wr⟩

/-- Some core (the registers play no part here). -/
def core0 : State := Silmaril.X86.Litmus.initCore 0 []

/-- Thread 0 of SB: store `1` to `x` (address 0), load `0` from `y` (address 1). -/
def sbTr0 : XTrace :=
  ⟨[⟨[act1 .store 0 [] [1]], core0⟩, ⟨[act1 .load 1 [0] []], core0⟩], core0⟩

/-- Thread 1 of SB: store `1` to `y`, load `0` from `x`. -/
def sbTr1 : XTrace :=
  ⟨[⟨[act1 .store 1 [] [1]], core0⟩, ⟨[act1 .load 0 [0] []], core0⟩], core0⟩

/-- The traces. -/
def sbTrs : List XTrace := [sbTr0, sbTr1]

/-- A test with `x` at 0 and `y` at 1, one byte each, initially `0`. -/
def sbTest : Test where
  name := "SB"
  source := ""
  doc := ""
  locs := [⟨"x", 0, 1, 0⟩, ⟨"y", 1, 1, 0⟩]
  threads := []
  quant := .exists_
  cond := .tt
  coverage := .tso
  tso := none
  xl := .allowed
  sc := none
  basis := ""

theorem sbTrs_traceX : sbTrs.mapIdx traceX = Silmaril.X86.MemoryModel.OpAx.sbP := rfl

theorem sbTrs_ok : TracesOk sbTrs := by
  intro tr htr a ha
  simp only [sbTrs, List.mem_cons, List.not_mem_nil, or_false] at htr
  rcases htr with rfl | rfl <;>
    simp only [sbTr0, sbTr1, Silmaril.X86.Litmus.Trace.acts, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at ha <;>
    rcases ha with rfl | rfl <;>
    simp [ActOk, act1, MemEvent.Kind.reads, MemEvent.Kind.writes]

theorem sbTrs_noTear : NoTear sbTrs := by
  unfold NoTear
  decide

theorem sbTrs_initReads :
    InitReads sbTest Silmaril.X86.MemoryModel.Tso.Litmus.zeroMem sbTrs := by
  intro tr htr a ha hr y h1 h2
  simp only [sbTrs, List.mem_cons, List.not_mem_nil, or_false] at htr
  rcases htr with rfl | rfl <;>
    simp only [sbTr0, sbTr1, Silmaril.X86.Litmus.Trace.acts, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at ha <;>
    rcases ha with rfl | rfl <;>
    simp only [act1, MemEvent.Kind.reads, Bool.false_eq_true] at hr h1 h2
  · obtain rfl : y = 1 := by omega
    rfl
  · obtain rfl : y = 0 := by omega
    rfl

/-- **The bridge is not vacuous**: SB's weak outcome, which the store-buffer run reaches and no SC
candidate explains, is an x86-TSO `AxReach` final state of the SB test. -/
theorem sb_axReach : ∃ m, AxReach sbTest [[sbTr0], [sbTr1]]
    Silmaril.X86.MemoryModel.Axiomatic.Exec.Tso (finalOf sbTrs m) := by
  obtain ⟨-, -, s, -, x, hx, hp⟩ := Silmaril.X86.MemoryModel.OpAx.sb_weak_explained
  rw [← sbTrs_traceX] at hx
  obtain ⟨m, hm, -⟩ := axReach_of_explains (t := sbTest) (T := [[sbTr0], [sbTr1]])
    (by simp [sbTrs]) sbTrs_ok sbTrs_noTear sbTrs_initReads hx hp
  exact ⟨m, hm⟩

/-- The litmus enumerator on SB's traces: one judged candidate, TSO- and XL- but not SC-consistent.
-/
theorem sbTest_axJudge : sbTest.axJudge [[sbTr0], [sbTr1]] =
    some [{ sc := false, tso := true, xl := true, out := [] }] := by decide

/-- **The weak outcome is not SC**: the traces in which both SB loads read `0`
have no SC `AxReach` final state, so `sb_axReach` lands on a genuinely TSO-only outcome. -/
theorem sb_not_axReach_sc (f : Silmaril.X86.MemoryModel.Litmus.Final) :
    ¬ AxReach sbTest [[sbTr0], [sbTr1]] Silmaril.X86.MemoryModel.Axiomatic.Exec.Sc f := by
  intro h
  have := (Silmaril.X86.MemoryModel.Litmus.axJudge_spec sbTest_axJudge .sc (sbTest.outcome f)).2
    ⟨f, h, rfl⟩
  simp [Silmaril.X86.MemoryModel.Litmus.outsBy, Silmaril.X86.MemoryModel.Litmus.Model.sel,
    Silmaril.X86.MemoryModel.Litmus.uniq] at this

end Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.Example
