module

public import Silmaril.Wasm.Institution.Operational.Memory32Graph.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.Memory32Graph.Core
import Silmaril.Proofs.Wasm.Institution.Operational.Memory32Graph.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.Memory32Graph.Typing
import Silmaril.Proofs.Wasm.Institution.Operational.Memory32Graph.Runs

/-! Exact finite Core and Lime1 correspondence from ordinary typed direct
entry. The fixed allocation selects one shared Memory32 instance. The
current bytes travel with the active phase and are retained on trap unwind. -/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Memory32Graph

open Execution
open Execution.Runtime (Value Frame MemAddr)
open CallContinuation.OuterCall (CallTarget)
open Wasm.SingleThreaded.Det (noHost)

theorem core_step_iff {H : Type} {P : Numerics.Profile} {p : Program}
    {s : Core.Store H} {a : MemAddr} {m : Core.MemInst} (layout : CoreLayout p s a m)
    {caller : Frame} {root : CallTarget} {f : Function} (link : Root p caller root f)
    {src : State} {dst : Core.Config H} (ready : Ready p f src.phase) :
    Core.Step P noHost (coreConfig s a m caller root src) dst ↔
      ∃ out, Step p f src out ∧ dst = coreConfig s a m caller root out :=
  ⟨fun h => Proofs.Core.readback layout link.found link.same (fun _ _ => link.resolves) ready src.bytes h,
    fun ⟨_, h, eq⟩ => eq.symm ▸ Proofs.Core.sound layout link.found link.same (fun _ _ => link.resolves) ready h⟩

theorem lime_step_iff {H : Type} {p : Program}
    {s : Wasm.Lime1.Execution.Store H} {a : MemAddr} {m : Execution.Runtime.MemInst} (layout : LimeLayout p s a m)
    {caller : Frame} {root : CallTarget} {f : Function} (link : Root p caller root f)
    {src : State} {dst : Wasm.Lime1.Execution.Config H} (ready : Ready p f src.phase) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeConfig s a m caller root src) dst ↔
      ∃ out, Step p f src out ∧ dst = limeConfig s a m caller root out :=
  ⟨fun h => Proofs.Lime1.readback layout link.found link.same (fun _ _ => link.resolves) ready src.bytes h,
    fun ⟨_, h, eq⟩ => eq.symm ▸ Proofs.Lime1.sound layout link.found link.same (fun _ _ => link.resolves) ready h⟩

theorem core_run_iff {H : Type} {P : Numerics.Profile} {p : Program} (checked : p.Checked)
    {s : Core.Store H} {a : MemAddr} {m : Core.MemInst} (layout : CoreLayout p s a m)
    {caller : Frame} {root : CallTarget} {f : Function} (link : Root p caller root f)
    {src : State} {dst : Core.Config H} (ready : Ready p f src.phase) :
    Core.Steps P noHost (coreConfig s a m caller root src) dst ↔
      ∃ out, Runs p f src out ∧ Ready p f out.phase ∧ out.bytes.size = src.bytes.size ∧
        dst = coreConfig s a m caller root out :=
  Proofs.runs_iff checked link.found _ _
    (fun g h => (core_step_iff layout link g).mpr ⟨_, h, rfl⟩)
    (fun g h => (core_step_iff layout link g).mp h) ready

theorem lime_run_iff {H : Type} {p : Program} (checked : p.Checked)
    {s : Wasm.Lime1.Execution.Store H} {a : MemAddr} {m : Execution.Runtime.MemInst} (layout : LimeLayout p s a m)
    {caller : Frame} {root : CallTarget} {f : Function} (link : Root p caller root f)
    {src : State} {dst : Wasm.Lime1.Execution.Config H} (ready : Ready p f src.phase) :
    Wasm.Lime1.Execution.Steps CallFrame.limeNoHost (limeConfig s a m caller root src) dst ↔
      ∃ out, Runs p f src out ∧ Ready p f out.phase ∧ out.bytes.size = src.bytes.size ∧
        dst = limeConfig s a m caller root out :=
  Proofs.runs_iff checked link.found _ _
    (fun g h => (lime_step_iff layout link g).mpr ⟨_, h, rfl⟩)
    (fun g h => (lime_step_iff layout link g).mp h) ready

theorem preserve {p : Program} {caller : Frame} {root : CallTarget} {f : Function}
    (checked : p.Checked) (link : Root p caller root f) {src dst : State}
    (step : Step p f src dst) (ready : Ready p f src.phase) : Ready p f dst.phase :=
  Proofs.preserve checked link.found step ready

theorem step_size {p : Program} {f : Function} {src dst : State} (step : Step p f src dst) :
    dst.bytes.size = src.bytes.size :=
  Proofs.bytes_preserved step

/-- At its allocated initial extent the legacy memory update commutes with the
existing Lime1-to-Core projection, including the translated memory metadata. -/
theorem limeStore_toCore {H : Type} (s : Wasm.Lime1.Execution.Store H) (a : MemAddr)
    (m : Execution.Runtime.MemInst) {bytes : ByteArray} (size : bytes.size = m.data.size) :
    (limeStore s a m bytes).toCore = coreStore s.toCore a m.toCore bytes :=
  congrArg Core.Config.store (MemoryWrite.lime_to_core s (⟨[], {}⟩ : Frame) a m
    (q := .written bytes) size)

theorem coreStore_initial {H : Type} {p : Program} {s : Core.Store H} {a : MemAddr} {m : Core.MemInst}
    (layout : CoreLayout p s a m) : coreStore s a m m.bytes = s := by
  obtain ⟨bound, found⟩ := List.getElem?_eq_some_iff.mp layout.mem
  simp only [coreStore, Core.Store.setMem]
  rw [← found, List.set_getElem_self]

theorem limeStore_initial {H : Type} {p : Program} {s : Wasm.Lime1.Execution.Store H}
    {a : MemAddr} {m : Execution.Runtime.MemInst} (layout : LimeLayout p s a m) :
    limeStore s a m m.data = s := by
  obtain ⟨bound, found⟩ := List.getElem?_eq_some_iff.mp layout.mem
  simp only [limeStore, Wasm.Lime1.Execution.setMemory]
  rw [← found, List.set_getElem_self]

end Silmaril.Wasm.Institution.Operational.Memory32Graph
