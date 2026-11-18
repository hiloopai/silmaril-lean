module

public import Silmaril.Machine.Vex.CFG.Rows.Defs
public import Silmaril.Machine.Vex.CFG.CallEdges.Thms

public section

namespace Silmaril.Machine.Vex.ControlFlow

open Silmaril.Semantics.Region.Tree (FlatCFG)

variable {Label Function : Type*} {context : Partition Label Function × Function}
variable {flat : FlatCFG Label} {entry block : Label} {support : Set Label} {exits : Set (Edge Label)}

theorem callReg_embed :
    (callFilling Label Function).Reg (CallCFG.embed flat) context support entry exits ↔
      (flatFilling Label Function).Reg flat context support entry exits := by
  simp [callFilling, flatFilling, graphFilling, GraphRow]

theorem callBB_embed :
    (callFilling Label Function).BB (CallCFG.embed flat) context block entry exits ↔
      (flatFilling Label Function).BB flat context block entry exits := by
  simp [callFilling, flatFilling, graphFilling, GraphRow]

theorem commonReg_iff {graph : CallCFG Label} (wf : CallCFG.WellFormed context.1 context.2 graph)
    (noExternal : ¬ graph.HasExternalCall context.1) :
    (∃ plain, FlatWellFormed context.1 context.2 plain ∧ CallCFG.embed plain = graph ∧
      (flatFilling Label Function).Reg plain context support entry exits) ↔
    ¬ graph.HasInternalCall context.1 ∧ (callFilling Label Function).Reg graph context support entry exits :=
  CallCFG.commonRow_iff
    (FlatRow := fun plain => (flatFilling Label Function).Reg plain context support entry exits)
    (CallRow := fun called => (callFilling Label Function).Reg called context support entry exits)
    (fun _ => callReg_embed) wf noExternal

theorem commonBB_iff {graph : CallCFG Label} (wf : CallCFG.WellFormed context.1 context.2 graph)
    (noExternal : ¬ graph.HasExternalCall context.1) :
    (∃ plain, FlatWellFormed context.1 context.2 plain ∧ CallCFG.embed plain = graph ∧
      (flatFilling Label Function).BB plain context block entry exits) ↔
    ¬ graph.HasInternalCall context.1 ∧ (callFilling Label Function).BB graph context block entry exits :=
  CallCFG.commonRow_iff
    (FlatRow := fun plain => (flatFilling Label Function).BB plain context block entry exits)
    (CallRow := fun called => (callFilling Label Function).BB called context block entry exits)
    (fun _ => callBB_embed) wf noExternal

end Silmaril.Machine.Vex.ControlFlow
