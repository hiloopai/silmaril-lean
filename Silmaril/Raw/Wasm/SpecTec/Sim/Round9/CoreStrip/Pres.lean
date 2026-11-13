module

public import Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Strip.Thms

/-!
# steps from export-free configurations stay export-free, store-locally (unrefined)

`stripped_stepAt`: `Round7.stripped_step` with `HostExportBlind host` replaced by
`HostStrippedAt host c.store`, that the host returns only export-free stores at the source's
store. Only the host-call case changes. One case per rule of `Step`, kept unrefined.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round7

variable {H : Type}

attribute [local simp] atomic_toAdmin atomic_plain atomic_ref atomic_trap atomic_constI32
  atomic_callRefType atomic_returnCallRefType allAtomic_append_iff allAtomic_cons_iff
  allAtomic_nil_iff allAtomic_vals_iff allAtomic_map_ref allAtomic_expression

set_option hygiene false in
/-- A case whose successor has the source's store and frame and atomic code. -/
macro "stripped_atomic_r9" : tactic => `(tactic| (
  intro _ hc
  obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
  exact stripped_mk hs hf (stripAdmins_atomic (by simp))))

/-- **Steps from export-free configurations stay export-free**, for a host that returns only
export-free stores at the source's store. -/
theorem stripped_stepAt {P : Profile} {host : HostSemantics H}
    {c c' : Config H} (h : Step P host c c') :
    HostStrippedAt host c.store → Stripped c → Stripped c' := by
  induction h with
  | parametric h =>
      intro _ hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      exact stripped_mk hs hf (stripAdmins_atomic (parametricStep_atomic' h))
  | numeric h =>
      intro _ hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      exact stripped_mk hs hf (stripAdmins_atomic (numericStep_atomic' h))
  | vector h =>
      intro _ hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      exact stripped_mk hs hf (stripAdmins_atomic (vectorStep_atomic' h))
  | «variable» h =>
      exact fun _ hc => stripped_fam hc (variableStep_funcs h).1 (variableStep_funcs h).2
        (variableStep_atomic' h)
  | table h =>
      exact fun _ hc => stripped_fam hc (tableStep_funcs h).1 (tableStep_funcs h).2
        (tableStep_atomic' h)
  | memory h =>
      exact fun _ hc => stripped_fam hc (memoryStep_funcs h).1 (memoryStep_funcs h).2
        (memoryStep_atomic' h)
  | reference h =>
      exact fun _ hc => stripped_fam hc (refStep_funcs h).1 (refStep_funcs h).2 (refStep_atomic' h)
  | aggregate h =>
      exact fun _ hc => stripped_fam hc (aggregateStep_funcs h).1 (aggregateStep_funcs h).2
        (aggregateStep_atomic' h)
  | ctxtInstrs h hne ih =>
      intro hS hc
      obtain ⟨hs, hf, hcode⟩ := stripped_iff.mp hc
      obtain ⟨h₁, hrest⟩ := stripAdmins_append_eq hcode
      obtain ⟨-, his⟩ := stripAdmins_append_eq h₁
      obtain ⟨hs', hf', his'⟩ := stripped_iff.mp (ih hS (stripped_mk hs hf his))
      exact stripped_mk hs' hf' (by simp only [stripAdmins_append, stripAdmins_vals, his', hrest])
  | ctxtLabel h ih =>
      intro hS hc
      obtain ⟨hs, hf, hcode⟩ := stripped_iff.mp hc
      obtain ⟨hs', hf', his'⟩ :=
        stripped_iff.mp (ih hS (stripped_mk hs hf (stripAdmins_label_eq hcode)))
      exact stripped_mk hs' hf' (by simp only [stripAdmins_cons, stripAdmins_nil, stripAdmin, his'])
  | ctxtHandler h ih =>
      intro hS hc
      obtain ⟨hs, hf, hcode⟩ := stripped_iff.mp hc
      obtain ⟨hs', hf', his'⟩ :=
        stripped_iff.mp (ih hS (stripped_mk hs hf (stripAdmins_handler_eq hcode)))
      exact stripped_mk hs' hf' (by simp only [stripAdmins_cons, stripAdmins_nil, stripAdmin, his'])
  | ctxtFrame h ih =>
      intro hS hc
      obtain ⟨hs, hf, hcode⟩ := stripped_iff.mp hc
      obtain ⟨hfi, hbody⟩ := stripAdmins_frame_eq hcode
      obtain ⟨hs', hfi', his'⟩ := stripped_iff.mp (ih hS (stripped_mk hs hfi hbody))
      exact stripped_mk hs' hf
        (by simp only [stripAdmins_cons, stripAdmins_nil, stripAdmin, hfi', his'])
  | block =>
      intro _ hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      exact stripped_mk hs hf (stripAdmins_label_atomic (by simp))
  | loop =>
      intro _ hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      exact stripped_mk hs hf (stripAdmins_label_atomic (by simp))
  | ifTrue => stripped_atomic_r9
  | ifFalse => stripped_atomic_r9
  | labelVals => stripped_atomic_r9
  | brLabelZero => stripped_atomic_r9
  | brLabelSucc => stripped_atomic_r9
  | brHandler => stripped_atomic_r9
  | brIfTrue => stripped_atomic_r9
  | brIfFalse => stripped_atomic_r9
  | brTableLt => stripped_atomic_r9
  | brTableGe => stripped_atomic_r9
  | brOnNullNull => stripped_atomic_r9
  | brOnNullAddr => stripped_atomic_r9
  | brOnNonNullNull => stripped_atomic_r9
  | brOnNonNullAddr => stripped_atomic_r9
  | brOnCastSucceed => stripped_atomic_r9
  | brOnCastFail => stripped_atomic_r9
  | brOnCastFailSucceed => stripped_atomic_r9
  | brOnCastFailFail => stripped_atomic_r9
  | call => stripped_atomic_r9
  | callRefNull => stripped_atomic_r9
  | callRefFunc hc' hf' =>
      intro _ hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      refine stripped_mk hs hf ?_
      simp only [stripAdmins_cons, stripAdmins_nil, stripAdmin,
        stripFrame_forCall_eq (stripFI_of_stripped hs hf'),
        stripAdmins_atomic (by simp : AllAtomic (expression _))]
  | callRefHost hc' hf' he hn hcode hhost =>
      intro hS hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      exact stripped_mk (hS _ _ _ _ hhost) hf
        (stripAdmins_atomic ((allAtomic_toAdmin _).mpr trivial))
  | callRefHostDiv =>
      intro _ hc
      exact hc
  | returnCall => stripped_atomic_r9
  | returnCallRefLabel hc' =>
      intro _ hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      exact stripped_mk hs hf (stripAdmins_atomic (by simp [atomic_of_isReturnCallRef hc']))
  | returnCallRefHandler hc' =>
      intro _ hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      exact stripped_mk hs hf (stripAdmins_atomic (by simp [atomic_of_isReturnCallRef hc']))
  | returnCallRefFrameNull => stripped_atomic_r9
  | returnCallRefFrameAddr hc' =>
      intro _ hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      exact stripped_mk hs hf (stripAdmins_atomic (by
        simp [atomic_retToCallIn (atomic_of_isReturnCallRef hc')]))
  | callIndirect => stripped_atomic_r9
  | returnCallIndirect => stripped_atomic_r9
  | frameVals => stripped_atomic_r9
  | returnFrame => stripped_atomic_r9
  | returnLabel => stripped_atomic_r9
  | returnHandler => stripped_atomic_r9
  | throw =>
      intro _ hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      exact stripped_mk (stripStore_addExn_eq hs _) hf (stripAdmins_atomic (by simp))
  | throwRefNull => stripped_atomic_r9
  | throwRefInstrs => stripped_atomic_r9
  | throwRefLabel => stripped_atomic_r9
  | throwRefFrame => stripped_atomic_r9
  | throwRefHandlerEmpty => stripped_atomic_r9
  | throwRefHandlerCatch => stripped_atomic_r9
  | throwRefHandlerCatchRef => stripped_atomic_r9
  | throwRefHandlerCatchAll => stripped_atomic_r9
  | throwRefHandlerCatchAllRef => stripped_atomic_r9
  | throwRefHandlerNext =>
      intro _ hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      exact stripped_mk hs hf (stripAdmins_handler_atomic (by simp))
  | tryTable =>
      intro _ hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      refine stripped_mk hs hf ?_
      simp only [stripAdmins_cons, stripAdmins_nil, stripAdmin, stripAdmins_label_atomic
        (by simp : AllAtomic (vals _ ++ expression _))]
  | handlerVals => stripped_atomic_r9
  | trapInstrs => stripped_atomic_r9
  | trapLabel => stripped_atomic_r9
  | trapHandler => stripped_atomic_r9
  | trapFrame => stripped_atomic_r9

end Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip
