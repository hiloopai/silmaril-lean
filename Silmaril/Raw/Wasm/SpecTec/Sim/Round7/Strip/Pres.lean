module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Strip.Pres

/-!
# Round 7: steps from export-free configurations stay export-free (unrefined)

`stripped_step`: for an export-blind host, a Core successor of a configuration without exports
has no exports. Every rule builds its successor from the source's pieces and the store's function
instances; a host call returns a store with its exports removed, by the second half of
`HostExportBlind`. One case per rule of `Step`, kept unrefined.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

attribute [local simp] atomic_toAdmin atomic_plain atomic_ref atomic_trap atomic_constI32
  atomic_callRefType atomic_returnCallRefType allAtomic_append_iff allAtomic_cons_iff
  allAtomic_nil_iff allAtomic_vals_iff allAtomic_map_ref allAtomic_expression

set_option hygiene false in
/-- A case whose successor has the source's store and frame and atomic code. -/
macro "stripped_atomic" : tactic => `(tactic| (
  intro hc
  obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
  exact stripped_mk hs hf (stripAdmins_atomic (by simp))))

/-- **Steps from export-free configurations stay export-free**, for export-blind hosts. -/
theorem stripped_step {P : Profile} {host : HostSemantics H} (hb : HostExportBlind host)
    {c c' : Config H} (h : Step P host c c') : Stripped c → Stripped c' := by
  induction h with
  | parametric h =>
      intro hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      exact stripped_mk hs hf (stripAdmins_atomic (parametricStep_atomic' h))
  | numeric h =>
      intro hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      exact stripped_mk hs hf (stripAdmins_atomic (numericStep_atomic' h))
  | vector h =>
      intro hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      exact stripped_mk hs hf (stripAdmins_atomic (vectorStep_atomic' h))
  | «variable» h =>
      exact fun hc => stripped_fam hc (variableStep_funcs h).1 (variableStep_funcs h).2
        (variableStep_atomic' h)
  | table h =>
      exact fun hc => stripped_fam hc (tableStep_funcs h).1 (tableStep_funcs h).2
        (tableStep_atomic' h)
  | memory h =>
      exact fun hc => stripped_fam hc (memoryStep_funcs h).1 (memoryStep_funcs h).2
        (memoryStep_atomic' h)
  | reference h =>
      exact fun hc => stripped_fam hc (refStep_funcs h).1 (refStep_funcs h).2 (refStep_atomic' h)
  | aggregate h =>
      exact fun hc => stripped_fam hc (aggregateStep_funcs h).1 (aggregateStep_funcs h).2
        (aggregateStep_atomic' h)
  | ctxtInstrs h hne ih =>
      intro hc
      obtain ⟨hs, hf, hcode⟩ := stripped_iff.mp hc
      obtain ⟨h₁, hrest⟩ := stripAdmins_append_eq hcode
      obtain ⟨-, his⟩ := stripAdmins_append_eq h₁
      obtain ⟨hs', hf', his'⟩ := stripped_iff.mp (ih (stripped_mk hs hf his))
      exact stripped_mk hs' hf' (by simp only [stripAdmins_append, stripAdmins_vals, his', hrest])
  | ctxtLabel h ih =>
      intro hc
      obtain ⟨hs, hf, hcode⟩ := stripped_iff.mp hc
      obtain ⟨hs', hf', his'⟩ :=
        stripped_iff.mp (ih (stripped_mk hs hf (stripAdmins_label_eq hcode)))
      exact stripped_mk hs' hf' (by simp only [stripAdmins_cons, stripAdmins_nil, stripAdmin, his'])
  | ctxtHandler h ih =>
      intro hc
      obtain ⟨hs, hf, hcode⟩ := stripped_iff.mp hc
      obtain ⟨hs', hf', his'⟩ :=
        stripped_iff.mp (ih (stripped_mk hs hf (stripAdmins_handler_eq hcode)))
      exact stripped_mk hs' hf' (by simp only [stripAdmins_cons, stripAdmins_nil, stripAdmin, his'])
  | ctxtFrame h ih =>
      intro hc
      obtain ⟨hs, hf, hcode⟩ := stripped_iff.mp hc
      obtain ⟨hfi, hbody⟩ := stripAdmins_frame_eq hcode
      obtain ⟨hs', hfi', his'⟩ := stripped_iff.mp (ih (stripped_mk hs hfi hbody))
      exact stripped_mk hs' hf
        (by simp only [stripAdmins_cons, stripAdmins_nil, stripAdmin, hfi', his'])
  | block =>
      intro hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      exact stripped_mk hs hf (stripAdmins_label_atomic (by simp))
  | loop =>
      intro hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      exact stripped_mk hs hf (stripAdmins_label_atomic (by simp))
  | ifTrue => stripped_atomic
  | ifFalse => stripped_atomic
  | labelVals => stripped_atomic
  | brLabelZero => stripped_atomic
  | brLabelSucc => stripped_atomic
  | brHandler => stripped_atomic
  | brIfTrue => stripped_atomic
  | brIfFalse => stripped_atomic
  | brTableLt => stripped_atomic
  | brTableGe => stripped_atomic
  | brOnNullNull => stripped_atomic
  | brOnNullAddr => stripped_atomic
  | brOnNonNullNull => stripped_atomic
  | brOnNonNullAddr => stripped_atomic
  | brOnCastSucceed => stripped_atomic
  | brOnCastFail => stripped_atomic
  | brOnCastFailSucceed => stripped_atomic
  | brOnCastFailFail => stripped_atomic
  | call => stripped_atomic
  | callRefNull => stripped_atomic
  | callRefFunc hc' hf' =>
      intro hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      refine stripped_mk hs hf ?_
      simp only [stripAdmins_cons, stripAdmins_nil, stripAdmin,
        stripFrame_forCall_eq (stripFI_of_stripped hs hf'),
        stripAdmins_atomic (by simp : AllAtomic (expression _))]
  | callRefHost hc' hf' he hn hcode hhost =>
      intro hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      rw [← hs] at hhost
      obtain ⟨o, -, heq⟩ := hb.2 _ _ _ _ hhost
      cases o with
      | diverged => exact absurd heq (by simp [stripOutcome])
      | returned s'' r'' =>
          simp only [stripOutcome, Silmaril.Wasm.Execution.Host.Outcome.returned.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          exact stripped_mk (stripStore_stripStore _) hf
            (stripAdmins_atomic ((allAtomic_toAdmin _).mpr trivial))
  | callRefHostDiv =>
      intro hc
      exact hc
  | returnCall => stripped_atomic
  | returnCallRefLabel hc' =>
      intro hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      exact stripped_mk hs hf (stripAdmins_atomic (by simp [atomic_of_isReturnCallRef hc']))
  | returnCallRefHandler hc' =>
      intro hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      exact stripped_mk hs hf (stripAdmins_atomic (by simp [atomic_of_isReturnCallRef hc']))
  | returnCallRefFrameNull => stripped_atomic
  | returnCallRefFrameAddr hc' =>
      intro hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      exact stripped_mk hs hf (stripAdmins_atomic (by
        simp [atomic_retToCallIn (atomic_of_isReturnCallRef hc')]))
  | callIndirect => stripped_atomic
  | returnCallIndirect => stripped_atomic
  | frameVals => stripped_atomic
  | returnFrame => stripped_atomic
  | returnLabel => stripped_atomic
  | returnHandler => stripped_atomic
  | throw =>
      intro hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      exact stripped_mk (stripStore_addExn_eq hs _) hf (stripAdmins_atomic (by simp))
  | throwRefNull => stripped_atomic
  | throwRefInstrs => stripped_atomic
  | throwRefLabel => stripped_atomic
  | throwRefFrame => stripped_atomic
  | throwRefHandlerEmpty => stripped_atomic
  | throwRefHandlerCatch => stripped_atomic
  | throwRefHandlerCatchRef => stripped_atomic
  | throwRefHandlerCatchAll => stripped_atomic
  | throwRefHandlerCatchAllRef => stripped_atomic
  | throwRefHandlerNext =>
      intro hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      exact stripped_mk hs hf (stripAdmins_handler_atomic (by simp))
  | tryTable =>
      intro hc
      obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
      refine stripped_mk hs hf ?_
      simp only [stripAdmins_cons, stripAdmins_nil, stripAdmin, stripAdmins_label_atomic
        (by simp : AllAtomic (vals _ ++ expression _))]
  | handlerVals => stripped_atomic
  | trapInstrs => stripped_atomic
  | trapLabel => stripped_atomic
  | trapHandler => stripped_atomic
  | trapFrame => stripped_atomic

end Silmaril.Wasm.SpecTec.Sim.Round7
