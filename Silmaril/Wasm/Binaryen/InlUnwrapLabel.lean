module

public import Silmaril.Wasm.Binaryen.InlUnwrapRel
public import Silmaril.Wasm.Execution.Core.Sim.Behaviour
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Label

@[expose] public section

/-! # Escape-free labels at arbitrary numerical profiles

An escape-free runtime region and the same region inside a label have exactly
the same terminal configurations and divergence, including every numerical and
host choice. Both directions use direct simulations. No normal-form uniqueness,
numerical determinism, host progress, or termination premise is needed.

This is the runtime label phase needed by the converse of block unwrapping.
It does not by itself establish the full module/pass converse: block entry,
related function bodies, code-folding phases and surrounding continuations
still need their own transport.
-/

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- The label phase, followed by exact agreement after its final step. -/
inductive LabelRel (n : Nat) (cont : List Instr) : Config H → Config H → Prop where
  | refl (c : Config H) : LabelRel n cont c c
  | running {s : Store H} {f : Frame} {body : List Admin} (safe : NoEsc body) :
      LabelRel n cont ⟨s, f, [.label n cont body]⟩ ⟨s, f, body⟩

private theorem label_not_result {n : Nat} {cont : List Instr} {body : List Admin}
    {r : Result} (h : [Admin.label n cont body] = r.toAdmin) : False := by
  cases r with
  | values vs =>
      cases vs with
      | nil => cases h
      | cons v vs =>
          have eq := congrArg (fun code => code.head?.bind Admin.val?) h
          have impossible : (none : Option Val) = some v := by
            simpa only [Result.toAdmin, vals, List.map_cons, List.head?_cons,
              Option.bind_some, Admin.val?_toAdmin,
              show (Admin.label n cont body).val? = none from rfl] using eq
          cases impossible
  | throw => cases h
  | trap => cases h

/-- Removing the label after a terminal result preserves the full store/frame. -/
theorem label_result_step (s : Store H) (f : Frame) (n : Nat) (cont : List Instr)
    (result : Result) :
    Step P host ⟨s, f, [.label n cont result.toAdmin]⟩ ⟨s, f, result.toAdmin⟩ := by
  cases result with
  | values vs => exact .labelVals
  | throw a => exact .throwRefLabel
  | trap => exact .trapLabel

/-- Erasing a runtime escape-free label, with bounded administrative stuttering. -/
noncomputable def labelEraseSim (P : Numerics.Profile) (host : HostSemantics H)
    (n : Nat) (cont : List Instr) : ConfigSim P host (LabelRel n cont) where
  toForwardSim := {
    measure := fun c => sizeOf c.code
    step := by
      intro c c' d step related
      cases related with
      | refl => exact ⟨c', .inl (.single step), .refl _⟩
      | @running s f body safe =>
          obtain ⟨s', f', code'⟩ := c'
          have step' : Step P host ⟨s, f, vals [] ++ [.label n cont body]⟩
              ⟨s', f', code'⟩ := by simpa only [vals, List.map_nil, List.nil_append] using step
          obtain ⟨after, red, code⟩ := Closure.Step.label_inv step'
          simp only [vals, List.map_nil, List.nil_append] at code
          subst code'
          cases red with
          | ctxt inner =>
              exact ⟨_, .inl (.single inner), .running (safe.step inner)⟩
          | values vs =>
              refine ⟨_, .inr ⟨rfl, ?_⟩, .refl _⟩
              simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec, Admin.label.sizeOf_spec]
              omega
          | brZero target count =>
              rename_i left right index rest
              exact (safe.no_br (vs := left ++ right) (l := index) (rest := rest)
                (by simp)).elim
          | brSucc target =>
              rename_i args index rest
              exact (safe.no_br (vs := args) (l := index) (rest := rest) (by simp)).elim
          | returnCallRef target =>
              rename_i args call rest
              exact (safe.no_retCall (vs := args) (rest := rest) target (by simp)).elim
          | return_ =>
              rename_i args rest
              exact (safe.no_return (vs := args) (rest := rest) (by simp)).elim
          | throwRef a =>
              refine ⟨_, .inr ⟨rfl, ?_⟩, .refl _⟩
              simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec, Admin.label.sizeOf_spec]
              omega
          | trap =>
              refine ⟨_, .inr ⟨rfl, ?_⟩, .refl _⟩
              simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec, Admin.label.sizeOf_spec]
              omega }
  terminal := by
    intro c d result related terminal
    cases related with
    | refl => exact ⟨_, .refl, terminal⟩
    | running => exact (label_not_result terminal).elim

/-- Inserting the label around escape-free code matches every computational
step directly; the final administrative label step is handled at termination. -/
noncomputable def labelInsertSim (P : Numerics.Profile) (host : HostSemantics H)
    (n : Nat) (cont : List Instr) : ConfigSim P host (fun c d => LabelRel n cont d c) where
  toForwardSim := {
    step := by
      intro c c' d step related
      cases related with
      | refl => exact ⟨_, .inl (.single step), .refl _⟩
      | running safe =>
          exact ⟨_, .inl (.single (.ctxtLabel step)), .running (safe.step step)⟩ }
  terminal := by
    intro c d result related terminal
    cases related with
    | refl => exact ⟨_, .refl, terminal⟩
    | @running s f body safe =>
        change body = result.toAdmin at terminal
        subst body
        exact ⟨_, (label_result_step s f n cont result).steps, rfl⟩

/-- All terminal outcomes, traps, escaping exceptions and divergence coincide
at the same arbitrary profile and host. -/
theorem label_behaviours_eq {s : Store H} {f : Frame} {body : List Admin}
    (safe : NoEsc body) (n : Nat) (cont : List Instr) :
    behavioursOf P host ⟨s, f, [.label n cont body]⟩ = behavioursOf P host ⟨s, f, body⟩ :=
  (labelEraseSim P host n cont).behavioursOf_eq (labelInsertSim P host n cont) (.running safe)

/-- Divergence correspondence uses the actual same numerical/host choices. -/
theorem label_diverges_iff {s : Store H} {f : Frame} {body : List Admin}
    (safe : NoEsc body) (n : Nat) (cont : List Instr) :
    Diverges P host ⟨s, f, [.label n cont body]⟩ ↔ Diverges P host ⟨s, f, body⟩ :=
  ⟨fun h => (labelEraseSim P host n cont).toForwardSim.diverges h (.running safe),
    fun h => (labelInsertSim P host n cont).toForwardSim.diverges h (.running safe)⟩

/-- Terminal runs agree on the entire final configuration, including every
memory, table, global and local; the result-only behaviour law loses none of
this state information in this label phase. -/
theorem label_steps_result_iff {s : Store H} {f : Frame} {body : List Admin}
    (safe : NoEsc body) (n : Nat) (cont : List Instr) {final : Config H}
    (result : Result) (terminal : final.code = result.toAdmin) :
    Steps P host ⟨s, f, [.label n cont body]⟩ final ↔
      Steps P host ⟨s, f, body⟩ final := by
  constructor
  · intro run
    obtain ⟨d, run', related⟩ :=
      (labelEraseSim P host n cont).toForwardSim.steps run (.running safe)
    cases related with
    | refl => exact run'
    | running => exact (label_not_result terminal).elim
  · intro run
    obtain ⟨d, run', related⟩ :=
      (labelInsertSim P host n cont).toForwardSim.steps run (.running safe)
    cases related with
    | refl => exact run'
    | @running s' f' body' _ =>
      change body' = result.toAdmin at terminal
      subst body'
      exact run'.trans (label_result_step s' f' n cont result).steps

end Silmaril.Wasm.Binaryen.Unwrap
