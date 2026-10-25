module

public import Silmaril.Wasm.Binaryen.PassAPI.ModeClient

@[expose] public section

/-! # Selecting pipelines by proved correctness mode

A stage's mode indexes its actual proof, rather than being an unchecked label.
Assembly rejects a stage whose supplied certificate is too weak for the chosen
mode. Accepted stages retain exact execution and order. Assembly only constructs
a verified pass: it does not execute any transformation, including on rejection.

This is a library API for future drivers. The existing optimizer CLI is unchanged.
-/

namespace Silmaril.Wasm.Binaryen.Modes

open Execution.Core Numerics Optimization

variable {H : Type} {P : Profile} {host : HostSemantics H}

structure Stage (P : Profile) (host : HostSemantics H) where
  name : String
  mode : Mode
  pass : Silmaril.Compile.PassAPI.Pass (contract mode P host)

def modeName : Mode → String
  | .equivalence => "equivalence"
  | .refinement => "refinement"
  | .trapInsertion => "trap-insertion"

/-- Select the stage's supplied certificate, weakening only in the proved
direction. Stronger modes reject a stage carrying only a weaker certificate. -/
def Stage.asPass (selected : Mode) (stage : Stage P host) :
    Except String (Silmaril.Compile.PassAPI.Pass (contract selected P host)) :=
  match stage with
  | ⟨_, .equivalence, pass⟩ =>
      match selected with
      | .equivalence => .ok pass
      | .refinement =>
          .ok (Silmaril.Compile.PassAPI.Pass.weaken (equivalence_le_refinement P host) pass)
      | .trapInsertion =>
          .ok (Silmaril.Compile.PassAPI.Pass.weaken (refinement_le_trapInsertion P host)
            (Silmaril.Compile.PassAPI.Pass.weaken (equivalence_le_refinement P host) pass))
  | ⟨name, .refinement, pass⟩ =>
      match selected with
      | .equivalence => .error (name ++ ": refinement certificate is too weak for equivalence")
      | .refinement => .ok pass
      | .trapInsertion =>
          .ok (Silmaril.Compile.PassAPI.Pass.weaken (refinement_le_trapInsertion P host) pass)
  | ⟨name, .trapInsertion, pass⟩ =>
      match selected with
      | .equivalence => .error (name ++ ": trap-insertion certificate is too weak for equivalence")
      | .refinement => .error (name ++ ": trap-insertion certificate is too weak for refinement")
      | .trapInsertion => .ok pass

theorem Stage.asPass_run (selected : Mode) (stage : Stage P host)
    {accepted : Silmaril.Compile.PassAPI.Pass (contract selected P host)}
    (h : stage.asPass selected = .ok accepted) : accepted.run = stage.pass.run := by
  rcases stage with ⟨name, mode, pass⟩
  cases mode <;> cases selected <;> cases h <;> rfl

def assemble (selected : Mode) :
    List (Stage P host) → Except String (Silmaril.Compile.PassAPI.Pass (contract selected P host))
  | [] => .ok .id
  | stage :: rest =>
      match stage.asPass selected with
      | .error e => .error e
      | .ok pass =>
          match assemble selected rest with
          | .error e => .error e
          | .ok following => .ok (pass.seq following)

/-- The original stage functions, run left to right without certificate changes. -/
def stageRuns : List (Stage P host) → BModule → BModule
  | [], input => input
  | stage :: rest, input => stageRuns rest (stage.pass.run input)

/-- Successful mode selection retains every stage's actual function and order. -/
theorem assemble_run (selected : Mode) (stages : List (Stage P host))
    {accepted : Silmaril.Compile.PassAPI.Pass (contract selected P host)}
    (h : assemble selected stages = .ok accepted) : accepted.run = stageRuns stages := by
  induction stages generalizing accepted with
  | nil => cases h; rfl
  | cons stage rest ih =>
      cases head : stage.asPass selected with
      | error e => simp [assemble, head] at h
      | ok pass =>
          cases tail : assemble selected rest with
          | error e => simp [assemble, head, tail] at h
          | ok following =>
              simp only [assemble, head, tail, Except.ok.injEq] at h
              cases h
              funext input
              change following.run (pass.run input) = stageRuns rest (stage.pass.run input)
              rw [Stage.asPass_run selected stage head, ih tail]

theorem assemble_sound (selected : Mode) (stages : List (Stage P host))
    {accepted : Silmaril.Compile.PassAPI.Pass (contract selected P host)}
    (h : assemble selected stages = .ok accepted) {input : BModule} (valid : input.Ok) :
    (stageRuns stages input).Ok ∧
      ExportCorrect selected P host input.lower (stageRuns stages input).lower := by
  have result : (accepted.run input).Ok ∧ ExportCorrect selected P host input.lower
      (accepted.run input).lower := ⟨accepted.inv_run valid, accepted.sound valid⟩
  simpa only [assemble_run selected stages h] using result

/-- A real exact optimizer stage, usable in any selected mode. -/
def cleanupStage (P : Profile) : Stage P (closedHost (H := H)) :=
  ⟨"cleanup", .equivalence, cleanupP (H := H) .equivalence P⟩

/-- This deliberately retains only the refinement certificate for the same
implementation. Mode selection uses the supplied proof, not claims about
which stronger theorem might exist elsewhere. -/
def cleanupRefinementStage (P : Profile) : Stage P (closedHost (H := H)) :=
  ⟨"cleanup-refinement", .refinement, cleanupP (H := H) .refinement P⟩

set_option maxRecDepth 2048 in
theorem refinement_certificate_rejected_by_exact (P : Profile) :
    (cleanupRefinementStage (H := H) P).asPass .equivalence =
      .error "cleanup-refinement: refinement certificate is too weak for equivalence" := rfl

set_option maxRecDepth 2048 in
theorem mixed_pipeline_accepted (P : Profile) :
    (assemble .refinement
      [cleanupStage (H := H) P, cleanupRefinementStage (H := H) P]).toOption.isSome = true := rfl

end Silmaril.Wasm.Binaryen.Modes
