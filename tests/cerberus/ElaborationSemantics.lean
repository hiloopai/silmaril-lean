import Silmaril.Compiler.Core.ElaborationSemantics.Thms

open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Compiler.Core.ElaborationSemantics

-- A bound's location is not focused; the enclosed pure expression supplies it.
example (file : Program) (labels : Labels) (env : Env) (frames : List Frame)
    (memory : Mem.Concrete.State) (number : Int) :
    SeqReach.Reaches file labels
      ⟨.effectExpr (.mk [.loc (.other "bound")]
        (.bound (.mk [.loc (.point "constant.c" 2 3)]
          (.pure (.mk [] () (.val (.loaded (.specified (.integer number))))))))) env, frames, memory⟩
      ⟨.value (.loaded (.specified (.integer number))), frames,
        SeqReach.focusMemory [.loc (.point "constant.c" 2 3)] memory⟩ :=
  bound_pure_reaches _ _ (SeqReach.pure_value [] (.loaded (.specified (.integer number))) env) frames memory

private def returnLabel : Sym := ⟨⟨[]⟩, 1, .return_⟩
private def parameter : Sym := ⟨⟨[]⟩, 2, .none⟩
private def occurrence : Sym := {parameter with description := .id "diagnostic rename"}
private def bodyAnnotations : List Annot := [.loc (.point "body.c" 4 5)]
private def runAnnotations : List Annot := [.loc (.point "return.c" 2 3)]
private def savedBody : EE := .mk bodyAnnotations (.pure (.mk [] () (.sym occurrence)))
private def localLabels : Labels := Map.ofList [(returnLabel, ([parameter], savedBody))]

-- An actual saved return with source locations discards a local bound frame,
-- resumes an arbitrary caller, and uses semantic symbol identity for its result.
example (file : Program) (env : Env) (caller : List Frame) (memory : Mem.Concrete.State) :
    ∃ finish : Mem.Concrete.State, finish.stdout = memory.stdout ∧
      SeqReach.Reaches file (∅ : Labels)
        ⟨.effectExpr (.mk runAnnotations (.run () returnLabel
          [.mk [] () (.val (.loaded (.specified (.integer 42))))])) env,
          [.bound] ++ .procedureReturn localLabels :: caller, memory⟩
        ⟨.value (.loaded (.specified (.integer 42))), caller, finish⟩ := by
  let finish : Mem.Concrete.State :=
    SeqReach.focusMemory bodyAnnotations (SeqReach.focusMemory runAnnotations memory)
  have stdout : finish.stdout = memory.stdout := by
    simp only [finish, SeqReach.focusMemory_stdout]
  have lookup : localLabels.lookup returnLabel = some ([parameter], savedBody) := rfl
  have reaches : SeqReach.Reaches file (∅ : Labels)
      ⟨.effectExpr (.mk runAnnotations (.run () returnLabel
        [.mk [] () (.val (.loaded (.specified (.integer 42))))])) env,
        [.bound] ++ .procedureReturn localLabels :: caller, memory⟩
      ⟨.value (.loaded (.specified (.integer 42))), caller, finish⟩ :=
    run_saved_value runAnnotations bodyAnnotations [] returnLabel parameter occurrence rfl env _ _
      (SeqReach.pure_value [] (.loaded (.specified (.integer 42))) env)
      [.bound] caller localLabels memory rfl lookup
  exact ⟨finish, stdout, reaches⟩

#print axioms bound_pure_reaches
#print axioms run_saved_value
#print axioms converted_int_pure
#print axioms constant_return_reaches
