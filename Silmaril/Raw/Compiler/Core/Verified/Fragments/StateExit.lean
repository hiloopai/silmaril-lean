module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.StateExit.Defs
public import Silmaril.Compiler.Core.Verified.StateExitLink.Defs
/-! # Fragment: State statements that return, call exit, or abort -/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.Fragments

open Spec Backend

def stateExitCompile (doc : Silmaril.Cerberus.Codec.Document) : Option Artifact := do
  let r ← StateExit.recognize doc
  (artifactOf (StateExitLink.link r)).toOption

theorem stateExitCompile_sound (doc : Silmaril.Cerberus.Codec.Document) (a : Artifact)
    (h : stateExitCompile doc = some a) : ArtifactSound doc a := by
  unfold stateExitCompile at h
  cases hr : StateExit.recognize doc with
  | none => simp [hr] at h
  | some r =>
    simp only [hr, bind, Option.bind] at h
    have ha := Fragment.toOption_ok h
    refine ⟨Fragment.argSize_ok ha, ?_⟩
    intro S exit E0 hl args _hok saved init o hb
    rcases StateExit.recognize_sound doc r hr args with ub | ⟨ok, beh⟩
    · exact .inr (.inl ub)
    · rcases StateExitLink.link_sound ha hl hb with ho | ⟨habort, hexit⟩
      · exact .inl ho
      · by_cases flag : r.test.val 0 = 1
        · rw [hexit ok.1 flag (ok.2 flag), Fragment.status_ofInt]
          exact .inr (.inr (by simpa [StateExit.Result.obs, flag] using beh))
        · rw [habort ok.1 flag]
          exact .inr (.inr (by simpa [StateExit.Result.obs, flag] using beh))

def stateExit : Fragment := ⟨stateExitCompile, stateExitCompile_sound⟩

end Silmaril.Compile.Core.Verified.Fragments
