module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.ParamCallTail.Defs
public import Silmaril.Compiler.Core.Verified.StateExitLink.Defs
/-! # Fragment: terminal CFG conditions containing a mutable-parameter call -/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.Fragments

open Spec Backend

def paramCallTailCompile (doc : Silmaril.Cerberus.Codec.Document) : Option Artifact := do
  let p ← ParamCallTail.recognize doc
  (artifactOf (StateExitLink.link p.result)).toOption

theorem paramCallTailCompile_sound (doc : Silmaril.Cerberus.Codec.Document) (a : Artifact)
    (h : paramCallTailCompile doc = some a) : ArtifactSound doc a := by
  unfold paramCallTailCompile at h
  cases hr : ParamCallTail.recognize doc with
  | none => simp [hr] at h
  | some p =>
    simp only [hr, bind, Option.bind] at h
    have ha := Fragment.toOption_ok h
    refine ⟨Fragment.argSize_ok ha, ?_⟩
    intro S exit E0 hl args _hok saved init o hb
    rcases ParamCallTail.recognize_sound doc p hr args with ub | ⟨ok, beh⟩
    · exact .inr (.inl ub)
    · rcases StateExitLink.link_sound ha hl hb with ho | ⟨habort, hexit⟩
      · exact .inl ho
      · by_cases flag : p.result.test.val 0 = 1
        · rw [hexit ok.1 flag (ok.2 flag), Fragment.status_ofInt]
          exact .inr (.inr (by simpa [StateExit.Result.obs, flag] using beh))
        · rw [habort ok.1 flag]
          exact .inr (.inr (by simpa [StateExit.Result.obs, flag] using beh))

def paramCallTail : Fragment := ⟨paramCallTailCompile, paramCallTailCompile_sound⟩

end Silmaril.Compile.Core.Verified.Fragments
