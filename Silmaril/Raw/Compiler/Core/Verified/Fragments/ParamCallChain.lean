module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.ParamCallChain.Defs
public import Silmaril.Compiler.Core.Verified.StateExitLink.Defs
/-! # Fragment: sequences of mutable-parameter call conditions ending in abort, exit or return -/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.Fragments

open Spec Backend

def paramCallChainCompile (doc : Silmaril.Cerberus.Codec.Document) : Option Artifact := do
  let p ← ParamCallChain.recognize doc
  (artifactOf (StateExitLink.link p)).toOption

theorem paramCallChainCompile_sound (doc : Silmaril.Cerberus.Codec.Document) (a : Artifact)
    (h : paramCallChainCompile doc = some a) : ArtifactSound doc a := by
  unfold paramCallChainCompile at h
  cases hr : ParamCallChain.recognize doc with
  | none => simp [hr] at h
  | some p =>
    simp only [hr, bind, Option.bind] at h
    have ha := Fragment.toOption_ok h
    refine ⟨Fragment.argSize_ok ha, ?_⟩
    intro S exit E0 hl args _hok saved init o hb
    rcases ParamCallChain.recognize_sound doc p hr args with ub | ⟨ok, beh⟩
    · exact .inr (.inl ub)
    · rcases StateExitLink.link_sound ha hl hb with ho | ⟨habort, hexit⟩
      · exact .inl ho
      · by_cases flag : p.test.val 0 = 1
        · rw [hexit ok.1 flag (ok.2 flag), Fragment.status_ofInt]
          exact .inr (.inr (by simpa [StateExit.Result.obs, flag] using beh))
        · rw [habort ok.1 flag]
          exact .inr (.inr (by simpa [StateExit.Result.obs, flag] using beh))

def paramCallChain : Fragment := ⟨paramCallChainCompile, paramCallChainCompile_sound⟩

end Silmaril.Compile.Core.Verified.Fragments
