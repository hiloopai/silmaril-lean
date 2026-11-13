module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.CallState.Defs
/-! # A real procedure call with an integer-state callee -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

open Silmaril.Cerberus Spec Backend

def callStateCompile (doc : Codec.Document) : Option Artifact := do
  let pl ← CallState.recognize doc
  (artifactOf (CallLink.planLink pl)).toOption

theorem callStateCompile_sound (doc : Codec.Document) (a : Artifact)
    (h : callStateCompile doc = some a) : ArtifactSound doc a := by
  unfold callStateCompile at h
  cases hr : CallState.recognize doc with
  | none => simp [hr] at h
  | some pl =>
    simp only [hr] at h
    have ha := Fragment.toOption_ok h
    refine ⟨Fragment.argSize_ok ha, ?_⟩
    intro S exit E0 hl args _ saved init o hb
    rcases CallState.recognize_sound doc pl hr args with ub | ⟨ok, beh⟩
    · exact .inr (.inl ub)
    · rcases CallLink.planLink_sound pl ok ha hl hb with rfl | rfl
      · exact .inl rfl
      · rw [Fragment.status_ofInt]
        exact .inr (.inr beh)

/-- `return g();`, with `g` a no-parameter procedure accepted by `State`. -/
def callState : Fragment where
  compile := callStateCompile
  sound := callStateCompile_sound

end Silmaril.Compile.Core.Verified.Fragments
