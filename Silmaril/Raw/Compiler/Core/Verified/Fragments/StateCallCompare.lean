module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.StateCallCompare.Defs
/-! # A procedure call used by an integer comparison -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

open Silmaril.Cerberus Spec Backend

def stateCallCompareCompile (doc : Codec.Document) : Option Artifact := do
  let p ← StateCallCompare.recognize doc
  (artifactOf (StateCallCompare.planLink p)).toOption

theorem stateCallCompareCompile_sound (doc : Codec.Document) (a : Artifact)
    (h : stateCallCompareCompile doc = some a) : ArtifactSound doc a := by
  unfold stateCallCompareCompile at h
  cases hr : StateCallCompare.recognize doc with
  | none => simp [hr] at h
  | some p =>
    simp only [hr] at h
    have ha := Fragment.toOption_ok h
    refine ⟨Fragment.argSize_ok ha, ?_⟩
    intro S exit E0 hl args _ saved init o hb
    rcases StateCallCompare.recognize_sound doc p hr args with ub | ⟨ok, beh⟩
    · exact .inr (.inl ub)
    · rcases StateCallCompare.planLink_sound p ok ha hl hb with rfl | rfl
      · exact .inl rfl
      · rw [Fragment.status_ofInt]
        exact .inr (.inr beh)

/-- A State-bodied procedure as the left operand of an int comparison. -/
def stateCallCompare : Fragment where
  compile := stateCallCompareCompile
  sound := stateCallCompareCompile_sound

end Silmaril.Compile.Core.Verified.Fragments
