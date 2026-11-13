module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.CallCompare.Defs
/-! # A procedure call used by an integer comparison -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

open Silmaril.Cerberus Spec Backend

def callCompareCompile (doc : Codec.Document) : Option Artifact := do
  let p ← CallCompare.recognize doc
  (artifactOf (CallCompare.planLink p)).toOption

theorem callCompareCompile_sound (doc : Codec.Document) (a : Artifact)
    (h : callCompareCompile doc = some a) : ArtifactSound doc a := by
  unfold callCompareCompile at h
  cases hr : CallCompare.recognize doc with
  | none => simp [hr] at h
  | some p =>
    simp only [hr] at h
    have ha := Fragment.toOption_ok h
    refine ⟨Fragment.argSize_ok ha, ?_⟩
    intro S exit E0 hl args _ saved init o hb
    rcases CallCompare.recognize_sound doc p hr args with ub | ⟨ok, beh⟩
    · exact .inr (.inl ub)
    · rcases CallCompare.planLink_sound p ok ha hl hb with rfl | rfl
      · exact .inl rfl
      · rw [Fragment.status_ofInt]
        exact .inr (.inr beh)

/-- A literal-returning procedure as the left operand of an int comparison. -/
def callCompare : Fragment where
  compile := callCompareCompile
  sound := callCompareCompile_sound

end Silmaril.Compile.Core.Verified.Fragments
