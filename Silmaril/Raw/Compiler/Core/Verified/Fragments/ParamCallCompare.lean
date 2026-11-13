module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.ParamCallCompare.Defs
/-! # A procedure call used by an integer comparison -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

open Silmaril.Cerberus Spec Backend

def paramCallCompareCompile (doc : Codec.Document) : Option Artifact := do
  let p ← ParamCallCompare.recognize doc
  (artifactOf (ParamCallCompare.planLink p)).toOption

theorem paramCallCompareCompile_sound (doc : Codec.Document) (a : Artifact)
    (h : paramCallCompareCompile doc = some a) : ArtifactSound doc a := by
  unfold paramCallCompareCompile at h
  cases hr : ParamCallCompare.recognize doc with
  | none => simp [hr] at h
  | some p =>
    simp only [hr] at h
    have ha := Fragment.toOption_ok h
    refine ⟨Fragment.argSize_ok ha, ?_⟩
    intro S exit E0 hl args _ saved init o hb
    rcases ParamCallCompare.recognize_sound doc p hr args with ub | ⟨ok, beh⟩
    · exact .inr (.inl ub)
    · rcases ParamCallCompare.planLink_sound p (ParamCallCompare.recognize_range doc hr) ok ha hl hb with rfl | rfl
      · exact .inl rfl
      · rw [Fragment.status_ofInt]
        exact .inr (.inr beh)

/-- A one-parameter procedure with mutable parameter slots as the left operand of an int comparison. -/
def paramCallCompare : Fragment where
  compile := paramCallCompareCompile
  sound := paramCallCompareCompile_sound

end Silmaril.Compile.Core.Verified.Fragments
