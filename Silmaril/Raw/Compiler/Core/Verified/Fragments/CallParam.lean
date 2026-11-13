module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.CallParam.Defs
/-! # Fragment: `return g(n);` with a mutable State parameter

The caller passes the literal in a register, and the callee computes its expression at run time.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

open Silmaril.Cerberus Spec Backend

def callParamCompile (doc : Codec.Document) : Option Artifact := do
  let (n, t) ← CallParam.recognize doc
  (artifactOf (CallArgLink.link n t)).toOption

theorem callParamCompile_sound (doc : Codec.Document) (a : Artifact)
    (h : callParamCompile doc = some a) : ArtifactSound doc a := by
  unfold callParamCompile at h
  cases hr : CallParam.recognize doc with
  | none => simp [hr] at h
  | some x =>
    obtain ⟨n, t⟩ := x
    simp only [hr] at h
    have ha := Fragment.toOption_ok h
    refine ⟨Fragment.argSize_ok ha, ?_⟩
    intro S exit E0 hl args _ saved init o hb
    rcases CallParam.recognize_sound doc n t hr args with ub | ⟨ok, beh⟩
    · exact .inr (.inl ub)
    · rcases CallArgLink.link_sound ok ha hl hb with rfl | rfl
      · exact .inl rfl
      · rw [Fragment.status_ofInt]
        exact .inr (.inr beh)

/-- `return g(n);`, where `g` takes one `int` parameter and `n` is an integer literal. -/
def callParam : Fragment where
  compile := callParamCompile
  sound := callParamCompile_sound

end Silmaril.Compile.Core.Verified.Fragments
