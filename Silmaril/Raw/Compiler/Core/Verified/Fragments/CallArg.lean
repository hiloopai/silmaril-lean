module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.CallArgLink.Defs
/-! # Fragment: `return g(n);` with one integer parameter

The caller passes the literal in a register, and the callee computes its expression at run time.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

open Silmaril.Cerberus Spec Backend

def callArgCompile (doc : Codec.Document) : Option Artifact := do
  let (n, t) ← CallArg.recognize doc
  (artifactOf (CallArgLink.link n t)).toOption

theorem callArgCompile_sound (doc : Codec.Document) (a : Artifact)
    (h : callArgCompile doc = some a) : ArtifactSound doc a := by
  unfold callArgCompile at h
  cases hr : CallArg.recognize doc with
  | none => simp [hr] at h
  | some x =>
    obtain ⟨n, t⟩ := x
    simp only [hr] at h
    have ha := Fragment.toOption_ok h
    refine ⟨Fragment.argSize_ok ha, ?_⟩
    intro S exit E0 hl args _ saved init o hb
    rcases CallArg.recognize_sound doc n t hr args with ub | ⟨ok, beh⟩
    · exact .inr (.inl ub)
    · rcases CallArgLink.link_sound ok ha hl hb with rfl | rfl
      · exact .inl rfl
      · rw [Fragment.status_ofInt]
        exact .inr (.inr beh)

/-- `return g(n);`, where `g` takes one `int` parameter and `n` is an integer literal. -/
def callArg : Fragment where
  compile := callArgCompile
  sound := callArgCompile_sound

end Silmaril.Compile.Core.Verified.Fragments
