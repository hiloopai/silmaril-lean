module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.Argc.Defs
public import Silmaril.Compiler.Core.Verified.ArgcLink.Defs
/-! # Fragment: `main(argc, argv)` returning an integer expression of argc -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

open Spec Backend

def argcCompile (doc : Silmaril.Cerberus.Codec.Document) : Option Artifact := do
  let t ← Argc.recognize doc
  (artifactOf (ArgcLink.link t)).toOption

theorem argcCompile_sound (doc : Silmaril.Cerberus.Codec.Document) (a : Artifact)
    (h : argcCompile doc = some a) : ArtifactSound doc a := by
  unfold argcCompile at h
  cases hr : Argc.recognize doc with
  | none => simp [hr] at h
  | some t =>
    simp only [hr, bind, Option.bind] at h
    have ha := Fragment.toOption_ok h
    refine ⟨Fragment.argSize_ok ha, ?_⟩
    intro S exit E0 hl args hok saved init o hb
    rcases Argc.recognize_sound doc t hr args hok with ub | ⟨ok, beh⟩
    · exact .inr (.inl ub)
    · rcases ArgcLink.link_sound ok ha hl hb with rfl | rfl
      · exact .inl rfl
      · rw [Fragment.status_ofInt]
        exact .inr (.inr beh)

def argc : Fragment := ⟨argcCompile, argcCompile_sound⟩

end Silmaril.Compile.Core.Verified.Fragments
