module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.ArgvAbortLink.Defs
/-! # Fragment: `main(argc, argv) { if (c) abort(); return e; }` over `argv[i][0]`

`ArgvAbort.recognize` gives the plan (the character `argv[i][0]`, `i ≤ 1`, the test and the return
expression); `ArgvAbortLink.link` reads the character from the argument block at run time,
computes the test and either records `abort` and traps or returns the expression. -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

open Spec Backend

def argvAbortCompile (doc : Silmaril.Cerberus.Codec.Document) : Option Artifact := do
  let P ← ArgvAbort.recognize doc
  (artifactOf (ArgvAbortLink.link P)).toOption

theorem argvAbortCompile_sound (doc : Silmaril.Cerberus.Codec.Document) (a : Artifact)
    (h : argvAbortCompile doc = some a) : ArtifactSound doc a := by
  unfold argvAbortCompile at h
  cases hr : ArgvAbort.recognize doc with
  | none => simp [hr] at h
  | some P =>
    simp only [hr, bind, Option.bind] at h
    have ha := Fragment.toOption_ok h
    refine ⟨Fragment.argSize_ok ha, ?_⟩
    intro S exit E0 hl args hok saved init o hb
    rcases ArgvAbort.recognize_sound doc P hr args hok with ub | ⟨ok, ne, beh⟩ | ⟨ok, eq, okr, beh⟩
    · exact .inr (.inl ub)
    · rcases ArgvAbortLink.link_sound ha hl hok (ArgvAbort.recognize_ij hr) hb with ho | ⟨habort, -⟩
      · exact .inl ho
      · rw [habort ok ne]
        exact .inr (.inr beh)
    · rcases ArgvAbortLink.link_sound ha hl hok (ArgvAbort.recognize_ij hr) hb with ho | ⟨-, hexit⟩
      · exact .inl ho
      · rw [hexit ok eq okr, Fragment.status_ofInt]
        exact .inr (.inr beh)

def argvAbort : Fragment := ⟨argvAbortCompile, argvAbortCompile_sound⟩

end Silmaril.Compile.Core.Verified.Fragments
