module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.TyRunLink.Defs
/-! # Fragment: a statement machine over globals and locals of every supported integer type

`Fragments.tyState` with the statements of `Fragments.stateGlobals`: globals initialised by
constant expressions (`TyGlobals`) and locals of type plain, `signed` or `unsigned` `char`,
`short`, `int`, `long` or `long long`, then `T x;`,
`T x = e;`, `x = e;`, `e;`, `abort();`, `if (c) A else B` with any statements in its arms, nested
blocks without locals, `return e;` and falling off the end of `main` (`TyRun.recognize`). The
result is closed; the Lir code computes its termination flag and its value at run time in
registers and traps after recording `abort` when the flag is `0` (`TyRunLink.link`). -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

open Spec Backend

def tyRunCompile (doc : Silmaril.Cerberus.Codec.Document) : Option Artifact := do
  let R ← TyRun.recognize doc
  (artifactOf (TyRunLink.link R)).toOption

theorem tyRunCompile_sound (doc : Silmaril.Cerberus.Codec.Document) (a : Artifact)
    (h : tyRunCompile doc = some a) : ArtifactSound doc a := by
  unfold tyRunCompile at h
  cases hr : TyRun.recognize doc with
  | none => simp [hr] at h
  | some R =>
    simp only [hr, bind, Option.bind] at h
    have ha := Fragment.toOption_ok h
    have wf := (TyRun.recognizeRes_of hr).2
    refine ⟨Fragment.argSize_ok ha, ?_⟩
    intro S exit E0 hl args _hok saved init o hb
    rcases TyRun.recognize_sound doc R hr args with ub | beh
    · exact .inr (.inl ub)
    · rcases TyRunLink.link_sound wf ha hl hb with ho | ⟨habort, hexit⟩
      · exact .inl ho
      · by_cases flag : R.test.val = 1
        · rw [hexit flag, Fragment.status_ofInt]
          exact .inr (.inr (by simpa [TyRun.Out.obs, flag] using beh))
        · rw [habort flag]
          exact .inr (.inr (by simpa [TyRun.Out.obs, flag] using beh))

/-- `TyRun.recognize`, linked with its termination flag (`TyRunLink.link`). -/
def tyRun : Fragment := ⟨tyRunCompile, tyRunCompile_sound⟩

end Silmaril.Compile.Core.Verified.Fragments
