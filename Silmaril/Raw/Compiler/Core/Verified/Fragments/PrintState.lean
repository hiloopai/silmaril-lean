module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.PrintState.Defs
/-! # Fragment: `int` statements among `printf` calls

`main` creates `int` locals, then runs `int` statements, `if`/`else` with any arms and
`printf("…")` or `printf("…%d…", e)` with `e` an `int` expression over the locals
(`PrintState.recognize`). The machine code computes every value at run time from registers: the
guards of the outputs (which arms the run takes), the decimals of the operands and the returned
value (`PrintStateLink.link`); crt0 prints the buffer and exits with the value. -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified

open Silmaril.Cerberus
open Spec Backend

namespace PrintState

/-- The link of a recognised document, when its outputs fit the buffer. -/
def compile (doc : Codec.Document) : Option Artifact :=
  match recognize doc with
  | some (T, os) =>
      if PrintStateLink.Fits os then (artifactOf (PrintStateLink.link os T)).toOption else none
  | none => none

theorem compile_sound (doc : Codec.Document) (a : Artifact) (h : compile doc = some a) :
    ArtifactSound doc a := by
  unfold compile at h
  split at h
  · rename_i T os hr
    split at h
    · rename_i fits
      have ha := Fragment.toOption_ok h
      refine ⟨Fragment.argSize_ok ha, ?_⟩
      intro S exit E0 hl args _ saved init o hb
      rcases recognize_sound doc hr args with ub | ⟨okT, okos, beh⟩
      · exact .inr (.inl ub)
      · rcases PrintStateLink.link_sound okos okT fits ha hl hb with rfl | rfl
        · exact .inl rfl
        · rw [Fragment.status_ofInt]
          exact .inr (.inr beh)
    · cases h
  · cases h

end PrintState

namespace Fragments

/-- `int` statements among `printf` calls (`PrintState.recognize`). -/
def printState : Fragment where
  compile := PrintState.compile
  sound := PrintState.compile_sound

end Fragments

end Silmaril.Compile.Core.Verified
