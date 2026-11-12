module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.Printf.Defs
/-! # Fragment: `main` prints with `printf`, then returns an integer

The statements print string literals, or a literal with one `%d` of a closed `int` expression.
The machine code writes the literals' bytes and the operands' decimal digits (computed at run
time) into the output buffer (`PrintLink.link`) and returns the integer; crt0 prints the buffer
and exits with it. -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified

open Silmaril.Cerberus
open Spec Backend

namespace Printf

/-- The link of a recognised document, when its output fits the buffer. -/
def compile (doc : Codec.Document) : Option Artifact :=
  match recognize doc with
  | some (n, outs) =>
      if PrintLink.Fits (items outs) then
        (artifactOf (PrintLink.link (items outs) (BitVec.ofInt 64 n))).toOption
      else none
  | none => none

theorem compile_sound (doc : Codec.Document) (a : Artifact) (h : compile doc = some a) :
    ArtifactSound doc a := by
  unfold compile at h
  split at h
  · rename_i n outs hr
    split at h
    · rename_i fits
      have ha := Fragment.toOption_ok h
      refine ⟨Fragment.argSize_ok ha, ?_⟩
      intro S exit E0 hl args _ saved init o hb
      rcases PrintLink.link_sound fits ha hl hb with rfl | rfl
      · exact .inl rfl
      · rw [Fragment.status_ofInt, render_items]
        exact .inr (.inr (recognize_sound doc hr args))
    · cases h
  · cases h

end Printf

namespace Fragments

/-- `main` printing string literals, then returning an integer (`Printf.recognize`). -/
def printf : Fragment where
  compile := Printf.compile
  sound := Printf.compile_sound

end Fragments

end Silmaril.Compile.Core.Verified
