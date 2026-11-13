module

public import Silmaril.Compiler.Core.Verified.Fragment.Defs
public import Silmaril.Compiler.Core.Verified.CallLink.Defs
/-! # Fragments for calls without parameters

The three entries distinguish a returned call, a statement call and a comma expression.
All emit a Lir call to a separate function through `CallLink.planLink`.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Fragments

open Silmaril.Cerberus Spec Backend

/-- The syntactic call shape: return, statement, comma. -/
def callKind : Call.Plan → Nat
  | .ret _ _ => 0
  | .stmt _ _ _ => 1
  | .comma _ _ _ => 2

def recognizeCall (kind : Nat) (doc : Codec.Document) : Option Call.Plan := do
  let pl ← Call.recognize doc
  if callKind pl = kind then some pl else none

theorem recognizeCall_eq {kind : Nat} {doc : Codec.Document} {pl : Call.Plan}
    (h : recognizeCall kind doc = some pl) : Call.recognize doc = some pl := by
  unfold recognizeCall at h
  cases hr : Call.recognize doc with
  | none => simp [hr] at h
  | some p =>
    rw [hr] at h
    change (if callKind p = kind then some p else none) = some pl at h
    split at h
    · exact h
    · cases h

def callCompile (kind : Nat) (doc : Codec.Document) : Option Artifact := do
  let pl ← recognizeCall kind doc
  (artifactOf (CallLink.planLink pl)).toOption

theorem callCompile_sound (kind : Nat) (doc : Codec.Document) (a : Artifact)
    (h : callCompile kind doc = some a) : ArtifactSound doc a := by
  unfold callCompile at h
  cases hr : recognizeCall kind doc with
  | none => simp [hr] at h
  | some pl =>
    simp only [hr] at h
    have ha := Fragment.toOption_ok h
    refine ⟨Fragment.argSize_ok ha, ?_⟩
    intro S exit E0 hl args _ saved init o hb
    rcases Call.recognize_sound doc pl (recognizeCall_eq hr) args with ub | ⟨ok, beh⟩
    · exact .inr (.inl ub)
    · rcases CallLink.planLink_sound pl ok ha hl hb with rfl | rfl
      · exact .inl rfl
      · rw [Fragment.status_ofInt]
        exact .inr (.inr beh)

/-- The common proof boundary for the three no-parameter call shapes. -/
def callFragment (kind : Nat) : Fragment where
  compile := callCompile kind
  sound := callCompile_sound kind

/-- `return g();`, where `g` has no parameters. -/
def callReturn : Fragment := callFragment 0

end Silmaril.Compile.Core.Verified.Fragments
