module

import Silmaril.Logic.ACL2.X86Step.Thms

namespace Silmaril.Logic.ACL2.X86Step

open Translated Standard

private def x : Name := ⟨"X86ISA", "X86"⟩
private def y : Name := ⟨"X86ISA", "Y"⟩
private def fault : Name := ⟨"X86ISA", "FAULT"⟩
private abbrev args := RawArgs.ofList

-- A matching spelling from another package cannot resolve the FAULT call.
example : (lower frontier [x] (.call ⟨"ACL2", "FAULT"⟩ (args [.var x]))).isNone := by decide

example : (lower frontier [x] (.call fault (args [.var x, .var x]))).isNone := by decide

example : (lower frontier [x] (.call Primitive.cons.name (args [.var x]))).isNone := by decide

example : (lower frontier [x] (.var ⟨"ACL2", "X86"⟩)).isNone := by decide

-- The actual can see X86. The lambda body cannot capture it from the caller.
example : (lower frontier [x] (.lambda [y] (.var x) (args [.var x]))).isNone := by decide

example : (lower frontier [x] (.lambda [y, y] (.var y) (args [.var x, .var x]))).isNone := by decide

example : (lower frontier [x] (.lambda [y] (.var y) (args [.var x, .var x]))).isNone := by decide

example : (Raw.quote (.symbol stepName)).calls = [] := rfl

-- Rebinding X86 in the lambda changes its position. CONS preserves the order
-- of the logical value components, including an external input in second place.
private def rebind : Raw :=
  .lambda [y, x] (.call Primitive.cons.name (args [.var x, .var y]))
    (args [.var x, .quote (.integer 7)])

private def rebound : Checked frontier [x] rebind := (lower frontier [x] rebind).get (by decide)

example (M : Interpretation frontier) (value : Object) :
    rebound.eval M (fun _ => value) = .cons (.integer 7) value := rfl

-- Integer zero is a non-NIL ACL2 object.
private def zeroTest : Raw := .ite (.quote (.integer 0)) (.var x) (.quote (.integer 7))
private def checkedZero : Checked frontier [x] zeroTest := (lower frontier [x] zeroTest).get (by decide)

example (M : Interpretation frontier) (value : Object) :
    checkedZero.eval M (fun _ => value) = value := rfl

#print axioms checked_agreement
#print axioms calls_exact
#print axioms frontier_partition
#print axioms frontier_exact
#print axioms defining_equation
#print axioms Translated.Definition.preserves

end Silmaril.Logic.ACL2.X86Step
