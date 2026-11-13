module

public import Silmaril.Compiler.C.Sem.C0.Defs
public import Silmaril.Compiler.C.Sem.C1Mono.Defs
@[expose] public section

/-!
# A second C0/C1 initialization gap

The previous conditional equality quantifies over all typed Ail satisfying `C0.check`.
That checker exempts main from parameter restrictions. On the nonstandard signature
`int main(int argc, int second)`, C0 leaves `second` uninitialized, while C1 passes
its argv address converted to int. The executable probe in idea830 returns UB in
C0 and status 0 in C1. This differs even with the nonempty-behaviour premise.

The definitions below record the witness without modifying the frozen interpreters.
`not_conditionalC1Equality_of_undefined_done` supplies the metatheoretic refutation once
its fragment and run equations are kernel-proved. Those concrete equations still
encounter the opaque type conversions in the frozen `Compile/C/Types.lean`.
-/

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Compile.C.Sem

namespace Silmaril.Compile.C.Sem.LadderMainGap

def qualifiers : Qualifiers := ⟨false, false, false⟩
def intCtype : Ctype := .mk [] (.basic (.integer (.signed .int)))
def intRvalue : GenTypeCategory := .rvalue (.basic (.integer (.concrete (.signed .int))))
def mainSym : Sym := ⟨⟨[]⟩, 1, .id "main"⟩
def argcSym : Sym := ⟨⟨[]⟩, 2, .id "argc"⟩
def secondSym : Sym := ⟨⟨[]⟩, 3, .id "second"⟩
def readSecond : TypedExpression :=
  .mk intRvalue [] .unknown
    (.rvalue (.mk (.lvalue qualifiers intCtype false) [] .unknown (.ident secondSym)))

/-- A main function with two integer parameters. C0.check accepts its nonstandard
signature because main is exempt from parameter restrictions. -/
def twoIntMainProgram : TypedProgram :=
  (some mainSym, {
    declarations := [(mainSym, .unknown, ⟨[]⟩,
      .function true (qualifiers, intCtype)
        [(qualifiers, intCtype, false), (qualifiers, intCtype, false)] false false false)],
    objectDefinitions := [],
    functionDefinitions := [(mainSym,
      ⟨.unknown, 0, ⟨[]⟩, [argcSym, secondSym],
        .mk .unknown ⟨false, none⟩ ⟨[]⟩ (.return_ readSecond)⟩)],
    staticAssertions := [], tagDefinitions := [], externIdmap := [],
    typedefAttributes := [], loopAttributes := [], cnFunctions := [],
    cnLemmata := [], cnPredicates := [], cnDatatypes := [],
    cnDeclSpecs := [], cnIdents := [] })

/-- The conditional equality accepted before the refinement restatement (6b8acc12). -/
def conditionalC1Equality : Prop :=
  ∀ p : TypedProgram, C0.InFragment p → C0.beh p ≠ ∅ → C1.beh p = C0.beh p

/-- Any accepted program which is undefined in C0 but defined in C1 refutes the
previous conditional equality, since nonempty C0 behaviour includes undefined behaviour. -/
theorem not_conditionalC1Equality_of_undefined_done {p : TypedProgram} {n m : Nat}
    {why : String} {o : Obs} (hc : C0.InFragment p)
    (h0 : C0.run n p = .undefined why) (h1 : C1.run m p = .done o) :
    ¬ conditionalC1Equality := by
  intro h
  have hu := C0.beh_of_undefined h0
  have hn : C0.beh p ≠ ∅ := by
    rw [hu]
    exact Set.univ_nonempty.ne_empty
  have heq : C1.beh p = Set.univ := (h p hc hn).trans hu
  have hall (a : Obs) : a = o := by
    have ha : a ∈ C1.beh p := by rw [heq]; trivial
    rcases ha with ⟨k, hk⟩ | ⟨k, w, hk⟩ | ⟨_, hk⟩
    · have eq := C1.run_agree hk h1 (by intro h; cases h) (by intro h; cases h)
      cases eq
      rfl
    · cases C1.run_agree hk h1 (by intro h; cases h) (by intro h; cases h)
    · cases h1.symm.trans (hk m)
  have h01 := (hall ⟨[], .status 0⟩).trans (hall ⟨[], .status 1⟩).symm
  cases h01

end Silmaril.Compile.C.Sem.LadderMainGap
