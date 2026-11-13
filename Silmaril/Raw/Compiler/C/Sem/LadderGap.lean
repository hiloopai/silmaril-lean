module

public import Silmaril.Compiler.C.Sem.C3.Defs
public import Silmaril.Compiler.C.Sem.C0Mono.Defs
@[expose] public section

/-!
# Witnesses and layout facts for the ladder-law audit

`Silmaril/Cerberus/Mem/Layout.lean:88` assigns every real floating type size and
alignment 8 (Cerberus DefaultImpl). C3 instead gives `float` size 4. The
coordinator's floating-type layout decision leaves
these frozen definitions intact and requests a behaviour-level refutation.
The two layout equations below are kernel proofs of the underlying discrepancy.

`sizeofFloatProgram` is hand-built typed Ail for
`int main(void) { return sizeof(float); }`. Executable evaluation accepts it in
C2, returning status 8 in C2 and 4 in C3. `pointerCastProgram` is
`int main(void) { return (int)(int *)0; }`: C0.check accepts, C0.run reports an
unsupported conversion, and C1.run returns status 0. This refutes the exact
C0 → C1 equality (`exactC1ExtendsC0`, the form before the coordinator's restatement
of `TargetsLadder.lean`); `not_exactC1ExtendsC0_of_witness` reduces its kernel proof to
the fragment check and the two run equations.

These executable observations were not kernel-proved behaviour statements in the
original audit. At that revision `ofCtype`, `ofGenType` and `eraseEnums` in
`Compile/C/Types.lean` were opaque `partial def` constants, and kernel evaluation
stopped at the type decoder even on simple integer expressions. The earlier
Core-realisation witnesses avoided that barrier using returnVoid and no declarations.

`ofGenType` and `ofCtype` are now structurally recursive definitions: the activation-body
increment example in `AssertionExecutionChecks.lean` is kernel-proved without a
type-decoder premise. `eraseEnums` remains partial. The whole-program
witness observations recorded here have not been upgraded to kernel proofs by
that change; the conditional behaviour-level statements below retain their explicit
execution premises. No axiom or native evaluation is used in the proofs here.
-/

namespace Silmaril.Compile.C.Sem.LadderGap

open Silmaril.Cerberus Silmaril.Cerberus.Ail

/-- The C type `float`. -/
def floatType : Ctype := .mk [] (.basic (.floating (.realFloating .float)))

/-- The pinned Cerberus layout uses eight bytes for `float`, at any positive fuel. -/
theorem default_float_layout (tags : Mem.Concrete.Tags) (fuel : Nat) :
    Mem.Concrete.typeLayout (fuel + 1) tags floatType = .ok ⟨8, 8, []⟩ := rfl

/-- C3 uses four bytes for `float`, at any positive fuel. -/
theorem c3_float_layout (tags : Mem.Concrete.Tags) (fuel : Nat) :
    C3.typeLayout tags (fuel + 1) floatType = .ok (4, 4, []) := rfl

/-- The two layout implementations disagree on the size of `float`. -/
theorem float_layout_sizes_ne (tags : Mem.Concrete.Tags) (fuel : Nat) :
    (Mem.Concrete.typeLayout (fuel + 1) tags floatType).toOption.map (·.size.toNat) ≠
      (C3.typeLayout tags (fuel + 1) floatType).toOption.map (·.1) := by
  rw [default_float_layout, c3_float_layout]
  decide

/-- An integer main returning the supplied expression, with an explicit prototype. -/
def returnProgram (e : TypedExpression) : TypedProgram :=
  let main : Sym := ⟨⟨[]⟩, 1, .id "main"⟩
  let intTy : Ctype := .mk [] (.basic (.integer (.signed .int)))
  (some main, {
    declarations := [(main, .unknown, ⟨[]⟩,
      .function true (⟨false, false, false⟩, intTy) [] false false false)],
    objectDefinitions := [],
    functionDefinitions := [(main,
      ⟨.unknown, 0, ⟨[]⟩, [], .mk .unknown ⟨false, none⟩ ⟨[]⟩ (.return_ e)⟩)],
    staticAssertions := [], tagDefinitions := [], externIdmap := [],
    typedefAttributes := [], loopAttributes := [], cnFunctions := [],
    cnLemmata := [], cnPredicates := [], cnDatatypes := [],
    cnDeclSpecs := [], cnIdents := [] })

/-- The requested hand-built typed-Ail `sizeof(float)` witness. -/
def sizeofFloatProgram : TypedProgram :=
  returnProgram (.mk (.rvalue (.basic (.integer .sizeT))) [] .unknown
    (.sizeof ⟨false, false, false⟩ floatType))

/-- A nested pointer cast that C0's expression checker accepts. -/
def pointerCastExpression : TypedExpression :=
  let q : Qualifiers := ⟨false, false, false⟩
  let intTy : Ctype := .mk [] (.basic (.integer (.signed .int)))
  let intAnn : GenTypeCategory := .rvalue (.basic (.integer (.concrete (.signed .int))))
  let zero : TypedExpression := .mk intAnn [] .unknown
    (.const (.integer (.iconstant 0 .decimal none)))
  let ptr : TypedExpression := .mk (.rvalue (.pointer q intTy)) [] .unknown
    (.cast q (.mk [] (.pointer q intTy)) zero)
  .mk intAnn [] .unknown (.cast q intTy ptr)

/-- The expression checker traverses casts without checking their target types. -/
theorem pointer_cast_checkE (P : C0.Prog) :
    C0.checkE P pointerCastExpression = .ok () := rfl

/-- An integer main returning the supplied expression, with no declarations. -/
def bareReturnProgram (e : TypedExpression) : TypedProgram :=
  let main : Sym := ⟨⟨[]⟩, 1, .id "main"⟩
  (some main, {
    declarations := [], objectDefinitions := [],
    functionDefinitions := [(main,
      ⟨.unknown, 0, ⟨[]⟩, [], .mk .unknown ⟨false, none⟩ ⟨[]⟩ (.return_ e)⟩)],
    staticAssertions := [], tagDefinitions := [], externIdmap := [],
    typedefAttributes := [], loopAttributes := [], cnFunctions := [],
    cnLemmata := [], cnPredicates := [], cnDatatypes := [],
    cnDeclSpecs := [], cnIdents := [] })

/-- `int main(void) { return (int)(int *)0; }`, declaration-free: the witness against the
exact C0 → C1 statement. -/
def pointerCastProgram : TypedProgram := bareReturnProgram pointerCastExpression

/-- The exact C0 → C1 ladder law, as first stated (`bd3dc19b3`), before the coordinator
restated it with the premise `C0.beh p ≠ ∅`. -/
def exactC1ExtendsC0 : Prop :=
  ∀ p : TypedProgram, C0.InFragment p → C1.beh p = C0.beh p

/-- A program in C0's fragment on which C0 stops as `unsupported` (no behaviour) and C1
terminates refutes the exact C0 → C1 law. -/
theorem not_exactC1ExtendsC0_of_witness {p : TypedProgram} {n m : Nat} {why : String}
    {o : Obs} (hc : C0.InFragment p) (h0 : C0.run n p = .unsupported why)
    (h1 : C1.run m p = .done o) : ¬ exactC1ExtendsC0 := by
  intro h
  have ho : o ∈ C0.beh p := by rw [← h p hc]; exact C1.beh_of_done h1
  rcases ho with ⟨k, hk⟩ | ⟨k, w, hk⟩ | ⟨_, hk⟩
  · cases C0.run_agree h0 hk (by intro h; cases h) (by intro h; cases h)
  · cases C0.run_agree h0 hk (by intro h; cases h) (by intro h; cases h)
  · cases h0.symm.trans (hk n)

end Silmaril.Compile.C.Sem.LadderGap
