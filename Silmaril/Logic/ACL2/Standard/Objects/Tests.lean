module

import Silmaril.Logic.ACL2.Standard.Objects.CdrSize
import Lean

namespace Silmaril.Logic.ACL2.Standard.Objects.Tests

private def half : Object := .rational (Rat.divInt 1 2)
private def i : Object := Object.ofParts 0 1
private def dotted : Object := .cons (.character 255) (.cons half .truth)

example : Symbol.nil.toName = ⟨"COMMON-LISP", "NIL"⟩ := by decide
example : Symbol.truth.toName = ⟨"COMMON-LISP", "T"⟩ := by decide
example : Symbol.ofName? ⟨"", "A"⟩ = none := by decide
example : Symbol.ofName? ⟨"ACL2", "Ā"⟩ = none := by decide
example : (Symbol.ofName? ⟨"P", "A"⟩).isSome = true := by decide
example : Symbol.ofName? ⟨"P", "A"⟩ ≠ Symbol.ofName? ⟨"Q", "A"⟩ := by decide
example : Symbol.ofName? ⟨"P", "A"⟩ ≠ Symbol.ofName? ⟨"P", "a"⟩ := by decide
example : Object.nil.symbolp = true ∧ Object.truth.symbolp = true := by decide
example : (Object.integer 0).car = .nil ∧ (Object.string [0]).cdr = .nil := by decide
example : dotted.cdr = .cons half .truth ∧ dotted.trueListp = false := by decide
example : dotted.append .nil = Object.ofList [.character 255, half] := by decide
example : dotted.coerce .truth = .string [255, 0] := by decide
example : dotted.coerce (.symbol Symbol.list) = .nil := by decide
example : (Object.integer (-1)).codeChar = .character 0 := by decide
example : (Object.integer 256).codeChar = .character 0 := by decide
example : half.codeChar = .character 0 := by decide
example : (Object.integer 255).codeChar = .character 255 := by decide
example : (Object.string [255]).charCode = .integer 0 := by decide

example : half.equal (.rational (Rat.divInt (-2) (-4))) = .truth := by decide
example : Object.ofParts (Rat.divInt 2 2) 0 = .integer 1 := by decide
example : i.complex half = Object.ofParts 0 (Rat.divInt 1 2) := by decide
example : half.complex i = half := by decide
example : half.integerp = false ∧ i.complexRationalp = true := by decide
example : (i.binaryAdd i.unaryMinus) = .integer 0 := by decide +kernel
example : (i.binaryMul i) = .integer (-1) := by decide +kernel
example : (Object.ofParts 1 2).reciprocal = Object.ofParts (Rat.divInt 1 5) (Rat.divInt (-2) 5) :=
  by decide +kernel
example : half.reciprocal = .integer 2 ∧ Object.truth.reciprocal = .integer 0 := by decide +kernel
example : Object.truth.binaryAdd half = half ∧ i.binaryMul .truth = .integer 0 := by decide +kernel
example : Object.truth.less i = .truth ∧ i.less .truth = .nil := by decide
example : i.numerator = .integer 0 ∧ i.denominator = .integer 1 := by decide
example : half.numerator = .integer 1 ∧ half.denominator = .integer 2 := by decide
example : Object.truth.realpart = .integer 0 ∧ Object.truth.imagpart = .integer 0 := by decide
example : half.zp = .truth ∧ (Object.integer (-2)).zp = .truth ∧ i.zp = .truth := by decide
example : (Object.integer 1).zp = .nil ∧ (Object.integer 1).decrement.natRank = 0 := by decide +kernel
example : half.ifix = .integer 0 ∧ (Object.integer (-2)).nfix = .integer 0 := by decide
example : Object.truth.decrement = .integer (-1) := by decide +kernel
example : dotted.acl2Count = 5 ∧ (Object.ofParts (Rat.divInt (-1) 2) 2).acl2Count = 6 := by decide

-- The same carrier supplies values to an arity-checked application and the core IF.
private def zpName : Name := ⟨"ACL2", "ZP"⟩
private def signature : Signature := Signature.empty.add zpName 1
private def zpSymbol : signature.Symbol 1 := Signature.empty.addSymbol zpName 1

private theorem zpArity {n : Nat} (f : signature.Symbol n) : n = 1 := by
  have h := f.property
  by_cases hn : f.val = zpName <;> simp_all [signature, Signature.add, Signature.empty]

private def model : Model signature :=
  objectModel signature fun f args => (args ⟨0, zpArity f ▸ Nat.zero_lt_one⟩).zp

private def testTerm : Term signature 1 := .ite (.app zpSymbol (fun _ => .var 0)) .nil (.var 0)

example : (signature.resolve zpName 2).isNone = true := by decide
example : testTerm.eval model (fun _ => half) = Object.nil := by rfl
example : testTerm.eval model (fun _ => .integer 3) = Object.integer 3 := by rfl
example : (Term.ite (.var 0) .truth .nil : Term signature 1).eval model (fun _ => .integer 0)
    = Object.truth := by rfl
example : objectCdrSize.size (objectPrimitives.cdr dotted) < objectCdrSize.size dotted :=
  objectCdrSize.cdr_lt dotted rfl

-- Audit every imported declaration from the public modules, including transitive proof dependencies.
run_elab do
  let env ← Lean.getEnv
  let modules := #[`Silmaril.Logic.ACL2.Standard.Objects.Defs,
    `Silmaril.Logic.ACL2.Standard.Objects.Thms, `Silmaril.Logic.ACL2.Standard.Objects.CdrSize]
  let moduleIndices ← modules.mapM fun m => do
    let some index := env.getModuleIdx? m | throwError "Missing audited module {m}"
    pure index
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants do
    if (env.getModuleIdxFor? name).any moduleIndices.contains then
      for axiomName in ← Lean.collectAxioms name do
        unless allowed.contains axiomName do
          throwError "{name} depends on unapproved axiom {axiomName}"
      count := count + 1
  if count == 0 then throwError "No standard object declarations audited"
  Lean.logInfo m!"Standard ACL2 objects: checked {count} declarations against the three-axiom ceiling"

end Silmaril.Logic.ACL2.Standard.Objects.Tests
