-- Structural adaptation of the statement analyses in the pinned C lowerer.
-- Silmaril/Compile/C/ToMir.lean; sha256=8ec7773f7338646762a5b5a9326bfe53d54b7c8ea10a977bb959ab3d80a9baf3.
module

public import Silmaril.Cerberus.Ail.Syntax.Defs
public import Std.Data.HashSet

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false

@[expose] public section
namespace Silmaril.Compiler.Native.Analysis
open Silmaril.Cerberus
open Silmaril.Cerberus.Ail

/-- Collect outer-switch labels in source traversal order. Nested switches,
parallel statements and expressions are not entered, as in the source scanner. -/
def switchCases (statement : TypedStatement) (accumulator : Array (Option (Int × Int))) :
    Array (Option (Int × Int)) :=
  let .mk _ _ _ node := statement
  match node with
  | .case_ value body => switchCases body (accumulator.push (some (value, value)))
  | .caseRangeGnu lower upper body => switchCases body (accumulator.push (some (lower, upper)))
  | .default body => switchCases body (accumulator.push none)
  | .block _ statements => statements.attach.foldl (fun acc child => switchCases child.val acc) accumulator
  | .if_ _ yes no => switchCases no (switchCases yes accumulator)
  | .while_ _ body _ | .do_ body _ _ | .label _ body _ | .marker _ body => switchCases body accumulator
  | _ => accumulator
termination_by sizeOf statement
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have bound := List.sizeOf_lt_of_mem child.property; omega

mutual

/-- The native lowerer's syntactic scan for directly addressed identifier symbols. -/
def addrTakenStatement (statement : TypedStatement) (accumulator : Std.HashSet Nat) : Std.HashSet Nat :=
  let .mk _ _ _ node := statement
  match node with
  | .expr expression | .return_ expression => addrTakenExpression expression accumulator
  | .block _ statements | .par statements =>
      statements.attach.foldl (fun acc child => addrTakenStatement child.val acc) accumulator
  | .if_ condition yes no =>
      addrTakenStatement no (addrTakenStatement yes (addrTakenExpression condition accumulator))
  | .while_ condition body _ | .do_ body condition _ | .switch condition body =>
      addrTakenStatement body (addrTakenExpression condition accumulator)
  | .case_ _ body | .caseRangeGnu _ _ body | .default body | .label _ body _ | .marker _ body =>
      addrTakenStatement body accumulator
  | .declaration declarations => declarations.attach.foldl (fun acc declaration =>
      match _declarationValue : declaration.val.2 with
      | some expression => addrTakenExpression expression acc
      | none => acc) accumulator
  | _ => accumulator
termination_by sizeOf statement
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | have bound := List.sizeOf_lt_of_mem child.property; omega
    | have bound := List.sizeOf_lt_of_mem declaration.property
      rcases declaration with ⟨⟨symbol, value⟩, membership⟩
      simp_all
      omega

/-- Scan all branches of conditional/generic expressions, including unevaluated
operands. This states the inherited traversal, not runtime evaluation or analysis adequacy. -/
def addrTakenExpression (expression : TypedExpression) (accumulator : Std.HashSet Nat) : Std.HashSet Nat :=
  let .mk _ _ _ node := expression
  let accumulator := match node with
    | .unary .address ⟨_, _, _, .ident symbol⟩ => accumulator.insert symbol.number
    | _ => accumulator
  match node with
  | .unary _ operand | .assert operand | .sizeofExpr operand | .annot _ operand | .vaEnd operand
  | .printType operand | .bmcAssume operand | .rvalue operand | .arrayDecay operand
  | .functionDecay operand | .atomic operand | .cast _ _ operand | .memberof operand _
  | .memberofptr operand _ | .compound _ _ operand | .vaArg operand _ | .vaStart operand _ =>
      addrTakenExpression operand accumulator
  | .binary left _ right | .assign left right | .compoundAssign left _ right | .vaCopy left right =>
      addrTakenExpression right (addrTakenExpression left accumulator)
  | .cond condition yes no =>
      let accumulator := addrTakenExpression no (addrTakenExpression condition accumulator)
      match yes with
      | some yes => addrTakenExpression yes accumulator
      | none => accumulator
  | .call function arguments =>
      arguments.attach.foldl (fun acc argument => addrTakenExpression argument.val acc)
        (addrTakenExpression function accumulator)
  | .array _ _ elements => elements.attach.foldl (fun acc element => match _elementValue : element.val with
      | some value => addrTakenExpression value acc
      | none => acc) accumulator
  | .struct _ members => members.attach.foldl (fun acc member => match _memberValue : member.val.2 with
      | some value => addrTakenExpression value acc
      | none => acc) accumulator
  | .union _ _ (some value) => addrTakenExpression value accumulator
  | .generic control _ associations => associations.attach.foldl (fun acc association =>
      match _associationValue : association.val with
      | .type_ _ _ value | .default value => addrTakenExpression value acc)
        (addrTakenExpression control accumulator)
  | .gccStatement _ statements =>
      statements.attach.foldl (fun acc child => addrTakenStatement child.val acc) accumulator
  | _ => accumulator
termination_by sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | have bound := List.sizeOf_lt_of_mem argument.property; omega
    | have bound := List.sizeOf_lt_of_mem child.property; omega
    | have bound := List.sizeOf_lt_of_mem element.property
      rcases element with ⟨value, membership⟩
      simp_all
      omega
    | have bound := List.sizeOf_lt_of_mem member.property
      rcases member with ⟨⟨identifier, value⟩, membership⟩
      simp_all
      omega
    | have bound := List.sizeOf_lt_of_mem association.property
      rcases association with ⟨value, membership⟩
      cases value <;> simp_all
      all_goals omega

end
end Silmaril.Compiler.Native.Analysis
