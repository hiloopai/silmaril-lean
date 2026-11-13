module

public import Silmaril.Cerberus.Frontend.Declarations.Defs

/-! # Expressions: `c_parser.mly:493-829` (§6.5–6.6)

Primary and postfix expressions, unary operators and casts, precedence climbing for
binary operators, conditionals, assignments and commas. All regions span the consumed
tokens; parenthesized expressions replace the inner region. The wire drops cursors.
The boolean returned by cast, binary and conditional parsing records whether the
production is also a `unary_expression`, as required on the left of an assignment.
This is a grammar restriction, not an lvalue check: `(a+b)=c` parses, `a+b=c` does not.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend.Expressions

open Silmaril.Cerberus Cabs P

/-- `generic_association` (`c_parser.mly:530-535`). -/
def genericAssociation (r : Rec) : P GenericAssociation := do
  if ← eatKeywordDefault then
    let _ ← expectPunct .colon
    return .default (← r.assignmentExpression)
  let ty ← r.typeName
  let _ ← expectPunct .colon
  return .type_ ty (← r.assignmentExpression)
where
  eatKeywordDefault : P Bool := do
    if ← atKeyword .default then let _ ← advance; return true
    return false

/-- `generic_selection` and its deliberately reversed `generic_assoc_list`
(`c_parser.mly:517-535`). -/
def genericSelection (r : Rec) : P Expression := do
  let t ← expectKeyword .generic
  let _ ← expectPunct .lparen
  let e ← r.assignmentExpression
  let _ ← expectPunct .comma
  let gas ← sepBy1 .comma (genericAssociation r)
  let _ ← expectPunct .rparen
  return .mk (t.start.region (← endPos)) (.generic e gas.toList.reverse)

/-- `primary_expression` (`c_parser.mly:493-515`). Identifier payloads are points.
The GNU statement-expression rule uses the block items without saving a scope. -/
def primaryExpression (r : Rec) : P Expression := do
  let t ← peek
  match t.kind with
  | .name x =>
    if (← env).isTypedef x then fail "unexpected type name"
    let _ ← advance
    return .mk (t.start.region t.stop) (.ident ⟨t.start.point, x⟩)
  | .constant c =>
    let _ ← advance
    return .mk (t.start.region t.stop) (.const c)
  | .string .. =>
    let s ← stringLiteral
    return .mk (t.start.region (← endPos)) (.string s)
  | .keyword .generic => genericSelection r
  | .punct .lparen =>
    let _ ← advance
    if ← atPunct .lbrace then
      let .mk _ _ stmt ← r.compoundStatement
      let .block items := stmt | fail "expected a block"
      let _ ← expectPunct .rparen
      return .mk (t.start.region (← endPos)) (.gccStatement items)
    let .mk _ e ← r.expression
    let _ ← expectPunct .rparen
    return .mk (t.start.region (← endPos)) e
  | _ => fail "expected a primary expression"

/-- Builtin alternatives of `postfix_expression` (`c_parser.mly:563-594`). Each
keyword has its own argument grammar; ordinary call syntax cannot replace it. -/
def builtinExpression (r : Rec) : P Expression := do
  let t ← advance
  let _ ← expectPunct .lparen
  let node ← match t.kind with
    | .keyword .assert => pure (.assert (← r.assignmentExpression))
    | .keyword .bmcAssume => pure (.bmcAssume (← r.assignmentExpression))
    | .keyword .printType => pure (.printType (← r.expression))
    | .keyword .vaEnd => pure (.vaEnd (← r.assignmentExpression))
    | .keyword .vaStart => do
      let e ← r.assignmentExpression
      let _ ← expectPunct .comma
      pure (.vaStart e (← Declarations.generalIdentifier))
    | .keyword .vaCopy => do
      let e ← r.assignmentExpression
      let _ ← expectPunct .comma
      pure (.vaCopy e (← r.assignmentExpression))
    | .keyword .vaArg => do
      let e ← r.assignmentExpression
      let _ ← expectPunct .comma
      pure (.vaArg e (← r.typeName))
    | .keyword .offsetof => do
      let ty ← r.typeName
      let _ ← expectPunct .comma
      pure (.offsetof ty (← Declarations.generalIdentifier))
    | .keyword .builtinTypesCompatibleP => do
      let ty ← r.typeName
      let _ ← expectPunct .comma
      pure (.builtinGnu (.typesCompatibleP ty (← r.typeName)))
    | .keyword .builtinChooseExpr => do
      let c ← r.assignmentExpression
      let _ ← expectPunct .comma
      let a ← r.assignmentExpression
      let _ ← expectPunct .comma
      pure (.builtinGnu (.chooseExpr c a (← r.assignmentExpression)))
    | _ => fail "expected an expression builtin"
  let _ ← expectPunct .rparen
  return .mk (t.start.region (← endPos)) node

/-- Whether a token starts one of the builtin postfix productions. -/
def isBuiltin (t : Token) : Bool :=
  match t.kind with
  | .keyword k => match k with
    | .assert | .bmcAssume | .printType | .vaStart | .vaCopy | .vaArg | .vaEnd |
        .offsetof | .builtinTypesCompatibleP | .builtinChooseExpr => true
    | _ => false
  | _ => false

/-- The suffix loop of `postfix_expression` (`c_parser.mly:541-558`), with arguments
in source order and member identifiers as regions. -/
def postfixRest (r : Rec) (start : Pos) (first : Expression) : P Expression := do
  let mut e := first
  for _ in [0:(← get).toks.size + 1] do
    let t ← peek
    let node ← match t.kind with
      | .punct .lbrack => do
        let _ ← advance
        let ix ← r.expression
        let _ ← expectPunct .rbrack
        pure (.subscript e ix)
      | .punct .lparen => do
        let _ ← advance
        let args ← if (← atPunct .rparen) then pure #[]
          else sepBy1 .comma r.assignmentExpression
        let _ ← expectPunct .rparen
        pure (.call e args.toList none)
      | .punct .dot => do
        let _ ← advance
        pure (.memberof e (← Declarations.generalIdentifier))
      | .punct .minusGt => do
        let _ ← advance
        pure (.memberofptr e (← Declarations.generalIdentifier))
      | .punct .plusPlus => do let _ ← advance; pure (.postincr e)
      | .punct .minusMinus => do let _ ← advance; pure (.postdecr e)
      | _ => break
    e := .mk (start.region (← endPos)) node
  return e

/-- `( type_name )` (`c_parser.mly:559,620,623,650`). -/
def parenthesizedTypeName (r : Rec) : P TypeName := do
  let _ ← expectPunct .lparen
  let ty ← r.typeName
  let _ ← expectPunct .rparen
  return ty

/-- A type name after `(` is distinguished by the current typedef environment. -/
def startsParenthesizedType : P Bool := do
  return isPunct (← peek) .lparen && (← Declarations.startsTypeName (← peekAt 1))

/-- The compound-literal production of `postfix_expression`, after `(type)`
(`c_parser.mly:559-561`). Reuse the declaration grammar's nonempty braced list. -/
def compoundLiteral (r : Rec) (start : Pos) (ty : TypeName) : P Expression := do
  if !(← atPunct .lbrace) then fail "expected a compound literal"
  let .list _ inits ← r.initr | fail "expected a braced list"
  let e := Expression.mk (start.region (← endPos)) (.compound ty inits)
  postfixRest r start e

/-- `postfix_expression` (`c_parser.mly:538-595`). -/
def postfixExpression (r : Rec) : P Expression := do
  let start ← startPos
  if ← startsParenthesizedType then
    let ty ← parenthesizedTypeName r
    return ← compoundLiteral r start ty
  let e ← if isBuiltin (← peek) then builtinExpression r else primaryExpression r
  postfixRest r start e

/-- `unary_operator` (`c_parser.mly:631-644`). -/
def unaryOperator? (t : Token) : Option UnaryOperator :=
  match t.kind with
  | .punct .ampersand => some .address
  | .punct .star => some .indirection
  | .punct .plus => some .plus
  | .punct .minus => some .minus
  | .punct .tilde => some .bnot
  | .punct .bang => some .not
  | _ => none

/-- `unary_expression` (`c_parser.mly:605-629`). Prefix increment and sizeof take
unary operands, whereas the other unary operators permit casts. -/
def unaryExpression (r : Rec) : P Expression := do
  let t ← peek
  if let some op := unaryOperator? t then
    let _ ← advance
    let (e, _) ← r.castExpression
    return .mk (t.start.region (← endPos)) (.unary op e)
  let node ← match t.kind with
    | .punct .plusPlus => do let _ ← advance; pure (.preincr (← r.unaryExpression))
    | .punct .minusMinus => do let _ ← advance; pure (.predecr (← r.unaryExpression))
    | .punct .ampersandAmpersand => do
      let _ ← advance
      pure (.labelAddressGnu (← Declarations.generalIdentifier))
    | .keyword .sizeof => do
      let _ ← advance
      if ← startsParenthesizedType then
        let start ← startPos
        let ty ← parenthesizedTypeName r
        if ← atPunct .lbrace then
          pure (.sizeofExpr (← compoundLiteral r start ty))
        else pure (.sizeofType ty)
      else pure (.sizeofExpr (← r.unaryExpression))
    | .keyword .alignof => do
      let _ ← advance
      pure (.alignof (← parenthesizedTypeName r))
    | _ => return ← postfixExpression r
  return .mk (t.start.region (← endPos)) node

/-- `cast_expression` (`c_parser.mly:647-653`). A compound literal is unary; a cast
is not. This remains true even when both begin with the same `(type)` tokens. -/
def castExpression (r : Rec) : P (Expression × Bool) := do
  if ← startsParenthesizedType then
    let start ← startPos
    let ty ← parenthesizedTypeName r
    if ← atPunct .lbrace then return (← compoundLiteral r start ty, true)
    let (e, _) ← r.castExpression
    return (.mk (start.region (← endPos)) (.cast ty e), false)
  return (← unaryExpression r, true)

/-- Binary levels of `c_parser.mly:656-767`: `multiplicative_expression` (10),
`additive_expression` (9), `shift_expression` (8), `relational_expression` (7),
`equality_expression` (6), `_AND_expression` (5), `exclusive_OR_expression` (4),
`inclusive_OR_expression` (3), `logical_AND_expression` (2), `logical_OR_expression` (1). -/
def binaryOperator? (t : Token) : Option (Nat × BinaryOperator) :=
  match t.kind with
  | .punct .star => some (10, .mul)
  | .punct .slash => some (10, .div)
  | .punct .percent => some (10, .mod)
  | .punct .plus => some (9, .add)
  | .punct .minus => some (9, .sub)
  | .punct .ltLt => some (8, .shl)
  | .punct .gtGt => some (8, .shr)
  | .punct .lt => some (7, .lt)
  | .punct .gt => some (7, .gt)
  | .punct .ltEq => some (7, .le)
  | .punct .gtEq => some (7, .ge)
  | .punct .eqEq => some (6, .eq)
  | .punct .bangEq => some (6, .ne)
  | .punct .ampersand => some (5, .band)
  | .punct .caret => some (4, .bxor)
  | .punct .pipe => some (3, .bor)
  | .punct .ampersandAmpersand => some (2, .and)
  | .punct .pipePipe => some (1, .or)
  | _ => none

/-- Precedence climbing over the binary nonterminals (`c_parser.mly:656-767`).
Each level is left associative; right operands start at the next tighter level.
Every operator is consumed once and the precedence recursion has at most ten levels. -/
def binaryExpression (r : Rec) (minimum : Nat) : P (Expression × Bool) := do
  let start ← startPos
  let mut result ← r.castExpression
  for _ in [0:(← get).toks.size + 1] do
    let some (prec, op) := binaryOperator? (← peek) | break
    if prec < minimum then break
    let _ ← advance
    let (rhs, _) ← r.binaryExpression (prec + 1)
    result := (.mk (start.region (← endPos)) (.binary op result.1 rhs), false)
  return result

/-- `conditional_expression` (`c_parser.mly:770-780`), including the adjacent GNU
`?:` token. The middle operand is a full expression; the last is conditional only. -/
def conditionalExpression (r : Rec) : P (Expression × Bool) := do
  let start ← startPos
  let (c, unary) ← binaryExpression r 1
  if ← eatPunct .question then
    let yes ← r.expression
    let _ ← expectPunct .colon
    let (no, _) ← r.conditionalExpression
    return (.mk (start.region (← endPos)) (.cond c yes no), false)
  if ← eatPunct .questionColon then
    let (no, _) ← r.conditionalExpression
    return (.mk (start.region (← endPos)) (.condGnu c no), false)
  return (c, unary)

/-- `assignment_operator` (`c_parser.mly:791-814`). -/
def assignmentOperator? (t : Token) : Option AssignmentOperator :=
  match t.kind with
  | .punct .eq => some .assign
  | .punct .starEq => some .mul
  | .punct .slashEq => some .div
  | .punct .percentEq => some .mod
  | .punct .plusEq => some .add
  | .punct .minusEq => some .sub
  | .punct .ltLtEq => some .shl
  | .punct .gtGtEq => some .shr
  | .punct .ampersandEq => some .band
  | .punct .caretEq => some .bxor
  | .punct .pipeEq => some .bor
  | _ => none

/-- `assignment_expression` (`c_parser.mly:783-789`): right associative, with a
syntactically unary left operand. Parentheses can make any expression unary. -/
def assignmentExpression (r : Rec) : P Expression := do
  let start ← startPos
  let (lhs, unary) ← conditionalExpression r
  if let some op := assignmentOperator? (← peek) then
    if !unary then fail "assignment requires a unary left operand"
    let _ ← advance
    let rhs ← r.assignmentExpression
    return .mk (start.region (← endPos)) (.assign op lhs rhs)
  return lhs

/-- `constant_expression` (`c_parser.mly:826-829`) permits conditionals only. -/
def constantExpression (r : Rec) : P Expression := do
  return (← conditionalExpression r).1

/-- `expression` (`c_parser.mly:817-823`): left associative comma expressions. -/
def expression (r : Rec) : P Expression := do
  let start ← startPos
  let mut e ← assignmentExpression r
  for _ in [0:(← get).toks.size + 1] do
    if !(← eatPunct .comma) then break
    let rhs ← r.assignmentExpression
    e := .mk (start.region (← endPos)) (.comma e rhs)
  return e

end Silmaril.Cerberus.Frontend.Expressions
