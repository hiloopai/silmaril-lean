module

public import Silmaril.Cerberus.Frontend.Declarations.Defs

/-! # Statements: `c_parser.mly:1298-1552` (§6.8 and GNU assembly)

Blocks use a loop for their items. Recursive statements pass through `Rec`; contexts
are saved at exactly the `scoped` grammar occurrences. A compound statement itself
does not save a context: function bodies and GNU statement expressions call it directly.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend.Statements

open Silmaril.Cerberus Cabs P

/-- `scoped(X)` (`c_parser.mly:472-475`). -/
def withContext {α : Type} (p : P α) : P α := do
  let ctxt ← env
  let x ← p
  setEnv ctxt
  return x

/-- A general identifier followed by `:` starts a label even if it is a typedef
name (`c_parser.mly:1314-1320`). -/
def startsLabel : P Bool := do
  match (← peek).kind with
  | .name _ => return isPunct (← peekAt 1) .colon
  | _ => return false

/-- Distinguish a block declaration from a statement, looking through leading
attributes without changing the parser state (`c_parser.mly:1358-1376`). -/
def startsBlockDeclaration : P Bool := do
  let saved ← get
  let attrs ← Declarations.attributeSpecifierSequence
  let yes ← if (← startsLabel) then pure false
    else if !attrs.isEmpty && (← atPunct .semicolon) then pure true
    else Declarations.startsDeclaration (← peek)
  set saved
  return yes

/-- `block_item`: declarations keep their entire region, including attributes and
semicolon (`c_parser.mly:1358-1365`). -/
def blockItem (r : Rec) : P Statement := do
  if ← startsBlockDeclaration then
    let start ← startPos
    let d ← Declarations.declaration r
    return .mk (start.region (← endPos)) (.mk []) (.decl d)
  r.statement

/-- `compound_statement`, including the cppmem parallel alternative
(`c_parser.mly:1349-1356`). -/
def compoundStatement (r : Rec) : P Statement := do
  let t ← advance
  let node ← if isPunct t .lbrace then do
      let items ← manyWhile (return !(← atPunct .rbrace)) (blockItem r)
      let _ ← expectPunct .rbrace
      pure (.block items.toList)
    else if isPunct t .lbraces then do
      let stmts ← sepBy1 .pipes r.statement
      let _ ← expectPunct .rbraces
      pure (.par stmts.toList)
    else fail "expected a compound statement"
  return .mk (t.start.region (← endPos)) (.mk []) node

/-- `expression?` before the given delimiter (`c_parser.mly:1383,1436-1443,1463`). -/
def optionalExpression (r : Rec) (delimiter : Punct) : P (Option Expression) := do
  if ← atPunct delimiter then return none
  return some (← r.expression)

/-- The parenthesized controlling expression of a selection or loop
(`c_parser.mly:1397-1421`). -/
def controllingExpression (r : Rec) : P Expression := do
  let _ ← expectPunct .lparen
  let e ← r.expression
  let _ ← expectPunct .rparen
  return e

/-- `selection_statement` and `iteration_statement` after the keyword. Bodies use
`scoped(statement)`; the caller scopes the whole production (`c_parser.mly:1397-1446`). -/
def controlStatement (r : Rec) (k : Keyword) : P StatementNode := do
  match k with
  | .if_ =>
    let e ← controllingExpression r
    let yes ← withContext r.statement
    let no ← if (← atKeyword .else_) then do
        let _ ← advance
        pure (some (← withContext r.statement))
      else pure none
    return .if_ e yes no
  | .switch => return .switch (← controllingExpression r) (← withContext r.statement)
  | .while_ => return .while_ (← controllingExpression r) (← withContext r.statement)
  | .do_ =>
    let body ← withContext r.statement
    let _ ← expectKeyword .while_
    let e ← controllingExpression r
    let _ ← expectPunct .semicolon
    return .do_ e body
  | .for_ =>
    let _ ← expectPunct .lparen
    let init ← if (← Declarations.startsDeclaration (← peek)) then do
        let start ← startPos
        let d ← Declarations.declaration r
        pure (some (.decl (start.region (← endPos)) d))
      else do
        let e ← optionalExpression r .semicolon
        let _ ← expectPunct .semicolon
        pure (e.map ForClause.expr)
    let cond ← optionalExpression r .semicolon
    let _ ← expectPunct .semicolon
    let step ← optionalExpression r .rparen
    let _ ← expectPunct .rparen
    return .for_ init cond step (← withContext r.statement)
  | _ => fail "expected a selection or iteration statement"

/-- `jump_statement` after its keyword (`c_parser.mly:1450-1468`). -/
def jumpStatement (r : Rec) (k : Keyword) : P StatementNode := do
  let node ← match k with
    | .goto => pure (.goto (← Declarations.generalIdentifier))
    | .continue_ => pure .continue_
    | .break_ => pure .break_
    | .return_ => pure (.return_ (← optionalExpression r .semicolon))
    | _ => fail "expected a jump statement"
  let _ ← expectPunct .semicolon
  return node

/-- `asm_label`: `NAME VARIABLE`, not a typedef name (`c_parser.mly:1496-1498`).
The same restriction applies to a symbolic operand name. -/
def asmLabel : P Unit := do
  let some (_, false) ← nameOf (← peek) | fail "expected an assembly identifier"
  let _ ← advance

/-- `asm_output_input` (`c_parser.mly:1487-1490`). Parse and drop the optional
symbolic name, constraint string and full expression, retaining context changes. -/
def asmOutputInput (r : Rec) : P Unit := do
  if ← eatPunct .lbrack then
    asmLabel
    let _ ← expectPunct .rbrack
  let _ ← stringLiteral
  let _ ← expectPunct .lparen
  let _ ← r.expression
  let _ ← expectPunct .rparen

/-- `separated_list(COMMA, asm_output_input)` in `asm_with_output` and
`asm_with_input` (`c_parser.mly:1500-1520`). -/
def asmOperands (r : Rec) : P Unit := do
  if isStringToken (← peek) || (← atPunct .lbrack) then
    let _ ← sepBy1 .comma (asmOutputInput r)

/-- `asm_clobber` and its comma-separated list (`c_parser.mly:1492-1494,1522-1530`). -/
def asmClobbers : P Unit := do
  if isStringToken (← peek) then
    let _ ← sepBy1 .comma stringLiteral

/-- `asm_with_labels`: zero or more `asm_label`s, with no commas
(`c_parser.mly:1532-1534`). -/
def asmLabels : P Unit := do
  let _ ← manyWhile (return (← nameOf (← peek)).isSome) asmLabel

/-- Whether a token is an `asm_qualifier` (`c_parser.mly:1477-1485`). -/
def isAsmQualifier (t : Token) : Bool :=
  isKeyword t .volatile || isKeyword t .asmVolatile ||
    isKeyword t .inline || isKeyword t .goto

/-- `asm_statement` (`c_parser.mly:1536-1552`). Qualifiers may repeat in any
order. Only volatility, inline and the unprefixed template's raw pieces survive;
the four optional colon sections are parsed with their own grammar and dropped. -/
def asmStatement (r : Rec) : P StatementNode := do
  let _ ← expectKeyword .asm
  let qs ← manyWhile (return isAsmQualifier (← peek)) advance
  let _ ← expectPunct .lparen
  let (pfx, strs) ← stringLiteral
  if ← eatPunct .colon then
    asmOperands r
    if ← eatPunct .colon then
      asmOperands r
      if ← eatPunct .colon then
        asmClobbers
        if ← eatPunct .colon then asmLabels
  let _ ← expectPunct .rparen
  let _ ← expectPunct .semicolon
  if pfx.isSome then fail "encoding prefix in assembly template"
  return .asm (qs.any fun t => isKeyword t .volatile || isKeyword t .asmVolatile)
    (qs.any fun t => isKeyword t .inline) strs

/-- `expression_statement` (`c_parser.mly:1382-1393`). -/
def expressionStatement (r : Rec) (previous attrStart : Pos)
    (groups : List (List Attribute)) : P Statement := do
  let start ← startPos
  if ← eatPunct .semicolon then
    if !groups.isEmpty then fail "attributes require an expression"
    return .mk (previous.region (← endPos)) (.mk []) .null
  let e ← r.expression
  let _ ← expectPunct .semicolon
  let start := if groups.isEmpty then start else attrStart
  return .mk (start.region (← endPos)) (Declarations.toAttrs groups) (.expr e)

/-- `statement` and `labeled_statement` (`c_parser.mly:1298-1345`). Attributes
on compound/control/jump statements do not widen the region; attributes on an
expression statement do. Null statements start at the previous token's end. -/
def statement (r : Rec) : P Statement := do
  let previous ← endPos
  let attrStart ← startPos
  let groups ← Declarations.attributeSpecifierSequence
  let attrs := Declarations.toAttrs groups
  let t ← peek
  if ← startsLabel then
    let id ← Declarations.generalIdentifier
    let _ ← expectPunct .colon
    let body ← r.statement
    return .mk (t.start.region (← endPos)) attrs (.label id body)
  if isKeyword t .case_ then
    let _ ← advance
    let lo ← r.constantExpression
    let hi ← if (← eatPunct .ellipsis) then some <$> r.constantExpression else pure none
    let _ ← expectPunct .colon
    let body ← r.statement
    let node := match hi with
      | none => StatementNode.case_ lo body
      | some hi => .caseRangeGnu lo hi body
    return .mk (t.start.region (← endPos)) attrs node
  if isKeyword t .default then
    let _ ← advance
    let _ ← expectPunct .colon
    let body ← r.statement
    return .mk (t.start.region (← endPos)) attrs (.default body)
  if isPunct t .lbrace || isPunct t .lbraces then
    let .mk loc (.mk inner) node ← withContext r.compoundStatement
    let .mk outer := attrs
    return .mk loc (.mk (inner ++ outer)) node
  let node ← match t.kind with
    | .keyword k =>
      if k == .asm then do
        if !groups.isEmpty then fail "attributes before assembly"
        asmStatement r
      else if k == .if_ || k == .switch || k == .while_ || k == .do_ || k == .for_ then do
        let _ ← advance
        withContext (controlStatement r k)
      else if k == .goto || k == .continue_ || k == .break_ || k == .return_ then do
        let _ ← advance
        jumpStatement r k
      else return ← expressionStatement r previous attrStart groups
    | _ => return ← expressionStatement r previous attrStart groups
  return .mk (t.start.region (← endPos)) attrs node
end Silmaril.Cerberus.Frontend.Statements
