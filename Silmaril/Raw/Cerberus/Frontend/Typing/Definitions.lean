module

public import Silmaril.Cerberus.Frontend.Typing.Expressions.Defs

@[expose] public section
namespace Silmaril.Cerberus.Frontend.Typing
open Silmaril.Cerberus Ail

/-- `genTyping.lem:2153`: one block-scope definition. -/
def annotateDefinition (annotate : AnnotationContext → Expression Unit → TypingM TypedExpression)
    (s : Sigma Unit) (g : Bindings) (d : Sym × Option (Expression Unit)) : TypingM (Sym × Option TypedExpression) := do
  match g.find? (fun p => symbolEqual p.1 d.1) with
  | none => unsupported .unknown "definition missing binding"
  | some (_, (_, _, _, t)) =>
      let e ← d.2.mapM (annotateDefinitionAux annotate s g t)
      return (d.1, e)

/-- `genTyping.lem:2174`: annotate declarations in source order. -/
def annotateDefinitions (annotate : AnnotationContext → Expression Unit → TypingM TypedExpression)
    (s : Sigma Unit) (g : Bindings) (ds : List (Sym × Option (Expression Unit))) :=
  ds.mapM (annotateDefinition annotate s g)

/-- `ailTyping.lem:94`: pairwise distinct symbols, using Lem equality. -/
def disjointBindings : Bindings → Bool
  | [] => true
  | (a, _) :: bs => bs.all (fun p => !symbolEqual a p.1) && disjointBindings bs

/-- `ailTyping.lem:103`: well-formed block bindings, with fresh Lem symbol keys. -/
def wellFormedBindings (s : Sigma Unit) (bs : Bindings) : TypingM Unit := do
  bs.forM fun (_, (_, _, q, t)) => wfLvalue s q t
  if !disjointBindings bs then
    unsupported .unknown "duplicate bindings"

/-- `genTyping.lem:2301`: bind locals in reverse order, as Lem's foldl does. -/
def annotateBlock (stmt : Sigma Unit → Bindings → Ctype → Statement Unit → TypingM TypedStatement)
    (ret : Option Ctype) : AnnotateBlock := fun l s g bs ss => do
  match ret with
  | none => unsupported l "file-scope GNU statement expression (§6.9#1)"
  | some t => ss.mapM (stmt s (bs.reverse ++ g) t)

/-- `genTyping.lem:2187`: annotate a statement node. The remaining diagnostic
printers and declaration checks are not ported. -/
partial def annotateStatement_ (l : Loc) (s : Sigma Unit) (g : Bindings)
    (ret : Ctype) (n : StatementNode Unit) : TypingM (StatementNode GenTypeCategory) := do
  let recurse := fun s g ret (st : Statement Unit) => do
    let .mk sl desug attrs sn := st
    let sn ← annotateStatement_ sl s g ret sn
    pure (Statement.mk sl desug attrs sn)
  let block := annotateBlock recurse (some ret)
  let annotate := annotateExpression block s g
  let sub := recurse s g ret
  show TypingM (StatementNode GenTypeCategory) from do
    match n with
    | .skip => pure .skip
    | .expr e => return .expr (← annotate .other e)
    | .block bs ss =>
        wellFormedBindings s bs
        if bs.any (fun b => s.declarations.any fun d => symbolEqual b.1 d.1) then
          unsupported l "nonfresh block binding"
        return .block bs (← block l s g bs ss)
    | .if_ e a b =>
        let e ← annotate .other e
        add "§6.8.4.1#1"
        if !isScalar (rvalueType e) then constraintViolation e.loc "statement requires expression of scalar type"
        let a ← sub a
        let b ← sub b
        return .if_ e a b
    | .while_ e a id =>
        let e ← annotate .other e
        add "§6.8.5#2"
        if !isScalar (rvalueType e) then constraintViolation e.loc "statement requires expression of scalar type"
        return .while_ e (← sub a) id
    | .do_ a e id =>
        let e ← annotate .other e
        add "§6.8.5#2"
        if !isScalar (rvalueType e) then constraintViolation e.loc "statement requires expression of scalar type"
        return .do_ (← sub a) e id
    | .break_ => pure .break_
    | .continue_ => pure .continue_
    | .returnVoid =>
        if !(match projCtype_ ret with | .void => true | _ => false) then constraintViolation l "void function should not return a value"
        pure .returnVoid
    | .return_ e =>
        if (match projCtype_ ret with | .void => true | _ => false) then constraintViolation l "void function should not return a value"
        return .return_ (← annotateAssignee (annotate .other) s false e.loc ret e)
    | .switch e a =>
        let e ← annotate .other e
        add "§6.8.4.2#1"
        if !isInteger (rvalueType e) then unsupported e.loc "switch control (§6.8.4.2#1)"
        return .switch e (← sub a)
    | .case_ n a => return .case_ n (← sub a)
    | .caseRangeGnu lo hi a => return .caseRangeGnu lo hi (← sub a)
    | .default a => return .default (← sub a)
    | .label x a an => return .label x (← sub a) an
    | .goto x => pure (.goto x)
    | .declaration ds => return .declaration (← annotateDefinitions annotate s g ds)
    | .par ss => return .par (← ss.mapM sub)
    | .regStore r e => return .regStore r (← annotate .other e)
    | .marker id a => return .marker id (← sub a)

/-- `genTyping.lem:2296`: retain the statement's location, provenance and attributes. -/
def annotateStatement (s : Sigma Unit) (g : Bindings) (ret : Ctype) (st : Statement Unit) : TypingM TypedStatement := do
  let .mk l desug attrs n := st
  return .mk l desug attrs (← annotateStatement_ l s g ret n)

/-- `genTyping.lem:2321`: check declarations, then objects, functions and tags in order. -/
def annotateSigma (s : Sigma Unit) : TypingM (Sigma GenTypeCategory) := do
  s.declarations.forM fun (_, (_, _, d)) => match d with
    | .object _ _ q t => wfLvalue s q t
    | .function _ r ps v _ _ => wfType s (.mk [] (.function r ps v))
  let objects ← s.objectDefinitions.mapM fun (x, e) => do
    match s.declarations.find? (fun p => symbolEqual p.1 x) with
    | some (_, (_, _, .object _ _ _ t)) =>
        let e ← annotateDefinitionAux (annotateExpression (annotateBlock annotateStatement none) s []) s [] t e
        return (x, e)
    | _ => unsupported e.loc "object declaration missing"
  let functions ← s.functionDefinitions.mapM fun (x, d) => do
    match s.declarations.find? (fun p => symbolEqual p.1 x) with
    | some (_, (_, _, .function _ (_, r) ps _ _ _)) =>
        let bs := (d.params.zip ps).map fun (x, (q, t, reg)) =>
          (x, ((d.loc, StorageDuration.automatic, reg), (none : Option Alignment), q, t))
        if bs.any (fun b => s.declarations.any fun p => symbolEqual p.1 b.1) then
          unsupported d.loc "nonfresh parameter"
        let body ← annotateStatement s bs.reverse r d.body
        return (x, { loc := d.loc, marker := d.marker, attrs := d.attrs, params := d.params, body := body : FunctionDefinition GenTypeCategory })
    | _ => unsupported d.loc "function declaration missing"
  s.tagDefinitions.forM fun (_, (_, _, d)) => do
    let (ms, flex) := match d with | .struct ms f => (ms, f) | .union ms => (ms, none)
    ms.forM fun (x, (_, _, _q, t)) => do
      add "§6.7.2.1#3"
      if (match d with | .struct .. => true | _ => false) && hasFlexibleArrayMember s t then
        constraintViolation x.loc "struct member has a type with a flexible array member"
      if isFunction t || !isComplete s t then unsupported x.loc "aggregate member (§6.7.2.1#3)"
    ms.forM fun (_, (_, _, q, t)) => wfLvalue s q t
    match flex with
    | none => pure ()
    | some (.mk _ _ q t) => wfLvalue s q (.mk [] (.array t none))
  return {
    declarations := s.declarations, objectDefinitions := objects, functionDefinitions := functions,
    staticAssertions := [], tagDefinitions := s.tagDefinitions, externIdmap := s.externIdmap,
    typedefAttributes := s.typedefAttributes, loopAttributes := s.loopAttributes,
    cnFunctions := s.cnFunctions, cnLemmata := s.cnLemmata, cnPredicates := s.cnPredicates,
    cnDatatypes := s.cnDatatypes, cnDeclSpecs := s.cnDeclSpecs, cnIdents := s.cnIdents }

/-- `genTyping.lem:2413`: startup checks (§5.1.2.2.1), then annotate sigma. -/
def annotateProgram (p : Program Unit) : TypingM TypedProgram := do
  let (startup, s) := p
  if let some x := startup then
    match s.declarations.find? (fun p => symbolEqual p.1 x) with
    | some (_, (l, _, .function _ (q, r) ps _ _ _)) =>
        let validParams := match ps with
          | [] => true
          | [(q, .mk _ .void, _)] => q == noQualifiers
          | [(q, .mk _ (.basic (.integer (.signed .int))), _),
              (q', .mk _ (.pointer q'' (.mk _ (.pointer q''' (.mk _ (.basic (.integer .char)))))), _)] =>
              q == noQualifiers && q' == noQualifiers && q'' == noQualifiers && q''' == noQualifiers
          | _ => false
        if !validParams then unsupported l "main parameters (§5.1.2.2.1)"
        if q != noQualifiers || !(match projCtype_ r with | .basic (.integer (.signed .int)) => true | _ => false) then
          unsupported l "main return type (§5.1.2.2.1)"
    | _ => unsupported .unknown "main declaration (§5.1.2.2.1)"
  return (startup, ← annotateSigma s)

end Silmaril.Cerberus.Frontend.Typing
