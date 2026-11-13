module

public import Silmaril.Cerberus.Frontend.Desugar.Initializers.Defs
public import Silmaril.Cerberus.Frontend.Desugar.Declarators.Defs

/-! # Statements

The statements of `cabs_to_ail.lem` at `b3e11ea3`: block-scope declarations
(`desugar_init_declarator_BROKEN`, 2581, and `desugar_declaration_base`, 3528), blocks
(3643), `desugar_statement_aux` (3691-4089), `desugar_statement` (4092) and
`register_labels` (4097), with `Cabs_to_ail_aux.has_continue`. Loops become `while` and
`do` loops whose `continue` jumps to a fresh label at the end of the body; a `for` loop
becomes a block with its first clause and a `while` loop (STD §6.8.5.3).

Not ported yet: static assertions.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend.Desugar

open Silmaril.Cerberus Silmaril.Cerberus.Ail

/-- `AilSyntax.mk_statement` (`ail/ailSyntax.lem:243`). -/
def mkStatement (loc : Loc) (node : StatementNode Unit) : Statement Unit :=
  .mk loc ⟨false, none⟩ noAttributes node

/-- `AilSyntaxAux.mark_as_forloop_body` (`ail/ailSyntaxAux.lem:51`). -/
def markAsForloopBody : Statement Unit → Statement Unit
  | .mk loc info attrs node => .mk loc { info with isForloopBody := true } attrs node

/-- `Cabs_to_ail_aux.has_continue` (`cabs_to_ail_aux.lem:263-307`): whether a `continue`
appears, nested loops included. -/
def hasContinue : Cabs.Statement → Bool
  | .mk _ _ stmt =>
    match stmt with
    | .label _ s | .case_ _ s | .default s | .switch _ s | .while_ _ s | .do_ _ s
    | .for_ _ _ _ s | .caseRangeGnu _ _ s | .marker s => hasContinue s
    | .block ss | .par ss => ss.attach.any fun ⟨s, _⟩ => hasContinue s
    | .if_ _ s₁ none => hasContinue s₁
    | .if_ _ s₁ (some s₂) => hasContinue s₁ || hasContinue s₂
    | .continue_ => true
    | .decl _ | .null | .expr _ | .goto _ | .break_ | .return_ _ | .asm .. => false

/-- `mk_ctype_atomic` (`ctype.lem:280`): an array, function or atomic type is a Lem `error`. -/
def mkCtypeAtomicM (ty : Ctype) : DesugM Ctype :=
  match mkCtypeAtomic ty with
  | some ty' => return ty'
  | none => internalError "Ctyp.mk_ctype_atomic: called on an invalid inner type"

/-- `desugar_init_declarator_BROKEN` (`cabs_to_ail.lem:2581-2626`): the identifier, whether
the declaration is tentative, the qualified type and the postponed initializer of a
block-scope init-declarator; it registers nothing and checks no storage class. -/
def desugarInitDeclaratorBroken (r : Rec) (baseQs : Qualifiers) (baseTy : Ctype)
    (scs : List Cabs.StorageClassSpecifier) : Cabs.InitDeclarator →
    DesugM (Identifier × Bool × (Qualifiers × Ctype) × (Unit → DesugM (Option (Ctype × Expression Unit))))
  | .mk _ decltor none => do
    let scope ← getScope
    let ((_, ident), mkQsCtype) ← r.declarator .notFunDef decltor
    let (qs, ty) := mkQsCtype baseQs baseTy
    -- STD §6.9.2#2, sentence 1
    let isTentative := match scope with
      | .file => isObject ty && (scs.contains .static || scs.isEmpty)
      | _ => false
    return (ident, isTentative, (qs, ty), fun _ => return none)
  | .mk loc decltor (some init) => do
    let scope ← getScope
    let ((_, ident), mkQsCtype) ← r.declarator .notFunDef decltor
    let (qs, ty) := mkQsCtype baseQs baseTy
    let kind : OrdinaryKind := if isFunction ty then .function else .object false
    let link ← determinateLinkage ident .ordinary kind scs
    -- STD §6.7.9#3
    checkInitialisedTypeConstraint loc ty
    -- STD §6.7.9#5
    if isBlockScope scope && (link == .external || link == .internal) then
      constraintViolation (locOfDeclarator decltor) .illegalLinkageAndInitialization
    else
      let mkDesugInit : Unit → DesugM (Option (Ctype × Expression Unit)) := fun _ => do
        return some (← r.wipInitializer loc (determinateStorageDuration link scs) ty init)
      return (ident, false, (qs, ty), mkDesugInit)

/-- The registration of one block-scope init-declarator (the fold of
`desugar_declaration_base`, `cabs_to_ail.lem:3536-3639`): a typedef name, a function
declaration, or an object with its declaration and initializer. A static object gets its
definition (zero without initializer); an automatic one is returned with its initializer. -/
def desugarBlockInitDeclarator (r : Rec) (attrs : Attributes) (specifs : Cabs.Specifiers)
    (specsQs : Qualifiers) (baseTy : Ctype) (acc : List (Sym × Option (Expression Unit)))
    (init : Cabs.InitDeclarator) : DesugM (List (Sym × Option (Expression Unit))) := do
  let .mk scs _ tquals fspecs aspecs := specifs
  let .mk loc _ _ := init
  let (isAtomic, tqualsQs) := translateTypeQualifiers tquals
  let baseQs := combineQualifiers specsQs tqualsQs
  let (ident, isTentative, (qs, ty₀), mkDesugInit) ← desugarInitDeclaratorBroken r baseQs baseTy scs init
  let identLoc := ident.loc
  let cty ← if isAtomic then mkCtypeAtomicM ty₀ else pure ty₀
  if isTentative then
    -- tentative definitions are file-scoped
    internalError "Cabs_to_ail.desugar_declaration_base found a positive is_tentative"
  else if scs == [.typedef] then
    registerTypedef ident attrs qs cty
    return acc
  else
    let doFunction (returnQsTy : Qualifiers × Ctype) (paramsOpt : Option (List (Qualifiers × Ctype × Bool)))
        (isVariadic : Bool) : DesugM (List (Sym × Option (Expression Unit))) := do
      checkStorageClassSpecifiers loc .functionDeclContext scs
      if !aspecs.isEmpty then constraintViolation identLoc (.illegalAlignas .function)
      else
        let (_, sym) ← registerOrdinaryIdentifier ident .function scs
        registerFunctionDeclaration identLoc attrs sym true
          (returnQsTy, paramsOpt, isVariadic, fspecs.contains .inline, fspecs.contains .noreturn)
        return acc
    match cty with
    | .mk _ (.function returnQsTy params isVariadic) => doFunction returnQsTy (some params) isVariadic
    | .mk _ (.functionNoParams returnQsTy) => doFunction returnQsTy none false
    | _ =>
      let isRegister := scs.contains .register
      if isRegister && !aspecs.isEmpty then constraintViolation identLoc (.illegalAlignas .register)
      else
        let alignOpt ← desugarAlignmentSpecifiers r identLoc cty aspecs
        checkStorageClassSpecifiers loc .objectDeclContext scs
        let (link, sym) ← registerOrdinaryIdentifier ident (.object false) scs
        let dur := determinateStorageDuration link scs
        match link with
        | .external =>
          registerExternalObjectDeclaration sym (false, identLoc, attrs, dur, isRegister, alignOpt, qs, cty)
        | _ => registerInternalObjectDeclaration sym (identLoc, dur, isRegister, alignOpt, qs, cty)
        let (ty', ret) ← match ← mkDesugInit () with
          | some (ty', dE) => do
            if !ctypeEqual cty ty' then updateInternalObjectType sym ty'
            match dur with
            | .static =>
              registerGlobalObjectDefinition2 identLoc sym link (.definition dE)
              pure (ty', acc)
            | .thread => internalError "TODO: desugar_declaration_base, Thread duration"
            | .automatic => pure (ty', (sym, some dE) :: acc)
          | none =>
            match dur with
            | .static =>
              if !scs.contains scExtern then
                registerGlobalObjectDefinition sym (.definition (mkZeroInit (← getTagDefinitions) cty))
              pure (cty, acc)
            | .automatic => pure (cty, (sym, none) :: acc)
            | .thread => pure (cty, acc)
        if link == .none_ && (← isIncompleteM ty') then
          undef identLoc .UB059_incomplete_no_linkage_identifier
        else return ret

/-- `desugar_declaration_base` (`cabs_to_ail.lem:3528-3640`): the automatic objects of a
block-scope declaration, in order, with their initializers. -/
def desugarDeclarationBase (r : Rec) (attrs : Attributes) (specifs : Cabs.Specifiers)
    (idecltors : List Cabs.InitDeclarator) : DesugM (List (Sym × Option (Expression Unit))) := do
  let .mk _ tspecs _ _ _ := specifs
  let (specsQs, baseTy) ← r.typeSpecifiers tspecs
  let acc ← idecltors.foldlM (desugarBlockInitDeclarator r attrs specifs specsQs baseTy) []
  return acc.reverse

/-- Whether a desugared statement is dropped from its block, or its body spliced in
(`desugar_block_statement`, `cabs_to_ail.lem:3664-3688`): a skip that the desugaring
introduced, and a block without bindings that it introduced, both without attributes. -/
def flattenBlockItem (cabsStmt : Cabs.Statement) (dStmt : Statement Unit) (acc : List (Statement Unit)) :
    List (Statement Unit) :=
  match cabsStmt, dStmt with
  -- a null statement of the source
  | .mk _ _ .null, .mk _ _ _ .skip => dStmt :: acc
  | _, .mk _ _ attrs .skip => if attrs == noAttributes then acc else dStmt :: acc
  -- a block of the source
  | .mk _ _ (.block _), .mk _ _ _ (.block _ _) => dStmt :: acc
  | _, .mk _ _ attrs (.block [] xs) => if attrs == noAttributes then xs ++ acc else dStmt :: acc
  | _, _ => dStmt :: acc

/-- `desugar_block_statement` (`cabs_to_ail.lem:3643-3688`): the items of a block in a fresh
block scope, with the bindings of its objects without static or thread storage duration. -/
def desugarBlockStatement (self : Cabs.Statement → DesugM (Statement Unit)) (ss : List Cabs.Statement) :
    DesugM (Bindings × List (Statement Unit)) := do
  let scope ← freshBlockScope
  let (bs_, dSs) ← collectWithScope scope (ss.mapM self)
  let bs := bs_.filter fun (_, ((_, dur, _), _)) =>
    match dur with
    | .static | .thread => false
    | _ => true
  let dSs' := (ss.zip dSs).foldr (fun (cabsStmt, dStmt) acc => flattenBlockItem cabsStmt dStmt acc) []
  return (bs, dSs')

/-- `continue` in a loop body: `cont: ;` after the body, as the label of the loop's
continuation (`cabs_to_ail.lem:3792-3802`). -/
def continueLabel (loc : Loc) (contSym : Sym) (loopId : Nat) (s : Statement Unit) : Statement Unit :=
  mkStatement loc (.label contSym s (some (.loopContinue loopId)))

/-- The label that `continue` jumps to in a loop: a fresh `__cerb_continue` label, registered
and resolved (`cabs_to_ail.lem:3770-3773`). -/
def freshContinueLabel (loc : Loc) : DesugM (Identifier × Sym) := do
  let contIdent ← freshify ⟨loc, "__cerb_continue"⟩
  registerLabel contIdent
  let contSym ← resolveLabel contIdent
  return (contIdent, contSym)

/-- The `for` loop whose first clause declares objects (`cabs_to_ail.lem:3836-3943`):
`for (D; E2; E3) S` is `{ D; while (E2) { S; cont: E3; } }`, the declared objects bound in
the outer block. Only `auto` and `register` are allowed (STD §6.8.5#3). -/
def desugarForDecl (r : Rec) (loc declLoc : Loc) (attrsOuter attrs : Attributes)
    (specifs : Cabs.Specifiers) (idecltors : List Cabs.InitDeclarator) (e₂Opt e₃Opt : Option Cabs.Expression)
    (s : Cabs.Statement) : DesugM (StatementNode Unit) := do
  let (contIdent, contSym) ← freshContinueLabel loc
  let ctx' : StmtContext := ⟨some contIdent⟩
  let forScope ← freshBlockScope
  underScope forScope do
    let .mk scs tspecs tquals _ aspecs := specifs
    let (specsQs, baseTy) ← r.typeSpecifiers tspecs
    let (isAtomic, tqualsQs) := translateTypeQualifiers tquals
    let baseQs := combineQualifiers specsQs tqualsQs
    let xs ← idecltors.mapM fun init => do
      let .mk iloc _ _ := init
      checkStorageClassSpecifiers iloc .objectDeclContext scs
      desugarInitDeclarator r attrs isAtomic (!aspecs.isEmpty) baseQs baseTy scs init
    let loopId ← freshInt
    recordLoopAttribute loopId attrsOuter (match e₂Opt with | some e₂ => (locOfExpression e₂) | none => .unknown) loc
    let isRegister := scs.contains .register
    -- Lem folds from the right over the reversed list: in order, each result consed
    let (symDEs, bindings) ← xs.foldlM (init := (([] : List (Sym × Option (Expression Unit))), ([] : Bindings)))
      fun (acc₁, acc₂) opt =>
        match opt with
        -- a typedef
        | none => constraintViolation loc .illegalStorageClassIterationStatement
        | some (identLoc, _, link, sym, isTentative, (qs, ty), mkDesugInit) =>
          if isTentative then
            internalError "Cabs_to_ail.desugar_statement, CabsSfor found a positive is_tentative"
          else if !(scs.isEmpty || scs == [.auto] || scs == [.register]) then
            constraintViolation identLoc .illegalStorageClassIterationStatement
          else match ty with
            | .mk _ (.function ..) => constraintViolation loc .illegalStorageClassIterationStatement
            | _ => do
              let dur := determinateStorageDuration link scs
              let binding := (sym, ((identLoc, dur, isRegister), (none : Option Alignment), qs, ty))
              match ← mkDesugInit () with
              | some (ty', dE) =>
                registerInternalObjectDeclaration sym (identLoc, dur, isRegister, none, qs,
                  if ctypeEqual ty ty' then ty else ty')
                return ((sym, some dE) :: acc₁, binding :: acc₂)
              | none =>
                registerInternalObjectDeclaration sym (identLoc, dur, isRegister, none, qs, ty)
                return (acc₁, binding :: acc₂)
    -- STD §6.8.5.3#2, second sentence
    let dE₂ ← match e₂Opt with
      | some e₂ => r.expression e₂
      | none => pure oneAil
    -- STD §6.8.5#5 the body has its own scope, desugared last (the expressions may declare
    -- enumeration constants)
    let sScope ← freshBlockScope
    let loopAnnot := some (LabelAnnot.loopContinue loopId)
    let dSBody ← match e₃Opt with
      | some e₃ => do
        let dE₃ ← r.expression e₃
        let dS ← underScope sScope (r.statementAux ctx' s)
        let dS := markAsForloopBody dS
        let dSE₃ := mkStatement .unknown (.expr dE₃)
        match dS with
        | .mk sLoc sInfo sAttrs (.block sBindings dSs) =>
          pure (Statement.mk sLoc sInfo sAttrs (.block sBindings (dSs ++ [mkStatement loc (.label contSym dSE₃ loopAnnot)])))
        | _ => pure (mkStatement loc (.block [] [dS, mkStatement loc (.label contSym dSE₃ loopAnnot)]))
      | none => do
        let dS ← underScope sScope (r.statementAux ctx' s)
        let dS := markAsForloopBody dS
        pure (mkStatement loc (.block [] [dS, continueLabel loc contSym loopId (mkStatement loc .skip)]))
    return .block bindings [mkStatement declLoc (.declaration symDEs), mkStatement loc (.while_ dE₂ dSBody loopId)]

/-- The other `for` loops (`cabs_to_ail.lem:3945-4018`): `for (E1; E2; E3) S` is
`{ E1; while (E2) { S; cont: E3; } }`; without a first clause there is no block. -/
def desugarFor (r : Rec) (loc : Loc) (attrs : Attributes) (fcOpt : Option Cabs.ForClause)
    (e₂Opt e₃Opt : Option Cabs.Expression) (s : Cabs.Statement) : DesugM (StatementNode Unit) := do
  let (contIdent, contSym) ← freshContinueLabel loc
  let loopId ← freshInt
  recordLoopAttribute loopId attrs (match e₂Opt with | some e₂ => (locOfExpression e₂) | none => .unknown) loc
  let ctx' : StmtContext := ⟨some contIdent⟩
  -- the statement is not a new block when the body is one
  let mkDSBody (dSE₃ : Statement Unit) : Statement Unit → Statement Unit
    | .mk sLoc sInfo sAttrs (.block bs dSs) => .mk sLoc sInfo sAttrs (.block bs (dSs ++ [dSE₃]))
    | stmt => mkStatement loc (.block [] [stmt, dSE₃])
  -- the expressions and the body are desugared in the order of the syntax
  let forScope ← freshBlockScope
  underScope forScope do
    let mkFor ← match fcOpt with
      | some (.expr e₁) => do
        let dE₁ ← r.expression e₁
        let dSE₁ := mkStatement (locOfExpression e₁) (.expr dE₁)
        pure fun (dE₂ : Expression Unit) (dSE₃ dS : Statement Unit) =>
          StatementNode.block [] [dSE₁, mkStatement loc (.while_ dE₂ (mkDSBody dSE₃ dS) loopId)]
      | some (.decl _ (.base ..)) =>
        internalError "desugar_statement_aux: Just (FC_decl (Declaration_base _ _ _)), _)"
      | some (.decl _ (.staticAssert _)) => notPorted loc "static assertions"
      | none => pure fun dE₂ dSE₃ dS => StatementNode.while_ dE₂ (mkDSBody dSE₃ dS) loopId
    -- STD §6.8.5.3#2, second sentence
    let dE₂ ← match e₂Opt with
      | some e₂ => r.expression e₂
      | none => pure oneAil
    let loopAnnot := some (LabelAnnot.loopContinue loopId)
    let dSE₃ ← match e₃Opt with
      | none => pure (mkStatement loc (.label contSym (mkStatement loc .skip) loopAnnot))
      | some e₃ => do
        let dE₃ ← r.expression e₃
        pure (mkStatement loc (.label contSym (mkStatement (locOfExpression e₃) (.expr dE₃)) loopAnnot))
    let sScope ← freshBlockScope
    let dS ← underScope sScope (r.statementAux ctx' s)
    return mkFor dE₂ dSE₃ (markAsForloopBody dS)

/-- `desugar_statement_aux` (`cabs_to_ail.lem:3691-4089`). -/
def desugarStatementAux (r : Rec) (ctx : StmtContext) : Cabs.Statement → DesugM (Statement Unit)
  | .mk loc attrs stmt_ => do
    let self := r.statementAux ctx
    let desugInfo : DesugInfo := ⟨false, match stmt_ with
      | .for_ .. => some .forloop
      | .continue_ => some .continue_
      | _ => none⟩
    let node ← match stmt_ with
      | .label ident s => do
        let sym ← resolveLabel ident
        let dS ← self s
        pure (.label sym dS none)
      | .case_ e s => do
        let dE ← r.expression e
        let n ← evaluateIntegerConstantExpression (locOfExpression e) none dE
        registerCase (locOfExpression e) (.const n)
        pure (.case_ n (← self s))
      | .default s => do
        registerDefault loc
        pure (.default (← self s))
      | .block ss => do
        let (bs, dSs') ← desugarBlockStatement self ss
        pure (.block bs dSs')
      | .decl (.base dAttrs specifs idecltors) => do
        match ← desugarDeclarationBase r dAttrs specifs idecltors with
        | [] => pure .skip
        | xs => pure (.declaration xs)
      | .decl (.staticAssert _) => notPorted loc "static assertions"
      | .null => pure .skip
      | .expr e => do pure (.expr (← r.expression e))
      -- STD §6.8.4#3 both the if-statement and its sub statements are distinct blocks
      | .if_ e s₁ s₂Opt => do
        let ifScope ← freshBlockScope
        let s₁Scope ← freshBlockScope
        underScope ifScope do
          let dE ← r.expression e
          let dS₁ ← underScope s₁Scope (self s₁)
          let dS₂ ← match s₂Opt with
            | none => pure (mkStatement loc .skip)
            | some z => do
              let s₂Scope ← freshBlockScope
              underScope s₂Scope (self z)
          pure (.if_ dE dS₁ dS₂)
      -- STD §6.8.4#3 both the switch-statement and its sub statement are distinct blocks
      | .switch e s => do
        let switchScope ← freshBlockScope
        let sScope ← freshBlockScope
        underScope switchScope do
          let dE ← r.expression e
          let dS ← underScope sScope (asSwitchBody (self s))
          pure (.switch dE dS)
      -- STD §6.8.5#5 both the while-statement and its body are distinct blocks
      | .while_ e s => do
        let (contIdent, contSym) ← freshContinueLabel loc
        let ctx' : StmtContext := ⟨some contIdent⟩
        let whileScope ← freshBlockScope
        let sScope ← freshBlockScope
        let (dE, dS) ← underScope whileScope do
          let dE ← r.expression e
          let dS ← underScope sScope (r.statementAux ctx' s)
          pure (dE, dS)
        let loopId ← freshInt
        recordLoopAttribute loopId attrs (locOfExpression e) loc
        if hasContinue s then
          -- while (E) S  ==>  while (E) { S; cont: ;}
          pure (.while_ dE (mkStatement loc (.block []
            [dS, continueLabel loc contSym loopId (mkStatement loc .skip)])) loopId)
        else pure (.while_ dE dS loopId)
      | .do_ e s => do
        let (contIdent, contSym) ← freshContinueLabel loc
        let ctx' : StmtContext := ⟨some contIdent⟩
        let whileScope ← freshBlockScope
        let sScope ← freshBlockScope
        let (dE, dS) ← underScope whileScope do
          let dS ← underScope sScope (r.statementAux ctx' s)
          let dE ← r.expression e
          pure (dE, dS)
        let loopId ← freshInt
        recordLoopAttribute loopId attrs (locOfExpression e) loc
        if hasContinue s then
          -- do S (E)  ==>  do { S; cont: ;} (E)
          pure (.do_ (mkStatement loc (.block []
            [dS, continueLabel loc contSym loopId (mkStatement loc .skip)])) dE loopId)
        else pure (.do_ dS dE loopId)
      | .for_ (some (.decl declLoc (.base dAttrs specifs idecltors))) e₂Opt e₃Opt s =>
        desugarForDecl r loc declLoc attrs dAttrs specifs idecltors e₂Opt e₃Opt s
      | .for_ fcOpt e₂Opt e₃Opt s => desugarFor r loc attrs fcOpt e₂Opt e₃Opt s
      | .goto ident => do pure (.goto (← resolveLabel ident))
      | .continue_ =>
        match ctx.contIdentOpt with
        | none => constraintViolation loc .continueOutsideLoop
        | some contIdent => do
          let stmt ← self (.mk loc noAttributes (.goto contIdent))
          pure stmt.node
      | .break_ => do
        if ← isInSwitch then pure .break_
        else match ctx.contIdentOpt with
          | some _ => pure .break_
          | none => constraintViolation loc .breakOutsideSwitchOrLoop
      | .return_ none => do
        match ← getCurrentReturnTypeOpt with
        -- only a file-scope GNU statement expression gets here
        | none => constraintViolation loc .gnuFileScopeStatementExpression
        | some (.mk _ .void) => pure .returnVoid
        | some _ => constraintViolation loc .voidReturnNonVoidFunction
      -- the typing checks that the function is not void
      | .return_ (some e) => do pure (.return_ (← r.expression e))
      | .par ss => do pure (.par (← ss.mapM self))
      -- inline assembly is erased
      | .asm .. => pure .skip
      | .caseRangeGnu e₁ e₂ s => do
        let desugarCaseConstant (e : Cabs.Expression) : DesugM Int := do
          evaluateIntegerConstantExpression (locOfExpression e) none (← r.expression e)
        if ← isInSwitch then
          let n₁ ← desugarCaseConstant e₁
          let n₂ ← desugarCaseConstant e₂
          registerCase (bboxLocation [locOfExpression e₁, locOfExpression e₂]) (.range n₁ n₂)
          if n₁ ≤ n₂ then pure (.caseRangeGnu n₁ n₂ (← self s))
          -- an empty range is discarded, with a warning
          else pure .skip
        else constraintViolation loc .labelStatementOutsideSwitch
      | .marker s => do
        let id ← recordMarker
        pure (.marker id (← self s))
    return .mk loc desugInfo attrs node

/-- `desugar_statement` (`cabs_to_ail.lem:4092`): outside any loop. -/
def desugarStatement (r : Rec) (stmt : Cabs.Statement) : DesugM (Statement Unit) :=
  r.statementAux ⟨none⟩ stmt

/-- `register_labels` (`cabs_to_ail.lem:4097-4146`): the labels of a function body, before it
is desugared, so that `goto` can jump forward (STD §6.2.1#3). -/
def registerLabels : Cabs.Statement → DesugM Unit
  | .mk _ _ stmt =>
    match stmt with
    | .label ident s => do
      registerLabel ident
      registerLabels s
    | .case_ _ s | .default s | .switch _ s | .while_ _ s | .do_ _ s | .for_ _ _ _ s
    | .caseRangeGnu _ _ s | .marker s => registerLabels s
    | .block ss => ss.attach.forM fun ⟨s, _⟩ => registerLabels s
    | .if_ _ s₁ s₂Opt => do
      registerLabels s₁
      match s₂Opt with
      | some s₂ => registerLabels s₂
      | none => return ()
    | .decl _ | .null | .expr _ | .goto _ | .continue_ | .break_ | .return_ _ | .par _ | .asm .. =>
      return ()

end Silmaril.Cerberus.Frontend.Desugar
