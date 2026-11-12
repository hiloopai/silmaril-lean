module

public import Silmaril.Cerberus.Frontend.Desugar.Effect.Defs

/-! # Aggregate and union initializers: `Desugaring_init`

A port of `frontend/model/desugaring_init.lem` at `b3e11ea3`: the interpretation of a braced
initializer (STD §6.7.9#17-#22) as a cursor walking the current object, which designators
move (STD §6.7.9#6-#7), then the value built from the map of initialised leaves, with zero for
the others (STD §6.7.9#10, #21). `desugarAggregateInitialiser` is the last case of
`wip_desugar_initializer_` (`cabs_to_ail.lem:3463-3497`), the only caller.

The interpretation fails in three ways, as in Lem: a desugaring error (a constraint
violation), Lem's `error` (Cerberus crashes: `internalError`), and Lem's `internal_error`, an
`Errors.INTERNAL_ERROR` that `wip_desugar_initializer_` catches to produce an `AilEinvalid`
node (the oracle prints it for many csmith programs). The last is a reject with the stage
`initStage`, never seen outside this file.

The desugaring functions the interpretation needs come in a record, as Lem's
`desugaring_init_funcs`, so that this file depends only on the desugaring state.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend.Desugar

open Silmaril.Cerberus Silmaril.Cerberus.Ail

/-- Where the cursor is in an array (the index and the size, `none` for a top-level array of
unknown size), a struct (the members before, the current one and those after) or a union
(the current member). Lem: `init_cursor_kind` (`desugaring_init.lem:8`). -/
inductive InitCursorKind where
  | array (currentIdx : Int) (size : Option Int)
  | struct (tagSym : Sym) (prev : List (Identifier × Ctype)) (current : Identifier)
      (next : List (Identifier × Ctype))
  | union (tagSym : Sym) (member : Identifier)

/-- One level of the cursor: whether a `{ … }` was entered at it, and whether it overflowed
its array or struct. Lem: `init_cursor_elem` (`desugaring_init.lem:13`). -/
structure InitCursorElem where
  isBlock : Bool
  isOverflowing : Bool
  kind : InitCursorKind

/-- The position of the cursor: the type of the current `{ … }`, the type at the cursor and
the cursor, innermost level first. Lem: `init_position` (`desugaring_init.lem:19`). -/
structure InitPosition where
  blockTy : Ctype
  ty : Ctype
  cursor : List InitCursorElem
  inBlock : Bool

/-- `mark_as_overflowing` (`desugaring_init.lem:26`). -/
def markAsOverflowing (pos : InitPosition) : InitPosition :=
  match pos.cursor with
  | elem :: cursor' => { pos with cursor := { elem with isOverflowing := true } :: cursor' }
  | _ => pos

/-- `unmark_as_overflowing` (`desugaring_init.lem:35`). -/
def unmarkAsOverflowing (pos : InitPosition) : InitPosition :=
  match pos.cursor with
  | elem :: cursor' => { pos with cursor := { elem with isOverflowing := false } :: cursor' }
  | _ => pos

/-- `cursor_overflowing` (`desugaring_init.lem:44`). -/
def cursorOverflowing : List InitCursorElem → Bool
  | [] => false
  | elem :: _ => elem.isOverflowing

/-- The result of a pure cursor operation: Lem's `desug_init_error` (`desugaring_init.lem:70`),
with Lem's `error` (Cerberus crashes) as one more case, `crash`. -/
inductive DesugInitResult (α : Type) where
  | internalError (msg : String)
  | nothing
  | ok (a : α)
  | crash (msg : String)

/-- `desug_init_bind` (`desugaring_init.lem:74`). -/
def DesugInitResult.bind {α β : Type} (m : DesugInitResult α) (f : α → DesugInitResult β) :
    DesugInitResult β :=
  match m with
  | .internalError msg => .internalError msg
  | .nothing => .nothing
  | .ok a => f a
  | .crash msg => .crash msg

/-- The members of a struct, the first apart, with their types, and its flexible array member.
Lem: `lookup_struct_members` (`desugaring_init.lem:50`), whose `error` is `crash`. -/
def lookupStructMembers (tagDefs : SymMap TagDefinition) (tagSym : Sym) :
    DesugInitResult ((Identifier × Ctype) × List (Identifier × Ctype) × Option FlexibleArrayMember) :=
  let aux : Identifier × (Attributes × Option Alignment × Qualifiers × Ctype) → Identifier × Ctype :=
    fun (ident, (_, _, _, ty)) => (ident, ty)
  match tagDefs.get? tagSym with
  | some (.struct _ _ _ (x :: xs) flexOpt) => .ok (aux x, xs.map aux, flexOpt)
  | _ => .crash "Desugaring_init.lookup_struct_members: Nothing or empty Struct definition"

/-- The members of a union, the first apart, with their types. Lem: `lookup_union_members`
(`desugaring_init.lem:60`), whose `error` is `crash`. -/
def lookupUnionMembers (tagDefs : SymMap TagDefinition) (tagSym : Sym) :
    DesugInitResult ((Identifier × Ctype) × List (Identifier × Ctype)) :=
  let aux : Identifier × (Attributes × Option Alignment × Qualifiers × Ctype) → Identifier × Ctype :=
    fun (ident, (_, _, _, ty)) => (ident, ty)
  match tagDefs.get? tagSym with
  | some (.union _ _ _ (x :: xs)) => .ok (aux x, xs.map aux)
  | _ => .crash "Desugaring_init.lookup_union_members: Nothing or empty Union definition"

/-- `go_down_aux` (`desugaring_init.lem:85`): move the cursor into the first element or member
of the aggregate or union at it; nothing at a scalar. Lem's message for other types prints the
type (`Pp.stringFromAil_ctype`), which is not ported: the `Option` is `none` then. -/
def goDownAux (tagDefs : SymMap TagDefinition) (enteringBlock : Bool) (pos : InitPosition) :
    Option (DesugInitResult InitPosition) :=
  if cursorOverflowing pos.cursor then
    -- OVERFLOWING
    some .nothing
  else
    let mkCursorElem (kind : InitCursorKind) : InitCursorElem := ⟨enteringBlock, false, kind⟩
    match unatomic pos.ty with
    | .mk _ (.basic _) => some .nothing
    | .mk _ (.pointer _ _) => some .nothing
    | .mk _ (.array elemTy sizeOpt) =>
      some (.ok { pos with ty := elemTy, cursor := mkCursorElem (.array 0 sizeOpt) :: pos.cursor })
    | .mk _ (.struct tagSym) =>
      some <| (lookupStructMembers tagDefs tagSym).bind fun ((firstIdent, firstTy), otherMembrs, _) =>
        .ok { pos with ty := firstTy,
                       cursor := mkCursorElem (.struct tagSym [] firstIdent otherMembrs) :: pos.cursor }
    | .mk _ (.union tagSym) =>
      some <| (lookupUnionMembers tagDefs tagSym).bind fun ((firstIdent, firstTy), _) =>
        .ok { pos with ty := firstTy, cursor := mkCursorElem (.union tagSym firstIdent) :: pos.cursor }
    | _ => none

/-- `go_down` (`desugaring_init.lem:111`). -/
def goDown (tagDefs : SymMap TagDefinition) (pos : InitPosition) : Option (DesugInitResult InitPosition) :=
  goDownAux tagDefs false pos

/-- `go_down_entering_block` (`desugaring_init.lem:112`). -/
def goDownEnteringBlock (tagDefs : SymMap TagDefinition) (pos : InitPosition) :
    Option (DesugInitResult InitPosition) :=
  goDownAux tagDefs true pos

/-- The stage of the rejects that stand for Lem's `Errors.INTERNAL_ERROR
(Internal_error_desugaring msg)`, which `desugarAggregateInitialiser` catches. -/
def initStage : String := "desugar: Internal_error_desugaring"

/-- `internal_error` (`desugaring_init.lem:117`). -/
def initInternalError {α : Type} (msg : String) : DesugM α :=
  throw ⟨initStage, .loc .unknown, msg⟩

/-- `go_down_aux` on a type that is not basic, a pointer, an array, a struct or a union: Lem's
internal error prints the type, which is not ported, so this rejects instead. -/
def goDownTypeNotPorted {α : Type} : DesugM α :=
  notPorted .unknown "the type printer of Desugaring_init.go_down_aux (Pp.stringFromAil_ctype)"

/-- A pure cursor result in the monad. -/
def DesugInitResult.toM {α : Type} (onNothing : DesugM α) : DesugInitResult α → DesugM α
  | .ok a => return a
  | .nothing => onNothing
  | .internalError msg => initInternalError msg
  | .crash msg => Desugar.internalError msg

/-- `go_bottom` (`desugaring_init.lem:121`): go down to a leaf. A type has finitely many
levels; the fuel bounds them. -/
def goBottom (tagDefs : SymMap TagDefinition) : Nat → InitPosition → DesugM InitPosition
  | 0, _ => internalError "Desugaring_init.go_bottom: out of fuel"
  | fuel + 1, pos =>
    match goDown tagDefs pos with
    | some (.ok pos') => goBottom tagDefs fuel pos'
    | some .nothing => return pos
    | some (.internalError msg) => initInternalError msg
    | some (.crash msg) => internalError msg
    | none => goDownTypeNotPorted

/-- `go_up_aux` (`desugaring_init.lem:133`): move the cursor to the enclosing aggregate or
union, unless `stopAtBlock` and a `{ … }` was entered at the current level. -/
def goUpAux (stopAtBlock : Bool) (pos : InitPosition) : DesugInitResult InitPosition :=
  match pos.cursor with
  | [] => .nothing
  | elem :: cursor' =>
    if stopAtBlock && elem.isBlock then .nothing
    else match elem.kind with
      | .array _ sizeOpt => .ok { pos with ty := .mk [] (.array pos.ty sizeOpt), cursor := cursor' }
      | .struct tagSym _ _ _ => .ok { pos with ty := .mk [] (.struct tagSym), cursor := cursor' }
      | .union tagSym _ => .ok { pos with ty := .mk [] (.union tagSym), cursor := cursor' }

/-- `go_up` (`desugaring_init.lem:155`). -/
def goUp (pos : InitPosition) : DesugInitResult InitPosition := goUpAux false pos

/-- `go_up_stop_at_block` (`desugaring_init.lem:156`). -/
def goUpStopAtBlock (pos : InitPosition) : DesugInitResult InitPosition := goUpAux true pos

/-- `go_next_aux` (`desugaring_init.lem:160`): move the cursor to the next leaf in the order of
STD §6.7.9#17: the next element or member, going up past the end of an aggregate not opened by
a `{ … }` (`goingUp`), and down into an aggregate. Each step goes up or down one level of the
type, and the type bounds both; the fuel bounds the steps. -/
def goNextAux (tagDefs : SymMap TagDefinition) : Nat → Bool → InitPosition →
    Option (DesugInitResult InitPosition)
  | 0, _, _ => some (.crash "Desugaring_init.go_next: out of fuel")
  | fuel + 1, goingUp, pos =>
    let goNext (pos : InitPosition) := goNextAux tagDefs fuel false pos
    let goNextGoingUp (pos : InitPosition) := goNextAux tagDefs fuel true pos
    -- go up, then next (going up); thunks, as Lean evaluates `let` eagerly
    let upThenNext (_ : Unit) : Option (DesugInitResult InitPosition) :=
      match goUp pos with
      | .ok pos' => goNextGoingUp pos'
      | .nothing => some .nothing
      | .internalError msg => some (.internalError msg)
      | .crash msg => some (.crash msg)
    -- go down, then next
    let downThenNext (_ : Unit) : Option (DesugInitResult InitPosition) :=
      match goDown tagDefs pos with
      | some (.ok pos') => goNext pos'
      | r => r
    if cursorOverflowing pos.cursor then
      -- TODO: check (OVERFLOWING)
      some .nothing
    else match pos.cursor with
    | [] => goDown tagDefs pos
    | elem :: cursor' =>
      match elem.kind with
      | .array currentIdx sizeOpt =>
        let newIdx := currentIdx + 1
        let indexIsOverflowing := match sizeOpt with
          | some size => decide (newIdx ≥ size)
          | none => false
        if indexIsOverflowing then
          if elem.isBlock then
            -- OVERFLOWING
            some (.ok { pos with cursor := { elem with isOverflowing := true } :: cursor' })
          else upThenNext ()
        else if isScalar (unatomic pos.ty) || goingUp then
          some (.ok { pos with cursor := ⟨elem.isBlock, elem.isOverflowing, .array newIdx sizeOpt⟩ :: cursor' })
        else downThenNext ()
      | .struct _ _ _ [] =>
        if elem.isBlock then
          -- OVERFLOWING
          some (.ok { pos with cursor := { elem with isOverflowing := true } :: cursor' })
        else upThenNext ()
      | .struct tagSym prevMembrs currentMember ((membIdent, membTy) :: nextMembrs) =>
        if isScalar (unatomic pos.ty) || goingUp then
          some (.ok { pos with
            ty := membTy,
            cursor := { elem with kind := .struct tagSym (prevMembrs ++ [(currentMember, pos.ty)])
                                    membIdent nextMembrs } :: cursor' })
        else downThenNext ()
      | .union _ _ =>
        if elem.isBlock then
          -- OVERFLOWING
          some (.ok { pos with cursor := { elem with isOverflowing := true } :: cursor' })
        else upThenNext ()

/-- The fuel of the cursor walks: far more steps than a type has levels. -/
def initFuel : Nat := 100000

/-- `go_next` (`desugaring_init.lem:210`). -/
def goNext (tagDefs : SymMap TagDefinition) (pos : InitPosition) : Option (DesugInitResult InitPosition) :=
  goNextAux tagDefs initFuel false pos

/-- `go_next_going_up` (`desugaring_init.lem:211`). -/
def goNextGoingUp (tagDefs : SymMap TagDefinition) (pos : InitPosition) :
    Option (DesugInitResult InitPosition) :=
  goNextAux tagDefs initFuel true pos

/-- `do_next_in_same_level` (`desugaring_init.lem:215`): after a `{ … }` closed, move to the
next element or member of the level it was at, or overflow at the top level. -/
def doNextInSameLevel (tagDefs : SymMap TagDefinition) (pos : InitPosition) :
    Option (DesugInitResult InitPosition) :=
  let upThenNext (_ : Unit) : Option (DesugInitResult InitPosition) :=
    match goUp pos with
    | .ok pos' => goNextGoingUp tagDefs pos'
    | .nothing => some .nothing
    | .internalError msg => some (.internalError msg)
    | .crash msg => some (.crash msg)
  if cursorOverflowing pos.cursor then some (.ok pos)
  else match pos.cursor with
  | elem :: cursor' =>
    match elem.kind with
    | .array currentIdx sizeOpt =>
      let newIdx := currentIdx + 1
      let indexIsOverflowing := match sizeOpt with
        | some size => decide (newIdx ≥ size)
        | none => false
      if indexIsOverflowing then
        if cursor'.isEmpty then
          -- OVERFLOWING
          some (.ok { pos with cursor := { elem with isOverflowing := true } :: cursor' })
        else upThenNext ()
      else some (.ok { pos with cursor := { elem with kind := .array newIdx sizeOpt } :: cursor' })
    | .struct _ _ _ [] =>
      if cursor'.isEmpty then
        -- OVERFLOWING
        some (.ok { pos with cursor := [{ elem with isOverflowing := true }] })
      else upThenNext ()
    | .struct tagSym prevMembrs currentMember ((membIdent, membTy) :: nextMembrs) =>
      some (.ok { pos with
        ty := membTy,
        cursor := { elem with kind := .struct tagSym (prevMembrs ++ [(currentMember, pos.ty)])
                                membIdent nextMembrs } :: cursor' })
    | .union _ _ =>
      if cursor'.isEmpty then
        -- OVERFLOWING
        some (.ok { pos with cursor := [{ elem with isOverflowing := true }] })
      else upThenNext ()
  | _ => some (.internalError "TODO: do_next_in_same_level _")

/-- `find_struct_member` (`desugaring_init.lem:256`): the type of a member and the members
before and after it, or whether the identifier names the flexible array member. -/
def findStructMember (tagDefs : SymMap TagDefinition) (ident : Identifier) (tagSym : Sym) :
    DesugInitResult (Bool ⊕ (Ctype × List (Identifier × Ctype) × List (Identifier × Ctype))) :=
  (lookupStructMembers tagDefs tagSym).bind fun (x, xs, flexOpt) =>
    let membrs := x :: xs
    match membrs.findIdx? (·.1.name == ident.name) with
    | some i =>
      match membrs.splitAt i with
      | (prev, (_, ty) :: next) => .ok (.inr (ty, prev, next))
      | _ => .crash "Desugaring_init.find_struct_member"
    | none =>
      let isFlexibleArrayMember := match flexOpt with
        | some (.mk _ flexIdent _ _) => ident.name == flexIdent.name
        | none => false
      .ok (.inl isFlexibleArrayMember)

/-- `find_union_member` (`desugaring_init.lem:278`). -/
def findUnionMember (tagDefs : SymMap TagDefinition) (ident : Identifier) (tagSym : Sym) :
    DesugInitResult (Option Ctype) :=
  (lookupUnionMembers tagDefs tagSym).bind fun (x, xs) =>
    .ok (((x :: xs).find? (·.1.name == ident.name)).map (·.2))

/-- The desugaring functions the interpretation calls. Lem: `desugaring_init_funcs`
(`desugaring_init.lem:284`). -/
structure DesugaringInitFuncs where
  desugarExpression : Cabs.Expression → DesugM (Expression Unit)
  isIntegerConstantExpression : Expression Unit → DesugM Bool
  isInitializerConstantExpressionOrStringLiteral : Expression Unit → DesugM Bool
  evaluateIntegerConstantExpression : Loc → Option Ctype → Expression Unit → DesugM Int

/-- `liftM` (`desugaring_init.lem:291`). -/
def liftInit {α : Type} (r : Option (DesugInitResult α)) : DesugM α :=
  match r with
  | some r => r.toM (initInternalError "liftM failed")
  | none => goDownTypeNotPorted

/-- `go_top_of_block` (`desugaring_init.lem:301`): go up to the level where the current
`{ … }` was entered. -/
def goTopOfBlock : Nat → InitPosition → DesugM InitPosition
  | 0, _ => internalError "Desugaring_init.go_top_of_block: out of fuel"
  | fuel + 1, pos =>
    match goUpStopAtBlock pos with
    | .nothing => return pos
    | .ok pos' => goTopOfBlock fuel pos'
    | .internalError msg => initInternalError msg
    | .crash msg => internalError msg

/-- The location of a Cabs expression (`Loc.locOf`). -/
def locOfCabsExpression : Cabs.Expression → Loc
  | .mk loc _ => loc

/-- `moveTo_aux` (`desugaring_init.lem:312`): follow a designation from the type and cursor of
the enclosing level (STD §6.7.9#6, #7). An array index must be a nonnegative integer constant
expression; past the size of the array the cursor overflows. -/
def moveToAux (tagDefs : SymMap TagDefinition) (funcs : DesugaringInitFuncs) (isTop : Bool)
    (acc : Ctype × List InitCursorElem) : List Cabs.Designator → DesugM (Ctype × List InitCursorElem)
  | [] => return acc
  | .array e :: desigs' => do
    let (tyAcc, cursorAcc) := acc
    let loc := locOfCabsExpression e
    let common : DesugM Int := do
      let dE ← funcs.desugarExpression e
      if !(← funcs.isIntegerConstantExpression dE) then
        constraintViolation loc .illegalTypeArrayDesignator
      else
        let idx ← funcs.evaluateIntegerConstantExpression loc none dE
        if idx < 0 then constraintViolation loc .illegalSizeArrayDesignator
        else return idx
    match unatomic tyAcc with
    | .mk _ (.array elemTy (some size)) =>
      let idx ← common
      let newElem : InitCursorElem :=
        if idx ≥ size then
          -- TODO: let* () = Eff.warn "array designator is larger than array" in
          ⟨isTop, true, .array (size - 1) (some size)⟩
        else ⟨isTop, false, .array idx (some size)⟩
      moveToAux tagDefs funcs false (elemTy, newElem :: cursorAcc) desigs'
    | .mk _ (.array elemTy none) =>
      let idx ← common
      moveToAux tagDefs funcs false (elemTy, ⟨isTop, false, .array idx none⟩ :: cursorAcc) desigs'
    | _ => constraintViolation loc .illegalArrayDesignatorUsage
  | .member ident :: desigs' => do
    let (tyAcc, cursorAcc) := acc
    let loc := ident.loc
    match unatomic tyAcc with
    | .mk _ (.struct tagSym) =>
      match ← (findStructMember tagDefs ident tagSym).toM (initInternalError "find_struct_member") with
      | .inr (newTy, prev, next) =>
        moveToAux tagDefs funcs false
          (newTy, ⟨isTop, false, .struct tagSym prev ident next⟩ :: cursorAcc) desigs'
      | .inl isFlexibleArrayMember =>
        if isFlexibleArrayMember then
          constraintViolation loc (.illegalMemberDesignatorFlexibleArrayMember ident)
        else notPorted loc "the message of IllegalMemberDesignator (prints a ctype)"
    | .mk _ (.union tagSym) =>
      match ← (findUnionMember tagDefs ident tagSym).toM (initInternalError "find_union_member") with
      | some newTy =>
        moveToAux tagDefs funcs false (newTy, ⟨isTop, false, .union tagSym ident⟩ :: cursorAcc) desigs'
      | none => notPorted loc "the message of IllegalMemberDesignator (prints a ctype)"
    | _ => constraintViolation loc .illegalMemberDesignatorUsage

/-- `moveTo` (`desugaring_init.lem:377`): a designation moves the cursor from the level of the
current `{ … }`. -/
def moveTo (tagDefs : SymMap TagDefinition) (funcs : DesugaringInitFuncs) (pos : InitPosition) :
    Option (List Cabs.Designator) → DesugM InitPosition
  | none => return pos
  | some desigs => do
    let pos ← goTopOfBlock initFuel pos
    let pos ← liftInit (some (goUp pos))
    let (ty', cursor') ← moveToAux tagDefs funcs true (pos.ty, pos.cursor) desigs
    return { pos with ty := ty', cursor := cursor' }

/-- An element of the path to a leaf. Lem: `init_element` (`desugaring_init.lem:401`). -/
inductive InitElement where
  | array (n : Int)
  | member (ident : Identifier)
  | union

/-- Lem's `setElemCompare` on `init_element` (`desugaring_init.lem:419`); identifiers compare
by their text (`symbol.lem:21`). -/
def InitElement.compare : InitElement → InitElement → Ordering
  | .array n₁, .array n₂ => Ord.compare n₁ n₂
  | .member ident₁, .member ident₂ => Ord.compare ident₁.name ident₂.name
  | elem₁, elem₂ =>
    let ord : InitElement → Nat
      | .array _ => 0
      | .member _ => 1
      | .union => 2
    Ord.compare (ord elem₁) (ord elem₂)

/-- The path to a leaf. Lem: `init_path` (`desugaring_init.lem:406`). -/
abbrev InitPath := List InitElement

/-- The lexicographic order of paths (Lem's `setElemCompare` on lists). -/
def InitPath.compare : InitPath → InitPath → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => match a.compare b with
    | .eq => InitPath.compare as bs
    | o => o

/-- The initialised leaves. Lem: `map init_path (AilSyntax.expression unit)`. -/
abbrev InitMap := Std.TreeMap InitPath (Expression Unit) InitPath.compare

/-- `to_init_path` (`desugaring_init.lem:443`): the path of the cursor, outermost first. -/
def toInitPath (cursor : List InitCursorElem) : InitPath :=
  cursor.reverse.map fun elem =>
    match elem.kind with
    | .array n _ => .array n
    | .struct _ _ ident _ => .member ident
    | .union _ _ => .union

/-- The `Init_expr` case of `interp_initializer_aux` (`desugaring_init.lem:449-470`): an
expression initialises the leaf under the cursor, unless the cursor overflowed; for an
object of static or thread storage duration it must be a constant (STD §6.7.9#4). -/
def interpInitialiserExpr (tagDefs : SymMap TagDefinition) (funcs : DesugaringInitFuncs)
    (isStaticOrThread : Bool) (initsAcc : InitMap) (maxIndex : Int) (pos : InitPosition)
    (e : Cabs.Expression) : DesugM (Int × InitMap × Bool × InitPosition) := do
  let dE ← funcs.desugarExpression e
  if !(← funcs.isInitializerConstantExpressionOrStringLiteral dE) && isStaticOrThread then
    -- STD §6.7.9#4
    constraintViolation dE.loc .illegalStorageClassStaticOrThreadInitializer
  -- NOTE: we dealing with a scalar, so we go down to a leaf
  let pos ← goBottom tagDefs initFuel pos
  let initsAcc' :=
    if cursorOverflowing pos.cursor then initsAcc
    else initsAcc.insert (toInitPath pos.cursor) dE
  return (maxIndex, initsAcc', false, pos)

mutual

/-- `interp_initializer_aux` (`desugaring_init.lem:448-539`): interpret an initializer at the
cursor, returning the largest index of a top-level array of unknown size, the initialised
leaves, whether a `{ … }` was interpreted and the new cursor. A braced initializer of a scalar
has one expression (STD §6.7.9#11); otherwise it opens a block, and each of its initializers
is interpreted at its designation or at the next position (STD §6.7.9#17-#20). -/
def interpInitialiserAux (tagDefs : SymMap TagDefinition) (funcs : DesugaringInitFuncs)
    (isStaticOrThread : Bool) (initsAcc : InitMap) (isInner : Bool) (maxIndex : Int)
    (pos : InitPosition) : Cabs.Initializer → DesugM (Int × InitMap × Bool × InitPosition)
  | .expr e => interpInitialiserExpr tagDefs funcs isStaticOrThread initsAcc maxIndex pos e
  | .list loc xs =>
    if isScalar (unatomic pos.ty) then
      match xs with
      | [(none, .expr e)] => interpInitialiserExpr tagDefs funcs isStaticOrThread initsAcc maxIndex pos e
      -- STD §6.7.9#11, sentence 1
      | _ => throw (scalarInitialiserNotSingleExpression loc)
    else do
      -- NOTE: we go on step down (an mark the opening of a block { ... })
      -- NOTE: this moves the cursor to the first member/index of the struct/array
      let pos ← liftInit (goDownEnteringBlock tagDefs pos)
      -- NOTE: for each element of the init list
      let (maxIndex, inits, pos) ←
        interpInitialiserList tagDefs funcs isStaticOrThread isInner (maxIndex, initsAcc, pos) xs
      return (maxIndex, inits, true, pos)

/-- `on_list` (`desugaring_init.lem:390`) over the initializers of a braced list, with the
function of `interp_initializer_aux` (`desugaring_init.lem:487-536`). -/
def interpInitialiserList (tagDefs : SymMap TagDefinition) (funcs : DesugaringInitFuncs)
    (isStaticOrThread : Bool) (isInner : Bool) (acc : Int × InitMap × InitPosition) :
    List (Option (List Cabs.Designator) × Cabs.Initializer) → DesugM (Int × InitMap × InitPosition)
  | [] => return acc
  | (desigsOpt, init) :: xs => do
    let isLast := xs.isEmpty
    let (maxIndex, initsAcc, pos) := acc
    -- NOTE: we move to the position specified by the designators
    let pos' ← moveTo tagDefs funcs pos desigsOpt
    -- this keeps track of the largest index used when initialising an array with unknown size
    let maxIndex' :=
      if isInner then maxIndex
      else match pos'.cursor with
        | [] => maxIndex
        | elem :: _ =>
          match elem.kind with
          | .array idx none => if idx > maxIndex then idx else maxIndex
          | _ => maxIndex
    -- NOTE: we recursively interpret the inner initializer (this may move the cursor)
    let (_, initsAcc', finishedList, pos') ←
      interpInitialiserAux tagDefs funcs isStaticOrThread initsAcc true 0 pos' init
    let pos' ←
      if isLast then
        if !isInner then
          -- NOTE: the whole initiliazer_ has been interpreted
          pure pos'
        else do
          -- NOTE: we move the cursor back to the level of the block we just opened
          let pos' ← goTopOfBlock initFuel pos'
          -- NOTE: we move up from this block
          let pos' ← liftInit (some (goUp (unmarkAsOverflowing pos')))
          liftInit (doNextInSameLevel tagDefs pos')
      else
        -- NOTE: otherwise (not the last element), we move to the next (logical) position
        if cursorOverflowing pos'.cursor then pure pos'
        else if finishedList then pure pos'
        else liftInit (goNext tagDefs pos')
    interpInitialiserList tagDefs funcs isStaticOrThread isInner (maxIndex', initsAcc', pos') xs

end

/-- `desugar_init` (`desugaring_init.lem:547`): interpret an initializer of an object of the
given type; an array of unknown size gets one more element than its largest index (STD
§6.7.9#22). -/
def desugarInit (tagDefs : SymMap TagDefinition) (funcs : DesugaringInitFuncs)
    (isStaticOrThread : Bool) (ty : Ctype) (init : Cabs.Initializer) :
    DesugM (Ctype × InitMap × InitPosition) := do
  let pos : InitPosition := ⟨ty, ty, [], false⟩
  let (size, initMap, _, lastPos) ← interpInitialiserAux tagDefs funcs isStaticOrThread ∅ false 0 pos init
  let ty' := match ty with
    | .mk annots (.array elemTy none) => Ctype.mk annots (.array elemTy (some (size + 1)))
    | _ => ty
  return (ty', initMap, lastPos)

/-- `constructValue_aux` (`desugaring_init.lem:563-610`): the value of an object of the given
type at a path: an array, struct or union of the values of its elements or members (a union
always takes its first member), or a leaf's initializer, zero if it has none (STD §6.7.9#10,
#21). Struct members come from the tag definitions, so the recursion carries fuel, one unit
per level; Lem's `error` cases (an array of unknown size, a tag without definition) give an
invalid node, as they are unreachable once the initializer was interpreted. -/
def constructValueAux (tagDefs : SymMap TagDefinition) (initMap : InitMap) :
    Nat → InitPath → Ctype → Expression Unit
  | 0, _, cty => .mk () [] (.other "Cabs_to_ail.constructValue") (.invalid cty (.other "out of fuel"))
  | fuel + 1, path, cty@(.mk _ ty) =>
    let loc := Loc.other "Cabs_to_ail.constructValue"
    let wrapExpr (expr : ExpressionNode Unit) : Expression Unit := .mk () [] loc expr
    match ty with
    | .array _ none => wrapExpr (.invalid cty (.other "constructValue_aux: Array Nothing"))
    | .array elemTy (some n) =>
      let es := (List.range n.toNat).map fun i =>
        some (constructValueAux tagDefs initMap fuel (path ++ [.array i]) elemTy)
      wrapExpr (.array false elemTy es)
    | .struct tagSym =>
      match tagDefs.get? tagSym with
      | some (.struct _ _ _ xs _) =>
        let membrs := xs.map fun (membIdent, (_, _, _, membTy)) =>
          -- TODO: this is only correct if the first member was the one initialised
          (membIdent, some (constructValueAux tagDefs initMap fuel (path ++ [.member membIdent]) membTy))
        wrapExpr (.struct tagSym membrs)
      | _ => wrapExpr (.invalid cty (.other "constructValue_aux, Struct"))
    | .union tagSym =>
      match tagDefs.get? tagSym with
      | some (.union _ _ _ ((firstMembIdent, (_, _, _, firstMembTy)) :: _)) =>
        wrapExpr (.union tagSym firstMembIdent
          (some (constructValueAux tagDefs initMap fuel (path ++ [.union]) firstMembTy)))
      | _ => wrapExpr (.invalid cty (.other "constructValue_aux, Union"))
    | .atomic ty' =>
      -- TODO: check this
      constructValueAux tagDefs initMap fuel path ty'
    | _ =>
      match initMap.get? path with
      | none => mkZeroInit tagDefs cty
      | some e => e

/-- `constructValue` (`desugaring_init.lem:612`). -/
def constructValue (tagDefs : SymMap TagDefinition) (initMap : InitMap) (ty : Ctype) : Expression Unit :=
  constructValueAux tagDefs initMap zeroInitDepth [] ty

/-- The aggregate and union case of `wip_desugar_initializer_` (`cabs_to_ail.lem:3463-3497`):
interpret the initializer and build the value. If the interpretation fails with an internal
error, the state is rolled back (`E.catch`) and the value is an invalid node with Lem's
message; an array of unknown size then gets size 1, to make the type complete. -/
def desugarAggregateInitialiser (funcs : DesugaringInitFuncs) (loc : Loc) (dur : StorageDuration)
    (currentTy : Ctype) (init : Cabs.Initializer) : DesugM (Ctype × Expression Unit) := do
  let tagDefs ← getTagDefinitions
  tryCatch
    (do
      let (currentTy', initSt, _) ←
        desugarInit tagDefs funcs (dur == .static || dur == .thread) currentTy init
      return (currentTy', constructValue tagDefs initSt currentTy'))
    fun err =>
      if err.stage == initStage then
        let currentTy' := match currentTy with
          | .mk annots (.array elemTy none) => Ctype.mk annots (.array elemTy (some 1))
          | _ => currentTy
        return (currentTy', .mk () [] loc (.invalid currentTy' (.desugaringInitFailed err.message)))
      else throw err

end Silmaril.Cerberus.Frontend.Desugar
