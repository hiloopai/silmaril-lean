module

public import Silmaril.Cerberus.Frontend.Desugar.Auxiliary.Defs
public import Silmaril.Cerberus.Frontend.Desugar.Errors.Defs
public import Silmaril.Cerberus.Frontend.Desugar.ScopeTable.Defs
public import Silmaril.Cerberus.Frontend.Location.Defs
public import Silmaril.Cerberus.Mem.Layout.Defs

/-! # The desugaring monad: `Cabs_to_ail_effect`

A port of `frontend/model/cabs_to_ail_effect.lem` at `b3e11ea3`: the kinds, scopes and
namespaces of identifiers (STD §6.2.1-6.2.3), the desugaring state (`state`, 221-281), the
monad `desugM` (293) as `StateT DesugState (Except Ail.Reject)`, and the registration and
resolution of identifiers, tags, declarations and definitions, down to `extract_program`
(2460), which builds the Ail program from the final state.

**Fresh numbers.** Cerberus draws symbol numbers, loop ids and markers from the
process-global counter `Cerb_fresh.int`; here it is the state's `freshSupply`, drawn in the
same order (the driver ranks the numbers, `Ail.Canonical`). The digest of every symbol is
the state's `digest` (`Cerb_fresh.set_digest`).

**Not ported.** The CN state (magic comments are off, so its lists stay empty), the markers
environment (filled only by the CN backend), `core_eval_stuff` (constant evaluation is
native). `get_alignof` shares the existing LP64 layout implementation.

**Maps.** A Lem map is a `Std.TreeMap` under the comparison of its key type: symbols by
`Symbol.symbol_compare`, identifiers by their text, namespaces by
`setElemCompare`. `toList` lists bindings in key order, as `Map_extra.toList` does.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend.Desugar

open Silmaril.Cerberus Silmaril.Cerberus.Ail

/-! ## Kinds, scopes and namespaces -/

/-- Lem: `Cabs_to_ail_effect.tag_kind` (`cabs_to_ail_effect.lem:18`). -/
inductive TagKind where
  | struct | union | enum
  deriving DecidableEq, Repr

/-- The kinds of identifiers that can have a linkage (STD §6.2.1#1, sentence 1); an object
records whether it is a function parameter. Lem: `ordinary_kind`
(`cabs_to_ail_effect.lem:25`). -/
inductive OrdinaryKind where
  | object (isParameter : Bool)
  | function
  | enumConstant
  | typedef
  deriving DecidableEq, Repr

/-- Lem: `identifier_kind` (`cabs_to_ail_effect.lem:35`). -/
inductive IdentifierKind where
  | ordinary (k : OrdinaryKind)
  | tag (k : TagKind)
  | label
  | member (k : TagKind)
  deriving DecidableEq, Repr

/-- `is_object_kind` (`cabs_to_ail_effect.lem:83`). -/
def isObjectKind : OrdinaryKind → Bool
  | .object _ => true
  | _ => false

/-- `is_parameter_object_kind` (`cabs_to_ail_effect.lem:89`). -/
def isParameterObjectKind : OrdinaryKind → Bool
  | .object true => true
  | _ => false

/-- Scopes (STD §6.2.1#2). Lem: `scope` (`cabs_to_ail_effect.lem:99`). -/
inductive Scope where
  | function
  | file
  | block (id : Nat)
  | prototype (id : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- `is_block_scope` (`cabs_to_ail_effect.lem:138`). -/
def isBlockScope : Scope → Bool
  | .block _ => true
  | _ => false

/-- Name spaces (STD §6.2.3#1); members are per struct or union, enumeration constants are
ordinary. Lem: `namespace` (`cabs_to_ail_effect.lem:149`). -/
inductive Namespace where
  | label
  | tag
  | member (x : Identifier)
  | ordinary

/-- `SetType namespace`'s `setElemCompare` (`cabs_to_ail_effect.lem:168-186`). -/
def Namespace.compare : Namespace → Namespace → Ordering
  | .member x, .member y => Ord.compare x.name y.name
  | a, b =>
    let ord : Namespace → Nat
      | .label => 0
      | .tag => 1
      | .member _ => 2
      | .ordinary => 3
    Ord.compare (ord a) (ord b)

/-- Lem's comparison of `(Symbol.identifier * namespace)` keys: the text, then the namespace. -/
def compareIdentNs (a b : Identifier × Namespace) : Ordering :=
  (Ord.compare a.1.name b.1.name).then (a.2.compare b.2)

/-- A Lem `map (Symbol.identifier * namespace) 'a`. -/
abbrev IdentNsMap (α : Type) := Std.TreeMap (Identifier × Namespace) α compareIdentNs

/-- How a scope binds an identifier: to a symbol with its kind and linkage, or to its entry
in `registeredExternalIdentifiers`. Lem: `registration` (`cabs_to_ail_effect.lem:207`). -/
inductive Registration where
  | internal (sym : Sym) (kind : IdentifierKind) (link : Option Linkage)
  | external

/-- What a file-scope object is defined by. Lem: `global_definition`
(`cabs_to_ail_effect.lem:211`). -/
inductive GlobalDefinition where
  | tentative (loc : Loc) (ty : Ctype)
  | definition (e : Expression Unit)
  | externalDefinition (e : Expression Unit)

/-- Lem: `case_selector` (`cabs_to_ail_effect.lem:217`); a range has `lo < hi`. -/
inductive CaseSelector where
  | const (n : Int)
  | range (lo hi : Int)

/-- The cases and default seen in a switch body. Lem: `switch_info`
(`cabs_to_ail_effect.lem:221`). -/
structure SwitchInfo where
  casesInfo : List (Loc × CaseSelector)
  defaultInfo : Option Loc

/-- `empty_switch_info` (`cabs_to_ail_effect.lem:551`). -/
def emptySwitchInfo : SwitchInfo := ⟨[], none⟩

/-- An object declared with linkage or at file scope: whether it is tentative, location,
attributes, storage duration, `register`, alignment, qualifiers and type. -/
abbrev ExternalObjectDeclaration :=
  Bool × Loc × Attributes × StorageDuration × Bool × Option Alignment × Qualifiers × Ctype

/-- An object without linkage: location, storage duration, `register`, alignment, qualifiers
and type. -/
abbrev InternalObjectDeclaration :=
  Loc × StorageDuration × Bool × Option Alignment × Qualifiers × Ctype

/-- A function definition: location, CN marker, attributes, parameter symbols and body. -/
abbrev FunctionDefinitionD := Loc × Nat × Attributes × List Sym × Statement Unit

/-! ## The state -/

/-- The desugaring state. Lem: `state` (`cabs_to_ail_effect.lem:228-281`) without the CN
state and `core_eval_stuff`, plus the global state the desugaring touches: the fresh
counter and digest (`Cerb_fresh`) and the implementation's enum registry
(`Ocaml_implementation.registered_enums`). -/
structure DesugState where
  /-- `Cerb_fresh`'s counter (`util/cerb_fresh.ml`). -/
  freshSupply : Nat
  /-- `Cerb_fresh.set_digest`: the digest of the C file. -/
  digest : Digest
  /-- Fresh Cabs label names (`freshify`). -/
  auxSupply : Nat
  scopeIdSupply : Nat
  registeredExternalIdentifiers : IdentNsMap (Scope × (Sym × IdentifierKind × Option Linkage))
  registeredIdentifiers : ScopeTable Scope (Identifier × Namespace) Registration compareIdentNs
  tagDefinitions : SymMap TagDefinition
  /-- Per function: whether it has a prototype, location, attributes and declaration. -/
  functionDeclarations : SymMap (Bool × Loc × Attributes × FunDeclaration)
  externalObjectDeclarations : SymMap ExternalObjectDeclaration
  internalObjectDeclarations : SymMap InternalObjectDeclaration
  functionDefinitions : SymMap FunctionDefinitionD
  globalObjectDefinitions : SymMap GlobalDefinition
  typedefDefinitions : SymMap (Attributes × Qualifiers × Ctype)
  staticAssertions : List (Expression Unit × StringLiteral)
  /-- STD §6.2.1#1, sentence 2. -/
  enumerationConstants : SymMap (ExpressionNode Unit)
  /-- The cases and defaults of the enclosing switch statements, innermost first. -/
  switchContext : List SwitchInfo
  /-- `used_identifier`, a Lem list used as a set (`Utils.list_insert`). -/
  usedIdentifier : SymMap Unit
  currentReturnType : Option Ctype
  loopAttributes : Std.TreeMap Nat LoopAttribute compare
  toplevelMagicStatements : List (Loc × String)
  /-- `Ocaml_implementation.registered_enums` (`ocaml_implementation.ml:125-150`). -/
  registeredEnums : List (Sym × IntegerType)

/-- `initial_state` (`cabs_to_ail_effect.lem:556-588`), for a file of digest `digest`. -/
def initialState (digest : Digest) : DesugState where
  freshSupply := 0
  digest := digest
  auxSupply := 0
  scopeIdSupply := 0
  registeredExternalIdentifiers := ∅
  registeredIdentifiers := ScopeTable.empty
  tagDefinitions := ∅
  functionDeclarations := ∅
  externalObjectDeclarations := ∅
  internalObjectDeclarations := ∅
  functionDefinitions := ∅
  globalObjectDefinitions := ∅
  typedefDefinitions := ∅
  staticAssertions := []
  enumerationConstants := ∅
  switchContext := []
  usedIdentifier := ∅
  currentReturnType := none
  loopAttributes := ∅
  toplevelMagicStatements := []
  registeredEnums := []

/-- The desugaring monad. Lem: `desugM 'a = stExceptM 'a state_with_markers Errors.error`
(`cabs_to_ail_effect.lem:293`). -/
abbrev DesugM := StateT DesugState (Except Ail.Reject)

/-! ## Failing -/

/-- `fail` (`cabs_to_ail_effect.lem:303`): a desugaring error. -/
def fail {α : Type} (loc : Loc) (cause : DesugarCause) : DesugM α := throw (cause.reject loc)

/-- `constraint_violation` (`cabs_to_ail_effect.lem:309`). -/
def constraintViolation {α : Type} (loc : Loc) (v : ConstraintViolation) : DesugM α :=
  fail loc (.constraintViolation v)

/-- `undef` (`cabs_to_ail_effect.lem:313`). -/
def undef {α : Type} (loc : Loc) (ub : UndefinedBehaviour) : DesugM α :=
  fail loc (.undefinedBehaviour ub)

/-- Lem's `error` (`Cerb_debug.error`): an uncaught failure, where Cerberus crashes. -/
def internalError {α : Type} (msg : String) : DesugM α :=
  throw ⟨"desugar", .loc .unknown, "Silmaril: internal error: " ++ msg⟩

/-- A construct whose desugaring is not ported yet: a reject that matches no oracle output. -/
def notPorted {α : Type} (loc : Loc) (what : String) : DesugM α :=
  throw ⟨"desugar", .loc loc, "Silmaril: not ported: " ++ what⟩

/-- `guard_extension` (`cabs_to_ail_effect.lem:2385`): the oracle is not permissive, so a GNU
extension is an `Errors.EXTENSION` error. -/
def guardExtension (loc : Loc) (ext : String) : DesugM Unit :=
  throw ⟨"desugar", .loc loc, s!"use of {ext} extension (try --permissive)"⟩

/-! ## Fresh numbers and scopes -/

/-- `Symbol.fresh_int` (`symbol.lem:226`, `Cerb_fresh.int`): the next number. -/
def freshInt : DesugM Nat := modifyGet fun st => (st.freshSupply + 1, { st with freshSupply := st.freshSupply + 1 })

/-- `Symbol.fresh_description` (`symbol.lem:256`). -/
def freshDescription (sd : SymbolDescription) : DesugM Sym := do
  let n ← freshInt
  return ⟨(← get).digest, n, sd⟩

/-- `Symbol.fresh_pretty` (`symbol.lem:234`). -/
def freshPretty (str : String) : DesugM Sym := freshDescription (.id str)

/-- `Symbol.fresh_object_address` (`symbol.lem:250`). -/
def freshObjectAddress (name : String) : DesugM Sym := freshDescription (.objectAddress name)

/-- `current_scope_is` (`cabs_to_ail_effect.lem:383`). -/
def currentScopeIs (scope : Scope) : DesugM Bool :=
  return ScopeTable.currentScopeIs (← get).registeredIdentifiers == scope

/-- `scope_is_visible` (`cabs_to_ail_effect.lem:389`). -/
def scopeIsVisible (scope : Scope) : DesugM Bool :=
  return ScopeTable.scopeIsVisible scope (← get).registeredIdentifiers

/-- `get_scope` (`cabs_to_ail_effect.lem:396`). -/
def getScope : DesugM Scope := return ScopeTable.currentScopeIs (← get).registeredIdentifiers

/-- `under_scope` (`cabs_to_ail_effect.lem:406-421`): run `m` in a new innermost scope. -/
def underScope {α : Type} (scope : Scope) (m : DesugM α) : DesugM α := do
  modify fun st => { st with registeredIdentifiers := ScopeTable.createScope scope st.registeredIdentifiers }
  let res ← m
  modify fun st => { st with registeredIdentifiers := (ScopeTable.destroyScope st.registeredIdentifiers).2 }
  return res

/-- A list sorted by symbol without its repeated symbols (they are adjacent). -/
def dedupSorted (xs : List Sym) : List Sym :=
  (xs.foldl (init := []) fun acc a =>
    match acc with
    | b :: _ => if symbolCompare b a == .eq then acc else a :: acc
    | [] => [a]).reverse

/-- `collect_with_scope` (`cabs_to_ail_effect.lem:428-475`): `under_scope`, returning also the
bindings of the objects without linkage declared in the scope (not the static or
thread-local ones). Lem folds over the set of the scope's registrations, which OCaml orders
by symbol; the bindings come out in that order. -/
def collectWithScope {α : Type} (scope : Scope) (m : DesugM α) : DesugM (Bindings × α) := do
  modify fun st => { st with registeredIdentifiers := ScopeTable.createScope scope st.registeredIdentifiers }
  let res ← m
  let st ← get
  let (identsMap, identTable') := ScopeTable.destroyScope st.registeredIdentifiers
  set { st with registeredIdentifiers := identTable' }
  let syms := identsMap.foldl (init := ([] : List Sym)) fun acc _ reg =>
    match reg with
    | .internal sym (.ordinary (.object false)) _ => sym :: acc
    | _ => acc
  let syms := dedupSorted (syms.mergeSort fun a b => symbolCompare a b != .gt)
  let bs := syms.filterMap fun sym =>
    match st.externalObjectDeclarations.get? sym with
    | some (_, loc, _, dur, isRegister, alignOpt, qs, ty) =>
      some (sym, ((loc, dur, isRegister), alignOpt, qs, ty))
    | none =>
      match st.internalObjectDeclarations.get? sym with
      | some (_, .static, _) | some (_, .thread, _) => none
      | some (loc, dur, isRegister, alignOpt, qs, ty) =>
        some (sym, ((loc, dur, isRegister), alignOpt, qs, ty))
      | none => none
  return (bs, res)

/-- The identifiers of one scope, as `Scope_table.destroy_scope` returns them. -/
abbrev IdentsMap := Std.TreeMap (Identifier × Namespace) Registration compareIdentNs

/-- `with_scope2` (`cabs_to_ail_effect.lem:490-505`): `under_scope`, returning also the
identifiers registered in the scope. -/
def withScope2 {α : Type} (scope : Scope) (m : DesugM α) : DesugM (IdentsMap × α) := do
  modify fun st => { st with registeredIdentifiers := ScopeTable.createScope scope st.registeredIdentifiers }
  let res ← m
  let identsMap ← modifyGet fun st =>
    let (identsMap, identTable') := ScopeTable.destroyScope st.registeredIdentifiers
    (identsMap, { st with registeredIdentifiers := identTable' })
  return (identsMap, res)

/-- `bindings_of_idents_map` (`cabs_to_ail_effect.lem:508-537`), the symbols only: the objects
of `identsMap` that have a declaration. Lem folds over the set of the registrations, which
OCaml orders by symbol. -/
def bindingsOfIdentsMap (identsMap : IdentsMap) : DesugM (List Sym) := do
  let st ← get
  let syms := identsMap.foldl (init := ([] : List Sym)) fun acc _ reg =>
    match reg with
    | .internal sym (.ordinary (.object _)) _ => sym :: acc
    | _ => acc
  let syms := dedupSorted (syms.mergeSort fun a b => symbolCompare a b != .gt)
  return syms.filter fun sym =>
    st.externalObjectDeclarations.contains sym || st.internalObjectDeclarations.contains sym

/-- `hack_inject_idents_map` (`cabs_to_ail_effect.lem:540-546`): register the identifiers of
`identsMap` in the innermost scope. -/
def hackInjectIdentsMap (identsMap : IdentsMap) : DesugM Unit :=
  modify fun st =>
    { st with registeredIdentifiers :=
        identsMap.foldl (init := st.registeredIdentifiers) fun acc k reg => ScopeTable.register k reg acc }

/-- `freshify` (`cabs_to_ail_effect.lem:633`): a Cabs label name with a fresh suffix. -/
def freshify (ident : Identifier) : DesugM Identifier :=
  modifyGet fun st => (⟨ident.loc, ident.name ++ toString st.auxSupply⟩, { st with auxSupply := st.auxSupply + 1 })

/-- `fresh_block_scope` (`cabs_to_ail_effect.lem:641`). -/
def freshBlockScope : DesugM Scope :=
  modifyGet fun st => (.block st.scopeIdSupply, { st with scopeIdSupply := st.scopeIdSupply + 1 })

/-- `fresh_prototype_scope` (`cabs_to_ail_effect.lem:648`). -/
def freshPrototypeScope : DesugM Scope :=
  modifyGet fun st => (.prototype st.scopeIdSupply, { st with scopeIdSupply := st.scopeIdSupply + 1 })

/-- `record_marker` (`cabs_to_ail_effect.lem:597`): a fresh marker id; the markers
environment is kept only by the CN backend. -/
def recordMarker : DesugM Nat := freshInt

/-- `fin_markers_env` (`cabs_to_ail_effect.lem:615`): the last marker. -/
def finMarkersEnv : DesugM Nat := recordMarker

/-! ## Registering identifiers -/

/-- `ident_is_in_scope` (`cabs_to_ail_effect.lem:657`), in the innermost scope only, as Lem
does through `return_scope`. -/
def identIsInScope (ident : Identifier) (ns : Namespace) : DesugM Bool :=
  return ScopeTable.isInScope (ident, ns) (ScopeTable.returnScope (← get).registeredIdentifiers)

/-- `ident_is_in_current_scope` (`cabs_to_ail_effect.lem:664`). -/
def identIsInCurrentScope (ident : Identifier) (ns : Namespace) : DesugM Bool :=
  return ScopeTable.isInCurrentScope (ident, ns) (ScopeTable.returnScope (← get).registeredIdentifiers)

/-- What a previous registration resolves to: its scope, symbol, kind and linkage. -/
abbrev Found := Scope × (Sym × IdentifierKind × Option Linkage)

/-- `internal_register_identifier` (`cabs_to_ail_effect.lem:671-804`): register `ident` in
the current scope, with a fresh symbol (an object address for objects), unless a previous
registration is found: then `ifFound` decides, given that registration and the fresh
registration as a fallback. An identifier with external linkage is looked up among the
external registrations only, and is bound in `registeredExternalIdentifiers`. -/
def internalRegisterIdentifier (ifFound : Found → (Unit → DesugM Sym) → DesugM Sym)
    (ident : Identifier) (ns : Namespace) (kind : IdentifierKind) (linkOpt : Option Linkage) :
    DesugM Sym := do
  let sc ← getScope
  match ns, kind, linkOpt with
  | .label, .label, none | .tag, .tag _, none | .member _, .member _, none
  | .ordinary, .ordinary .enumConstant, none | .ordinary, .ordinary .typedef, none
  | .ordinary, .ordinary _, some _ => pure ()
  | _, _, _ => internalError "cabs_to_ail_effect.internal_register_identifier"
  let doFresh (_ : Unit) : DesugM Sym := do
    let sym ← match kind with
      | .ordinary (.object _) => freshObjectAddress ident.name
      | _ => freshPretty ident.name
    modify fun st =>
      match linkOpt with
      | some .external =>
        { st with
          registeredExternalIdentifiers :=
            st.registeredExternalIdentifiers.insert (ident, ns) (sc, (sym, kind, linkOpt))
          registeredIdentifiers := ScopeTable.register (ident, ns) .external st.registeredIdentifiers }
      | _ =>
        { st with
          registeredIdentifiers :=
            ScopeTable.register (ident, ns) (.internal sym kind linkOpt) st.registeredIdentifiers }
    return sym
  let st ← get
  match linkOpt with
  | some .external =>
    match st.registeredExternalIdentifiers.get? (ident, ns) with
    | none => doFresh ()
    | some found => ifFound found doFresh
  | _ =>
    match ScopeTable.resolve (ident, ns) st.registeredIdentifiers with
    | some (scope, .external) =>
      match st.registeredExternalIdentifiers.get? (ident, ns) with
      | none => internalError "[Cabs_to_ail_effect.internal_register_identifier] - internal ERROR"
      | some (_, decl) => ifFound (scope, decl) doFresh
    | some (scope, .internal sym kind' link') => ifFound (scope, (sym, kind', link')) doFresh
    | none =>
      match st.registeredExternalIdentifiers.get? (ident, ns) with
      | none => doFresh ()
      | some found => ifFound found doFresh

/-- Lem's equality on alignments. -/
def alignmentEqual : Option Alignment → Option Alignment → Bool
  | none, none => true
  | some (.integer a), some (.integer b) => a == b
  | some (.ctype a), some (.ctype b) => ctypeEqual a b
  | _, _ => false

/-- `register_typedef` (`cabs_to_ail_effect.lem:806-849`): register a typedef name (reusing
an existing declaration) and its type; a redefinition must have the same type (STD §6.7#3,
first bullet). `[[cerb::byte]]` makes an `unsigned char` typedef the byte type. -/
def registerTypedef (ident : Identifier) (attrs : Attributes) (qs : Qualifiers) (ty : Ctype) :
    DesugM Unit := do
  let loc := ident.loc
  let hasByteAttr := isCerbByte attrs
  let mkByte (ty : Ctype) : DesugM Ctype :=
    if hasByteAttr then
      if isUnsignedChar ty then return .mk [] .byte
      else constraintViolation loc .typedefBytesAreUnsignedCharsOnly
    else return ty
  let sym ← internalRegisterIdentifier (fun (_, (sym, _, _)) _ => return sym)
    ident .ordinary (.ordinary .typedef) none
  let st ← get
  match st.typedefDefinitions.get? sym with
  | some (attrs', qs', ty') =>
    -- STD §6.7#3, first bullet
    if variablyModified ty then constraintViolation loc .typedefRedefinitionVariablyModifiedType
    else if qs != qs' || !ctypeEqual ty ty' then constraintViolation loc .typedefRedefinition
    else
      let ty' ← mkByte ty'
      set { st with typedefDefinitions := st.typedefDefinitions.insert sym (combineAttributes attrs attrs', qs', ty') }
  | none =>
    let ty ← mkByte ty
    set { st with typedefDefinitions := st.typedefDefinitions.insert sym (attrs, qs, ty) }

/-- `resolve_typedef` (`cabs_to_ail_effect.lem:853`). -/
def resolveTypedef (sym : Sym) : DesugM (Attributes × Qualifiers × Ctype) := do
  match (← get).typedefDefinitions.get? sym with
  | some x => return x
  | none => internalError "TODO(msg) Cabs_to_ail_effect.resolve_typedef"

/-! ## Switch statements -/

/-- `register_case` (`cabs_to_ail_effect.lem:863`). -/
def registerCase (loc : Loc) (caseSel : CaseSelector) : DesugM Unit := do
  let st ← get
  match st.switchContext with
  | [] => constraintViolation loc .labelStatementOutsideSwitch
  | x :: xs => set { st with switchContext := { x with casesInfo := (loc, caseSel) :: x.casesInfo } :: xs }

/-- `register_default` (`cabs_to_ail_effect.lem:874`). -/
def registerDefault (loc : Loc) : DesugM Unit := do
  let st ← get
  match st.switchContext with
  | [] => constraintViolation loc .labelStatementOutsideSwitch
  | x :: xs =>
    match x.defaultInfo with
    | some prevLoc => constraintViolation loc (.mutipleDefaultStatement prevLoc)
    | none => set { st with switchContext := { x with defaultInfo := some loc } :: xs }

/-- `check_case_overlap` (`cabs_to_ail_effect.lem:889`): the location of a previous case that
overlaps `newCase`. -/
def checkCaseOverlap (newCase : CaseSelector) : List (Loc × CaseSelector) → Option Loc
  | [] => none
  | (loc, prevCase) :: xs =>
    let overlaps := match newCase, prevCase with
      | .const n, .const p => n == p
      | .const n, .range p₁ p₂ => p₁ ≤ n && n ≤ p₂
      | .range n₁ n₂, .const p => n₁ ≤ p && p ≤ n₂
      | .range n₁ n₂, .range p₁ p₂ => p₁ ≤ n₂ && n₁ ≤ p₂
    if overlaps then some loc else checkCaseOverlap newCase xs

/-- `check_case_overlaps_aux` (`cabs_to_ail_effect.lem:910`). -/
def checkCaseOverlapsAux (acc : List (Loc × CaseSelector)) :
    List (Loc × CaseSelector) → Option (Loc × Loc)
  | [] => none
  | (loc, x) :: xs =>
    match checkCaseOverlap x acc with
    | none => checkCaseOverlapsAux ((loc, x) :: acc) xs
    | some prevLoc => some (loc, prevLoc)

/-- `check_case_overlaps` (`cabs_to_ail_effect.lem:920`). -/
def checkCaseOverlaps (xs : List (Loc × CaseSelector)) : Option (Loc × Loc) :=
  -- without ranges, the same search through a map from each value to its latest location
  let consts := xs.filterMap fun
    | (loc, .const n) => some (loc, n)
    | (_, .range ..) => none
  if consts.length == xs.length then
    let rec go (seen : Std.TreeMap Int Loc compare) : List (Loc × Int) → Option (Loc × Loc)
      | [] => none
      | (loc, n) :: rest =>
        match seen.get? n with
        | some prevLoc => some (loc, prevLoc)
        | none => go (seen.insert n loc) rest
    go ∅ consts
  else checkCaseOverlapsAux [] xs

/-- `is_in_switch` (`cabs_to_ail_effect.lem:924`). -/
def isInSwitch : DesugM Bool := return !(← get).switchContext.isEmpty

/-- `as_switch_body` (`cabs_to_ail_effect.lem:933-951`): run `m` as the body of a switch,
then check that its cases do not overlap. -/
def asSwitchBody {α : Type} (m : DesugM α) : DesugM α := do
  modify fun st => { st with switchContext := emptySwitchInfo :: st.switchContext }
  let ret ← m
  let st ← get
  match st.switchContext with
  | [] => internalError "Cabs_to_ail.as_switch_body: switch_context = []"
  | switchInfo :: xs =>
    set { st with switchContext := xs }
    match checkCaseOverlaps switchInfo.casesInfo with
    | none => return ret
    | some (loc, prevLoc) => constraintViolation loc (.caseStatementOverlap prevLoc)

/-! ## Loops -/

/-- `record_loop_attribute` (`cabs_to_ail_effect.lem:1324`). -/
def recordLoopAttribute (id : Nat) (attr : Attributes) (locCondition locLoop : Loc) : DesugM Unit := do
  let markerId ← recordMarker
  modify fun st =>
    { st with loopAttributes := st.loopAttributes.insert id ⟨markerId, attr, locCondition, locLoop⟩ }

/-! ## Resolving identifiers and linkage -/

/-- How an ordinary identifier resolves. Lem: `ordinary_registration`
(`cabs_to_ail_effect.lem:1427`). -/
inductive OrdinaryRegistration where
  | enumConstant (sym : Sym)
  | typedef (sym : Sym)
  | other (sym : Sym) (kind : OrdinaryKind) (link : Linkage)

/-- `resolve_ordinary_identifier` (`cabs_to_ail_effect.lem:1433-1472`). -/
def resolveOrdinaryIdentifier (_loc : Loc) (ident : Identifier) :
    DesugM (Option (Scope × OrdinaryRegistration)) := do
  let st ← get
  let regOpt ← match ScopeTable.resolve (ident, .ordinary) st.registeredIdentifiers with
    | none => pure (st.registeredExternalIdentifiers.get? (ident, .ordinary))
    | some (scope, .external) =>
      match st.registeredExternalIdentifiers.get? (ident, .ordinary) with
      | none => internalError "[Cabs_to_ail_effect.resolve_ordinary_identifier] - internal ERROR"
      | some (_, decl) => pure (some (scope, decl))
    | some (scope, .internal sym kind linkOpt) => pure (some (scope, (sym, kind, linkOpt)))
  match regOpt with
  | none => return none
  | some (scope, (sym, .ordinary .enumConstant, none)) => return some (scope, .enumConstant sym)
  | some (scope, (sym, .ordinary .typedef, none)) => return some (scope, .typedef sym)
  | some (scope, (sym, .ordinary okind, some link)) => return some (scope, .other sym okind link)
  | some _ => internalError "Cabs_to_ail_effect.resolve_ordinary_identifier ==> found INVALID"

/-- `resolve_extraordinary_identifier` (`cabs_to_ail_effect.lem:1477`): a tag, label or
member. -/
def resolveExtraordinaryIdentifier (ident : Identifier) (ns : Namespace) :
    DesugM (Option (Scope × (Sym × IdentifierKind))) := do
  match ScopeTable.resolve (ident, ns) (← get).registeredIdentifiers with
  | none => return none
  | some (_, .external) => internalError "Cabs_to_ail_effect.resolve_extraordinary_identifier (1)"
  | some (_, .internal _ (.ordinary _) _) =>
    internalError "Cabs_to_ail_effect.resolve_extraordinary_identifier (2)"
  | some (_, .internal _ _ (some _)) => internalError "Cabs_to_ail_effect.resolve_extraordinary_identifier (3)"
  | some (scope, .internal sym kind none) => return some (scope, (sym, kind))

/-- `internal_resolve_identifier` (`cabs_to_ail_effect.lem:1495`). -/
def internalResolveIdentifier (ident : Identifier) (ns : Namespace) :
    DesugM (Option (Scope × Registration)) :=
  return ScopeTable.resolve (ident, ns) (← get).registeredIdentifiers

/-- `determinate_linkage` (`cabs_to_ail_effect.lem:1502-1547`), STD §6.2.2#3-6. A `_Thread_local`
is ignored (Lem deletes its first occurrence). -/
def determinateLinkage (ident : Identifier) (ns : Namespace) (kind : OrdinaryKind)
    (storageClasses : List Cabs.StorageClassSpecifier) : DesugM Linkage := do
  let scope ← getScope
  let scs := storageClasses.erase .threadLocal
  -- STD §6.2.2#4
  let externLinkage : DesugM Linkage := do
    match ← internalResolveIdentifier ident ns with
    | some (_, .external) => return .external
    | some (_, .internal _ _ (some .internal)) => return .internal
    | some (_, .internal _ _ (some _)) => return .external
    | some _ => internalError "determinate_linkage ==> resolved an previous registration with Nothing as linkage"
    | none => return .external
  if scope == .file && (kind == .object false || kind == .function) && scs.contains .static then
    -- STD §6.2.2#3
    return .internal
  else if scs.contains scExtern then
    externLinkage
  else if kind == .function && scs.isEmpty then
    -- STD §6.2.2#5, sentence 1
    externLinkage
  else if scope == .file && kind == .object false && scs.isEmpty then
    -- STD §6.2.2#5, sentence 2
    return .external
  else
    -- STD §6.2.2#6
    if !(isObjectKind kind || kind == .function) || isParameterObjectKind kind ||
        (isBlockScope scope && isObjectKind kind && scs != [scExtern]) then
      return .none_
    else internalError "[Cabs_to_ail_effect.determinate_linkage] unknown case"

/-- `register_ordinary_identifier` (`cabs_to_ail_effect.lem:1590-1659`): register an object or
function identifier with its linkage (STD §6.2.2#7). Not for typedef names. -/
def registerOrdinaryIdentifier (ident : Identifier) (kind : OrdinaryKind)
    (storageClasses : List Cabs.StorageClassSpecifier) : DesugM (Linkage × Sym) := do
  if kind == .enumConstant then
    internalError "cabs_to_ail_effect.register_ordinary_identifier"
  let link ← determinateLinkage ident .ordinary kind storageClasses
  let sym ← internalRegisterIdentifier (fun (scope, (sym, prevKind, prevLinkOpt)) doFresh =>
    match link with
    | .external =>
      -- STD §6.2.2#7
      match prevLinkOpt with
      | some .none_ => doFresh ()
      | some .internal => undef ident.loc .UB008_multiple_linkage
      | some .external => do
        modify fun st =>
          { st with registeredIdentifiers :=
              ScopeTable.register (ident, .ordinary) .external st.registeredIdentifiers }
        return sym
      | none => internalError "TODO: is this possible? (register_ordinary_identifer, prev_link_opt = Nothing)"
    | .none_ => do
      if ← currentScopeIs scope then
        constraintViolation ident.loc (.noLinkageMultipleDeclaration ident)
      else doFresh ()
    | .internal =>
      if IdentifierKind.ordinary kind != prevKind then
        internalError "TODO: Cabs_to_ail_effect.register_ordinary_identifier, kind <> kind'"
      else if some link != prevLinkOpt then
        -- STD §6.2.2#7
        undef ident.loc .UB008_multiple_linkage
      else return sym)
    ident .ordinary (.ordinary kind) (some link)
  return (link, sym)

/-! ## Tags -/

/-- `register_tag` (`cabs_to_ail_effect.lem:1663-1679`): an unnamed tag gets a fresh symbol;
a named one is reused in the scope that declared it with the same kind. -/
def registerTag (loc : Loc) (kind : TagKind) : Option Identifier → DesugM Sym
  | none => freshDescription (.unnamedTag loc)
  | some tagIdent =>
    internalRegisterIdentifier (fun (scope, (sym, prevKind, _)) doFresh => do
      if ← currentScopeIs scope then
        if IdentifierKind.tag kind == prevKind then return sym
        else constraintViolation tagIdent.loc (.tagRedeclaration sym)
      else doFresh ())
      tagIdent .tag (.tag kind) none

/-- `Ocaml_implementation.register_enum` (`ocaml_implementation.ml:130-142`): an enum's
type is `int` if a value is negative, else `unsigned int` (no `-fshort-enums`); false if the
tag is already registered. -/
def registerEnum (tagSym : Sym) (ns : List Int) : DesugM Bool := do
  let st ← get
  if st.registeredEnums.any (·.1.key == tagSym.key) then return false
  let ity : IntegerType := if ns.any (· < 0) then .signed .int else .unsigned .int
  set { st with registeredEnums := (tagSym, ity) :: st.registeredEnums }
  return true

/-- `Ocaml_implementation.typeof_enum` (`ocaml_implementation.ml:144-150`) under the current
registry. -/
def getTypeofEnum : DesugM (Sym → Option IntegerType) := do
  let enums := (← get).registeredEnums
  return fun sym => (enums.find? (·.1.key == sym.key)).map (·.2)

/-- `register_tag_definition` (`cabs_to_ail_effect.lem:1683-1707`): a tag can be defined once
(the error is at `Loc.with_cursor loc`, which the caller passes as `cursorLoc`); an enum also
registers its type with the implementation. -/
def registerTagDefinition (_loc cursorLoc : Loc) (tagSym : Sym) (tagDecl : TagDefinition) :
    DesugM Unit := do
  if (← get).tagDefinitions.contains tagSym then
    constraintViolation cursorLoc (.tagRedefinition tagSym)
  match tagDecl with
  | .enum nsRev =>
    unless ← registerEnum tagSym nsRev do internalError "cabs_to_ail_effect: register_tag_definition"
  | _ => pure ()
  modify fun st => { st with tagDefinitions := st.tagDefinitions.insert tagSym tagDecl }

/-- `resolve_tag_definition` (`cabs_to_ail_effect.lem:1711`). -/
def resolveTagDefinition (tagSym : Sym) : DesugM (Option TagDefinition) :=
  return (← get).tagDefinitions.get? tagSym

/-- `get_tag_definitions` (`cabs_to_ail_effect.lem:1730`). -/
def getTagDefinitions : DesugM (SymMap TagDefinition) := return (← get).tagDefinitions

/-- A struct or union member: its identifier, attributes, alignment, qualifiers and type. -/
abbrev Member := Identifier × (Attributes × Option Alignment × Qualifiers × Ctype)

/-- `get_anonymous_struct_or_union` (`cabs_to_ail_effect.lem:1739-1765`): the members of an
anonymous struct or union type (an atomic one is not anonymous, as in clang); an anonymous
struct cannot have a flexible array member. -/
def getAnonymousStructOrUnion (ty : Ctype) : DesugM (Option (List Member)) := do
  match ty with
  | .mk _ (.struct tagSym) =>
    match ← resolveTagDefinition tagSym with
    | some (.struct _ _ _ _ (some _)) => fail .unknown (.constraintViolation .structMemberFlexibleArray)
    | some (.struct _ _ isAnonymous membrs none) => return if isAnonymous then some membrs else none
    | _ => internalError "Cabs_to_ail_effect.is_anonymous_struct_or_union, Struct -- Union_definition"
  | .mk _ (.union tagSym) =>
    match ← resolveTagDefinition tagSym with
    | some (.union _ _ isAnonymous membrs) => return if isAnonymous then some membrs else none
    | _ => internalError "Cabs_to_ail_effect.is_anonymous_struct_or_union, Union -- Struct_definition"
  | _ => return none

/-! ## Declarations and definitions -/

/-- `is_static_object_identifier` (`cabs_to_ail_effect.lem:1889`). -/
def isStaticObjectIdentifier (sym : Sym) : DesugM Bool := do
  let st ← get
  match st.externalObjectDeclarations.get? sym with
  | some (_, _, _, .static, _) => return true
  | _ =>
    match st.internalObjectDeclarations.get? sym with
    | some (_, .static, _) => return true
    | _ => return false

/-- `fetch_object_declaration` (`cabs_to_ail_effect.lem:1907`). -/
def fetchObjectDeclaration (sym : Sym) :
    DesugM (Bool × Loc × StorageDuration × Bool × Option Alignment × Qualifiers × Ctype) := do
  let st ← get
  match st.externalObjectDeclarations.get? sym with
  | some (isTentative, loc, _, dur, isRegister, alignOpt, qs, ty) =>
    return (isTentative, loc, dur, isRegister, alignOpt, qs, ty)
  | none =>
    match st.internalObjectDeclarations.get? sym with
    | some (loc, dur, isRegister, alignOpt, qs, ty) => return (false, loc, dur, isRegister, alignOpt, qs, ty)
    | none => internalError s!"TODO: failed to fetch object declaration ==> {stringOfSym sym}"

/-- `register_global_object_definition2` (`cabs_to_ail_effect.lem:1925-1976`): record the
definition of a file-scope object; tentative definitions combine (their composite type), a
real definition overrides a tentative one, and two definitions are an error (STD §6.9#3,
§6.9#5). -/
def registerGlobalObjectDefinition2 (loc : Loc) (sym : Sym) (link : Linkage)
    (gdef : GlobalDefinition) : DesugM Unit := do
  let st ← get
  let doUpdate (newGdef : GlobalDefinition) : DesugM Unit :=
    set { st with globalObjectDefinitions := st.globalObjectDefinitions.insert sym newGdef }
  match st.globalObjectDefinitions.get? sym with
  | none => doUpdate gdef
  | some prevGdef =>
    match prevGdef, gdef with
    | .tentative _ prevTy, .tentative locDef ty =>
      match makeComposite (← getTypeofEnum) prevTy ty with
      | none => internalError "[register_global_object_definition2] make_composite failed"
      | some ty' => doUpdate (.tentative locDef ty')
    | _, .tentative .. => return ()
    | .tentative .., _ => doUpdate gdef
    | .definition _, _ => internalError "[Cabs_to_ail_effect.register_global_object_definition] - internal ERROR 1"
    | .externalDefinition _, .externalDefinition _ =>
      match link with
      | .internal =>
        -- STD §6.9#3, sentence 1
        constraintViolation loc (.externalRedefinition sym)
      | .external =>
        -- STD §6.9#5, sentence 2
        undef loc .UB084
      | .none_ => internalError "[Cabs_to_ail_effect.register_global_object_definition] - internal ERROR 2"
    | .externalDefinition _, .definition _ =>
      internalError "[Cabs_to_ail_effect.register_global_object_definition] - internal ERROR 3"

/-- `register_global_object_definition` (`cabs_to_ail_effect.lem:1980-2002`): the definition
of an object with static or thread storage duration (no redefinition check). -/
def registerGlobalObjectDefinition (sym : Sym) (gdef : GlobalDefinition) : DesugM Unit := do
  match ← fetchObjectDeclaration sym with
  | (_, _, .static, _) | (_, _, .thread, _) =>
    modify fun st => { st with globalObjectDefinitions := st.globalObjectDefinitions.insert sym gdef }
  | _ =>
    internalError ("[Cabs_to_ail_effect] failed guard: register_static_global_definition must only " ++
      "be called for object with static storage duration ==> " ++ stringOfSym sym ++ ".")

/-- `register_function_definition` (`cabs_to_ail_effect.lem:2006`). -/
def registerFunctionDefinition (sym : Sym) (fdef : FunctionDefinitionD) : DesugM Unit :=
  modify fun st => { st with functionDefinitions := st.functionDefinitions.insert sym fdef }

/-- `global_object_is_defined` (`cabs_to_ail_effect.lem:2019`). -/
def globalObjectIsDefined (sym : Sym) : DesugM Bool :=
  return (← get).globalObjectDefinitions.contains sym

/-- `is_function_designator` (`cabs_to_ail_effect.lem:2025`). -/
def isFunctionDesignator (sym : Sym) : DesugM Bool :=
  return (← get).functionDeclarations.contains sym

/-- `function_is_defined` (`cabs_to_ail_effect.lem:2031`). -/
def functionIsDefined (sym : Sym) : DesugM Bool :=
  return (← get).functionDefinitions.contains sym

/-- `register_function_declaration` (`cabs_to_ail_effect.lem:2039-2104`): record a function's
declaration; a redeclaration must be compatible and makes the composite, keeping the first
declaration's prototype flag and location and concatenating the attributes. -/
def registerFunctionDeclaration (loc : Loc) (attrs : Attributes) (sym : Sym) (isProto : Bool)
    (decl : FunDeclaration) : DesugM Unit := do
  match (← get).functionDeclarations.get? sym with
  | some (prevHasProto, prevLoc, prevAttrs, prevDecl) =>
    match makeCompositeFdecl (← getTypeofEnum) prevDecl decl with
    | none => constraintViolation loc .sameScopeIncompatibleDeclarations
    | some decl' =>
      let entry := (prevHasProto, prevLoc, combineAttributes prevAttrs attrs, decl')
      modify fun st => { st with functionDeclarations := st.functionDeclarations.insert sym entry }
  | none =>
    modify fun st =>
      { st with functionDeclarations := st.functionDeclarations.insert sym (isProto, loc, attrs, decl) }

/-- `get_alignof` (`cabs_to_ail_effect.lem:2107-2117`): capture current tag definitions,
then use the shared LP64 layout. The implementation's enum registry is read at query
time, as in OCaml, so an alignment type name can declare an enum. Unsupported layouts
remain explicit rather than inventing an alignment. -/
def getAlignof : DesugM (Ctype → DesugM (Option Int)) := do
  let st ← get
  return fun ty => do
    let enums := (← get).registeredEnums
    let definitions := st.tagDefinitions.toList.filterMap fun (sym, def_) =>
      match def_ with
      | .struct loc _ _ xs flexibleOpt => some (sym, (loc, Silmaril.Cerberus.TagDefinition.struct xs flexibleOpt))
      | .union loc _ _ xs => some (sym, (loc, Silmaril.Cerberus.TagDefinition.union xs))
      | .enum _ => none
    let tags : Mem.Concrete.Tags :=
      { definitions := Map.ofList definitions, enums := Map.ofList enums }
    return (Mem.Concrete.alignment tags ty).toOption

/-- `get_compatible_alignment_requirements` (`cabs_to_ail_effect.lem:2121-2154`),
STD §6.7.5#7: a redeclaration can omit alignment, but specifying alignment requires
an equally strict previous requirement. The oracle's concrete implementation compares
the alignments of type specifiers. -/
def getCompatibleAlignmentRequirements (loc : Loc) (newAlignOpt prevAlignOpt : Option Alignment) :
    DesugM (Option Alignment) := do
  let alignofTy ← getAlignof
  let value : Alignment → DesugM Int
    | .integer n => pure n
    | .ctype ty => do
      match ← alignofTy ty with
      | some n => pure n
      | none => notPorted loc "alignment of this type in a redeclaration"
  match newAlignOpt, prevAlignOpt with
  | none, none => return none
  -- STD §6.7.5#7, sentence 2
  | some _, none => undef loc .UB072_incompatible_alignment_specifiers
  | none, some _ => return prevAlignOpt
  | some newAl, some prevAl =>
    if (← value newAl) == (← value prevAl) then return prevAlignOpt
    else undef loc .UB072_incompatible_alignment_specifiers

/-- `register_external_object_declaration` (`cabs_to_ail_effect.lem:2157-2217`): record an
object declared with linkage or at file scope; a redeclaration must keep `_Thread_local`
and a compatible type (STD §6.2.7#2), and replaces the previous declaration. -/
def registerExternalObjectDeclaration (sym : Sym) (newDecl : ExternalObjectDeclaration) :
    DesugM Unit := do
  let (isTentative, loc, attrs, newDur, isRegister, newAlignOpt, newQs, newTy) := newDecl
  match (← get).externalObjectDeclarations.get? sym with
  | some (_, _, _, prevDur, _, prevAlignOpt, prevQs, prevTy) =>
    let typeofEnum ← getTypeofEnum
    if !(prevDur != .thread || newDur == .thread) then
      constraintViolation loc .threadLocalShouldAppearInEveryDeclaration
    else if !areCompatible typeofEnum (newQs, newTy) (prevQs, prevTy) then
      -- STD §6.2.7#2
      undef loc .UB015_incompatible_redeclaration
    else
      let alignOpt ← getCompatibleAlignmentRequirements loc newAlignOpt prevAlignOpt
      match makeComposite typeofEnum prevTy newTy with
      | some _ =>
        let decl := (isTentative, loc, attrs, newDur, isRegister, alignOpt, newQs, newTy)
        modify fun st =>
          { st with externalObjectDeclarations := st.externalObjectDeclarations.insert sym decl }
      | none => internalError "WIP: register_external_object_declaration, make_composite failed"
  | none =>
    modify fun st =>
      { st with externalObjectDeclarations := st.externalObjectDeclarations.insert sym newDecl }

/-- `update_external_object_type` (`cabs_to_ail_effect.lem:2221`). -/
def updateExternalObjectType (sym : Sym) (ty : Ctype) : DesugM Unit := do
  let st ← get
  match st.externalObjectDeclarations.get? sym with
  | none => internalError "[Cabs_to_ail_effect.update_external_object_type] called on an unregistered symbol"
  | some (isTentative, loc, attrs, dur, isRegister, alignOpt, qs, _) =>
    set { st with externalObjectDeclarations :=
      st.externalObjectDeclarations.insert sym (isTentative, loc, attrs, dur, isRegister, alignOpt, qs, ty) }

/-- Lem's equality on internal object declarations. -/
def internalObjectDeclarationEqual (a b : InternalObjectDeclaration) : Bool :=
  let (l₁, d₁, r₁, a₁, q₁, t₁) := a
  let (l₂, d₂, r₂, a₂, q₂, t₂) := b
  l₁ == l₂ && d₁ == d₂ && r₁ == r₂ && alignmentEqual a₁ a₂ && q₁ == q₂ && ctypeEqual t₁ t₂

/-- `register_internal_object_declaration` (`cabs_to_ail_effect.lem:2241-2262`). -/
def registerInternalObjectDeclaration (sym : Sym) (decl : InternalObjectDeclaration) : DesugM Unit := do
  match (← get).internalObjectDeclarations.get? sym with
  | some decl' =>
    -- STD §6.2.7#2
    if !internalObjectDeclarationEqual decl decl' then undef decl.1 .UB015_incompatible_redeclaration
  | none =>
    modify fun st =>
      { st with internalObjectDeclarations := st.internalObjectDeclarations.insert sym decl }

/-- `update_internal_object_type` (`cabs_to_ail_effect.lem:2266`). -/
def updateInternalObjectType (sym : Sym) (ty : Ctype) : DesugM Unit := do
  let st ← get
  match st.internalObjectDeclarations.get? sym with
  | none => internalError "[Cabs_to_ail_effect.update_internal_object_type] called on an unregistered symbol"
  | some (loc, dur, isRegister, alignOpt, qs, _) =>
    set { st with internalObjectDeclarations :=
      st.internalObjectDeclarations.insert sym (loc, dur, isRegister, alignOpt, qs, ty) }

/-- `register_static_assertion` (`cabs_to_ail_effect.lem:2286`). -/
def registerStaticAssertion (e : Expression Unit) (strCst : StringLiteral) : DesugM Unit :=
  modify fun st => { st with staticAssertions := (e, strCst) :: st.staticAssertions }

/-- `register_label` (`cabs_to_ail_effect.lem:2293`). -/
def registerLabel (ident : Identifier) : DesugM Unit := do
  let _ ← internalRegisterIdentifier (fun _ _ => constraintViolation ident.loc (.labelRedefinition ident))
    ident .label .label none

/-- `resolve_label` (`cabs_to_ail_effect.lem:2300`). -/
def resolveLabel (ident : Identifier) : DesugM Sym := do
  match ← internalResolveIdentifier ident .label with
  | some (_, .internal sym _ _) => return sym
  | _ => constraintViolation ident.loc (.undeclaredLabel ident)

/-- `get_current_return_type_opt` (`cabs_to_ail_effect.lem:2312`). -/
def getCurrentReturnTypeOpt : DesugM (Option Ctype) := return (← get).currentReturnType

/-- `set_current_return_type` (`cabs_to_ail_effect.lem:2315`). -/
def setCurrentReturnType (tyOpt : Option Ctype) : DesugM Unit :=
  modify fun st => { st with currentReturnType := tyOpt }

/-- `inside_function` (`cabs_to_ail_effect.lem:2320`). -/
def insideFunction {α : Type} (returnTy : Ctype) (m : DesugM α) : DesugM α := do
  let saved ← getCurrentReturnTypeOpt
  setCurrentReturnType (some returnTy)
  let res ← m
  setCurrentReturnType saved
  return res

/-- `is_inside_function` (`cabs_to_ail_effect.lem:2328`). -/
def isInsideFunction : DesugM Bool := return (← get).currentReturnType.isSome

/-- `add_used_identifier` (`cabs_to_ail_effect.lem:2335`), `Utils.list_insert`. -/
def addUsedIdentifier (sym : Sym) : DesugM Unit :=
  modify fun st =>
    { st with usedIdentifier := st.usedIdentifier.insert sym () }

/-- `get_used_identifier` (`cabs_to_ail_effect.lem:2342`). -/
def getUsedIdentifier : DesugM (List Sym) := return (← get).usedIdentifier.keys

/-- `register_enum_constant` (`cabs_to_ail_effect.lem:2353-2368`): an enumeration constant
cannot be redeclared in its scope (STD footnote 127). -/
def registerEnumConstant (ident : Identifier) (expr : ExpressionNode Unit) : DesugM Unit := do
  let sym ← internalRegisterIdentifier (fun (scope, _) doFresh => do
    if ← currentScopeIs scope then fail ident.loc (.miscViolation (.multipleEnumDeclaration ident))
    else doFresh ())
    ident .ordinary (.ordinary .enumConstant) none
  modify fun st => { st with enumerationConstants := st.enumerationConstants.insert sym expr }

/-- `resolve_enum_constant` (`cabs_to_ail_effect.lem:2372`). -/
def resolveEnumConstant (sym : Sym) : DesugM (ExpressionNode Unit) := do
  match (← get).enumerationConstants.get? sym with
  | some e => return e
  | none => internalError "cabs_to_ail_effect.resolve_enum_constant"

/-! ## Sigma -/

/-- A sigma with the given declarations, definitions and tag definitions, and nothing else. -/
def sigmaOf {α : Type} (declarations : List (Sym × (Loc × Attributes × Declaration)))
    (functionDefinitions : List (Sym × FunctionDefinition α))
    (tagDefinitions : List (Sym × (Loc × Attributes × Silmaril.Cerberus.TagDefinition))) : Sigma α where
  declarations := declarations
  objectDefinitions := []
  functionDefinitions := functionDefinitions
  staticAssertions := []
  tagDefinitions := tagDefinitions
  externIdmap := []
  typedefAttributes := []
  loopAttributes := []
  cnFunctions := []
  cnLemmata := []
  cnPredicates := []
  cnDatatypes := []
  cnDeclSpecs := []
  cnIdents := []

/-- The struct and union definitions of the state, in symbol order, as sigma tag
definitions (enums are not tags of Ail). -/
def ailTagDefinitions (tagDefs : SymMap TagDefinition) :
    List (Sym × (Loc × Attributes × Silmaril.Cerberus.TagDefinition)) :=
  tagDefs.toList.filterMap fun (sym, def_) =>
    match def_ with
    | .struct loc attrs _ xs flexibleOpt => some (sym, (loc, attrs, .struct xs flexibleOpt))
    | .union loc attrs _ xs => some (sym, (loc, attrs, .union xs))
    | .enum _ => none

/-- `mk_current_ail_sigma` (`cabs_to_ail_effect.lem:2410-2437`): the tag definitions so far. -/
def mkCurrentAilSigma : DesugM (Sigma Unit) :=
  return sigmaOf [] [] (ailTagDefinitions (← get).tagDefinitions)

/-- `is_complete_object` (`cabs_to_ail_effect.lem:2441`). -/
def isCompleteObjectM (ty : Ctype) : DesugM Bool :=
  return isCompleteObject (← mkCurrentAilSigma) ty

/-- `is_incomplete` (`cabs_to_ail_effect.lem:2447`). -/
def isIncompleteM (ty : Ctype) : DesugM Bool :=
  return isIncomplete (← mkCurrentAilSigma) ty

/-- A function declaration as an Ail declaration (`extract_program`, 2474-2486). -/
def functionDeclarationOf : Bool × Loc × Attributes × FunDeclaration → Loc × Attributes × Declaration
  | (hasProto, loc, attrs, (retQsTy, paramsOpt, isVariadic, isInline, isNoreturn)) =>
    (loc, attrs, .function hasProto retQsTy (paramsOpt.getD []) isVariadic isInline isNoreturn)

/-- `get_gamma_sofar` (`cabs_to_ail_effect.lem:2646`): every object without linkage declared
so far. -/
def getGammaSofar : DesugM Bindings := do
  return (← get).internalObjectDeclarations.toList.map fun (sym, (loc, dur, b, alignOpt, qs, ty)) =>
    (sym, ((loc, dur, b), alignOpt, qs, ty))

/-- `get_sigma_sofar` (`cabs_to_ail_effect.lem:2660-2711`): the declarations, function
definitions, static assertions, tags, typedef attributes and loop attributes so far. -/
def getSigmaSofar : DesugM (Sigma Unit) := do
  let st ← get
  let decls : SymMap (Loc × Attributes × Declaration) :=
    st.externalObjectDeclarations.foldl (init := st.functionDeclarations.map fun _ d => functionDeclarationOf d)
      fun acc sym (_, loc, attrs, dur, isRegister, _, qs, ty) =>
        acc.insert sym (loc, attrs, .object (dur, isRegister) none qs ty)
  let fdefs := st.functionDefinitions.toList.map fun (sym, (loc, marker, attrs, params, body)) =>
    (sym, (⟨loc, marker, attrs, params, body⟩ : FunctionDefinition Unit))
  return { sigmaOf decls.toList fdefs (ailTagDefinitions st.tagDefinitions) with
    staticAssertions := st.staticAssertions
    typedefAttributes := st.typedefDefinitions.toList.map fun (sym, (z, _, _)) => (sym, z)
    loopAttributes := st.loopAttributes.toList }

/-! ## Extracting the program -/

/-- `extract_program` (`cabs_to_ail_effect.lem:2460-2626`): the Ail program of the final
state. The startup function is the external `startupStr`. The declarations are the function
declarations, the external objects (a tentative `T a[]` becomes `T a[1]`, STD §6.9.2#5
EXAMPLE 2) and the static and thread-local objects without linkage; every list is in symbol
order. Tentative definitions get zero values (and must be complete); internal identifiers
used but not defined, and external inline functions not defined, are errors (STD §6.9#3,
§6.7.4#7). -/
def extractProgram (startupStr : String) : DesugM (Program Unit) := do
  let st ← get
  let startupSymOpt :=
    (st.registeredExternalIdentifiers.get? (⟨.unknown, startupStr⟩, .ordinary)).map (·.2.1)
  let decls₁ : SymMap (Loc × Attributes × Declaration) :=
    st.functionDeclarations.map fun _ d => functionDeclarationOf d
  let decls₂ := st.externalObjectDeclarations.foldl (init := decls₁)
    fun acc sym (isTentative, loc, attrs, dur, isRegister, alignOpt, qs, ty) =>
      let ty' :=
        if isTentative then
          match ty with
          | .mk annots (.array elemTy none) => .mk annots (.array elemTy (some 1))
          | _ => ty
        else ty
      acc.insert sym (loc, attrs, .object (dur, isRegister) alignOpt qs ty')
  let decls := st.internalObjectDeclarations.foldl (init := decls₂)
    fun acc sym (loc, dur, isRegister, alignOpt, qs, ty) =>
      match dur with
      | .static | .thread => acc.insert sym (loc, noAttributes, .object (dur, isRegister) alignOpt qs ty)
      | .automatic => acc
  let declsMap := decls
  let decls := decls.toList
  let fundefSyms := st.functionDefinitions
  let externIdmap : Std.TreeMap Identifier (Sym × IdKind) (fun a b => Ord.compare a.name b.name) :=
    st.registeredExternalIdentifiers.foldl (init := ∅) fun acc (cid, ns) (scope, (sym, _, mLink)) =>
      match ns, scope, mLink with
      | .ordinary, .file, some .external =>
        let kind : IdKind := match st.globalObjectDefinitions.get? sym with
          | some (.tentative ..) => .tentative
          | some (.definition _) | some (.externalDefinition _) => .definition
          | none => if fundefSyms.contains sym then .definition else .declaration
        acc.insert cid (sym, kind)
      | _, _, _ => acc
  let objectDefs ← st.globalObjectDefinitions.toList.mapM fun (sym, gdef) =>
    match gdef with
    | .tentative loc (.mk _ (.array elemTy none)) =>
      -- STD §6.9.2#5 EXAMPLE 2
      return (sym, Expression.mk () [] loc (.const (.array elemTy [mkZeroInitAux st.tagDefinitions zeroInitDepth elemTy])))
    | .tentative loc ty => do
      if ← isIncompleteM ty then notPorted loc "the message of TentativeNotCompleted (prints a ctype)"
      else return (sym, mkZeroInit st.tagDefinitions ty)
    | .definition e | .externalDefinition e => return (sym, e)
  for ((ident, _), (_, (sym, kind, linkOpt))) in st.registeredExternalIdentifiers.toList do
    match linkOpt with
    | some .internal =>
      if st.usedIdentifier.contains sym &&
          (kind == .ordinary (.object false) || kind == .ordinary .function) &&
          !objectDefs.any (·.1.key == sym.key) && !st.functionDefinitions.contains sym then
        -- STD §6.9#3, sentence 2
        constraintViolation ident.loc (.externalRedefinition sym)
    | some .external =>
      if kind == .ordinary .function && !st.functionDefinitions.contains sym then
        match declsMap.get? sym with
        | some (loc, _, .function _ _ _ _ true _) => undef loc .UB070_inline_not_defined
        | _ => pure ()
    | _ => pure ()
  let fdefs := st.functionDefinitions.toList.map fun (sym, (loc, marker, attrs, params, body)) =>
    (sym, (⟨loc, marker, attrs, params, body⟩ : FunctionDefinition Unit))
  return (startupSymOpt, { sigmaOf decls fdefs (ailTagDefinitions st.tagDefinitions) with
    objectDefinitions := objectDefs
    staticAssertions := st.staticAssertions
    externIdmap := externIdmap.toList
    typedefAttributes := st.typedefDefinitions.toList.map fun (sym, (z, _, _)) => (sym, z)
    loopAttributes := st.loopAttributes.toList })

/-- `eval` (`cabs_to_ail_effect.lem:622-628`): run `m` from the initial state, then draw the
final marker. -/
def eval {α : Type} (digest : Digest) (m : DesugM α) : Except Ail.Reject α :=
  (do let res ← m; let _ ← finMarkersEnv; return res).run' (initialState digest)

end Silmaril.Cerberus.Frontend.Desugar
