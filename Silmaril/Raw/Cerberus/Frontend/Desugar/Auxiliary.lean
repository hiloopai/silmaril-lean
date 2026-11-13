module

public import Silmaril.Cerberus.Frontend.Typing.TypesAux.Defs
public import Silmaril.Cerberus.Frontend.Declarations.Defs

/-! # Auxiliary definitions of the desugaring: `Cabs_to_ail_aux`

A port of `frontend/model/cabs_to_ail_aux.lem` at `b3e11ea3` (the tag definitions and
linkages of the desugaring state, storage durations, zero values of tentative definitions,
`_Atomic` wrapping and composite function declarations), with the comparisons of the Lem
map keys the desugaring state uses.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend.Desugar

open Silmaril.Cerberus Silmaril.Cerberus.Ail

/-- Lexicographic comparison of byte lists, as OCaml's `compare` on the strings of
`Digest.compare`. -/
def compareBytes : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => match compare a b with
    | .eq => compareBytes as bs
    | o => o

/-- `Symbol.symbol_compare` (`symbol.lem:154`): the digest, then the number. -/
def symbolCompare (a b : Sym) : Ordering :=
  if a.digest == b.digest then compare a.number b.number
  else compareBytes a.digest.bytes b.digest.bytes

/-- The constructor index of a storage class (the C keyword `ext` ++ `ern` is index 1; the
evaluator's trust scan refuses the word, see `Declarations.scExtern`). -/
def storageClassIndex : Cabs.StorageClassSpecifier → Nat
  | .typedef => 0
  | .static => 2
  | .threadLocal => 3
  | .auto => 4
  | .register => 5
  | _ => 1

/-- Lem's equality on storage classes. -/
instance : BEq Cabs.StorageClassSpecifier := ⟨fun a b => storageClassIndex a == storageClassIndex b⟩

/-- `SC_extern`. -/
def scExtern : Cabs.StorageClassSpecifier := Declarations.scExtern

/-- Lem's equality on type qualifiers. -/
instance : BEq Cabs.TypeQualifier where
  beq
    | .const, .const | .restrict, .restrict | .volatile, .volatile | .atomic, .atomic => true
    | _, _ => false

/-- Lem's equality on function specifiers. -/
instance : BEq Cabs.FunctionSpecifier where
  beq
    | .inline, .inline | .noreturn, .noreturn => true
    | _, _ => false

/-- A Lem `map Symbol.sym 'a`. -/
abbrev SymMap (α : Type) := Std.TreeMap Sym α symbolCompare

/-- The desugaring's tag definitions: a struct or union with its location, attributes,
whether it is anonymous, its members and its flexible array member; an enum with its
values. Lem: `Cabs_to_ail_aux.tag_definition` (`cabs_to_ail_aux.lem:9-12`). -/
inductive TagDefinition where
  | struct (loc : Loc) (attrs : Attributes) (isAnonymous : Bool)
      (members : List (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype)))
      (flexible : Option FlexibleArrayMember)
  | union (loc : Loc) (attrs : Attributes) (isAnonymous : Bool)
      (members : List (Identifier × (Attributes × Option Alignment × Qualifiers × Ctype)))
  | enum (values : List Int)

/-- Linkages (STD §6.2.2#1). Lem: `Cabs_to_ail_aux.linkage` (`cabs_to_ail_aux.lem:16-19`). -/
inductive Linkage where
  | external | internal | none_
  deriving DecidableEq, Repr

/-- `Cabs_to_ail_aux.specifiers_of_external_declaration` (`cabs_to_ail_aux.lem:41`). -/
def specifiersOfExternalDeclaration : Cabs.ExternalDeclaration → Option Cabs.Specifiers
  | .func f => some f.specifiers
  | .decl (.base _ specifs _) => some specifs
  | _ => none

/-- `Cabs_to_ail_aux.determinate_storage_duration` (`cabs_to_ail_aux.lem:67-83`). Lem's
`error` (no linkage and `static`, unreachable) is `static` here. -/
def determinateStorageDuration (link : Linkage) (scs : List Cabs.StorageClassSpecifier) :
    StorageDuration :=
  if !scs.contains .threadLocal &&
      (link == .external || link == .internal || scs.contains .static) then
    -- STD §6.2.4#3, sentence 1
    .static
  else if scs.contains .threadLocal then
    -- STD §6.2.4#4, sentence 1
    .thread
  else
    -- STD §6.2.4#5, sentence 1
    .automatic

/-- `Cabs_to_ail_aux.mk_zeroInit_aux` (`cabs_to_ail_aux.lem:112-157`): the zero constant of an
object type. Struct members are looked up in the tag definitions, so the recursion carries
fuel (one unit per level of nesting; a type is far shallower than the bound). Lem's `error`
cases (void, function and unsized array types, unreachable for a complete object type) give
`null`. -/
def mkZeroInitAux (tagDefs : SymMap TagDefinition) : Nat → Ctype → Constant
  | 0, _ => .null
  | fuel + 1, .mk _ ty =>
    match ty with
    | .basic (.integer _) | .byte => .integer (.iconstant 0 .octal none)
    | .basic (.floating _) => .floating ("0.0", none)
    | .array elemTy (some n) => .array elemTy (List.replicate n.toNat (mkZeroInitAux tagDefs fuel elemTy))
    | .pointer .. => .null
    | .atomic atomTy => mkZeroInitAux tagDefs fuel atomTy
    | .struct tag =>
      match tagDefs.get? tag with
      | some (.struct _ _ _ xs _) =>
        -- the flexible array member is not initialised (no space is allocated for it)
        .struct tag (xs.map fun (membIdent, (_, _, _, membTy)) =>
          (membIdent, mkZeroInitAux tagDefs fuel membTy))
      | _ => .null
    | .union tag =>
      match tagDefs.get? tag with
      | some (.union _ _ _ ((membIdent, (_, _, _, membTy)) :: _)) =>
        .union tag membIdent (mkZeroInitAux tagDefs fuel membTy)
      | _ => .null
    | _ => .null

/-- The fuel of `mkZeroInitAux`. -/
def zeroInitDepth : Nat := 100000

/-- `Cabs_to_ail_aux.mk_zeroInit` (`cabs_to_ail_aux.lem:158`). -/
def mkZeroInit (tagDefs : SymMap TagDefinition) (ty : Ctype) : Expression Unit :=
  .mk () [] .unknown (.const (mkZeroInitAux tagDefs zeroInitDepth ty))

/-- `Cabs_to_ail_aux.zeroAil` (`cabs_to_ail_aux.lem:163`). -/
def zeroAil : Expression Unit := .mk () [] .unknown (.const (.integer (.iconstant 0 .octal none)))

/-- `Cabs_to_ail_aux.oneAil` (`cabs_to_ail_aux.lem:168`). -/
def oneAil : Expression Unit := .mk () [] .unknown (.const (.integer (.iconstant 1 .decimal none)))

/-- `Cabs_to_ail_aux.wrap_atomic` (`cabs_to_ail_aux.lem:174-187`): `_Atomic` on the return
type of a function, through pointers, or on the type. -/
def wrapAtomic : Ctype → Ctype
  | .mk annots (.function (rq, rt) ps v) => .mk annots (.function (rq, .mk [] (.atomic rt)) ps v)
  | .mk annots (.functionNoParams (rq, rt)) => .mk annots (.functionNoParams (rq, .mk [] (.atomic rt)))
  | .mk annots (.pointer rq rt) => .mk annots (.pointer rq (wrapAtomic rt))
  | ty@(.mk _ (.atomic _)) => ty
  | ty => .mk [] (.atomic ty)

/-- A function declaration: the qualified return type, the parameters (`none` without a
parameter type list; the `Bool` is `register`), and whether it is variadic, `inline` and
`_Noreturn`. Lem: `Cabs_to_ail_aux.fun_declaration` (`cabs_to_ail_aux.lem:189`). -/
abbrev FunDeclaration :=
  (Qualifiers × Ctype) × Option (List (Qualifiers × Ctype × Bool)) × Bool × Bool × Bool

/-- `Cabs_to_ail_aux.make_composite_fdecl` (`cabs_to_ail_aux.lem:192-222`): the composite of
two declarations of a function, or `none` if they are incompatible. As in Lem, the return
types are compared under the first declaration's qualifiers. -/
def makeCompositeFdecl (typeofEnum : Sym → Option IntegerType) (fdecl₁ fdecl₂ : FunDeclaration) :
    Option FunDeclaration :=
  let ((retQs₁, retTy₁), paramsOpt₁, isVariadic₁, isInline₁, isNoreturn₁) := fdecl₁
  let ((_, retTy₂), paramsOpt₂, isVariadic₂, isInline₂, isNoreturn₂) := fdecl₂
  if !areCompatible typeofEnum (retQs₁, retTy₁) (retQs₁, retTy₂) then none
  else if isVariadic₁ != isVariadic₂ then none
  else match makeComposite typeofEnum retTy₁ retTy₂ with
    | none => none
    | some retTy' =>
      let mkComposite z :=
        some ((retQs₁, retTy'), z, isVariadic₁, isInline₁ || isInline₂, isNoreturn₁ || isNoreturn₂)
      match paramsOpt₁, paramsOpt₂ with
      | some params₁, some params₂ =>
        match makeCompositeParams typeofEnum params₁ params₂ with
        | some params => mkComposite (some params)
        | none => none
      | none, some params | some params, none => mkComposite (some params)
      | none, none => mkComposite none

end Silmaril.Cerberus.Frontend.Desugar
