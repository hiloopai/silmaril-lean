module

public import Silmaril.Cerberus.Cabs.Syntax.Defs
public import Silmaril.Cerberus.Cabs.Wire.Defs

/-! # The wire codec of Cabs documents

Cerberus's oracle (`cerb-export2 --level cabs`) prints the Cabs of a translation
unit, or the error that stopped it, in the tagged S-expression dialect of
`docs/projects/cerberus.md`:

```
($document_cabs 1 ($str "<cerberus commit>") ($str "<impl>") <Cabs.translation_unit>)
($reject 1 ($str "<cerberus commit>") ($str "<impl>") ($str "<stage>") <Loc.t> ($str "<message>"))
```

each followed by one newline. Tags are the Lem names of `Silmaril.Cerberus.Cabs.Names`.
A Lem `string` that is not valid UTF-8 prints as `($bytes "<hex>")`, the dialect
extension of the Silmaril exporter; at the Cabs level it occurs only in string-literal
lexemes (`RawString`).

For each type there is an emitter `emitX : X → Out → Out` that appends the canonical
text, and a decoder `decodeX : Sx → Except String X`. Both follow the Lem
declarations constructor by constructor; types that are mutually recursive in Lem
are `partial` here, since the encodings recurse through lists and products.
`parseCabsDocument` reads, decodes, prints again and compares, so its success
theorem `print_parseCabsDocument` is the byte-exact print∘parse law.
`Silmaril.Cerberus.Cabs.CodecSpec` states how this printer relates to
`Formats.SExpEncoding.printTagged` and the `TaggedCodec` laws.
-/

@[expose] public section

namespace Silmaril.Cerberus.Cabs.Codec

open Silmaril.Cerberus Wire
open Silmaril.Cerberus.Cabs (RawString)

/-! ## Locations, identifiers and attributes

The wire forms of the Core port's types, as `Codec.loc`, `Codec.identifier` and
`Codec.attributes` encode them. -/

def emitLoc (l : Loc) (o : Out) : Out :=
  match l with
  | .unknown => o ++ "($loc_unknown)"
  | .other s => o |> open_ "$loc_other" |> arg (emitStr s) |> close
  | .point f l c => o |> open_ "$loc_point" |> arg (emitStr f) |> arg (emitInt l) |> arg (emitInt c)
    |> close
  | .region f l c f' l' c' =>
    o |> open_ "$loc_region" |> arg (emitStr f) |> arg (emitInt l) |> arg (emitInt c)
      |> arg (emitStr f') |> arg (emitInt l') |> arg (emitInt c') |> close

def decodeLoc : Sx → Except String Loc
  | .node "$loc_unknown" #[] => return .unknown
  | .node "$loc_other" #[s] => return .other (← decodeStr s)
  | .node "$loc_point" #[f, l, c] => return .point (← decodeStr f) (← decodeInt l) (← decodeInt c)
  | .node "$loc_region" #[f, l, c, f', l', c'] =>
    return .region (← decodeStr f) (← decodeInt l) (← decodeInt c) (← decodeStr f') (← decodeInt l')
      (← decodeInt c')
  | t => mismatch "Loc.t" t

def emitIdentifier (x : Identifier) (o : Out) : Out :=
  o |> open_ "Identifier" |> arg (emitLoc x.loc) |> arg (emitStr x.name) |> close

def decodeIdentifier : Sx → Except String Identifier
  | .node "Identifier" #[l, s] => return ⟨← decodeLoc l, ← decodeStr s⟩
  | t => mismatch "Symbol.identifier" t

/-- `list (Loc.t * string * list (Loc.t * string))`: a flat triple. -/
def emitAttributeArg (a : Loc × String × List (Loc × String)) (o : Out) : Out :=
  o |> open_ "$tuple" |> arg (emitLoc a.1) |> arg (emitStr a.2.1)
    |> arg (emitList (emitTuple2 emitLoc emitStr) a.2.2) |> close

def decodeAttributeArg : Sx → Except String (Loc × String × List (Loc × String))
  | .node "$tuple" #[l, s, xs] =>
    return (← decodeLoc l, ← decodeStr s, ← decodeList (decodeTuple2 decodeLoc decodeStr) xs)
  | t => mismatch "an attribute argument" t

def emitAttribute (a : Attribute) (o : Out) : Out :=
  o |> open_ "attribute" |> arg (emitOption emitIdentifier a.ns) |> arg (emitIdentifier a.id)
    |> arg (emitList emitAttributeArg a.args) |> close

def decodeAttribute : Sx → Except String Attribute
  | .node "attribute" #[ns, id, args] =>
    return ⟨← decodeOption decodeIdentifier ns,← decodeIdentifier id,
      ← decodeList decodeAttributeArg args⟩
  | t => mismatch "Annot.attribute" t

def emitAttributes (a : Attributes) (o : Out) : Out :=
  match a with
  | .mk as => o |> open_ "Attrs" |> arg (emitList emitAttribute as) |> close

def decodeAttributes : Sx → Except String Attributes
  | .node "Attrs" #[as] => return .mk (← decodeList decodeAttribute as)
  | t => mismatch "Annot.attributes" t

/-! ## Raw strings: `$str` or `$bytes` -/

def hexDigit (n : UInt8) : Char := "0123456789abcdef".toList[n.toNat]!

/-- Lowercase hexadecimal, two digits per byte. -/
def hex (b : ByteArray) : String :=
  b.foldl (fun s x => (s.push (hexDigit (x / 16))).push (hexDigit (x % 16))) ""

def unhexDigit (c : Char) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
  else none

/-- Decode lowercase hexadecimal; `none` on an odd length or another character. -/
def unhex (s : String) : Option ByteArray := go s.toList .empty
where
  go : List Char → ByteArray → Option ByteArray
    | [], acc => some acc
    | h :: l :: rest, acc => do go rest (acc.push ((← unhexDigit h) * 16 + (← unhexDigit l)))
    | [_], _ => none

def emitRawString (s : RawString) (o : Out) : Out :=
  match s with
  | .utf8 s => emitStr s o
  | .bytes b => o |> open_ "$bytes" |> arg (quoted (hex b)) |> close

def decodeRawString : Sx → Except String RawString
  | .node "$str" #[.str s] => return .utf8 s
  | .node "$bytes" #[.str h] => match unhex h with
    | some b => return .bytes b
    | none => throw s!"invalid $bytes payload {h.take 40}"
  | t => mismatch "a raw string" t

/-! ## CN types -/

section Cn
open Silmaril.Cerberus.Cn

def emitCnSign (x : Sign) (o : Out) : Out :=
  match x with
  | .unsigned => o ++ "(CN_unsigned)"
  | .signed => o ++ "(CN_signed)"

partial def emitCnBaseType {α : Type} (ea : α → Out → Out) (x : BaseType α) (o : Out) : Out :=
  match x with
  | .unit => o ++ "(CN_unit)"
  | .bool => o ++ "(CN_bool)"
  | .integer => o ++ "(CN_integer)"
  | .bits sign width =>
    o |> open_ "CN_bits" |> arg (emitCnSign sign) |> arg (emitInt width) |> close
  | .real => o ++ "(CN_real)"
  | .loc => o ++ "(CN_loc)"
  | .allocId => o ++ "(CN_alloc_id)"
  | .struct tag =>
    o |> open_ "CN_struct" |> arg (ea tag) |> close
  | .record fields =>
    o |> open_ "CN_record" |> arg (emitList (emitTuple2 emitIdentifier (emitCnBaseType ea)) fields)
      |> close
  | .datatype name =>
    o |> open_ "CN_datatype" |> arg (ea name) |> close
  | .map key value =>
    o |> open_ "CN_map" |> arg (emitCnBaseType ea key) |> arg (emitCnBaseType ea value) |> close
  | .list elem =>
    o |> open_ "CN_list" |> arg (emitCnBaseType ea elem) |> close
  | .tuple elems =>
    o |> open_ "CN_tuple" |> arg (emitList (emitCnBaseType ea) elems) |> close
  | .set elem =>
    o |> open_ "CN_set" |> arg (emitCnBaseType ea elem) |> close
  | .userTypeName name =>
    o |> open_ "CN_user_type_name" |> arg (ea name) |> close
  | .cTypedefName name =>
    o |> open_ "CN_c_typedef_name" |> arg (ea name) |> close

/-- `list ('a * cn_base_type 'a)`: the arguments of CN functions, lemmas and predicates. -/
def emitCnArgs {α : Type} (ea : α → Out → Out) (xs : List (α × BaseType α)) (o : Out) : Out :=
  emitList (emitTuple2 ea (emitCnBaseType ea)) xs o

def emitCnBinop (x : Binop) (o : Out) : Out :=
  match x with
  | .add => o ++ "(CN_add)"
  | .sub => o ++ "(CN_sub)"
  | .mul => o ++ "(CN_mul)"
  | .div => o ++ "(CN_div)"
  | .mod => o ++ "(CN_mod)"
  | .equal => o ++ "(CN_equal)"
  | .inequal => o ++ "(CN_inequal)"
  | .lt => o ++ "(CN_lt)"
  | .le => o ++ "(CN_le)"
  | .gt => o ++ "(CN_gt)"
  | .ge => o ++ "(CN_ge)"
  | .or => o ++ "(CN_or)"
  | .and => o ++ "(CN_and)"
  | .implies => o ++ "(CN_implies)"
  | .mapGet => o ++ "(CN_map_get)"
  | .band => o ++ "(CN_band)"
  | .bor => o ++ "(CN_bor)"
  | .bxor => o ++ "(CN_bxor)"

def emitCnCKind (x : CKind) (o : Out) : Out :=
  match x with
  | .var => o ++ "(C_kind_var)"
  | .enum => o ++ "(C_kind_enum)"

def emitCnConst (x : Const) (o : Out) : Out :=
  match x with
  | .null => o ++ "(CNConst_NULL)"
  | .integer n =>
    o |> open_ "CNConst_integer" |> arg (emitInt n) |> close
  | .bits type n =>
    o |> open_ "CNConst_bits" |> arg (emitTuple2 emitCnSign emitInt type) |> arg (emitInt n)
      |> close
  | .bool b =>
    o |> open_ "CNConst_bool" |> arg (emitBool b) |> close
  | .unit => o ++ "(CNConst_unit)"

mutual

partial def emitCnPatNode {α : Type} (ea : α → Out → Out) (x : PatNode α) (o : Out) : Out :=
  match x with
  | .sym x =>
    o |> open_ "CNPat_sym" |> arg (ea x) |> close
  | .wild => o ++ "(CNPat_wild)"
  | .constructor ctor args =>
    o |> open_ "CNPat_constructor" |> arg (ea ctor)
      |> arg (emitList (emitTuple2 emitIdentifier (emitCnPat ea)) args) |> close

partial def emitCnPat {α : Type} (ea : α → Out → Out) (x : Pat α) (o : Out) : Out :=
  match x with
  | .mk loc node =>
    o |> open_ "CNPat" |> arg (emitLoc loc) |> arg (emitCnPatNode ea node) |> close

end

mutual

partial def emitCnExprNode {α τ : Type} (ea : α → Out → Out) (et : τ → Out → Out)
    (x : ExprNode α τ) (o : Out) : Out :=
  match x with
  | .const c =>
    o |> open_ "CNExpr_const" |> arg (emitCnConst c) |> close
  | .var x =>
    o |> open_ "CNExpr_var" |> arg (ea x) |> close
  | .list elems =>
    o |> open_ "CNExpr_list" |> arg (emitList (emitCnExpr ea et) elems) |> close
  | .memberof e member =>
    o |> open_ "CNExpr_memberof" |> arg (emitCnExpr ea et e) |> arg (emitIdentifier member) |> close
  | .arrow e member =>
    o |> open_ "CNExpr_arrow" |> arg (emitCnExpr ea et e) |> arg (emitIdentifier member) |> close
  | .record fields =>
    o |> open_ "CNExpr_record"
      |> arg (emitList (emitTuple2 emitIdentifier (emitCnExpr ea et)) fields) |> close
  | .struct tag fields =>
    o |> open_ "CNExpr_struct" |> arg (ea tag)
      |> arg (emitList (emitTuple2 emitIdentifier (emitCnExpr ea et)) fields) |> close
  | .memberUpdates e updates =>
    o |> open_ "CNExpr_memberupdates" |> arg (emitCnExpr ea et e)
      |> arg (emitList (emitTuple2 emitIdentifier (emitCnExpr ea et)) updates) |> close
  | .arrayIndexUpdates e updates =>
    o |> open_ "CNExpr_arrayindexupdates" |> arg (emitCnExpr ea et e)
      |> arg (emitList (emitTuple2 (emitCnExpr ea et) (emitCnExpr ea et)) updates) |> close
  | .binop op lhs rhs =>
    o |> open_ "CNExpr_binop" |> arg (emitCnBinop op) |> arg (emitCnExpr ea et lhs)
      |> arg (emitCnExpr ea et rhs) |> close
  | .sizeof type =>
    o |> open_ "CNExpr_sizeof" |> arg (et type) |> close
  | .offsetof tag member =>
    o |> open_ "CNExpr_offsetof" |> arg (ea tag) |> arg (emitIdentifier member) |> close
  | .memberShift e type member =>
    o |> open_ "CNExpr_membershift" |> arg (emitCnExpr ea et e) |> arg (emitOption et type)
      |> arg (emitIdentifier member) |> close
  | .addr x =>
    o |> open_ "CNExpr_addr" |> arg (ea x) |> close
  | .cast type e =>
    o |> open_ "CNExpr_cast" |> arg (emitCnBaseType ea type) |> arg (emitCnExpr ea et e) |> close
  | .arrayShift base type index =>
    o |> open_ "CNExpr_array_shift" |> arg (emitCnExpr ea et base) |> arg (emitOption et type)
      |> arg (emitCnExpr ea et index) |> close
  | .call function args =>
    o |> open_ "CNExpr_call" |> arg (ea function) |> arg (emitList (emitCnExpr ea et) args) |> close
  | .cons ctor args =>
    o |> open_ "CNExpr_cons" |> arg (ea ctor)
      |> arg (emitList (emitTuple2 emitIdentifier (emitCnExpr ea et)) args) |> close
  | .each x type range body =>
    o |> open_ "CNExpr_each" |> arg (ea x) |> arg (emitCnBaseType ea type)
      |> arg (emitTuple2 emitInt emitInt range) |> arg (emitCnExpr ea et body) |> close
  | .let_ x value body =>
    o |> open_ "CNExpr_let" |> arg (ea x) |> arg (emitCnExpr ea et value)
      |> arg (emitCnExpr ea et body) |> close
  | .match_ scrutinee cases =>
    o |> open_ "CNExpr_match" |> arg (emitCnExpr ea et scrutinee)
      |> arg (emitList (emitTuple2 (emitCnPat ea) (emitCnExpr ea et)) cases) |> close
  | .ite cond then_ else_ =>
    o |> open_ "CNExpr_ite" |> arg (emitCnExpr ea et cond) |> arg (emitCnExpr ea et then_)
      |> arg (emitCnExpr ea et else_) |> close
  | .good type e =>
    o |> open_ "CNExpr_good" |> arg (et type) |> arg (emitCnExpr ea et e) |> close
  | .deref e =>
    o |> open_ "CNExpr_deref" |> arg (emitCnExpr ea et e) |> close
  | .valueOfCAtom x kind =>
    o |> open_ "CNExpr_value_of_c_atom" |> arg (ea x) |> arg (emitCnCKind kind) |> close
  | .unchanged e =>
    o |> open_ "CNExpr_unchanged" |> arg (emitCnExpr ea et e) |> close
  | .atEnv e env =>
    o |> open_ "CNExpr_at_env" |> arg (emitCnExpr ea et e) |> arg (emitStr env) |> close
  | .not e =>
    o |> open_ "CNExpr_not" |> arg (emitCnExpr ea et e) |> close
  | .negate e =>
    o |> open_ "CNExpr_negate" |> arg (emitCnExpr ea et e) |> close
  | .default type =>
    o |> open_ "CNExpr_default" |> arg (emitCnBaseType ea type) |> close
  | .bnot e =>
    o |> open_ "CNExpr_bnot" |> arg (emitCnExpr ea et e) |> close

partial def emitCnExpr {α τ : Type} (ea : α → Out → Out) (et : τ → Out → Out)
    (x : Expr α τ) (o : Out) : Out :=
  match x with
  | .mk loc node =>
    o |> open_ "CNExpr" |> arg (emitLoc loc) |> arg (emitCnExprNode ea et node) |> close

end

def emitCnPred {α τ : Type} (ea : α → Out → Out) (et : τ → Out → Out)
    (x : Pred α τ) (o : Out) : Out :=
  match x with
  | .owned type =>
    o |> open_ "CN_owned" |> arg (emitOption et type) |> close
  | .block type =>
    o |> open_ "CN_block" |> arg (emitOption et type) |> close
  | .named name =>
    o |> open_ "CN_named" |> arg (ea name) |> close

def emitCnResource {α τ : Type} (ea : α → Out → Out) (et : τ → Out → Out)
    (x : Resource α τ) (o : Out) : Out :=
  match x with
  | .pred loc pred args =>
    o |> open_ "CN_pred" |> arg (emitLoc loc) |> arg (emitCnPred ea et pred)
      |> arg (emitList (emitCnExpr ea et) args) |> close
  | .each x type guard loc pred args =>
    o |> open_ "CN_each" |> arg (ea x) |> arg (emitCnBaseType ea type)
      |> arg (emitCnExpr ea et guard) |> arg (emitLoc loc) |> arg (emitCnPred ea et pred)
      |> arg (emitList (emitCnExpr ea et) args) |> close

def emitCnAssertion {α τ : Type} (ea : α → Out → Out) (et : τ → Out → Out)
    (x : Assertion α τ) (o : Out) : Out :=
  match x with
  | .expr e =>
    o |> open_ "CN_assert_exp" |> arg (emitCnExpr ea et e) |> close
  | .quantified x type guard body =>
    o |> open_ "CN_assert_qexp" |> arg (ea x) |> arg (emitCnBaseType ea type)
      |> arg (emitCnExpr ea et guard) |> arg (emitCnExpr ea et body) |> close

def emitCnCondition {α τ : Type} (ea : α → Out → Out) (et : τ → Out → Out)
    (x : Condition α τ) (o : Out) : Out :=
  match x with
  | .letResource loc x resource =>
    o |> open_ "CN_cletResource" |> arg (emitLoc loc) |> arg (ea x)
      |> arg (emitCnResource ea et resource) |> close
  | .letExpr loc x e =>
    o |> open_ "CN_cletExpr" |> arg (emitLoc loc) |> arg (ea x) |> arg (emitCnExpr ea et e) |> close
  | .constraint loc assertion =>
    o |> open_ "CN_cconstr" |> arg (emitLoc loc) |> arg (emitCnAssertion ea et assertion) |> close

partial def emitCnClause {α τ : Type} (ea : α → Out → Out) (et : τ → Out → Out)
    (x : Clause α τ) (o : Out) : Out :=
  match x with
  | .letResource loc x resource rest =>
    o |> open_ "CN_letResource" |> arg (emitLoc loc) |> arg (ea x)
      |> arg (emitCnResource ea et resource) |> arg (emitCnClause ea et rest) |> close
  | .letExpr loc x e rest =>
    o |> open_ "CN_letExpr" |> arg (emitLoc loc) |> arg (ea x) |> arg (emitCnExpr ea et e)
      |> arg (emitCnClause ea et rest) |> close
  | .assert loc assertion rest =>
    o |> open_ "CN_assert" |> arg (emitLoc loc) |> arg (emitCnAssertion ea et assertion)
      |> arg (emitCnClause ea et rest) |> close
  | .return_ loc e =>
    o |> open_ "CN_return" |> arg (emitLoc loc) |> arg (emitCnExpr ea et e) |> close

partial def emitCnClauses {α τ : Type} (ea : α → Out → Out) (et : τ → Out → Out)
    (x : Clauses α τ) (o : Out) : Out :=
  match x with
  | .clause loc clause =>
    o |> open_ "CN_clause" |> arg (emitLoc loc) |> arg (emitCnClause ea et clause) |> close
  | .if_ loc cond then_ else_ =>
    o |> open_ "CN_if" |> arg (emitLoc loc) |> arg (emitCnExpr ea et cond)
      |> arg (emitCnClause ea et then_) |> arg (emitCnClauses ea et else_) |> close

def emitCnAccFunc {α : Type} (ea : α → Out → Out) (x : AccFunc α) (o : Out) : Out :=
  match x with
  | .accesses xs =>
    o |> open_ "CN_accesses" |> arg (emitList ea xs) |> close
  | .mkFunction x =>
    o |> open_ "CN_mk_function" |> arg (ea x) |> close

/-- A `requires` or `ensures` clause,
`(Loc.t * (list ('a * cn_base_type 'a) * list cn_condition))`. -/
def emitCnSpecClause {α τ : Type} (ea : α → Out → Out) (et : τ → Out → Out)
    (c : Loc × List (α × BaseType α) × List (Condition α τ)) (o : Out) : Out :=
  emitTuple2 emitLoc (emitTuple2 (emitCnArgs ea) (emitList (emitCnCondition ea et))) c o

def emitCnFuncSpec {α τ : Type} (ea : α → Out → Out) (et : τ → Out → Out)
    (x : FuncSpec α τ) (o : Out) : Out :=
  match x with
  | ⟨trusted, accFunc, requires, ensures⟩ =>
    o |> open_ "cn_func_spec"
      |> arg (emitOption emitLoc trusted)
      |> arg (emitOption (emitTuple2 emitLoc (emitCnAccFunc ea)) accFunc)
      |> arg (emitOption (emitCnSpecClause ea et) requires)
      |> arg (emitOption (emitCnSpecClause ea et) ensures) |> close

def emitCnDeclSpec {α τ : Type} (ea : α → Out → Out) (et : τ → Out → Out)
    (x : DeclSpec α τ) (o : Out) : Out :=
  match x with
  | ⟨loc, name, args, funcSpec⟩ =>
    o |> open_ "cn_decl_spec"
      |> arg (emitLoc loc)
      |> arg (ea name)
      |> arg (emitCnArgs ea args)
      |> arg (emitCnFuncSpec ea et funcSpec) |> close

def emitCnFunction {α τ : Type} (ea : α → Out → Out) (et : τ → Out → Out)
    (x : Function α τ) (o : Out) : Out :=
  match x with
  | ⟨magicLoc, loc, name, attrs, args, body, returnType⟩ =>
    o |> open_ "cn_function"
      |> arg (emitLoc magicLoc)
      |> arg (emitLoc loc)
      |> arg (ea name)
      |> arg (emitList emitIdentifier attrs)
      |> arg (emitCnArgs ea args)
      |> arg (emitOption (emitCnExpr ea et) body)
      |> arg (emitCnBaseType ea returnType) |> close

def emitCnLemma {α τ : Type} (ea : α → Out → Out) (et : τ → Out → Out)
    (x : Lemma α τ) (o : Out) : Out :=
  match x with
  | ⟨magicLoc, loc, name, args, requires, ensures⟩ =>
    o |> open_ "cn_lemma"
      |> arg (emitLoc magicLoc)
      |> arg (emitLoc loc)
      |> arg (ea name)
      |> arg (emitCnArgs ea args)
      |> arg (emitList (emitCnCondition ea et) requires)
      |> arg (emitList (emitCnCondition ea et) ensures) |> close

def emitCnPredicate {α τ : Type} (ea : α → Out → Out) (et : τ → Out → Out)
    (x : Predicate α τ) (o : Out) : Out :=
  match x with
  | ⟨magicLoc, loc, name, attrs, output, iargs, clauses⟩ =>
    o |> open_ "cn_predicate"
      |> arg (emitLoc magicLoc)
      |> arg (emitLoc loc)
      |> arg (ea name)
      |> arg (emitList emitIdentifier attrs)
      |> arg (emitTuple2 emitLoc (emitCnBaseType ea) output)
      |> arg (emitCnArgs ea iargs)
      |> arg (emitOption (emitCnClauses ea et) clauses) |> close

def emitCnDatatype {α : Type} (ea : α → Out → Out) (x : Datatype α) (o : Out) : Out :=
  match x with
  | ⟨magicLoc, loc, name, cases⟩ =>
    o |> open_ "cn_datatype"
      |> arg (emitLoc magicLoc)
      |> arg (emitLoc loc)
      |> arg (ea name)
      |> arg (emitList (emitTuple2 ea (emitList (emitTuple2 emitIdentifier
            (emitCnBaseType ea)))) cases)
        |> close

def emitCnTypeSynonym {α : Type} (ea : α → Out → Out) (x : TypeSynonym α) (o : Out) : Out :=
  match x with
  | ⟨magicLoc, loc, name, rhs⟩ =>
    o |> open_ "cn_type_synonym"
      |> arg (emitLoc magicLoc)
      |> arg (emitLoc loc)
      |> arg (ea name)
      |> arg (emitCnBaseType ea rhs) |> close


def decodeCnSign : Sx → Except String Sign
  | .node "CN_unsigned" #[] => return .unsigned
  | .node "CN_signed" #[] => return .signed
  | t => mismatch "Cn.sign" t

partial def decodeCnBaseType {α : Type} (da : Sx → Except String α) :
    Sx → Except String (BaseType α)
  | .node "CN_unit" #[] => return .unit
  | .node "CN_bool" #[] => return .bool
  | .node "CN_integer" #[] => return .integer
  | .node "CN_bits" #[sign, width] => do
    return .bits (← decodeCnSign sign) (← decodeInt width)
  | .node "CN_real" #[] => return .real
  | .node "CN_loc" #[] => return .loc
  | .node "CN_alloc_id" #[] => return .allocId
  | .node "CN_struct" #[tag] => do
    return .struct (← da tag)
  | .node "CN_record" #[fields] => do
    return .record (← decodeList (decodeTuple2 decodeIdentifier (decodeCnBaseType da)) fields)
  | .node "CN_datatype" #[name] => do
    return .datatype (← da name)
  | .node "CN_map" #[key, value] => do
    return .map (← decodeCnBaseType da key) (← decodeCnBaseType da value)
  | .node "CN_list" #[elem] => do
    return .list (← decodeCnBaseType da elem)
  | .node "CN_tuple" #[elems] => do
    return .tuple (← decodeList (decodeCnBaseType da) elems)
  | .node "CN_set" #[elem] => do
    return .set (← decodeCnBaseType da elem)
  | .node "CN_user_type_name" #[name] => do
    return .userTypeName (← da name)
  | .node "CN_c_typedef_name" #[name] => do
    return .cTypedefName (← da name)
  | t => mismatch "Cn.cn_base_type" t

def decodeCnArgs {α : Type} (da : Sx → Except String α) :
    Sx → Except String (List (α × BaseType α)) :=
  decodeList (decodeTuple2 da (decodeCnBaseType da))

def decodeCnBinop : Sx → Except String Binop
  | .node "CN_add" #[] => return .add
  | .node "CN_sub" #[] => return .sub
  | .node "CN_mul" #[] => return .mul
  | .node "CN_div" #[] => return .div
  | .node "CN_mod" #[] => return .mod
  | .node "CN_equal" #[] => return .equal
  | .node "CN_inequal" #[] => return .inequal
  | .node "CN_lt" #[] => return .lt
  | .node "CN_le" #[] => return .le
  | .node "CN_gt" #[] => return .gt
  | .node "CN_ge" #[] => return .ge
  | .node "CN_or" #[] => return .or
  | .node "CN_and" #[] => return .and
  | .node "CN_implies" #[] => return .implies
  | .node "CN_map_get" #[] => return .mapGet
  | .node "CN_band" #[] => return .band
  | .node "CN_bor" #[] => return .bor
  | .node "CN_bxor" #[] => return .bxor
  | t => mismatch "Cn.cn_binop" t

def decodeCnCKind : Sx → Except String CKind
  | .node "C_kind_var" #[] => return .var
  | .node "C_kind_enum" #[] => return .enum
  | t => mismatch "Cn.cn_c_kind" t

def decodeCnConst : Sx → Except String Const
  | .node "CNConst_NULL" #[] => return .null
  | .node "CNConst_integer" #[n] => do
    return .integer (← decodeInt n)
  | .node "CNConst_bits" #[type, n] => do
    return .bits (← decodeTuple2 decodeCnSign decodeInt type) (← decodeInt n)
  | .node "CNConst_bool" #[b] => do
    return .bool (← decodeBool b)
  | .node "CNConst_unit" #[] => return .unit
  | t => mismatch "Cn.cn_const" t

mutual

partial def decodeCnPatNode {α : Type} (da : Sx → Except String α) : Sx → Except String (PatNode α)
  | .node "CNPat_sym" #[x] => do
    return .sym (← da x)
  | .node "CNPat_wild" #[] => return .wild
  | .node "CNPat_constructor" #[ctor, args] => do
    return .constructor (← da ctor)
      (← decodeList (decodeTuple2 decodeIdentifier (decodeCnPat da)) args)
  | t => mismatch "Cn.cn_pat_" t

partial def decodeCnPat {α : Type} (da : Sx → Except String α) : Sx → Except String (Pat α)
  | .node "CNPat" #[loc, node] => do
    return .mk (← decodeLoc loc) (← decodeCnPatNode da node)
  | t => mismatch "Cn.cn_pat" t

end

mutual

partial def decodeCnExprNode {α τ : Type} (da : Sx → Except String α) (dt : Sx → Except String τ) :
    Sx → Except String (ExprNode α τ)
  | .node "CNExpr_const" #[c] => do
    return .const (← decodeCnConst c)
  | .node "CNExpr_var" #[x] => do
    return .var (← da x)
  | .node "CNExpr_list" #[elems] => do
    return .list (← decodeList (decodeCnExpr da dt) elems)
  | .node "CNExpr_memberof" #[e, member] => do
    return .memberof (← decodeCnExpr da dt e) (← decodeIdentifier member)
  | .node "CNExpr_arrow" #[e, member] => do
    return .arrow (← decodeCnExpr da dt e) (← decodeIdentifier member)
  | .node "CNExpr_record" #[fields] => do
    return .record (← decodeList (decodeTuple2 decodeIdentifier (decodeCnExpr da dt)) fields)
  | .node "CNExpr_struct" #[tag, fields] => do
    return .struct (← da tag)
      (← decodeList (decodeTuple2 decodeIdentifier (decodeCnExpr da dt)) fields)
  | .node "CNExpr_memberupdates" #[e, updates] => do
    return .memberUpdates (← decodeCnExpr da dt e)
      (← decodeList (decodeTuple2 decodeIdentifier (decodeCnExpr da dt)) updates)
  | .node "CNExpr_arrayindexupdates" #[e, updates] => do
    return .arrayIndexUpdates (← decodeCnExpr da dt e)
      (← decodeList (decodeTuple2 (decodeCnExpr da dt) (decodeCnExpr da dt)) updates)
  | .node "CNExpr_binop" #[op, lhs, rhs] => do
    return .binop (← decodeCnBinop op) (← decodeCnExpr da dt lhs) (← decodeCnExpr da dt rhs)
  | .node "CNExpr_sizeof" #[type] => do
    return .sizeof (← dt type)
  | .node "CNExpr_offsetof" #[tag, member] => do
    return .offsetof (← da tag) (← decodeIdentifier member)
  | .node "CNExpr_membershift" #[e, type, member] => do
    return .memberShift (← decodeCnExpr da dt e) (← decodeOption dt type)
      (← decodeIdentifier member)
  | .node "CNExpr_addr" #[x] => do
    return .addr (← da x)
  | .node "CNExpr_cast" #[type, e] => do
    return .cast (← decodeCnBaseType da type) (← decodeCnExpr da dt e)
  | .node "CNExpr_array_shift" #[base, type, index] => do
    return .arrayShift (← decodeCnExpr da dt base) (← decodeOption dt type)
      (← decodeCnExpr da dt index)
  | .node "CNExpr_call" #[function, args] => do
    return .call (← da function) (← decodeList (decodeCnExpr da dt) args)
  | .node "CNExpr_cons" #[ctor, args] => do
    return .cons (← da ctor)
      (← decodeList (decodeTuple2 decodeIdentifier (decodeCnExpr da dt)) args)
  | .node "CNExpr_each" #[x, type, range, body] => do
    return .each (← da x) (← decodeCnBaseType da type) (← decodeTuple2 decodeInt decodeInt range)
      (← decodeCnExpr da dt body)
  | .node "CNExpr_let" #[x, value, body] => do
    return .let_ (← da x) (← decodeCnExpr da dt value) (← decodeCnExpr da dt body)
  | .node "CNExpr_match" #[scrutinee, cases] => do
    return .match_ (← decodeCnExpr da dt scrutinee)
      (← decodeList (decodeTuple2 (decodeCnPat da) (decodeCnExpr da dt)) cases)
  | .node "CNExpr_ite" #[cond, then_, else_] => do
    return .ite (← decodeCnExpr da dt cond) (← decodeCnExpr da dt then_)
      (← decodeCnExpr da dt else_)
  | .node "CNExpr_good" #[type, e] => do
    return .good (← dt type) (← decodeCnExpr da dt e)
  | .node "CNExpr_deref" #[e] => do
    return .deref (← decodeCnExpr da dt e)
  | .node "CNExpr_value_of_c_atom" #[x, kind] => do
    return .valueOfCAtom (← da x) (← decodeCnCKind kind)
  | .node "CNExpr_unchanged" #[e] => do
    return .unchanged (← decodeCnExpr da dt e)
  | .node "CNExpr_at_env" #[e, env] => do
    return .atEnv (← decodeCnExpr da dt e) (← decodeStr env)
  | .node "CNExpr_not" #[e] => do
    return .not (← decodeCnExpr da dt e)
  | .node "CNExpr_negate" #[e] => do
    return .negate (← decodeCnExpr da dt e)
  | .node "CNExpr_default" #[type] => do
    return .default (← decodeCnBaseType da type)
  | .node "CNExpr_bnot" #[e] => do
    return .bnot (← decodeCnExpr da dt e)
  | t => mismatch "Cn.cn_expr_" t

partial def decodeCnExpr {α τ : Type} (da : Sx → Except String α) (dt : Sx → Except String τ) :
    Sx → Except String (Expr α τ)
  | .node "CNExpr" #[loc, node] => do
    return .mk (← decodeLoc loc) (← decodeCnExprNode da dt node)
  | t => mismatch "Cn.cn_expr" t

end

def decodeCnPred {α τ : Type} (da : Sx → Except String α) (dt : Sx → Except String τ) :
    Sx → Except String (Pred α τ)
  | .node "CN_owned" #[type] => do
    return .owned (← decodeOption dt type)
  | .node "CN_block" #[type] => do
    return .block (← decodeOption dt type)
  | .node "CN_named" #[name] => do
    return .named (← da name)
  | t => mismatch "Cn.cn_pred" t

def decodeCnResource {α τ : Type} (da : Sx → Except String α) (dt : Sx → Except String τ) :
    Sx → Except String (Resource α τ)
  | .node "CN_pred" #[loc, pred, args] => do
    return .pred (← decodeLoc loc) (← decodeCnPred da dt pred)
      (← decodeList (decodeCnExpr da dt) args)
  | .node "CN_each" #[x, type, guard, loc, pred, args] => do
    return .each (← da x) (← decodeCnBaseType da type) (← decodeCnExpr da dt guard)
      (← decodeLoc loc) (← decodeCnPred da dt pred) (← decodeList (decodeCnExpr da dt) args)
  | t => mismatch "Cn.cn_resource" t

def decodeCnAssertion {α τ : Type} (da : Sx → Except String α) (dt : Sx → Except String τ) :
    Sx → Except String (Assertion α τ)
  | .node "CN_assert_exp" #[e] => do
    return .expr (← decodeCnExpr da dt e)
  | .node "CN_assert_qexp" #[x, type, guard, body] => do
    return .quantified (← da x) (← decodeCnBaseType da type) (← decodeCnExpr da dt guard)
      (← decodeCnExpr da dt body)
  | t => mismatch "Cn.cn_assertion" t

def decodeCnCondition {α τ : Type} (da : Sx → Except String α) (dt : Sx → Except String τ) :
    Sx → Except String (Condition α τ)
  | .node "CN_cletResource" #[loc, x, resource] => do
    return .letResource (← decodeLoc loc) (← da x) (← decodeCnResource da dt resource)
  | .node "CN_cletExpr" #[loc, x, e] => do
    return .letExpr (← decodeLoc loc) (← da x) (← decodeCnExpr da dt e)
  | .node "CN_cconstr" #[loc, assertion] => do
    return .constraint (← decodeLoc loc) (← decodeCnAssertion da dt assertion)
  | t => mismatch "Cn.cn_condition" t

partial def decodeCnClause {α τ : Type} (da : Sx → Except String α) (dt : Sx → Except String τ) :
    Sx → Except String (Clause α τ)
  | .node "CN_letResource" #[loc, x, resource, rest] => do
    return .letResource (← decodeLoc loc) (← da x) (← decodeCnResource da dt resource)
      (← decodeCnClause da dt rest)
  | .node "CN_letExpr" #[loc, x, e, rest] => do
    return .letExpr (← decodeLoc loc) (← da x) (← decodeCnExpr da dt e)
      (← decodeCnClause da dt rest)
  | .node "CN_assert" #[loc, assertion, rest] => do
    return .assert (← decodeLoc loc) (← decodeCnAssertion da dt assertion)
      (← decodeCnClause da dt rest)
  | .node "CN_return" #[loc, e] => do
    return .return_ (← decodeLoc loc) (← decodeCnExpr da dt e)
  | t => mismatch "Cn.cn_clause" t

partial def decodeCnClauses {α τ : Type} (da : Sx → Except String α) (dt : Sx → Except String τ) :
    Sx → Except String (Clauses α τ)
  | .node "CN_clause" #[loc, clause] => do
    return .clause (← decodeLoc loc) (← decodeCnClause da dt clause)
  | .node "CN_if" #[loc, cond, then_, else_] => do
    return .if_ (← decodeLoc loc) (← decodeCnExpr da dt cond) (← decodeCnClause da dt then_)
      (← decodeCnClauses da dt else_)
  | t => mismatch "Cn.cn_clauses" t

def decodeCnAccFunc {α : Type} (da : Sx → Except String α) : Sx → Except String (AccFunc α)
  | .node "CN_accesses" #[xs] => do
    return .accesses (← decodeList da xs)
  | .node "CN_mk_function" #[x] => do
    return .mkFunction (← da x)
  | t => mismatch "Cn.cn_acc_func" t

def decodeCnSpecClause {α τ : Type} (da : Sx → Except String α) (dt : Sx → Except String τ) :
    Sx → Except String (Loc × List (α × BaseType α) × List (Condition α τ)) :=
  decodeTuple2 decodeLoc (decodeTuple2 (decodeCnArgs da) (decodeList (decodeCnCondition da dt)))

def decodeCnFuncSpec {α τ : Type} (da : Sx → Except String α) (dt : Sx → Except String τ) :
    Sx → Except String (FuncSpec α τ)
  | .node "cn_func_spec" #[trusted, accFunc, requires, ensures] => do
    return ⟨← decodeOption decodeLoc trusted,
      ← decodeOption (decodeTuple2 decodeLoc (decodeCnAccFunc da)) accFunc,
      ← decodeOption (decodeCnSpecClause da dt) requires,
      ← decodeOption (decodeCnSpecClause da dt) ensures⟩
  | t => mismatch "Cn.cn_func_spec" t

def decodeCnDeclSpec {α τ : Type} (da : Sx → Except String α) (dt : Sx → Except String τ) :
    Sx → Except String (DeclSpec α τ)
  | .node "cn_decl_spec" #[loc, name, args, funcSpec] => do
    return ⟨← decodeLoc loc,← da name,← decodeCnArgs da args,
      ← decodeCnFuncSpec da dt funcSpec⟩
  | t => mismatch "Cn.cn_decl_spec" t

def decodeCnFunction {α τ : Type} (da : Sx → Except String α) (dt : Sx → Except String τ) :
    Sx → Except String (Function α τ)
  | .node "cn_function" #[magicLoc, loc, name, attrs, args, body, returnType] => do
    return ⟨← decodeLoc magicLoc,← decodeLoc loc,← da name,← decodeList decodeIdentifier attrs,
      ← decodeCnArgs da args,
      ← decodeOption (decodeCnExpr da dt) body,← decodeCnBaseType da returnType⟩
  | t => mismatch "Cn.cn_function" t

def decodeCnLemma {α τ : Type} (da : Sx → Except String α) (dt : Sx → Except String τ) :
    Sx → Except String (Lemma α τ)
  | .node "cn_lemma" #[magicLoc, loc, name, args, requires, ensures] => do
    return ⟨← decodeLoc magicLoc,← decodeLoc loc,← da name,
      ← decodeCnArgs da args,
      ← decodeList (decodeCnCondition da dt) requires,
      ← decodeList (decodeCnCondition da dt) ensures⟩
  | t => mismatch "Cn.cn_lemma" t

def decodeCnPredicate {α τ : Type} (da : Sx → Except String α) (dt : Sx → Except String τ) :
    Sx → Except String (Predicate α τ)
  | .node "cn_predicate" #[magicLoc, loc, name, attrs, output, iargs, clauses] => do
    return ⟨← decodeLoc magicLoc,← decodeLoc loc,← da name,← decodeList decodeIdentifier attrs,
      ← decodeTuple2 decodeLoc (decodeCnBaseType da) output,
      ← decodeCnArgs da iargs,
      ← decodeOption (decodeCnClauses da dt) clauses⟩
  | t => mismatch "Cn.cn_predicate" t

def decodeCnDatatype {α : Type} (da : Sx → Except String α) : Sx → Except String (Datatype α)
  | .node "cn_datatype" #[magicLoc, loc, name, cases] => do
    return ⟨← decodeLoc magicLoc,← decodeLoc loc,← da name,
      ← decodeList (decodeTuple2 da (decodeList (decodeTuple2 decodeIdentifier
          (decodeCnBaseType da)))) cases⟩
  | t => mismatch "Cn.cn_datatype" t

def decodeCnTypeSynonym {α : Type} (da : Sx → Except String α) : Sx → Except String (TypeSynonym α)
  | .node "cn_type_synonym" #[magicLoc, loc, name, rhs] => do
    return ⟨← decodeLoc magicLoc, ← decodeLoc loc, ← da name, ← decodeCnBaseType da rhs⟩
  | t => mismatch "Cn.cn_type_synonym" t


end Cn

/-! ## Cabs types -/

section Cabs
open Silmaril.Cerberus.Cabs

def emitIntegerSuffix (x : IntegerSuffix) (o : Out) : Out :=
  match x with
  | .u => o ++ "(CabsSuffix_U)"
  | .ul => o ++ "(CabsSuffix_UL)"
  | .ull => o ++ "(CabsSuffix_ULL)"
  | .l => o ++ "(CabsSuffix_L)"
  | .ll => o ++ "(CabsSuffix_LL)"

def emitFloatingSuffix (x : FloatingSuffix) (o : Out) : Out :=
  match x with
  | .f => o ++ "(CabsFloatingSuffix_F)"
  | .l => o ++ "(CabsFloatingSuffix_L)"

def emitCharacterPrefix (x : CharacterPrefix) (o : Out) : Out :=
  match x with
  | .wide => o ++ "(CabsPrefix_L)"
  | .utf16 => o ++ "(CabsPrefix_u)"
  | .utf32 => o ++ "(CabsPrefix_U)"

def emitConstant (x : Constant) (o : Out) : Out :=
  match x with
  | .integer c =>
    o |> open_ "CabsInteger_const" |> arg (emitTuple2 emitStr (emitOption emitIntegerSuffix) c)
      |> close
  | .floating c =>
    o |> open_ "CabsFloating_const" |> arg (emitTuple2 emitStr (emitOption emitFloatingSuffix) c)
      |> close
  | .character c =>
    o |> open_ "CabsCharacter_const" |> arg (emitTuple2 (emitOption emitCharacterPrefix) emitStr c)
      |> close

def emitEncodingPrefix (x : EncodingPrefix) (o : Out) : Out :=
  match x with
  | .utf8 => o ++ "(CabsEncPrefix_u8)"
  | .utf16 => o ++ "(CabsEncPrefix_u)"
  | .utf32 => o ++ "(CabsEncPrefix_U)"
  | .wide => o ++ "(CabsEncPrefix_L)"

/-- `cabs_string_literal`, an alias: the prefix and the lexemes of each piece. -/
def emitStringLiteral (s : StringLiteral) (o : Out) : Out :=
  emitTuple2 (emitOption emitEncodingPrefix) (emitList (emitTuple2 emitLoc
      (emitList emitRawString))) s o

def emitUnaryOperator (x : UnaryOperator) (o : Out) : Out :=
  match x with
  | .address => o ++ "(CabsAddress)"
  | .indirection => o ++ "(CabsIndirection)"
  | .plus => o ++ "(CabsPlus)"
  | .minus => o ++ "(CabsMinus)"
  | .bnot => o ++ "(CabsBnot)"
  | .not => o ++ "(CabsNot)"

def emitBinaryOperator (x : BinaryOperator) (o : Out) : Out :=
  match x with
  | .mul => o ++ "(CabsMul)"
  | .div => o ++ "(CabsDiv)"
  | .mod => o ++ "(CabsMod)"
  | .add => o ++ "(CabsAdd)"
  | .sub => o ++ "(CabsSub)"
  | .shl => o ++ "(CabsShl)"
  | .shr => o ++ "(CabsShr)"
  | .lt => o ++ "(CabsLt)"
  | .gt => o ++ "(CabsGt)"
  | .le => o ++ "(CabsLe)"
  | .ge => o ++ "(CabsGe)"
  | .eq => o ++ "(CabsEq)"
  | .ne => o ++ "(CabsNe)"
  | .band => o ++ "(CabsBand)"
  | .bxor => o ++ "(CabsBxor)"
  | .bor => o ++ "(CabsBor)"
  | .and => o ++ "(CabsAnd)"
  | .or => o ++ "(CabsOr)"

def emitAssignmentOperator (x : AssignmentOperator) (o : Out) : Out :=
  match x with
  | .assign => o ++ "(Assign)"
  | .mul => o ++ "(Assign_Mul)"
  | .div => o ++ "(Assign_Div)"
  | .mod => o ++ "(Assign_Mod)"
  | .add => o ++ "(Assign_Add)"
  | .sub => o ++ "(Assign_Sub)"
  | .shl => o ++ "(Assign_Shl)"
  | .shr => o ++ "(Assign_Shr)"
  | .band => o ++ "(Assign_Band)"
  | .bxor => o ++ "(Assign_Bxor)"
  | .bor => o ++ "(Assign_Bor)"

def emitStorageClassSpecifier (x : StorageClassSpecifier) (o : Out) : Out :=
  match x with
  | .typedef => o ++ "(SC_typedef)"
  | .extern => o ++ "(SC_extern)"
  | .static => o ++ "(SC_static)"
  | .threadLocal => o ++ "(SC_Thread_local)"
  | .auto => o ++ "(SC_auto)"
  | .register => o ++ "(SC_register)"

def emitTypeQualifier (x : TypeQualifier) (o : Out) : Out :=
  match x with
  | .const => o ++ "(Q_const)"
  | .restrict => o ++ "(Q_restrict)"
  | .volatile => o ++ "(Q_volatile)"
  | .atomic => o ++ "(Q_Atomic)"

def emitFunctionSpecifier (x : FunctionSpecifier) (o : Out) : Out :=
  match x with
  | .inline => o ++ "(FS_inline)"
  | .noreturn => o ++ "(FS_Noreturn)"

mutual

partial def emitExpressionNode (x : ExpressionNode) (o : Out) : Out :=
  match x with
  | .ident x =>
    o |> open_ "CabsEident" |> arg (emitIdentifier x) |> close
  | .const c =>
    o |> open_ "CabsEconst" |> arg (emitConstant c) |> close
  | .string s =>
    o |> open_ "CabsEstring"
      |> arg (emitStringLiteral s)
      |> close
  | .generic controlling associations =>
    o |> open_ "CabsEgeneric" |> arg (emitExpression controlling)
      |> arg (emitList emitGenericAssociation associations) |> close
  | .subscript array index =>
    o |> open_ "CabsEsubscript" |> arg (emitExpression array) |> arg (emitExpression index) |> close
  | .call function args attrs =>
    o |> open_ "CabsEcall" |> arg (emitExpression function) |> arg (emitList emitExpression args)
      |> arg (emitOption emitAttributes attrs) |> close
  | .memberof e member =>
    o |> open_ "CabsEmemberof" |> arg (emitExpression e) |> arg (emitIdentifier member) |> close
  | .memberofptr e member =>
    o |> open_ "CabsEmemberofptr" |> arg (emitExpression e) |> arg (emitIdentifier member) |> close
  | .postincr e =>
    o |> open_ "CabsEpostincr" |> arg (emitExpression e) |> close
  | .postdecr e =>
    o |> open_ "CabsEpostdecr" |> arg (emitExpression e) |> close
  | .compound type inits =>
    o |> open_ "CabsEcompound" |> arg (emitTypeName type)
      |> arg (emitList (emitTuple2 (emitOption (emitList emitDesignator)) emitInitializer) inits)
      |> close
  | .preincr e =>
    o |> open_ "CabsEpreincr" |> arg (emitExpression e) |> close
  | .predecr e =>
    o |> open_ "CabsEpredecr" |> arg (emitExpression e) |> close
  | .unary op e =>
    o |> open_ "CabsEunary" |> arg (emitUnaryOperator op) |> arg (emitExpression e) |> close
  | .sizeofExpr e =>
    o |> open_ "CabsEsizeof_expr" |> arg (emitExpression e) |> close
  | .sizeofType type =>
    o |> open_ "CabsEsizeof_type" |> arg (emitTypeName type) |> close
  | .alignof type =>
    o |> open_ "CabsEalignof" |> arg (emitTypeName type) |> close
  | .cast type e =>
    o |> open_ "CabsEcast" |> arg (emitTypeName type) |> arg (emitExpression e) |> close
  | .binary op lhs rhs =>
    o |> open_ "CabsEbinary" |> arg (emitBinaryOperator op) |> arg (emitExpression lhs)
      |> arg (emitExpression rhs) |> close
  | .cond cond then_ else_ =>
    o |> open_ "CabsEcond" |> arg (emitExpression cond) |> arg (emitExpression then_)
      |> arg (emitExpression else_) |> close
  | .assign op lhs rhs =>
    o |> open_ "CabsEassign" |> arg (emitAssignmentOperator op) |> arg (emitExpression lhs)
      |> arg (emitExpression rhs) |> close
  | .comma lhs rhs =>
    o |> open_ "CabsEcomma" |> arg (emitExpression lhs) |> arg (emitExpression rhs) |> close
  | .assert e =>
    o |> open_ "CabsEassert" |> arg (emitExpression e) |> close
  | .offsetof type member =>
    o |> open_ "CabsEoffsetof" |> arg (emitTypeName type) |> arg (emitIdentifier member) |> close
  | .vaStart list param =>
    o |> open_ "CabsEva_start" |> arg (emitExpression list) |> arg (emitIdentifier param) |> close
  | .vaCopy dst src =>
    o |> open_ "CabsEva_copy" |> arg (emitExpression dst) |> arg (emitExpression src) |> close
  | .vaArg list type =>
    o |> open_ "CabsEva_arg" |> arg (emitExpression list) |> arg (emitTypeName type) |> close
  | .vaEnd list =>
    o |> open_ "CabsEva_end" |> arg (emitExpression list) |> close
  | .printType e =>
    o |> open_ "CabsEprint_type" |> arg (emitExpression e) |> close
  | .bmcAssume e =>
    o |> open_ "CabsEbmc_assume" |> arg (emitExpression e) |> close
  | .labelAddressGnu label =>
    o |> open_ "CabsElabel_addressGNU" |> arg (emitIdentifier label) |> close
  | .gccStatement body =>
    o |> open_ "CabsEgcc_statement" |> arg (emitList emitStatement body) |> close
  | .condGnu cond else_ =>
    o |> open_ "CabsEcondGNU" |> arg (emitExpression cond) |> arg (emitExpression else_) |> close
  | .builtinGnu builtin =>
    o |> open_ "CabsEbuiltinGNU" |> arg (emitGnuBuiltinFunction builtin) |> close

partial def emitGnuBuiltinFunction (x : GnuBuiltinFunction) (o : Out) : Out :=
  match x with
  | .typesCompatibleP t1 t2 =>
    o |> open_ "GNUbuiltin_types_compatible_p" |> arg (emitTypeName t1) |> arg (emitTypeName t2)
      |> close
  | .chooseExpr cond then_ else_ =>
    o |> open_ "GNUbuiltin_choose_expr" |> arg (emitExpression cond) |> arg (emitExpression then_)
      |> arg (emitExpression else_) |> close

partial def emitExpression (x : Expression) (o : Out) : Out :=
  match x with
  | .mk loc node =>
    o |> open_ "CabsExpression" |> arg (emitLoc loc) |> arg (emitExpressionNode node) |> close

partial def emitGenericAssociation (x : GenericAssociation) (o : Out) : Out :=
  match x with
  | .type_ type e =>
    o |> open_ "GA_type" |> arg (emitTypeName type) |> arg (emitExpression e) |> close
  | .default e =>
    o |> open_ "GA_default" |> arg (emitExpression e) |> close

partial def emitDeclaration (x : Declaration) (o : Out) : Out :=
  match x with
  | .base attrs specifiers declarators =>
    o |> open_ "Declaration_base" |> arg (emitAttributes attrs) |> arg (emitSpecifiers specifiers)
      |> arg (emitList emitInitDeclarator declarators) |> close
  | .staticAssert assertion =>
    o |> open_ "Declaration_static_assert" |> arg (emitStaticAssertDeclaration assertion) |> close

partial def emitSpecifiers (x : Specifiers) (o : Out) : Out :=
  match x with
  | ⟨storageClasses, typeSpecifiers, typeQualifiers, functionSpecifiers, alignmentSpecifiers⟩ =>
    o |> open_ "specifiers"
      |> arg (emitList emitStorageClassSpecifier storageClasses)
      |> arg (emitList emitTypeSpecifier typeSpecifiers)
      |> arg (emitList emitTypeQualifier typeQualifiers)
      |> arg (emitList emitFunctionSpecifier functionSpecifiers)
      |> arg (emitList emitAlignmentSpecifier alignmentSpecifiers) |> close

partial def emitInitDeclarator (x : InitDeclarator) (o : Out) : Out :=
  match x with
  | .mk loc declarator init =>
    o |> open_ "InitDecl" |> arg (emitLoc loc) |> arg (emitDeclarator declarator)
      |> arg (emitOption emitInitializer init) |> close

partial def emitTypeSpecifierNode (x : TypeSpecifierNode) (o : Out) : Out :=
  match x with
  | .void => o ++ "(TSpec_void)"
  | .char => o ++ "(TSpec_char)"
  | .short => o ++ "(TSpec_short)"
  | .int => o ++ "(TSpec_int)"
  | .long => o ++ "(TSpec_long)"
  | .float => o ++ "(TSpec_float)"
  | .double => o ++ "(TSpec_double)"
  | .signed => o ++ "(TSpec_signed)"
  | .unsigned => o ++ "(TSpec_unsigned)"
  | .bool => o ++ "(TSpec_Bool)"
  | .complex => o ++ "(TSpec_Complex)"
  | .atomic type =>
    o |> open_ "TSpec_Atomic" |> arg (emitTypeName type) |> close
  | .struct attrs tag members =>
    o |> open_ "TSpec_struct" |> arg (emitAttributes attrs) |> arg (emitOption emitIdentifier tag)
      |> arg (emitOption (emitList emitStructDeclaration) members) |> close
  | .union attrs tag members =>
    o |> open_ "TSpec_union" |> arg (emitAttributes attrs) |> arg (emitOption emitIdentifier tag)
      |> arg (emitOption (emitList emitStructDeclaration) members) |> close
  | .enum tag enumerators =>
    o |> open_ "TSpec_enum" |> arg (emitOption emitIdentifier tag)
      |> arg (emitOption (emitList (emitTuple2 emitIdentifier
          (emitOption emitExpression))) enumerators)
      |> close
  | .name name =>
    o |> open_ "TSpec_name" |> arg (emitIdentifier name) |> close
  | .typeofExpr e =>
    o |> open_ "TSpec_typeof_expr" |> arg (emitExpression e) |> close
  | .typeofType type =>
    o |> open_ "TSpec_typeof_type" |> arg (emitTypeName type) |> close

partial def emitTypeSpecifier (x : TypeSpecifier) (o : Out) : Out :=
  match x with
  | .mk loc node =>
    o |> open_ "TSpec" |> arg (emitLoc loc) |> arg (emitTypeSpecifierNode node) |> close

partial def emitStructDeclaration (x : StructDeclaration) (o : Out) : Out :=
  match x with
  | .member attrs typeSpecifiers typeQualifiers alignmentSpecifiers declarators =>
    o |> open_ "Struct_declaration" |> arg (emitAttributes attrs)
      |> arg (emitList emitTypeSpecifier typeSpecifiers)
      |> arg (emitList emitTypeQualifier typeQualifiers)
      |> arg (emitList emitAlignmentSpecifier alignmentSpecifiers)
      |> arg (emitList emitStructDeclarator declarators) |> close
  | .staticAssert assertion =>
    o |> open_ "Struct_assert" |> arg (emitStaticAssertDeclaration assertion) |> close

partial def emitStructDeclarator (x : StructDeclarator) (o : Out) : Out :=
  match x with
  | .simple declarator =>
    o |> open_ "SDecl_simple" |> arg (emitDeclarator declarator) |> close
  | .bitfield declarator width =>
    o |> open_ "SDecl_bitfield" |> arg (emitOption emitDeclarator declarator)
      |> arg (emitExpression width) |> close

partial def emitAlignmentSpecifier (x : AlignmentSpecifier) (o : Out) : Out :=
  match x with
  | .type_ type =>
    o |> open_ "AS_type" |> arg (emitTypeName type) |> close
  | .expr e =>
    o |> open_ "AS_expr" |> arg (emitExpression e) |> close

partial def emitDeclarator (x : Declarator) (o : Out) : Out :=
  match x with
  | .mk pointer direct =>
    o |> open_ "Declarator" |> arg (emitOption emitPointerDeclarator pointer)
      |> arg (emitDirectDeclarator direct) |> close

partial def emitDirectDeclarator (x : DirectDeclarator) (o : Out) : Out :=
  match x with
  | .identifier attrs name =>
    o |> open_ "DDecl_identifier" |> arg (emitAttributes attrs) |> arg (emitIdentifier name)
      |> close
  | .declarator inner =>
    o |> open_ "DDecl_declarator" |> arg (emitDeclarator inner) |> close
  | .array inner array =>
    o |> open_ "DDecl_array" |> arg (emitDirectDeclarator inner) |> arg (emitArrayDeclarator array)
      |> close
  | .function inner params =>
    o |> open_ "DDecl_function" |> arg (emitDirectDeclarator inner)
      |> arg (emitParameterTypeList params) |> close

partial def emitArrayDeclarator (x : ArrayDeclarator) (o : Out) : Out :=
  match x with
  | .mk loc qualifiers isStatic size =>
    o |> open_ "ADecl" |> arg (emitLoc loc) |> arg (emitList emitTypeQualifier qualifiers)
      |> arg (emitBool isStatic) |> arg (emitOption emitArrayDeclaratorSize size) |> close

partial def emitArrayDeclaratorSize (x : ArrayDeclaratorSize) (o : Out) : Out :=
  match x with
  | .expression e =>
    o |> open_ "ADeclSize_expression" |> arg (emitExpression e) |> close
  | .asterisk => o ++ "(ADeclSize_asterisk)"

partial def emitPointerDeclarator (x : PointerDeclarator) (o : Out) : Out :=
  match x with
  | .mk loc qualifiers next =>
    o |> open_ "PDecl" |> arg (emitLoc loc) |> arg (emitList emitTypeQualifier qualifiers)
      |> arg (emitOption emitPointerDeclarator next) |> close

partial def emitParameterTypeList (x : ParameterTypeList) (o : Out) : Out :=
  match x with
  | .mk params variadic =>
    o |> open_ "Params" |> arg (emitList emitParameterDeclaration params) |> arg (emitBool variadic)
      |> close

partial def emitParameterDeclaration (x : ParameterDeclaration) (o : Out) : Out :=
  match x with
  | .declarator specifiers declarator =>
    o |> open_ "PDeclaration_decl" |> arg (emitSpecifiers specifiers)
      |> arg (emitDeclarator declarator) |> close
  | .abstract specifiers declarator =>
    o |> open_ "PDeclaration_abs_decl" |> arg (emitSpecifiers specifiers)
      |> arg (emitOption emitAbstractDeclarator declarator) |> close

partial def emitTypeName (x : TypeName) (o : Out) : Out :=
  match x with
  | .mk typeSpecifiers typeQualifiers alignmentSpecifiers declarator =>
    o |> open_ "Type_name" |> arg (emitList emitTypeSpecifier typeSpecifiers)
      |> arg (emitList emitTypeQualifier typeQualifiers)
      |> arg (emitList emitAlignmentSpecifier alignmentSpecifiers)
      |> arg (emitOption emitAbstractDeclarator declarator) |> close

partial def emitAbstractDeclarator (x : AbstractDeclarator) (o : Out) : Out :=
  match x with
  | .pointer pointer =>
    o |> open_ "AbsDecl_pointer" |> arg (emitPointerDeclarator pointer) |> close
  | .direct pointer direct =>
    o |> open_ "AbsDecl_direct" |> arg (emitOption emitPointerDeclarator pointer)
      |> arg (emitDirectAbstractDeclarator direct) |> close

partial def emitDirectAbstractDeclarator (x : DirectAbstractDeclarator) (o : Out) : Out :=
  match x with
  | .abstract inner =>
    o |> open_ "DAbs_abs_declarator" |> arg (emitAbstractDeclarator inner) |> close
  | .array inner array =>
    o |> open_ "DAbs_array" |> arg (emitOption emitDirectAbstractDeclarator inner)
      |> arg (emitArrayDeclarator array) |> close
  | .function inner params =>
    o |> open_ "DAbs_function" |> arg (emitOption emitDirectAbstractDeclarator inner)
      |> arg (emitParameterTypeList params) |> close

partial def emitInitializer (x : Initializer) (o : Out) : Out :=
  match x with
  | .expr e =>
    o |> open_ "Init_expr" |> arg (emitExpression e) |> close
  | .list loc inits =>
    o |> open_ "Init_list" |> arg (emitLoc loc)
      |> arg (emitList (emitTuple2 (emitOption (emitList emitDesignator)) emitInitializer) inits)
      |> close

partial def emitDesignator (x : Designator) (o : Out) : Out :=
  match x with
  | .array index =>
    o |> open_ "Desig_array" |> arg (emitExpression index) |> close
  | .member member =>
    o |> open_ "Desig_member" |> arg (emitIdentifier member) |> close

partial def emitStaticAssertDeclaration (x : StaticAssertDeclaration) (o : Out) : Out :=
  match x with
  | .mk cond message =>
    o |> open_ "Static_assert" |> arg (emitExpression cond)
      |> arg (emitStringLiteral message)
      |> close

partial def emitStatementNode (x : StatementNode) (o : Out) : Out :=
  match x with
  | .label label s =>
    o |> open_ "CabsSlabel" |> arg (emitIdentifier label) |> arg (emitStatement s) |> close
  | .case_ e s =>
    o |> open_ "CabsScase" |> arg (emitExpression e) |> arg (emitStatement s) |> close
  | .default s =>
    o |> open_ "CabsSdefault" |> arg (emitStatement s) |> close
  | .block items =>
    o |> open_ "CabsSblock" |> arg (emitList emitStatement items) |> close
  | .decl d =>
    o |> open_ "CabsSdecl" |> arg (emitDeclaration d) |> close
  | .null => o ++ "(CabsSnull)"
  | .expr e =>
    o |> open_ "CabsSexpr" |> arg (emitExpression e) |> close
  | .if_ cond then_ else_ =>
    o |> open_ "CabsSif" |> arg (emitExpression cond) |> arg (emitStatement then_)
      |> arg (emitOption emitStatement else_) |> close
  | .switch e s =>
    o |> open_ "CabsSswitch" |> arg (emitExpression e) |> arg (emitStatement s) |> close
  | .while_ cond body =>
    o |> open_ "CabsSwhile" |> arg (emitExpression cond) |> arg (emitStatement body) |> close
  | .do_ cond body =>
    o |> open_ "CabsSdo" |> arg (emitExpression cond) |> arg (emitStatement body) |> close
  | .for_ init cond step body =>
    o |> open_ "CabsSfor" |> arg (emitOption emitForClause init)
      |> arg (emitOption emitExpression cond) |> arg (emitOption emitExpression step)
      |> arg (emitStatement body) |> close
  | .goto label =>
    o |> open_ "CabsSgoto" |> arg (emitIdentifier label) |> close
  | .continue_ => o ++ "(CabsScontinue)"
  | .break_ => o ++ "(CabsSbreak)"
  | .return_ e =>
    o |> open_ "CabsSreturn" |> arg (emitOption emitExpression e) |> close
  | .par threads =>
    o |> open_ "CabsSpar" |> arg (emitList emitStatement threads) |> close
  | .asm isVolatile isInline templates =>
    o |> open_ "CabsSasm" |> arg (emitBool isVolatile) |> arg (emitBool isInline)
      |> arg (emitList (emitTuple2 emitLoc (emitList emitRawString)) templates) |> close
  | .caseRangeGnu lo hi s =>
    o |> open_ "CabsScaseGNU" |> arg (emitExpression lo) |> arg (emitExpression hi)
      |> arg (emitStatement s) |> close
  | .marker s =>
    o |> open_ "CabsSmarker" |> arg (emitStatement s) |> close

partial def emitStatement (x : Statement) (o : Out) : Out :=
  match x with
  | .mk loc attrs node =>
    o |> open_ "CabsStatement" |> arg (emitLoc loc) |> arg (emitAttributes attrs)
      |> arg (emitStatementNode node) |> close

partial def emitForClause (x : ForClause) (o : Out) : Out :=
  match x with
  | .expr e =>
    o |> open_ "FC_expr" |> arg (emitExpression e) |> close
  | .decl loc d =>
    o |> open_ "FC_decl" |> arg (emitLoc loc) |> arg (emitDeclaration d) |> close

end

def emitFunctionDefinition (x : FunctionDefinition) (o : Out) : Out :=
  match x with
  | .mk loc attrs specifiers declarator body =>
    o |> open_ "FunDef" |> arg (emitLoc loc) |> arg (emitAttributes attrs)
      |> arg (emitSpecifiers specifiers) |> arg (emitDeclarator declarator)
      |> arg (emitStatement body) |> close

def emitExternalDeclaration (x : ExternalDeclaration) (o : Out) : Out :=
  match x with
  | .func f =>
    o |> open_ "EDecl_func" |> arg (emitFunctionDefinition f) |> close
  | .decl d =>
    o |> open_ "EDecl_decl" |> arg (emitDeclaration d) |> close
  | .magic comment =>
    o |> open_ "EDecl_magic" |> arg (emitTuple2 emitLoc emitStr comment) |> close
  | .funcCn f =>
    o |> open_ "EDecl_funcCN" |> arg (emitCnFunction emitIdentifier emitTypeName f) |> close
  | .lemmaCn l =>
    o |> open_ "EDecl_lemmaCN" |> arg (emitCnLemma emitIdentifier emitTypeName l) |> close
  | .predCn p =>
    o |> open_ "EDecl_predCN" |> arg (emitCnPredicate emitIdentifier emitTypeName p) |> close
  | .datatypeCn d =>
    o |> open_ "EDecl_datatypeCN" |> arg (emitCnDatatype emitIdentifier d) |> close
  | .typeSynCn t =>
    o |> open_ "EDecl_type_synCN" |> arg (emitCnTypeSynonym emitIdentifier t) |> close
  | .funSpecCn s =>
    o |> open_ "EDecl_fun_specCN" |> arg (emitCnDeclSpec emitIdentifier emitTypeName s) |> close

def emitTranslationUnit (x : TranslationUnit) (o : Out) : Out :=
  match x with
  | .mk declarations =>
    o |> open_ "TUnit" |> arg (emitList emitExternalDeclaration declarations) |> close

def decodeIntegerSuffix : Sx → Except String IntegerSuffix
  | .node "CabsSuffix_U" #[] => return .u
  | .node "CabsSuffix_UL" #[] => return .ul
  | .node "CabsSuffix_ULL" #[] => return .ull
  | .node "CabsSuffix_L" #[] => return .l
  | .node "CabsSuffix_LL" #[] => return .ll
  | t => mismatch "Cabs.cabs_integer_suffix" t

def decodeFloatingSuffix : Sx → Except String FloatingSuffix
  | .node "CabsFloatingSuffix_F" #[] => return .f
  | .node "CabsFloatingSuffix_L" #[] => return .l
  | t => mismatch "Cabs.cabs_floating_suffix" t

def decodeCharacterPrefix : Sx → Except String CharacterPrefix
  | .node "CabsPrefix_L" #[] => return .wide
  | .node "CabsPrefix_u" #[] => return .utf16
  | .node "CabsPrefix_U" #[] => return .utf32
  | t => mismatch "Cabs.cabs_character_prefix" t

def decodeConstant : Sx → Except String Constant
  | .node "CabsInteger_const" #[c] => do
    return .integer (← decodeTuple2 decodeStr (decodeOption decodeIntegerSuffix) c)
  | .node "CabsFloating_const" #[c] => do
    return .floating (← decodeTuple2 decodeStr (decodeOption decodeFloatingSuffix) c)
  | .node "CabsCharacter_const" #[c] => do
    return .character (← decodeTuple2 (decodeOption decodeCharacterPrefix) decodeStr c)
  | t => mismatch "Cabs.cabs_constant" t

def decodeEncodingPrefix : Sx → Except String EncodingPrefix
  | .node "CabsEncPrefix_u8" #[] => return .utf8
  | .node "CabsEncPrefix_u" #[] => return .utf16
  | .node "CabsEncPrefix_U" #[] => return .utf32
  | .node "CabsEncPrefix_L" #[] => return .wide
  | t => mismatch "Cabs.cabs_encoding_prefix" t

def decodeStringLiteral : Sx → Except String StringLiteral :=
  decodeTuple2 (decodeOption decodeEncodingPrefix) (decodeList (decodeTuple2 decodeLoc
      (decodeList decodeRawString)))

def decodeUnaryOperator : Sx → Except String UnaryOperator
  | .node "CabsAddress" #[] => return .address
  | .node "CabsIndirection" #[] => return .indirection
  | .node "CabsPlus" #[] => return .plus
  | .node "CabsMinus" #[] => return .minus
  | .node "CabsBnot" #[] => return .bnot
  | .node "CabsNot" #[] => return .not
  | t => mismatch "Cabs.cabs_unary_operator" t

def decodeBinaryOperator : Sx → Except String BinaryOperator
  | .node "CabsMul" #[] => return .mul
  | .node "CabsDiv" #[] => return .div
  | .node "CabsMod" #[] => return .mod
  | .node "CabsAdd" #[] => return .add
  | .node "CabsSub" #[] => return .sub
  | .node "CabsShl" #[] => return .shl
  | .node "CabsShr" #[] => return .shr
  | .node "CabsLt" #[] => return .lt
  | .node "CabsGt" #[] => return .gt
  | .node "CabsLe" #[] => return .le
  | .node "CabsGe" #[] => return .ge
  | .node "CabsEq" #[] => return .eq
  | .node "CabsNe" #[] => return .ne
  | .node "CabsBand" #[] => return .band
  | .node "CabsBxor" #[] => return .bxor
  | .node "CabsBor" #[] => return .bor
  | .node "CabsAnd" #[] => return .and
  | .node "CabsOr" #[] => return .or
  | t => mismatch "Cabs.cabs_binary_operator" t

def decodeAssignmentOperator : Sx → Except String AssignmentOperator
  | .node "Assign" #[] => return .assign
  | .node "Assign_Mul" #[] => return .mul
  | .node "Assign_Div" #[] => return .div
  | .node "Assign_Mod" #[] => return .mod
  | .node "Assign_Add" #[] => return .add
  | .node "Assign_Sub" #[] => return .sub
  | .node "Assign_Shl" #[] => return .shl
  | .node "Assign_Shr" #[] => return .shr
  | .node "Assign_Band" #[] => return .band
  | .node "Assign_Bxor" #[] => return .bxor
  | .node "Assign_Bor" #[] => return .bor
  | t => mismatch "Cabs.cabs_assignment_operator" t

def decodeStorageClassSpecifier : Sx → Except String StorageClassSpecifier
  | .node "SC_typedef" #[] => return .typedef
  | .node "SC_extern" #[] => return .extern
  | .node "SC_static" #[] => return .static
  | .node "SC_Thread_local" #[] => return .threadLocal
  | .node "SC_auto" #[] => return .auto
  | .node "SC_register" #[] => return .register
  | t => mismatch "Cabs.storage_class_specifier" t

def decodeTypeQualifier : Sx → Except String TypeQualifier
  | .node "Q_const" #[] => return .const
  | .node "Q_restrict" #[] => return .restrict
  | .node "Q_volatile" #[] => return .volatile
  | .node "Q_Atomic" #[] => return .atomic
  | t => mismatch "Cabs.cabs_type_qualifier" t

def decodeFunctionSpecifier : Sx → Except String FunctionSpecifier
  | .node "FS_inline" #[] => return .inline
  | .node "FS_Noreturn" #[] => return .noreturn
  | t => mismatch "Cabs.function_specifier" t

mutual

partial def decodeExpressionNode : Sx → Except String ExpressionNode
  | .node "CabsEident" #[x] => do
    return .ident (← decodeIdentifier x)
  | .node "CabsEconst" #[c] => do
    return .const (← decodeConstant c)
  | .node "CabsEstring" #[s] => do
    return .string
      (← decodeStringLiteral s)
  | .node "CabsEgeneric" #[controlling, associations] => do
    return .generic (← decodeExpression controlling)
      (← decodeList decodeGenericAssociation associations)
  | .node "CabsEsubscript" #[array, index] => do
    return .subscript (← decodeExpression array) (← decodeExpression index)
  | .node "CabsEcall" #[function, args, attrs] => do
    return .call (← decodeExpression function) (← decodeList decodeExpression args)
      (← decodeOption decodeAttributes attrs)
  | .node "CabsEmemberof" #[e, member] => do
    return .memberof (← decodeExpression e) (← decodeIdentifier member)
  | .node "CabsEmemberofptr" #[e, member] => do
    return .memberofptr (← decodeExpression e) (← decodeIdentifier member)
  | .node "CabsEpostincr" #[e] => do
    return .postincr (← decodeExpression e)
  | .node "CabsEpostdecr" #[e] => do
    return .postdecr (← decodeExpression e)
  | .node "CabsEcompound" #[type, inits] => do
    return .compound (← decodeTypeName type)
      (← decodeList (decodeTuple2 (decodeOption
          (decodeList decodeDesignator)) decodeInitializer) inits)
  | .node "CabsEpreincr" #[e] => do
    return .preincr (← decodeExpression e)
  | .node "CabsEpredecr" #[e] => do
    return .predecr (← decodeExpression e)
  | .node "CabsEunary" #[op, e] => do
    return .unary (← decodeUnaryOperator op) (← decodeExpression e)
  | .node "CabsEsizeof_expr" #[e] => do
    return .sizeofExpr (← decodeExpression e)
  | .node "CabsEsizeof_type" #[type] => do
    return .sizeofType (← decodeTypeName type)
  | .node "CabsEalignof" #[type] => do
    return .alignof (← decodeTypeName type)
  | .node "CabsEcast" #[type, e] => do
    return .cast (← decodeTypeName type) (← decodeExpression e)
  | .node "CabsEbinary" #[op, lhs, rhs] => do
    return .binary (← decodeBinaryOperator op) (← decodeExpression lhs) (← decodeExpression rhs)
  | .node "CabsEcond" #[cond, then_, else_] => do
    return .cond (← decodeExpression cond) (← decodeExpression then_) (← decodeExpression else_)
  | .node "CabsEassign" #[op, lhs, rhs] => do
    return .assign (← decodeAssignmentOperator op) (← decodeExpression lhs) (← decodeExpression rhs)
  | .node "CabsEcomma" #[lhs, rhs] => do
    return .comma (← decodeExpression lhs) (← decodeExpression rhs)
  | .node "CabsEassert" #[e] => do
    return .assert (← decodeExpression e)
  | .node "CabsEoffsetof" #[type, member] => do
    return .offsetof (← decodeTypeName type) (← decodeIdentifier member)
  | .node "CabsEva_start" #[list, param] => do
    return .vaStart (← decodeExpression list) (← decodeIdentifier param)
  | .node "CabsEva_copy" #[dst, src] => do
    return .vaCopy (← decodeExpression dst) (← decodeExpression src)
  | .node "CabsEva_arg" #[list, type] => do
    return .vaArg (← decodeExpression list) (← decodeTypeName type)
  | .node "CabsEva_end" #[list] => do
    return .vaEnd (← decodeExpression list)
  | .node "CabsEprint_type" #[e] => do
    return .printType (← decodeExpression e)
  | .node "CabsEbmc_assume" #[e] => do
    return .bmcAssume (← decodeExpression e)
  | .node "CabsElabel_addressGNU" #[label] => do
    return .labelAddressGnu (← decodeIdentifier label)
  | .node "CabsEgcc_statement" #[body] => do
    return .gccStatement (← decodeList decodeStatement body)
  | .node "CabsEcondGNU" #[cond, else_] => do
    return .condGnu (← decodeExpression cond) (← decodeExpression else_)
  | .node "CabsEbuiltinGNU" #[builtin] => do
    return .builtinGnu (← decodeGnuBuiltinFunction builtin)
  | t => mismatch "Cabs.cabs_expression_" t

partial def decodeGnuBuiltinFunction : Sx → Except String GnuBuiltinFunction
  | .node "GNUbuiltin_types_compatible_p" #[t1, t2] => do
    return .typesCompatibleP (← decodeTypeName t1) (← decodeTypeName t2)
  | .node "GNUbuiltin_choose_expr" #[cond, then_, else_] => do
    return .chooseExpr (← decodeExpression cond) (← decodeExpression then_)
      (← decodeExpression else_)
  | t => mismatch "Cabs.gnu_builtin_function" t

partial def decodeExpression : Sx → Except String Expression
  | .node "CabsExpression" #[loc, node] => do
    return .mk (← decodeLoc loc) (← decodeExpressionNode node)
  | t => mismatch "Cabs.cabs_expression" t

partial def decodeGenericAssociation : Sx → Except String GenericAssociation
  | .node "GA_type" #[type, e] => do
    return .type_ (← decodeTypeName type) (← decodeExpression e)
  | .node "GA_default" #[e] => do
    return .default (← decodeExpression e)
  | t => mismatch "Cabs.cabs_generic_association" t

partial def decodeDeclaration : Sx → Except String Declaration
  | .node "Declaration_base" #[attrs, specifiers, declarators] => do
    return .base (← decodeAttributes attrs) (← decodeSpecifiers specifiers)
      (← decodeList decodeInitDeclarator declarators)
  | .node "Declaration_static_assert" #[assertion] => do
    return .staticAssert (← decodeStaticAssertDeclaration assertion)
  | t => mismatch "Cabs.cabs_declaration" t

partial def decodeSpecifiers : Sx → Except String Specifiers
  | .node "specifiers"
      #[storageClasses, typeSpecifiers, typeQualifiers, functionSpecifiers,
        alignmentSpecifiers] => do
    return ⟨← decodeList decodeStorageClassSpecifier storageClasses,
      ← decodeList decodeTypeSpecifier typeSpecifiers,
      ← decodeList decodeTypeQualifier typeQualifiers,
      ← decodeList decodeFunctionSpecifier functionSpecifiers,
      ← decodeList decodeAlignmentSpecifier alignmentSpecifiers⟩
  | t => mismatch "Cabs.specifiers" t

partial def decodeInitDeclarator : Sx → Except String InitDeclarator
  | .node "InitDecl" #[loc, declarator, init] => do
    return .mk (← decodeLoc loc) (← decodeDeclarator declarator)
      (← decodeOption decodeInitializer init)
  | t => mismatch "Cabs.init_declarator" t

partial def decodeTypeSpecifierNode : Sx → Except String TypeSpecifierNode
  | .node "TSpec_void" #[] => return .void
  | .node "TSpec_char" #[] => return .char
  | .node "TSpec_short" #[] => return .short
  | .node "TSpec_int" #[] => return .int
  | .node "TSpec_long" #[] => return .long
  | .node "TSpec_float" #[] => return .float
  | .node "TSpec_double" #[] => return .double
  | .node "TSpec_signed" #[] => return .signed
  | .node "TSpec_unsigned" #[] => return .unsigned
  | .node "TSpec_Bool" #[] => return .bool
  | .node "TSpec_Complex" #[] => return .complex
  | .node "TSpec_Atomic" #[type] => do
    return .atomic (← decodeTypeName type)
  | .node "TSpec_struct" #[attrs, tag, members] => do
    return .struct (← decodeAttributes attrs) (← decodeOption decodeIdentifier tag)
      (← decodeOption (decodeList decodeStructDeclaration) members)
  | .node "TSpec_union" #[attrs, tag, members] => do
    return .union (← decodeAttributes attrs) (← decodeOption decodeIdentifier tag)
      (← decodeOption (decodeList decodeStructDeclaration) members)
  | .node "TSpec_enum" #[tag, enumerators] => do
    return .enum (← decodeOption decodeIdentifier tag)
      (← decodeOption (decodeList (decodeTuple2 decodeIdentifier
          (decodeOption decodeExpression))) enumerators)
  | .node "TSpec_name" #[name] => do
    return .name (← decodeIdentifier name)
  | .node "TSpec_typeof_expr" #[e] => do
    return .typeofExpr (← decodeExpression e)
  | .node "TSpec_typeof_type" #[type] => do
    return .typeofType (← decodeTypeName type)
  | t => mismatch "Cabs.cabs_type_specifier_" t

partial def decodeTypeSpecifier : Sx → Except String TypeSpecifier
  | .node "TSpec" #[loc, node] => do
    return .mk (← decodeLoc loc) (← decodeTypeSpecifierNode node)
  | t => mismatch "Cabs.cabs_type_specifier" t

partial def decodeStructDeclaration : Sx → Except String StructDeclaration
  | .node "Struct_declaration"
      #[attrs, typeSpecifiers, typeQualifiers, alignmentSpecifiers, declarators] => do
    return .member (← decodeAttributes attrs) (← decodeList decodeTypeSpecifier typeSpecifiers)
      (← decodeList decodeTypeQualifier typeQualifiers)
      (← decodeList decodeAlignmentSpecifier alignmentSpecifiers)
      (← decodeList decodeStructDeclarator declarators)
  | .node "Struct_assert" #[assertion] => do
    return .staticAssert (← decodeStaticAssertDeclaration assertion)
  | t => mismatch "Cabs.struct_declaration" t

partial def decodeStructDeclarator : Sx → Except String StructDeclarator
  | .node "SDecl_simple" #[declarator] => do
    return .simple (← decodeDeclarator declarator)
  | .node "SDecl_bitfield" #[declarator, width] => do
    return .bitfield (← decodeOption decodeDeclarator declarator) (← decodeExpression width)
  | t => mismatch "Cabs.struct_declarator" t

partial def decodeAlignmentSpecifier : Sx → Except String AlignmentSpecifier
  | .node "AS_type" #[type] => do
    return .type_ (← decodeTypeName type)
  | .node "AS_expr" #[e] => do
    return .expr (← decodeExpression e)
  | t => mismatch "Cabs.alignment_specifier" t

partial def decodeDeclarator : Sx → Except String Declarator
  | .node "Declarator" #[pointer, direct] => do
    return .mk (← decodeOption decodePointerDeclarator pointer) (← decodeDirectDeclarator direct)
  | t => mismatch "Cabs.declarator" t

partial def decodeDirectDeclarator : Sx → Except String DirectDeclarator
  | .node "DDecl_identifier" #[attrs, name] => do
    return .identifier (← decodeAttributes attrs) (← decodeIdentifier name)
  | .node "DDecl_declarator" #[inner] => do
    return .declarator (← decodeDeclarator inner)
  | .node "DDecl_array" #[inner, array] => do
    return .array (← decodeDirectDeclarator inner) (← decodeArrayDeclarator array)
  | .node "DDecl_function" #[inner, params] => do
    return .function (← decodeDirectDeclarator inner) (← decodeParameterTypeList params)
  | t => mismatch "Cabs.direct_declarator" t

partial def decodeArrayDeclarator : Sx → Except String ArrayDeclarator
  | .node "ADecl" #[loc, qualifiers, isStatic, size] => do
    return .mk (← decodeLoc loc) (← decodeList decodeTypeQualifier qualifiers)
      (← decodeBool isStatic) (← decodeOption decodeArrayDeclaratorSize size)
  | t => mismatch "Cabs.array_declarator" t

partial def decodeArrayDeclaratorSize : Sx → Except String ArrayDeclaratorSize
  | .node "ADeclSize_expression" #[e] => do
    return .expression (← decodeExpression e)
  | .node "ADeclSize_asterisk" #[] => return .asterisk
  | t => mismatch "Cabs.array_declarator_size" t

partial def decodePointerDeclarator : Sx → Except String PointerDeclarator
  | .node "PDecl" #[loc, qualifiers, next] => do
    return .mk (← decodeLoc loc) (← decodeList decodeTypeQualifier qualifiers)
      (← decodeOption decodePointerDeclarator next)
  | t => mismatch "Cabs.pointer_declarator" t

partial def decodeParameterTypeList : Sx → Except String ParameterTypeList
  | .node "Params" #[params, variadic] => do
    return .mk (← decodeList decodeParameterDeclaration params) (← decodeBool variadic)
  | t => mismatch "Cabs.parameter_type_list" t

partial def decodeParameterDeclaration : Sx → Except String ParameterDeclaration
  | .node "PDeclaration_decl" #[specifiers, declarator] => do
    return .declarator (← decodeSpecifiers specifiers) (← decodeDeclarator declarator)
  | .node "PDeclaration_abs_decl" #[specifiers, declarator] => do
    return .abstract (← decodeSpecifiers specifiers)
      (← decodeOption decodeAbstractDeclarator declarator)
  | t => mismatch "Cabs.parameter_declaration" t

partial def decodeTypeName : Sx → Except String TypeName
  | .node "Type_name" #[typeSpecifiers, typeQualifiers, alignmentSpecifiers, declarator] => do
    return .mk (← decodeList decodeTypeSpecifier typeSpecifiers)
      (← decodeList decodeTypeQualifier typeQualifiers)
      (← decodeList decodeAlignmentSpecifier alignmentSpecifiers)
      (← decodeOption decodeAbstractDeclarator declarator)
  | t => mismatch "Cabs.type_name" t

partial def decodeAbstractDeclarator : Sx → Except String AbstractDeclarator
  | .node "AbsDecl_pointer" #[pointer] => do
    return .pointer (← decodePointerDeclarator pointer)
  | .node "AbsDecl_direct" #[pointer, direct] => do
    return .direct (← decodeOption decodePointerDeclarator pointer)
      (← decodeDirectAbstractDeclarator direct)
  | t => mismatch "Cabs.abstract_declarator" t

partial def decodeDirectAbstractDeclarator : Sx → Except String DirectAbstractDeclarator
  | .node "DAbs_abs_declarator" #[inner] => do
    return .abstract (← decodeAbstractDeclarator inner)
  | .node "DAbs_array" #[inner, array] => do
    return .array (← decodeOption decodeDirectAbstractDeclarator inner)
      (← decodeArrayDeclarator array)
  | .node "DAbs_function" #[inner, params] => do
    return .function (← decodeOption decodeDirectAbstractDeclarator inner)
      (← decodeParameterTypeList params)
  | t => mismatch "Cabs.direct_abstract_declarator" t

partial def decodeInitializer : Sx → Except String Initializer
  | .node "Init_expr" #[e] => do
    return .expr (← decodeExpression e)
  | .node "Init_list" #[loc, inits] => do
    return .list (← decodeLoc loc)
      (← decodeList (decodeTuple2 (decodeOption
          (decodeList decodeDesignator)) decodeInitializer) inits)
  | t => mismatch "Cabs.initializer_" t

partial def decodeDesignator : Sx → Except String Designator
  | .node "Desig_array" #[index] => do
    return .array (← decodeExpression index)
  | .node "Desig_member" #[member] => do
    return .member (← decodeIdentifier member)
  | t => mismatch "Cabs.designator" t

partial def decodeStaticAssertDeclaration : Sx → Except String StaticAssertDeclaration
  | .node "Static_assert" #[cond, message] => do
    return .mk (← decodeExpression cond)
      (← decodeStringLiteral message)
  | t => mismatch "Cabs.static_assert_declaration" t

partial def decodeStatementNode : Sx → Except String StatementNode
  | .node "CabsSlabel" #[label, s] => do
    return .label (← decodeIdentifier label) (← decodeStatement s)
  | .node "CabsScase" #[e, s] => do
    return .case_ (← decodeExpression e) (← decodeStatement s)
  | .node "CabsSdefault" #[s] => do
    return .default (← decodeStatement s)
  | .node "CabsSblock" #[items] => do
    return .block (← decodeList decodeStatement items)
  | .node "CabsSdecl" #[d] => do
    return .decl (← decodeDeclaration d)
  | .node "CabsSnull" #[] => return .null
  | .node "CabsSexpr" #[e] => do
    return .expr (← decodeExpression e)
  | .node "CabsSif" #[cond, then_, else_] => do
    return .if_ (← decodeExpression cond) (← decodeStatement then_)
      (← decodeOption decodeStatement else_)
  | .node "CabsSswitch" #[e, s] => do
    return .switch (← decodeExpression e) (← decodeStatement s)
  | .node "CabsSwhile" #[cond, body] => do
    return .while_ (← decodeExpression cond) (← decodeStatement body)
  | .node "CabsSdo" #[cond, body] => do
    return .do_ (← decodeExpression cond) (← decodeStatement body)
  | .node "CabsSfor" #[init, cond, step, body] => do
    return .for_ (← decodeOption decodeForClause init) (← decodeOption decodeExpression cond)
      (← decodeOption decodeExpression step) (← decodeStatement body)
  | .node "CabsSgoto" #[label] => do
    return .goto (← decodeIdentifier label)
  | .node "CabsScontinue" #[] => return .continue_
  | .node "CabsSbreak" #[] => return .break_
  | .node "CabsSreturn" #[e] => do
    return .return_ (← decodeOption decodeExpression e)
  | .node "CabsSpar" #[threads] => do
    return .par (← decodeList decodeStatement threads)
  | .node "CabsSasm" #[isVolatile, isInline, templates] => do
    return .asm (← decodeBool isVolatile) (← decodeBool isInline)
      (← decodeList (decodeTuple2 decodeLoc (decodeList decodeRawString)) templates)
  | .node "CabsScaseGNU" #[lo, hi, s] => do
    return .caseRangeGnu (← decodeExpression lo) (← decodeExpression hi) (← decodeStatement s)
  | .node "CabsSmarker" #[s] => do
    return .marker (← decodeStatement s)
  | t => mismatch "Cabs.cabs_statement_" t

partial def decodeStatement : Sx → Except String Statement
  | .node "CabsStatement" #[loc, attrs, node] => do
    return .mk (← decodeLoc loc) (← decodeAttributes attrs) (← decodeStatementNode node)
  | t => mismatch "Cabs.cabs_statement" t

partial def decodeForClause : Sx → Except String ForClause
  | .node "FC_expr" #[e] => do
    return .expr (← decodeExpression e)
  | .node "FC_decl" #[loc, d] => do
    return .decl (← decodeLoc loc) (← decodeDeclaration d)
  | t => mismatch "Cabs.for_clause" t

end

def decodeFunctionDefinition : Sx → Except String FunctionDefinition
  | .node "FunDef" #[loc, attrs, specifiers, declarator, body] => do
    return .mk (← decodeLoc loc) (← decodeAttributes attrs) (← decodeSpecifiers specifiers)
      (← decodeDeclarator declarator) (← decodeStatement body)
  | t => mismatch "Cabs.function_definition" t

def decodeExternalDeclaration : Sx → Except String ExternalDeclaration
  | .node "EDecl_func" #[f] => do
    return .func (← decodeFunctionDefinition f)
  | .node "EDecl_decl" #[d] => do
    return .decl (← decodeDeclaration d)
  | .node "EDecl_magic" #[comment] => do
    return .magic (← decodeTuple2 decodeLoc decodeStr comment)
  | .node "EDecl_funcCN" #[f] => do
    return .funcCn (← decodeCnFunction decodeIdentifier decodeTypeName f)
  | .node "EDecl_lemmaCN" #[l] => do
    return .lemmaCn (← decodeCnLemma decodeIdentifier decodeTypeName l)
  | .node "EDecl_predCN" #[p] => do
    return .predCn (← decodeCnPredicate decodeIdentifier decodeTypeName p)
  | .node "EDecl_datatypeCN" #[d] => do
    return .datatypeCn (← decodeCnDatatype decodeIdentifier d)
  | .node "EDecl_type_synCN" #[t] => do
    return .typeSynCn (← decodeCnTypeSynonym decodeIdentifier t)
  | .node "EDecl_fun_specCN" #[s] => do
    return .funSpecCn (← decodeCnDeclSpec decodeIdentifier decodeTypeName s)
  | t => mismatch "Cabs.external_declaration" t

def decodeTranslationUnit : Sx → Except String TranslationUnit
  | .node "TUnit" #[declarations] => do
    return .mk (← decodeList decodeExternalDeclaration declarations)
  | t => mismatch "Cabs.translation_unit" t

end Cabs

/-! ## Documents and rejects -/

/-- Why Cerberus stopped: the stage (`cpp`, `parse`, `desugar` or `typing`), the
location and the short message of its `Errors.error`. At the Cabs level the stage
of a `.i` input is always `parse`. -/
structure Reject where
  stage : String
  loc : Loc
  message : String

/-- One oracle output at the Cabs level: a translation unit or a reject, with the
Cerberus commit and the implementation name of the header. -/
inductive Output where
  | document (commit impl : String) (unit : TranslationUnit)
  | reject (commit impl : String) (reject : Reject)

/-- The pinned Cerberus commit. -/
def cerberusCommit : String := "b3e11ea334e95359907d4abf9194f0e7fedc6c6a"

/-- The implementation name the oracle prints (Cabs does not depend on it). -/
def cerberusImpl : String := "gcc_4.9.0_x86_64-apple-darwin10.8.0"

def emitOutput (x : Output) (o : Out) : Out :=
  match x with
  | .document commit impl unit =>
    o |> open_ "$document_cabs" |> arg (emitInt 1) |> arg (emitStr commit) |> arg (emitStr impl)
      |> arg (emitTranslationUnit unit) |> close
  | .reject commit impl r =>
    o |> open_ "$reject" |> arg (emitInt 1) |> arg (emitStr commit) |> arg (emitStr impl)
      |> arg (emitStr r.stage) |> arg (emitLoc r.loc) |> arg (emitStr r.message) |> close

def decodeOutput : Sx → Except String Output
  | .node "$document_cabs" #[.atom "1", commit, impl, unit] =>
    return .document (← decodeStr commit) (← decodeStr impl) (← decodeTranslationUnit unit)
  | .node "$reject" #[.atom "1", commit, impl, stage, l, msg] =>
    return .reject (← decodeStr commit) (← decodeStr impl) ⟨← decodeStr stage,← decodeLoc l,
      ← decodeStr msg⟩
  | t => mismatch "a version 1 $document_cabs or $reject" t

/-- The canonical text of an output, with its final newline. -/
def printCabsDocument (x : Output) : String := (emitOutput x "").push '\n'

/-- Decode an output without checking its layout (the `read` mode of `cerb-lean`). -/
def readCabsDocument (text : String) : Except String Output := do
  decodeOutput (← Wire.read text.toByteArray)

/-- Decode an output and check that printing it gives back exactly `text`. -/
def parseCabsDocument (text : String) : Except String Output := do
  let x ← readCabsDocument text
  if printCabsDocument x == text then return x else throw "noncanonical document"

/-- A checked document prints back to exactly its input. -/
theorem print_parseCabsDocument {text : String} {x : Output}
    (h : parseCabsDocument text = .ok x) : printCabsDocument x = text := by
  unfold parseCabsDocument at h
  cases hr : readCabsDocument text with
  | error e => simp [hr, bind, Except.bind] at h
  | ok y =>
    simp only [hr, bind, Except.bind] at h
    split at h
    · rename_i heq
      cases h
      exact beq_iff_eq.mp heq
    · cases h

end Silmaril.Cerberus.Cabs.Codec
