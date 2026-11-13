module
public import Silmaril.Formats.Json.Thms
/-! Orthogonal JSON semantic profiles. They retain the base AST and use the
same `Profile` refinement mechanism as CBOR's wire restrictions. -/
@[expose] public section
namespace Silmaril.Formats.Json

def allStrings {N : Type} (accept : Units → Bool) :
    {i : Silmaril.Formats.JsonIx} → Syn N i → Bool
  | _, .scalar (some (.string s)) => accept s
  | _, .scalar _ => true
  | _, .list xs => allStrings accept xs
  | _, .map xs => allStrings accept xs
  | _, .nil => true
  | _, .cons x xs => allStrings accept x && allStrings accept xs
  | _, .objNil => true
  | _, .objCons k v xs => accept k && allStrings accept v && allStrings accept xs

def allNumbers {N : Type} (accept : N → Bool) :
    {i : Silmaril.Formats.JsonIx} → Syn N i → Bool
  | _, .scalar (some (.number n)) => accept n
  | _, .scalar _ => true
  | _, .list xs => allNumbers accept xs
  | _, .map xs => allNumbers accept xs
  | _, .nil => true
  | _, .cons x xs => allNumbers accept x && allNumbers accept xs
  | _, .objNil => true
  | _, .objCons _ v xs => allNumbers accept v && allNumbers accept xs

/-- The keys of an object tail, in order. One structural recursion over every sort, so the
kernel evaluates it (`keyList_eq_keys`: it is `RawSyn.keys`). -/
def keyList {N : Type} : {i : Silmaril.Formats.JsonIx} → Syn N i → List Units
  | _, .objCons k _ xs => k :: keyList xs
  | _, _ => []

theorem keyList_eq_keys {N : Type} : ∀ xs : Syn N .obj, keyList xs = xs.keys
  | .objNil => by simp [keyList]
  | .objCons k v xs => by simp [keyList, keyList_eq_keys xs]

def distinctKeys {N : Type} : {i : Silmaril.Formats.JsonIx} → Syn N i → Bool
  | _, .scalar _ => true
  | _, .list xs => distinctKeys xs
  | _, .map xs => distinctKeys xs
  | _, .nil => true
  | _, .cons x xs => distinctKeys x && distinctKeys xs
  | _, .objNil => true
  | _, .objCons k v xs => !((keyList xs).contains k) && distinctKeys v && distinctKeys xs

def unicode {N : Type} : Profile (Ast N) := .value (allStrings scalarUnicode)
def uniqueKeys {N : Type} : Profile (Ast N) := .value distinctKeys

/-- RFC 4627's original restriction on top-level JSON values. -/
def containerRoot {N : Type} : Profile (Ast N) := .value fun
  | .list _ | .map _ => true
  | _ => false

/-- I-JSON's mandatory string repertoire restriction (RFC 7493 §2.1). -/
def ijsonString (us : Units) : Bool :=
  match unitsChars? us with
  | none => false
  | some cs => cs.all fun c =>
      !(0xFDD0 ≤ c.toNat && c.toNat ≤ 0xFDEF) && c.toNat % 65536 < 65534

/-- Exact round-to-nearest finite-binary64 magnitude boundary. Precision is
not constrained: e.g. exact decimal `0.1` passes without being dyadic. -/
def Decimal.finiteBinary64Magnitude (d : Decimal) : Bool :=
  let threshold := (2 ^ 54 - 1) * 2 ^ 970
  if d.coefficient == 0 then true
  else if d.exponent ≥ 0 then
    if d.exponent > 309 then false
    else d.coefficient * 10 ^ d.exponent.toNat < threshold
  else if d.exponent.natAbs > d.coefficient.repr.length then true
  else d.coefficient < threshold * 10 ^ d.exponent.natAbs

/-- I-JSON repertoire, unique keys, and the finite-magnitude recommendation.
RFC 7493's precision recommendation is intentionally not claimed here. -/
def ijsonMagnitude : Profile (Ast Decimal) :=
  ((Profile.value (allStrings ijsonString)).meet uniqueKeys).meet
    (.value (allNumbers Decimal.finiteBinary64Magnitude))

/-- An exactly interoperable integer subset, with unique names and Unicode
scalar strings. The range is `-(2^53-1) .. 2^53-1`. -/
def portableIntegers : Profile (Ast Int) :=
  (unicode.meet uniqueKeys).meet (.value (allNumbers fun n => n.natAbs ≤ 9007199254740991))

/-- An explicitly bounded *decimal* interchange subset. This does not claim
binary64 exactness: decimal `0.1` remains the exact decimal one tenth. -/
def boundedDecimals (digits : Nat) (minExponent maxExponent : Int) : Profile (Ast Decimal) :=
  (unicode.meet uniqueKeys).meet (.value (allNumbers fun d =>
    d.coefficient.repr.length ≤ digits && minExponent ≤ d.exponent && d.exponent ≤ maxExponent))

def parsePortableInteger? : Bytes → Option (Ast Int) := restrict parseInteger? portableIntegers

end Silmaril.Formats.Json
