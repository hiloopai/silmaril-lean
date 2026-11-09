module
public import Silmaril.Formats.JsonWire.Ast.Defs

/-! A simple total JSON printer. Strings use UTF-16 escapes, preserving lone
surrogates exactly. This is deterministic structural printing, not JCS or
canonicalization of mathematical decimal values or object-member order. -/
@[expose] public section
namespace Silmaril.Formats.JsonWire

def Decimal.literal (d : Decimal) : String :=
  (if d.negative then "-" else "") ++ d.coefficient.repr ++
    (if d.exponent = 0 then "" else "e" ++ d.exponent.repr)

def Number.literal : Number → String
  | .finite d => d.literal
  | .infinity negative => if negative then "-Infinity" else "Infinity"
  | .nan => "NaN"

def quote (units : Units) : String :=
  let chars := units.flatMap fun u => '\\' :: 'u' ::
    ((List.range 4).map fun i =>
      let n := u.toNat / 16 ^ (3 - i) % 16
      Char.ofNat (if n < 10 then 48 + n else 87 + n))
  String.ofList ('"' :: (chars ++ ['"']))

def render {N : Type} (number : N → String) :
    {i : Silmaril.Formats.JsonIx} → Syn N i → String
  | _, .scalar none => "null"
  | _, .scalar (some (.bool b)) => if b then "true" else "false"
  | _, .scalar (some (.string s)) => quote s
  | _, .scalar (some (.number n)) => number n
  | _, .list xs => "[" ++ render number xs ++ "]"
  | _, .map xs => "{" ++ render number xs ++ "}"
  | _, .nil => ""
  | _, .cons x xs => render number x ++ (match xs with | .nil => "" | _ => ",") ++ render number xs
  | _, .objNil => ""
  | _, .objCons k v xs => quote k ++ ":" ++ render number v ++
      (match xs with | .objNil => "" | _ => ",") ++ render number xs

def encode (ast : Ast Decimal) : Bytes := ⟨(render Decimal.literal ast).toUTF8⟩
def encodeInteger (ast : Ast Int) : Bytes := ⟨(render Int.repr ast).toUTF8⟩
def encodeJson5 (ast : Ast Number) : Bytes := ⟨(render Number.literal ast).toUTF8⟩

end Silmaril.Formats.JsonWire
