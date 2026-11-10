module
public import Silmaril.Formats.JsonWire.Lexer.Defs

@[expose] public section
namespace Silmaril.Formats.JsonWire.Internal

mutual
  def value? (dialect : Dialect) : Nat → List Token → Option (Ast Number × List Token)
    | 0, _ => none
    | fuel + 1, ts => match ts with
      | .null :: rest => some (.scalar none, rest)
      | .bool b :: rest => some (.scalar (some (.bool b)), rest)
      | .string s :: rest => some (.scalar (some (.string s)), rest)
      | .number n :: rest => some (.scalar (some (.number n)), rest)
      | .identifier name true :: rest =>
          if name == stringUnits "null" then some (.scalar none, rest)
          else if name == stringUnits "true" then some (.scalar (some (.bool true)), rest)
          else if name == stringUnits "false" then some (.scalar (some (.bool false)), rest)
          else if name == stringUnits "Infinity" then some (.scalar (some (.number (.infinity false))), rest)
          else if name == stringUnits "NaN" then some (.scalar (some (.number .nan)), rest)
          else none
      | .arrayOpen :: rest => do
          let (xs, rest) ← array? dialect fuel true rest
          pure (.list xs, rest)
      | .objectOpen :: rest => do
          let (xs, rest) ← object? dialect fuel true rest
          pure (.map xs, rest)
      | _ => none

  def array? (dialect : Dialect) : Nat → Bool → List Token →
      Option (Syn Number .arr × List Token)
    | 0, _, _ => none
    | fuel + 1, allowEmpty, ts => match ts with
      | .arrayClose :: rest => if allowEmpty then some (.nil, rest) else none
      | _ => do
        let (head, rest) ← value? dialect fuel ts
        match rest with
        | .arrayClose :: rest => some (.cons head .nil, rest)
        | .comma :: rest => do
            let (tail, rest) ← array? dialect fuel (dialect == .json5) rest
            pure (.cons head tail, rest)
        | _ => none

  def object? (dialect : Dialect) : Nat → Bool → List Token →
      Option (Syn Number .obj × List Token)
    | 0, _, _ => none
    | fuel + 1, allowEmpty, ts => match ts with
      | .objectClose :: rest => if allowEmpty then some (.objNil, rest) else none
      | _ => do
        let (key, rest) ← match ts with
          | .string key :: .colon :: rest => some (key, rest)
          | .identifier key _ :: .colon :: rest =>
              if dialect == .json5 then some (key, rest) else none
          | _ => none
        let (head, rest) ← value? dialect fuel rest
        match rest with
        | .objectClose :: rest => some (.objCons key head .objNil, rest)
        | .comma :: rest => do
            let (tail, rest) ← object? dialect fuel (dialect == .json5) rest
            pure (.objCons key head tail, rest)
        | _ => none
end

def decode (dialect : Dialect) (bytes : Bytes) : Option (Ast Number × List (Located TokenKind)) := do
  let text ← String.fromUTF8? bytes.data
  let lexed ← lex dialect (text.toList.length + 1) 0 text.toList
  let (ast, rest) ← value? dialect (2 * lexed.tokens.length + 1) lexed.tokens
  if rest.isEmpty then some (ast, lexed.concrete) else none

end Silmaril.Formats.JsonWire.Internal
