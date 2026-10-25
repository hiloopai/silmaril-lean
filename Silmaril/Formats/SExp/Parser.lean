module

public import Silmaril.Formats.SExp.Tagged

/-! A total parser for Lisp-style S-expressions and checked sublanguages. -/

@[expose] public section

universe uα uβ uγ uι uκ uτ uυ uφ
variable {α : Type uα} {β : Type uβ} {γ : Type uγ}
variable {ι : Type uι} {κ : Type uκ} {n : Nat}
variable {τ : Type uτ} {υ : Type uυ} {φ : Type uφ}

namespace Silmaril.Formats.SExpParser

/-- Lexical distinction retained by the richer parsers. -/
inductive Lexeme where
  | symbol (value : String)
  | string (value : String)
  deriving DecidableEq, Repr

namespace Lexeme

def value : Lexeme → String
  | .symbol value | .string value => value

end Lexeme

structure Input where
  source : String
  pos : String.Pos.Raw

def Input.current (input : Input) : Option Char := input.pos.get? input.source

def Input.next (input : Input) : Input :=
  ⟨input.source, input.pos.next input.source⟩

def space (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\n' || c = '\r'

def wsFuel : Nat → Bool → Input → Input
  | 0, _, input => input
  | fuel + 1, comment, input =>
      match input.current with
      | none => input
      | some c =>
          if comment then
            wsFuel fuel (c ≠ '\n') input.next
          else if c = ';' then
            wsFuel fuel true input.next
          else if space c then
            wsFuel fuel false input.next
          else input

def ws (input : Input) : Input := wsFuel (input.source.length + 1) false input

def quoted : Nat → Input → Option (List Char × Input)
  | 0, _ => none
  | fuel + 1, input =>
      match input.current with
      | none => none
      | some '"' => some ([], input.next)
      | some '\\' =>
          let input := input.next
          match input.current with
          | none => none
          | some c => do
              let (tail, rest) ← quoted fuel input.next
              let decoded := match c with
                | 'n' => '\n'
                | 'r' => '\r'
                | 't' => '\t'
                | 'b' => Char.ofNat 8
                | 'f' => Char.ofNat 12
                | c => c
              some (decoded :: tail, rest)
      | some c => do
          let (tail, rest) ← quoted fuel input.next
          some (c :: tail, rest)

def delimiter (c : Char) : Bool := space c || c = '(' || c = ')' || c = ';'

def dottedMarker (input : Input) : Bool :=
  input.current = some '.' && match input.next.current with
    | none => true
    | some c => delimiter c

def bare : Input → List Char × Input
  | input => go (input.source.length + 1) input
where
  go : Nat → Input → List Char × Input
    | 0, input => ([], input)
    | fuel + 1, input =>
        match input.current with
        | none => ([], input)
        | some c => if delimiter c then ([], input) else
            let (token, rest) := go fuel input.next
            (c :: token, rest)

mutual
  def expr : Nat → Input → Option (SExp2 Lexeme × Input)
    | 0, _ => none
    | fuel + 1, input =>
        let input := ws input
        match input.current with
        | none | some ')' => none
        | some '(' => list fuel [] input.next
        | some '"' => do
            let (token, rest) ← quoted fuel input.next
            some (.atom (.string (String.ofList token)), rest)
        | some _ =>
            let (token, rest) := bare input
            if token.isEmpty then none else some (.atom (.symbol (String.ofList token)), rest)

  def list : Nat → List (SExp2 Lexeme) → Input →
      Option (SExp2 Lexeme × Input)
    | 0, _, _ => none
    | fuel + 1, acc, input =>
        let input := ws input
        match input.current with
        | none => none
        | some ')' => some (acc.foldr .cons .nil, input.next)
        | some '.' =>
            if !dottedMarker input then do
              let (head, rest) ← expr fuel input
              list fuel (acc ++ [head]) rest
            else if acc.isEmpty then none else do
              let (tail, rest) ← expr fuel input.next
              let rest := ws rest
              if rest.current = some ')' then
                some (acc.foldr .cons tail, rest.next)
              else none
        | some _ => do
            let (head, rest) ← expr fuel input
            list fuel (acc ++ [head]) rest
end

/-- Parse one complete expression while retaining whether an atom was a quoted
string literal or an unquoted symbol. -/
def parseLexemes? (text : String) : Option (SExp2 Lexeme) := do
  let (value, rest) ← expr (text.length + 1) ⟨text, 0⟩
  if (ws rest).current.isNone then some value else none

/-- Parse one complete dotted or proper Lisp S-expression. This compatibility
view deliberately erases the symbol/string lexical distinction. -/
def parseSExp2? (text : String) : Option (SExp2 String) :=
  SExp2.map Lexeme.value <$> parseLexemes? text

/-! POSE has a deliberately smaller string escape language and only proper
lists, so its syntax is recognized separately while reusing the same String
cursor, whitespace/comment scanner, and bare-token scanner. -/

def poseQuoted : Nat → Input → Option (String × Input)
  | 0, _ => none
  | fuel + 1, input =>
      match input.current with
      | none => none
      | some '"' => some ("", input.next)
      | some '\\' =>
          let input := input.next
          match input.current with
          | some '\\' | some '"' => do
              let (tail, rest) ← poseQuoted fuel input.next
              some (String.singleton input.current.get! ++ tail, rest)
          | _ => none
      | some c => do
          let (tail, rest) ← poseQuoted fuel input.next
          some (String.singleton c ++ tail, rest)

mutual
  def poseExpr : Nat → Input → Option (SExp Lexeme × Input)
    | 0, _ => none
    | fuel + 1, input =>
        let input := ws input
        match input.current with
        | none | some ')' => none
        | some '(' => do
            let (children, rest) ← poseList fuel [] input.next
            some (SExp.ofList children, rest)
        | some '"' => do
            let (value, rest) ← poseQuoted fuel input.next
            some (.atom (.string value), rest)
        | some _ =>
            let (token, rest) := bare input
            if token.isEmpty then none else
              some (.atom (.symbol (String.ofList token)), rest)

  def poseList : Nat → List (SExp Lexeme) → Input →
      Option (List (SExp Lexeme) × Input)
    | 0, _, _ => none
    | fuel + 1, acc, input =>
        let input := ws input
        match input.current with
        | none => none
        | some ')' => some (acc, input.next)
        | some _ => do
            let (head, rest) ← poseExpr fuel input
            poseList fuel (acc ++ [head]) rest
end

def poseMany : Nat → List (SExp Lexeme) → Input →
    Option (List (SExp Lexeme))
  | 0, _, _ => none
  | fuel + 1, acc, input =>
      let input := ws input
      match input.current with
      | none => some acc
      | some _ => do
          let (head, rest) ← poseExpr fuel input
          poseMany fuel (acc ++ [head]) rest

/-- Parse the lexical and proper-list layer of a complete POSE document. Atom
validation and number/symbol classification are performed by `Pose.parse?`. -/
def parsePoseLexemes? (text : String) : Option (List (SExp Lexeme)) :=
  poseMany (text.length + 1) [] ⟨text, 0⟩

mutual
  def toProper : Nat → SExp2 α → Option (SExp α)
    | 0, _ => none
    | _ + 1, .nil => some SExp.nil
    | _ + 1, .atom value => some (.atom value)
    | fuel + 1, .cons car cdr => do
        let car ← toProper fuel car
        let cdr ← toProperList fuel cdr
        some (SExp.ofList (car :: cdr))

  def toProperList : Nat → SExp2 α → Option (List (SExp α))
    | 0, _ => none
    | _ + 1, .nil => some []
    | _ + 1, .atom _ => none
    | fuel + 1, .cons car cdr => do
        let car ← toProper fuel car
        let cdr ← toProperList fuel cdr
        some (car :: cdr)
end

/-- Parse only intrinsically proper S-expressions. -/
def parseSExp? (text : String) : Option (SExp String) := do
  let value ← parseSExp2? text
  toProper (text.length + 2) value

example : (parseSExp2? "(a b . c)").isSome = true := by decide +kernel
example : (parseSExp? "(a b . c)").isNone = true := by decide +kernel

end Silmaril.Formats.SExpParser
