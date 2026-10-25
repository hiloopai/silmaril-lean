module

public import Silmaril.Formats.SExp.Pose
public import Silmaril.Formats.SExp.Rivest

/-!
# S-expression printers

Printers for the general Lisp syntax, POSE, and Rivest's canonical binary
syntax.  The checked entry points make the parser/printer contract executable:
returning `some text` entails that parsing `text` recovers the input exactly.
-/

@[expose] public section

universe uα uβ uγ uι uκ uτ uυ uφ
variable {α : Type uα} {β : Type uβ} {γ : Type uγ}
variable {ι : Type uι} {κ : Type uκ} {n : Nat}
variable {τ : Type uτ} {υ : Type uυ} {φ : Type uφ}

namespace Silmaril.Formats

namespace SExpPrinter

def escapeChar : Char → String
  | '\\' => "\\\\"
  | '"' => "\\\""
  | '\n' => "\\n"
  | '\r' => "\\r"
  | '\t' => "\\t"
  | c => String.singleton c

/-- Quote an arbitrary string as a Lisp string literal. -/
def quote (value : String) : String :=
  "\"" ++ String.join (value.toList.map escapeChar) ++ "\""

mutual
  /-- Print a binary S-expression using a caller-supplied atom representation. -/
  def printSExp2With (printAtom : α → String) : SExp2 α → String
    | .nil => "()"
    | .atom value => printAtom value
    | .cons car cdr => "(" ++ printSExp2With printAtom car ++
        printTailWith printAtom cdr ++ ")"

  def printTailWith (printAtom : α → String) : SExp2 α → String
    | .nil => ""
    | .cons car cdr => " " ++ printSExp2With printAtom car ++
        printTailWith printAtom cdr
    | tail => " . " ++ printSExp2With printAtom tail

end

/-- Print a possibly improper S-expression.  Atoms are quoted so every
`String` is representable without imposing a symbol grammar. -/
def printSExp2 (value : SExp2 String) : String := printSExp2With quote value

/-- Print an intrinsically proper S-expression. -/
def printSExp (value : SExp String) : String :=
  printSExp2With quote value.toSExp2

/-- A checked general printer.  Failure would expose a disagreement between
the printer and parser rather than silently emitting a lossy representation. -/
def printSExp2? (value : SExp2 String) : Option String :=
  let text := printSExp2 value
  if SExpParser.parseSExp2? text = some value then some text else none

theorem printSExp2?_sound {value : SExp2 String} {text : String}
    (h : printSExp2? value = some text) :
    SExpParser.parseSExp2? text = some value := by
  simp only [printSExp2?] at h
  split at h <;> simp_all

/-- Checked printer for intrinsically proper expressions. -/
def printSExp? (value : SExp String) : Option String :=
  let text := printSExp value
  match SExpParser.parseSExp? text with
  | some parsed => if parsed.toSExp2 = value.toSExp2 then some text else none
  | none => none

theorem printSExp?_sound {value : SExp String} {text : String}
    (h : printSExp? value = some text) :
    SExpParser.parseSExp? text = some value := by
  simp only [printSExp?] at h
  split at h
  next parsed heq =>
    split at h
    next hs =>
      simp only [Option.some.injEq] at h
      subst text
      have hp : parsed = value := SExp.toSExp2_injective hs
      simpa [hp] using heq
    next => contradiction
  next => contradiction

end SExpPrinter

namespace Pose

def quoteChar : Char → String
  | '\\' => "\\\\"
  | '"' => "\\\""
  | c => String.singleton c

def quote (value : String) : String :=
  "\"" ++ String.join (value.toList.map quoteChar) ++ "\""

def printAtom : PoseAtom → String
  | .symbol name => name
  | .string value => quote value
  | .number (.integer literal) | .number (.float literal) => literal

def render : Pose → String
  | value => SExpPrinter.printSExp2With printAtom value.toSExp2

/-- Print a POSE value when its public, unrestricted atom fields actually
satisfy the POSE grammar. -/
def print? (value : Pose) : Option String :=
  let text := render value
  match parse? text with
  | some parsed => if parsed.toSExp2 = value.toSExp2 then some text else none
  | none => none

theorem print?_sound {value : Pose} {text : String} (h : print? value = some text) :
    parse? text = some value := by
  simp only [print?] at h
  split at h
  next parsed heq =>
    split at h
    next hs =>
      simp only [Option.some.injEq] at h
      subst text
      have hp : parsed = value := SExp.toSExp2_injective hs
      simpa [hp] using heq
    next => contradiction
  next => contradiction

/-- Print a complete POSE document, checking all atom invariants. -/
def printDocument? (value : PoseDocument) : Option String :=
  let text := String.intercalate "\n" (value.map render)
  match parseDocument? text with
  | some parsed =>
      if parsed.map SExp.toSExp2 = value.map SExp.toSExp2 then some text else none
  | none => none

theorem printDocument?_sound {value : PoseDocument} {text : String}
    (h : printDocument? value = some text) : parseDocument? text = some value := by
  simp only [printDocument?] at h
  split at h
  next parsed heq =>
    split at h
    next hs =>
      simp only [Option.some.injEq] at h
      subst text
      have hp : parsed = value :=
        (List.map_injective_iff.mpr SExp.toSExp2_injective) hs
      simpa [hp] using heq
    next => contradiction
  next => contradiction

end Pose

namespace RivestSExp

def ascii (value : String) : Bytes := ⟨value.toByteArray⟩

mutual
  def printCanonical2 : SExp2 Bytes → Bytes
    | .nil => ascii "()"
    | .atom value => (ascii (toString value.length ++ ":")).append value
    | .cons car cdr =>
        (ascii "(").append (printCanonical2 car) |>.append (printCanonicalTail cdr)
          |>.append (ascii ")")

  def printCanonicalTail : SExp2 Bytes → Bytes
    | .nil => Bytes.empty
    | .cons car cdr => (printCanonical2 car).append (printCanonicalTail cdr)
    | _ => Bytes.empty -- unreachable for the image of `SExp.toSExp2`
end

/-- The mandatory canonical representation from draft-rivest-sexp-04. -/
def printCanonical (value : RivestSExp) : Bytes := printCanonical2 value.toSExp2

/-- Checked canonical printer, useful as an executable parser/printer
round-trip contract. -/
def printCanonical? (value : RivestSExp) : Option Bytes :=
  let bytes := printCanonical value
  match parseCanonical? bytes with
  | some parsed => if parsed.toSExp2 = value.toSExp2 then some bytes else none
  | none => none

theorem printCanonical?_sound {value : RivestSExp} {bytes : Bytes}
    (h : printCanonical? value = some bytes) : parseCanonical? bytes = some value := by
  simp only [printCanonical?] at h
  split at h
  next parsed heq =>
    split at h
    next hs =>
      simp only [Option.some.injEq] at h
      subst bytes
      have hp : parsed = value := SExp.toSExp2_injective hs
      simpa [hp] using heq
    next => contradiction
  next => contradiction

end RivestSExp

attribute [local cbv_eval] String.join_eq_foldl in
example :
    SExpPrinter.printSExp2?
      (.cons (.atom "a b") (.cons (.atom "x\n\"y") (.atom "tail"))) =
      some "(\"a b\" \"x\\n\\\"y\" . \"tail\")" := by
  have rendered : SExpPrinter.printSExp2
      (.cons (.atom "a b") (.cons (.atom "x\n\"y") (.atom "tail"))) =
      "(\"a b\" \"x\\n\\\"y\" . \"tail\")" := by cbv
  have parsed : SExpParser.parseSExp2? "(\"a b\" \"x\\n\\\"y\" . \"tail\")" =
      some (.cons (.atom "a b") (.cons (.atom "x\n\"y") (.atom "tail"))) := by
    cbv
  simp only [SExpPrinter.printSExp2?, rendered, parsed, ↓reduceIte]

attribute [local cbv_eval] String.contains_bool_eq String.join_eq_foldl in
example :
    Pose.print? (SExp.ofList [
      .atom (.symbol "foo"), .atom (.number (.integer "-12")),
      .atom (.string "a\\b\"c")]) =
      some "(foo -12 \"a\\\\b\\\"c\")" := by
  have rendered : Pose.render (SExp.ofList [
      .atom (.symbol "foo"), .atom (.number (.integer "-12")),
      .atom (.string "a\\b\"c")]) = "(foo -12 \"a\\\\b\\\"c\")" := by cbv
  have parsed : Pose.parse? "(foo -12 \"a\\\\b\\\"c\")" = some (SExp.ofList [
      .atom (.symbol "foo"), .atom (.number (.integer "-12")),
      .atom (.string "a\\b\"c")]) := by cbv
  simp only [Pose.print?, rendered, parsed, ↓reduceIte]

attribute [local cbv_eval] Nat.repr_eq_ofList_toDigits in
example :
    RivestSExp.printCanonical?
      (SExp.ofList [.atom ⟨ByteArray.mk #[0, 255, 40, 41]⟩, SExp.nil]) =
      some ⟨(ByteArray.mk #[40, 52, 58, 0, 255, 40, 41, 40, 41, 41])⟩ := by
  have rendered : RivestSExp.printCanonical
      (SExp.ofList [.atom ⟨ByteArray.mk #[0, 255, 40, 41]⟩, SExp.nil]) =
      ⟨(ByteArray.mk #[40, 52, 58, 0, 255, 40, 41, 40, 41, 41])⟩ := by
    cbv
    rw [Nat.toDigits_of_lt_base (by decide : 4 < 10)]
    rw [Nat.digitChar_eq_four.mpr rfl]
    cbv
  have parsed : RivestSExp.parseCanonical?
      ⟨(ByteArray.mk #[40, 52, 58, 0, 255, 40, 41, 40, 41, 41])⟩ =
      some (SExp.ofList [.atom ⟨ByteArray.mk #[0, 255, 40, 41]⟩, SExp.nil]) := by
    cbv
    congr 1
    apply SExp.toSExp2_injective
    cbv
  simp only [RivestSExp.printCanonical?, rendered, parsed, ↓reduceIte]

end Silmaril.Formats
