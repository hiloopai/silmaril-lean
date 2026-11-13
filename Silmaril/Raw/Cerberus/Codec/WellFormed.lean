module

public import Silmaril.Cerberus.Codec.File.Defs
public import Silmaril.Formats.SExp.Parser

/-! # Checked Cerberus documents

`parseDocument` checks canonical layout, decodes with child-path diagnostics,
then checks the exporter's semantic restrictions. Every digest is empty or
16 bytes. All eight file maps have strictly increasing keys under their typed
Lem comparators. This check runs on the retained bindings, so `Map.ofList` cannot hide a
duplicate or a diagnostic key representative from validation.

Symbols compare digest bytes, then number, ignoring descriptions. Identifiers
compare text, ignoring locations. Implementation constants follow Lem's
`implementation_constant_compare`. The digest walk visits typed symbol and
prefix subtrees to keep each failure's original child path. It does not guess
map comparators from the spelling of keys.

The syntax codec's round-trip laws include all representable values. The
checked parser additionally enforces layout, digest form and map order; its
success theorem proves byte-for-byte re-encoding. It does not check Core typing,
execution, or the provenance of the recorded commit and implementation strings.
-/

@[expose] public section

namespace Silmaril.Cerberus.Codec.WellFormed

open Silmaril.TaggedCodec Codec
open Silmaril.Formats.SExpEncoding

/-- Lem's `symbol_compare`, on the bytes represented by the wire digest. -/
def compareSym (a b : Sym) : Ordering :=
  (compare a.digest.bytes b.digest.bytes).then (compare a.number b.number)

/-- Lem's `SetType identifier` comparison. -/
def compareIdentifier (a b : Identifier) : Ordering := compare a.name b.name

/-- Lem's `implementation_constant_to_nat`. -/
def implementationConstantToNat : ImplementationConstant → Nat
  | .environmentStartupName => 0
  | .environmentStartupType => 1
  | .charactersBitsInByte => 2
  | .charactersExecutionCharacterSetValues => 3
  | .charactersTodo1 => 4
  | .charactersTodo2 => 5
  | .charactersPlainCharIsSigned => 6
  | .charactersTodo3 => 7
  | .charactersTodo4 => 8
  | .charactersTodo5 => 9
  | .charactersTodo6 => 10
  | .charactersTodo7 => 11
  | .charactersTodo8 => 12
  | .charactersTodo9 => 13
  | .charactersTodo10 => 14
  | .integerEncode => 15
  | .integerDecode => 16
  | .integerConvNonrepresentableSignedInteger => 17
  | .sizeof => 18
  | .alignof => 19
  | .shrSignedNegative => 20
  | .bitwiseComplement => 21
  | .plainBitfieldSign => 22
  | .bitfieldOtherTypes => 23
  | .atomicBitfieldPermitted => 24
  | .ctypeMin => 25
  | .ctypeMax => 26
  | .builtinFunction _ => 27

/-- Lem's `implementation_constant_compare`. -/
def compareImplementationConstant :
    ImplementationConstant → ImplementationConstant → Ordering
  | .builtinFunction a, .builtinFunction b => compare a b
  | x, y => compare (implementationConstantToNat x) (implementationConstantToNat y)

/-- Return the first key that is not strictly above its predecessor. -/
def orderProblem {κ ν : Type} (cmp : κ → κ → Ordering) (path : List Nat) :
    Nat → List (κ × ν) → Option DecodeError
  | i, a :: b :: rest =>
    if cmp a.1 b.1 == .lt then orderProblem cmp path (i + 1) (b :: rest)
    else some ⟨path ++ [i + 1, 0], "map keys are not strictly increasing under the Lem comparator"⟩
  | _, _ => none

/-- Check each map with its declared key type. Paths refer to the document tree,
where child 3 is the file and a binding's child 0 is its key. -/
def mapProblems (f : FileBindings) : List DecodeError :=
  [orderProblem compareSym [3, 2] 0 f.tagDefs,
   orderProblem compareSym [3, 3] 0 f.stdlib,
   orderProblem compareImplementationConstant [3, 4] 0 f.impl,
   orderProblem compareSym [3, 6] 0 f.funs,
   orderProblem compareIdentifier [3, 7] 0 f.extern,
   orderProblem compareSym [3, 8] 0 f.funInfo,
   orderProblem compare [3, 9] 0 f.loopAttributes,
   orderProblem compare [3, 10] 0 f.visibleObjects].filterMap id

/-- Enum registrations share the symbol comparator and the pinned DefaultImpl
signed/unsigned int choices, ocaml_implementation.ml:130-149. -/
def enumProblems (enums : Option (List (Sym × IntegerType))) : List DecodeError :=
  let entries := enums.getD []
  (orderProblem compareSym [4] 0 entries).toList ++
    entries.zipIdx.filterMap fun ((_, ty), i) => match ty with
      | .signed .int | .unsigned .int => none
      | _ => some ⟨[4, i, 1], "enum registration must select signed or unsigned int"⟩

/-- The empty standard-library digest, or the exporter's 16-byte MD5. -/
def digestOk (d : Digest) : Bool := d.bytes.isEmpty || d.bytes.length == 16

def digestIndex (tag : String) : Option Nat :=
  if tag == (tag% Sym.mk) then some 0
  else if [(tag% Prefix.funArg), (tag% Prefix.stringLiteral),
    (tag% Prefix.compoundLiteral), (tag% Prefix.temporaryLifetime)].contains tag then some 1
  else none

/-- Digest-length errors, with paths through the decoded symbol and prefix forms. -/
def digestProblems (path : List Nat) : Tree → List DecodeError
  | .atom _ => []
  | .tag tag _ cs =>
    let children := List.ofFn cs
    let here := do
      let index ← digestIndex tag
      let child ← children[index]?
      let d ← digest.dec child
      if digestOk d then none
      else some (⟨path ++ [index], "digest must be empty or 16 bytes"⟩ : DecodeError)
    here.toList ++ (List.ofFn fun i => digestProblems (path ++ [i.val]) (cs i)).flatten

/-- Parse and decode a document with the canonical layout and well-formed maps
digests and enum registrations. Every failure includes a zero-based child path. -/
def parseDocument (text : String) : Except DecodeError Document := do
  let some s := parseDoc? text
    | throw ⟨[], "invalid S-expression syntax"⟩
  let some t := taggedDoc? s
    | throw ⟨[], "invalid tagged S-expression syntax"⟩
  if printTagged t ++ "\n" != text then throw ⟨[], "noncanonical document layout"⟩
  let doc ← document.decode t
  let problems := digestProblems [] t ++ mapProblems doc.bindings ++ enumProblems doc.enumBindings
  match problems with
  | e :: _ => throw e
  | [] => return doc

/-- Acceptance exposes the lexical, structural, syntax and validation steps. -/
theorem parseDocument_eq_ok_iff {text : String} {doc : Document} :
    parseDocument text = .ok doc ↔
      ∃ s t, parseDoc? text = some s ∧ taggedDoc? s = some t ∧
        printTagged t ++ "\n" = text ∧ document.dec t = some doc ∧
        digestProblems [] t ++ mapProblems doc.bindings ++ enumProblems doc.enumBindings = [] := by
  cases hs : parseDoc? text with
  | none => simp [parseDocument, hs]
  | some s =>
    cases ht : taggedDoc? s with
    | none => simp [parseDocument, hs, ht]
    | some t =>
      by_cases hl : printTagged t ++ "\n" = text
      · cases hd : document.dec t with
        | none => simp [parseDocument, hs, ht, hl, Codec.decode, hd, bind, Except.bind]
        | some d =>
          cases hp : digestProblems [] t ++ mapProblems d.bindings ++ enumProblems d.enumBindings with
          | nil =>
            simp [parseDocument, hs, ht, hl, Codec.decode, hd, hp, bind, Except.bind, pure, Except.pure]
            intro h
            subst doc
            simpa only [List.append_eq_nil_iff, and_assoc] using hp
          | cons e es =>
            simp [parseDocument, hs, ht, hl, Codec.decode, hd, hp, bind, Except.bind]
            intro h hg hm he
            subst doc
            simp [hg, hm, he] at hp
      · simp [parseDocument, hs, ht, hl, bind, Except.bind]

/-- A checked document prints back to exactly its input bytes. -/
theorem print_parseDocument {text : String} {doc : Document}
    (h : parseDocument text = .ok doc) : printTagged (document.enc doc) ++ "\n" = text := by
  obtain ⟨s, t, _, _, hl, hd, _⟩ := parseDocument_eq_ok_iff.1 h
  rw [document.canonical t doc hd, hl]

/-- The syntax codec is complete for every document value, including values
that the stricter document parser rejects for map order or digest length. -/
theorem document_complete (doc : Document) : document.dec (document.enc doc) = some doc :=
  Codec.complete_of_budget rfl doc

example : digestOk ⟨[]⟩ = true := by rfl
example : digestOk ⟨[0]⟩ = false := by rfl
example : orderProblem (ν := Unit) compare [3, 9] 0 [(1, ()), (1, ())] =
    some ⟨[3, 9, 1, 0], "map keys are not strictly increasing under the Lem comparator"⟩ := by rfl

end Silmaril.Cerberus.Codec.WellFormed
