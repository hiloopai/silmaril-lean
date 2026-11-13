module

public import Silmaril.Semantics.CPort.Encoding.TaggedCodec.Defs
public import Silmaril.Semantics.CPort.Formats.SExp.EncodingCompareParser.Defs
public import Silmaril.Formats.SExp.Printer

/-!
# Tagged syntax on the shared S-expression target

Tags are symbols; atoms inside `$str` are UTF-8 strings. The structural
reader erases lexical classes, while the canonical text convention checks
their spelling. Text parsing uses the existing `parseDoc?` reader.
-/

@[expose] public section

namespace Silmaril.Formats.SExpEncoding

open Silmaril TaggedCodec

/-- Embed tagged syntax, quoting atoms in a `$str` node. -/
def ofTagged (quoted : Bool) : Tree → SExp
  | .atom s => .atom (if quoted then .str (Unicode.utf8 s) else .sym s)
  | .tag tag _ cs => listOf (kw tag :: List.ofFn fun i => ofTagged (tag == "$str") (cs i))

mutual
  /-- Read the tagged convention, requiring symbol tags and valid UTF-8 strings. -/
  def tagged? : SExp → Option Tree
    | .atom (.sym s) => some (.atom s)
    | .atom (.str bs) => Formats.TExpr.atom <$> Unicode.utf8? bs
    | .cons (.atom (.sym tag)) rest => node tag <$> taggedChildren? rest
    | _ => none

  /-- Read a proper list of tagged children. -/
  def taggedChildren? : SExp → Option (List Tree)
    | .nil => some []
    | .cons x xs => do
      let x ← tagged? x
      let xs ← taggedChildren? xs
      return x :: xs
    | .atom _ => none
end

theorem taggedChildren?_listOf (xs : List SExp) (ts : List Tree)
    (h : xs.map tagged? = ts.map some) : taggedChildren? (listOf xs) = some ts := by
  induction xs generalizing ts with
  | nil => cases ts <;> simp_all [taggedChildren?]
  | cons x xs ih =>
    cases ts with
    | nil => simp at h
    | cons t ts =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp [taggedChildren?, h.1, ih ts h.2]

/-- The embedding retains every tagged tree, independently of quoting context. -/
@[simp] theorem tagged?_ofTagged (t : Tree) (q : Bool) :
    tagged? (ofTagged q t) = some t := by
  induction t generalizing q with
  | atom s => cases q <;> simp [ofTagged, tagged?]
  | tag tag n cs ih =>
    have h := taggedChildren?_listOf
      (List.ofFn fun i => ofTagged (tag == "$str") (cs i)) (List.ofFn cs) (by
        simp only [List.map_ofFn]
        congr 1
        funext i
        exact ih i (tag == "$str"))
    simp only [ofTagged, listOf_cons, kw, tagged?, h, Option.map_eq_map, Option.map_some]
    rw [node_ofFn]

/-- One top-level tagged datum in the shared document convention. -/
def taggedDoc (t : Tree) : SExp := doc [ofTagged false t]

/-- Documents contain exactly one tagged datum. -/
def taggedDoc? : SExp → Option Tree
  | .cons x .nil => tagged? x
  | _ => none

/-- Parse one tagged document through the shared lexical reader. -/
def parseTagged? (text : String) : Option Tree := (parseDoc? text).bind taggedDoc?

@[simp] theorem taggedDoc?_taggedDoc (t : Tree) : taggedDoc? (taggedDoc t) = some t :=
  tagged?_ofTagged t false

theorem taggedDoc_injective : Function.Injective taggedDoc := by
  intro a b h
  have := congrArg taggedDoc? h
  simpa using this

/-- Atom spelling uses the shared printer and UTF-8 decoder. -/
def printTaggedAtom : Atom → String
  | .sym s => s
  | .str bs => SExpPrinter.quote ((Unicode.utf8? bs).getD "")
  | .id s => "$" ++ s

/-- Canonical tagged layout, without the document's final newline. -/
def printTagged (t : Tree) : String :=
  SExpPrinter.printSExp2With printTaggedAtom (ofTagged false t)

/-- Canonical layout is a restriction of the existing Lisp lexical convention. -/
def TaggedCanonical (text : String) : Prop :=
  ∃ s t, parseDoc? text = some s ∧ taggedDoc? s = some t ∧ printTagged t ++ "\n" = text

/-- Cerberus uses the existing Lisp reader with its exact canonical spelling. -/
def sexpCerberus : EncRel String SExp :=
  (EncRel.ofDecoder parseDoc?).restrictCarrier TaggedCanonical

theorem sexpCerberus_functional : sexpCerberus.Functional :=
  (EncRel.ofDecoder_functional parseDoc?).anti
    (EncRel.restrictCarrier_le _ _)

end Silmaril.Formats.SExpEncoding
