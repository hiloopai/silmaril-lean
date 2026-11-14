module

public import Init

/-!
# ASN.1: tags and value trees

A BER or DER encoding is a tree of tag-length-value triples (X.690 §8.1).
`Value` is that tree with the length fields erased: a primitive value carries
its contents octets, a constructed value its children. The constructed bit of
the identifier octet is the constructor (`Value.prim` versus `Value.cons`), not
part of the `Tag`.

The DER layer (`Silmaril.Formats.ASN1.Der`) relates byte strings to these
trees; typed views of the universal types (`Universal`, `Time`) and schemas
(`Codec`) are built on top, so the byte layer does not depend on any
particular ASN.1 module.
-/

@[expose] public section

namespace Silmaril.Formats.ASN1

/-- The tag class (X.680 §8.1; bits 8–7 of the identifier octet, X.690
§8.1.2.2). -/
inductive TagClass where
  | universal
  | application
  | contextSpecific
  | «private»
  deriving DecidableEq, Repr

namespace TagClass

/-- The two class bits as a number in `0..3`. -/
def bits : TagClass → Nat
  | universal => 0
  | application => 1
  | contextSpecific => 2
  | «private» => 3

/-- The class with the given two class bits (only `n % 4` matters). -/
def ofBits (n : Nat) : TagClass :=
  match n % 4 with
  | 0 => universal
  | 1 => application
  | 2 => contextSpecific
  | _ => «private»

theorem bits_lt (c : TagClass) : c.bits < 4 := by cases c <;> decide

@[simp] theorem ofBits_bits (c : TagClass) : ofBits c.bits = c := by cases c <;> rfl

theorem bits_ofBits : ∀ n < 4, (ofBits n).bits = n := by decide

end TagClass

/-- An ASN.1 tag: class and number. Numbers of 31 and above use the
high-tag-number form of the identifier octets. -/
structure Tag where
  cls : TagClass
  number : Nat
  deriving DecidableEq, Repr

namespace Tag

/-- `[UNIVERSAL n]`. -/
abbrev universal (n : Nat) : Tag := ⟨.universal, n⟩

/-- `[n]`, context-specific. -/
abbrev context (n : Nat) : Tag := ⟨.contextSpecific, n⟩

/-- The end-of-contents tag `[UNIVERSAL 0]`, reserved for BER indefinite
lengths (X.690 §8.1.5); it never occurs in DER. -/
abbrev eoc : Tag := universal 0

/-! Universal tag numbers of X.680 §8.6, Table 1. -/

abbrev boolean : Tag := universal 1
abbrev integer : Tag := universal 2
abbrev bitString : Tag := universal 3
abbrev octetString : Tag := universal 4
abbrev null : Tag := universal 5
abbrev oid : Tag := universal 6
abbrev utf8String : Tag := universal 12
abbrev sequence : Tag := universal 16
abbrev set : Tag := universal 17
abbrev printableString : Tag := universal 19
abbrev ia5String : Tag := universal 22
abbrev utcTime : Tag := universal 23
abbrev generalizedTime : Tag := universal 24

end Tag

/-- An ASN.1 value as a tree of tag-length-value triples, lengths erased. -/
inductive Value where
  /-- A primitive encoding: tag and contents octets. -/
  | prim (tag : Tag) (content : List UInt8)
  /-- A constructed encoding: tag and the values in the contents octets. -/
  | cons (tag : Tag) (children : List Value)
  deriving Repr

namespace Value

instance : Inhabited Value := ⟨prim Tag.null []⟩

/-- The tag of a value. -/
def tag : Value → Tag
  | prim t _ => t
  | cons t _ => t

@[simp] theorem tag_prim (t : Tag) (b : List UInt8) : (prim t b).tag = t := rfl
@[simp] theorem tag_cons (t : Tag) (vs : List Value) : (cons t vs).tag = t := rfl

mutual
/-- Decidable equality, written by hand because `Value` is a nested inductive. -/
def decEq : (a b : Value) → Decidable (a = b)
  | prim t b, prim t' b' =>
      if h : t = t' ∧ b = b' then isTrue (by rw [h.1, h.2])
      else isFalse (by intro e; cases e; exact h ⟨rfl, rfl⟩)
  | cons t vs, cons t' vs' =>
      match decEqList vs vs' with
      | isTrue hv =>
          if ht : t = t' then isTrue (by rw [ht, hv])
          else isFalse (by intro e; cases e; exact ht rfl)
      | isFalse hv => isFalse (by intro e; cases e; exact hv rfl)
  | prim _ _, cons _ _ => isFalse (by intro e; cases e)
  | cons _ _, prim _ _ => isFalse (by intro e; cases e)

/-- Decidable equality on lists of values. -/
def decEqList : (a b : List Value) → Decidable (a = b)
  | [], [] => isTrue rfl
  | v :: vs, w :: ws =>
      match decEq v w, decEqList vs ws with
      | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
      | isFalse h₁, _ => isFalse (by intro e; cases e; exact h₁ rfl)
      | _, isFalse h₂ => isFalse (by intro e; cases e; exact h₂ rfl)
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
end

instance : DecidableEq Value := decEq

end Value

end Silmaril.Formats.ASN1
