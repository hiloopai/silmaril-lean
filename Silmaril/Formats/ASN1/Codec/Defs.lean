module

public import Silmaril.Formats.ASN1.Der.Defs

/-!
# ASN.1 codecs: typed views and schema combinators

A `Codec σ α` relates a carrier `σ` (contents octets, a value tree, or the
children of a constructed value) to a typed view `α`: a predicate `WF` on the
typed values that have an encoding, an encoder and a decoder. Codecs are plain
data, so they compute (and the known-answer checks run them by `decide`); their
laws are a separate predicate `Codec.Lawful`: the decoder inverts the encoder
on `WF`, and everything the decoder returns is `WF` and re-encodes to its input.
For a lawful codec the relation `Codec.rel` (`WF a ∧ enc a = s`) is functional
and deterministic and the decoder is sound and complete for it
(`Silmaril.Formats.ASN1.Codec.Thms`).

Schemas are assembled with combinators, each with a lawfulness theorem:

| combinator | ASN.1 (X.680) |
| --- | --- |
| `prim t c` | a primitive type, or `[n] IMPLICIT` of one (`t` is the tag) |
| `cons t c` | `SEQUENCE {…}`, `SEQUENCE OF`, `SET OF`, or `[n] IMPLICIT` of one |
| `explicit n c` | `[n] EXPLICIT T` |
| `nil`, `field`, `optField`, `optLast` | the components of a `SEQUENCE`, with `OPTIONAL` ones |
| `defaulted` | a `DEFAULT` component (DER omits the default value, X.690 §11.5) |
| `seqOf` | the components of `SEQUENCE OF` |
| `setOf` | the components of `SET OF`, in the DER order of X.690 §11.6 |
| `orElse` | `CHOICE` |
| `any` | an open type (`ANY`), uninterpreted |
| `iso`, `refine` | change of representation, and constraints |

`derCodec c` lifts a value codec to DER octets.
-/

@[expose] public section

namespace Silmaril.Formats.ASN1

open Silmaril

/-- A codec between carrier values `σ` and typed values `α`. -/
structure Codec (σ α : Type) where
  /-- The typed values that have an encoding. -/
  WF : α → Prop
  /-- The encoder. -/
  enc : α → σ
  /-- The decoder. -/
  dec : σ → Option α

namespace Codec

variable {σ α β γ : Type}

/-- The codec laws: a partial isomorphism between carrier values and
well-formed typed values. -/
structure Lawful (c : Codec σ α) : Prop where
  /-- The decoder inverts the encoder on well-formed values. -/
  dec_enc : ∀ a, c.WF a → c.dec (c.enc a) = some a
  /-- Decoded values are well formed and re-encode to the input. -/
  enc_dec : ∀ {s a}, c.dec s = some a → c.WF a ∧ c.enc a = s

/-- The encoding relation of a codec: `s` spells `a` when `a` is well formed
and encodes to `s`. -/
def rel (c : Codec σ α) : EncRel σ α := fun s a => c.WF a ∧ c.enc a = s

/-! ## Change of representation, constraints, `CHOICE` -/

/-- Transport along maps `f : α → β` and `g : β → α`; lawful when they are
inverse on the well-formed values (`lawful_iso`). -/
def iso (c : Codec σ α) (f : α → β) (g : β → α) : Codec σ β where
  WF b := c.WF (g b)
  enc b := c.enc (g b)
  dec s := (c.dec s).map f

/-- Restrict to the values satisfying a decidable constraint. -/
def refine (c : Codec σ α) (P : α → Prop) [DecidablePred P] : Codec σ α where
  WF a := c.WF a ∧ P a
  enc := c.enc
  dec s := match c.dec s with
    | some a => if P a then some a else none
    | none => none

/-- `CHOICE` between two alternatives, trying the first one first; lawful when
the first alternative rejects the encodings of the second (`lawful_orElse`). -/
def orElse (c₁ : Codec σ α) (c₂ : Codec σ β) : Codec σ (α ⊕ β) where
  WF x := match x with
    | .inl a => c₁.WF a
    | .inr b => c₂.WF b
  enc x := match x with
    | .inl a => c₁.enc a
    | .inr b => c₂.enc b
  dec s := match c₁.dec s with
    | some a => some (.inl a)
    | none => (c₂.dec s).map .inr

/-! ## Values -/

/-- Any value, uninterpreted (open types). -/
def any : Codec Value Value where
  WF _ := True
  enc v := v
  dec v := some v

/-- A primitive value with tag `t` whose contents octets are read by `c`. With
a universal tag this is the type itself; with a context tag it is
`[n] IMPLICIT`. -/
def prim (t : Tag) (c : Codec (List UInt8) α) : Codec Value α where
  WF := c.WF
  enc a := .prim t (c.enc a)
  dec v := match v with
    | .prim t' b => if t' = t then c.dec b else none
    | .cons _ _ => none

/-- A constructed value with tag `t` whose children are read by `c`. -/
def cons (t : Tag) (c : Codec (List Value) α) : Codec Value α where
  WF := c.WF
  enc a := .cons t (c.enc a)
  dec v := match v with
    | .cons t' vs => if t' = t then c.dec vs else none
    | .prim _ _ => none

/-! ## Component lists -/

/-- The empty component list. -/
def nil : Codec (List Value) Unit where
  WF _ := True
  enc _ := []
  dec vs := match vs with
    | [] => some ()
    | _ :: _ => none

/-- A mandatory component followed by the rest. -/
def field (c : Codec Value α) (rest : Codec (List Value) β) : Codec (List Value) (α × β) where
  WF p := c.WF p.1 ∧ rest.WF p.2
  enc p := c.enc p.1 :: rest.enc p.2
  dec vs := match vs with
    | v :: vs => match c.dec v, rest.dec vs with
      | some a, some b => some (a, b)
      | _, _ => none
    | [] => none

/-- Every well-formed value of `c` has tag `t`. -/
def TagIs (c : Codec Value α) (t : Tag) : Prop := ∀ a, c.WF a → (c.enc a).tag = t

/-- No well-formed encoding of the component list `c` starts with tag `t`. -/
def HeadNot (c : Codec (List Value) β) (t : Tag) : Prop :=
  ∀ b, c.WF b → ∀ v ∈ (c.enc b).head?, v.tag ≠ t

/-- An `OPTIONAL` component with tag `t`, followed by the rest. The component
is present exactly when the next value has tag `t`; lawful when `c` has tag `t`
and the rest never starts with `t` (`lawful_optField`; X.680 §25.6 requires
these tags to be distinct). -/
def optField (t : Tag) (c : Codec Value α) (rest : Codec (List Value) β) :
    Codec (List Value) (Option α × β) where
  WF p := (∀ a ∈ p.1, c.WF a) ∧ rest.WF p.2
  enc p := match p.1 with
    | some a => c.enc a :: rest.enc p.2
    | none => rest.enc p.2
  dec vs := match vs with
    | v :: vs' =>
        if v.tag = t then
          match c.dec v, rest.dec vs' with
          | some a, some b => some (some a, b)
          | _, _ => none
        else (rest.dec (v :: vs')).map (fun b => (none, b))
    | [] => (rest.dec []).map (fun b => (none, b))

/-- An optional last component of any tag (e.g. `parameters ANY OPTIONAL`). -/
def optLast (c : Codec Value α) : Codec (List Value) (Option α) where
  WF o := ∀ a ∈ o, c.WF a
  enc o := match o with
    | some a => [c.enc a]
    | none => []
  dec vs := match vs with
    | [] => some none
    | [v] => (c.dec v).map some
    | _ :: _ :: _ => none

/-- Decode every element of a list. -/
def decAll {τ : Type} (d : τ → Option α) : List τ → Option (List α)
  | [] => some []
  | x :: xs => match d x, decAll d xs with
    | some a, some as => some (a :: as)
    | _, _ => none

/-- The components of `SEQUENCE OF` (and, unordered, of `SET OF`). -/
def seqOf (c : Codec Value α) : Codec (List Value) (List α) where
  WF l := ∀ a ∈ l, c.WF a
  enc l := l.map c.enc
  dec := decAll c.dec

/-! ## SET OF ordering (X.690 §11.6) -/

/-- Lexicographic `≤` on octet strings. -/
def lexLe : List UInt8 → List UInt8 → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && lexLe as bs)

/-- X.690 §11.6: encodings are compared as octet strings, the shorter one
padded at its trailing end with zero octets. -/
def derSetLe (a b : List UInt8) : Bool :=
  lexLe (a ++ List.replicate (b.length - a.length) 0) (b ++ List.replicate (a.length - b.length) 0)

/-- The list is in ascending order. -/
def sortedBy (le : γ → γ → Bool) : List γ → Bool
  | a :: b :: r => le a b && sortedBy le (b :: r)
  | _ => true

/-- The components of `SET OF`, required to be in the DER order of their
encodings. -/
def setOf (c : Codec Value α) : Codec (List Value) (List α) :=
  (seqOf c).refine (fun l => sortedBy derSetLe (l.map (fun a => encode (c.enc a))) = true)

/-! ## Tagging and defaults -/

/-- `[n] EXPLICIT T`. -/
def explicit (n : Nat) (c : Codec Value α) : Codec Value α :=
  cons (Tag.context n) ((field c nil).iso Prod.fst (fun a => (a, ())))

/-- `DEFAULT d`: DER omits a component equal to its default (X.690 §11.5), so
an explicit default is rejected and an absent component reads as `d`. -/
def defaulted [DecidableEq α] (d : α) (c : Codec σ (Option α × γ)) : Codec σ (α × γ) :=
  (c.refine (fun p => p.1 ≠ some d)).iso (fun p => (p.1.getD d, p.2))
    (fun p => (if p.1 = d then none else some p.1, p.2))

/-! ## DER octets -/

/-- A value codec read from and written to DER octets. -/
def derCodec (c : Codec Value α) : Codec (List UInt8) α where
  WF a := c.WF a ∧ (c.enc a).wf = true
  enc a := encode (c.enc a)
  dec s := match decode s with
    | some v => c.dec v
    | none => none

end Codec

end Silmaril.Formats.ASN1
