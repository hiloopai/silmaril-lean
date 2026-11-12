module

public import Silmaril.Semantics.CPort.Encoding.TaggedCodec.Defs

/-!
# Concrete syntaxes for S-expression trees and their laws

This is the law layer of the S-expression standard (`docs/projects/spectec/README.md`). A
`TreeSyntax σ T` pairs a printer `T → σ` with a parser `σ → Option T`, where
`σ` is the source (`String` or `ByteArray`) and `T` is a tree type of the
family. Each dialect proves the laws it has, stated by two predicates:

* `RoundTripOn P`: `parse (print t) = some t` for every tree with `P t`
  (`P` is the dialect's printable fragment, e.g. atoms without spaces);
* `Canonical`: every accepted source is the printing of its tree, that is
  `print (parse s) = s` on the success set.

The constructions below prove their laws once, for every dialect:

* `checked` makes any syntax canonical by re-printing, which is how the
  Cerberus document reader obtains its byte-exact law;
* `mapEquiv` transports a syntax along a proved conversion between trees of
  the family (lists versus cons cells, tagged versus plain);
* `withCodec` composes a tree syntax with a `TaggedCodec.Codec`, giving the
  end-to-end laws for a Lean type;
* `utf8` moves a text syntax to bytes.
-/

@[expose] public section

namespace Silmaril.Formats

/-- A printer and a parser between sources `σ` and trees `T`. -/
structure TreeSyntax (σ : Type) (T : Type) where
  print : T → σ
  parse : σ → Option T

namespace TreeSyntax

variable {σ T U α : Type} (S : TreeSyntax σ T)

/-- Printed trees satisfying `P` parse back to themselves. -/
def RoundTripOn (P : T → Prop) : Prop := ∀ t, P t → S.parse (S.print t) = some t

/-- Every accepted source is the printing of its tree: one spelling per tree. -/
def Canonical : Prop := ∀ s t, S.parse s = some t → S.print t = s

/-- The relation in the shared encoding theory: a source encodes its parse. -/
def rel : EncRel σ T := EncRel.ofDecoder S.parse

theorem rel_functional : S.rel.Functional := EncRel.ofDecoder_functional _

variable {S}

theorem RoundTripOn.mono {P Q : T → Prop} (h : S.RoundTripOn P) (hQ : ∀ t, Q t → P t) :
    S.RoundTripOn Q := fun t ht => h t (hQ t ht)

/-- The printer is injective on the printable fragment. -/
theorem RoundTripOn.print_inj {P : T → Prop} (h : S.RoundTripOn P) {t u : T}
    (ht : P t) (hu : P u) (e : S.print t = S.print u) : t = u := by
  have := h t ht
  rw [e, h u hu] at this
  exact (Option.some.inj this).symm

/-- The printer lies inside the relation on the printable fragment. -/
theorem RoundTripOn.encoderCorrectOn {P : T → Prop} (h : S.RoundTripOn P) :
    S.rel.EncoderCorrectOn P S.print := h

/-- A canonical syntax accepts at most one source per tree. -/
theorem Canonical.parse_inj (h : S.Canonical) {s s' : σ} {t : T}
    (hs : S.parse s = some t) (hs' : S.parse s' = some t) : s = s' :=
  (h s t hs).symm.trans (h s' t hs')

/-- In a canonical syntax, every tree the parser produces round trips. -/
theorem Canonical.parse_print (h : S.Canonical) {s : σ} {t : T}
    (hs : S.parse s = some t) : S.parse (S.print t) = some t := by
  rw [h s t hs]
  exact hs

/-- A canonical syntax round trips exactly on the trees it can produce. -/
theorem Canonical.roundTripOn (h : S.Canonical) :
    S.RoundTripOn (fun t => ∃ s, S.parse s = some t) :=
  fun _ ⟨_, hs⟩ => h.parse_print hs

/-! ## Canonical by re-printing -/

variable (S)

/-- Accept a source only if it is the printing of its parse. -/
def checked [DecidableEq σ] : TreeSyntax σ T where
  print := S.print
  parse s := (S.parse s).filter fun t => decide (S.print t = s)

theorem checked_parse_eq_some [DecidableEq σ] {s : σ} {t : T} :
    S.checked.parse s = some t ↔ S.parse s = some t ∧ S.print t = s := by
  simp [checked, Option.filter_eq_some_iff]

theorem checked_canonical [DecidableEq σ] : S.checked.Canonical :=
  fun _ _ h => ((S.checked_parse_eq_some).1 h).2

variable {S}

theorem RoundTripOn.checked [DecidableEq σ] {P : T → Prop} (h : S.RoundTripOn P) :
    S.checked.RoundTripOn P :=
  fun t ht => (S.checked_parse_eq_some).2 ⟨h t ht, rfl⟩

/-- Re-printing changes nothing for a syntax that is already canonical. -/
theorem Canonical.checked_parse [DecidableEq σ] (h : S.Canonical) (s : σ) :
    S.checked.parse s = S.parse s := by
  cases hs : S.parse s with
  | none => simp [checked, hs]
  | some t => exact (S.checked_parse_eq_some).2 ⟨hs, h s t hs⟩

/-! ## Transport along tree conversions -/

variable (S)

/-- Read and print a different member of the tree family through a proved
conversion. -/
def mapEquiv (e : T ≃ U) : TreeSyntax σ U where
  print u := S.print (e.symm u)
  parse s := (S.parse s).map e

variable {S}

theorem RoundTripOn.mapEquiv {P : T → Prop} (h : S.RoundTripOn P) (e : T ≃ U) :
    (S.mapEquiv e).RoundTripOn (fun u => P (e.symm u)) := by
  intro u hu
  simp [TreeSyntax.mapEquiv, h _ hu]

theorem Canonical.mapEquiv (h : S.Canonical) (e : T ≃ U) : (S.mapEquiv e).Canonical := by
  intro s u hs
  simp only [TreeSyntax.mapEquiv, Option.map_eq_some_iff] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  simpa [TreeSyntax.mapEquiv] using h s t ht

/-! ## Composition with value codecs -/

open TaggedCodec

variable (S : TreeSyntax σ TaggedCodec.Tree)

/-- Print and read values of a Lean type through a tagged codec. The codec
does not depend on the dialect. -/
def withCodec (c : Codec α) : TreeSyntax σ α where
  print x := S.print (c.enc x)
  parse s := S.parse s >>= c.dec

variable {S}

/-- End-to-end round trip: printable encodings within the codec's budget. -/
theorem RoundTripOn.withCodec {P : TaggedCodec.Tree → Prop} (h : S.RoundTripOn P)
    (c : Codec α) :
    (S.withCodec c).RoundTripOn
      (fun x => P (c.enc x) ∧ c.budget.allows (depth (c.enc x))) := by
  intro x ⟨hp, hb⟩
  simp [TreeSyntax.withCodec, h _ hp, c.complete x hb]

/-- A canonical tree syntax and a codec give one spelling per value. -/
theorem Canonical.withCodec (h : S.Canonical) (c : Codec α) :
    (S.withCodec c).Canonical := by
  intro s x hs
  simp only [TreeSyntax.withCodec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hs
  obtain ⟨t, ht, hx⟩ := hs
  show S.print (c.enc x) = s
  rw [c.canonical t x hx]
  exact h s t ht

/-! ## Text to bytes -/

variable (S : TreeSyntax String T)

/-- Read UTF-8 bytes and print them. -/
def utf8 : TreeSyntax ByteArray T where
  print t := (S.print t).toByteArray
  parse b := String.fromUTF8? b >>= S.parse

theorem fromUTF8?_toByteArray (s : String) : String.fromUTF8? s.toByteArray = some s := by
  simp only [String.fromUTF8?, s.isValidUTF8, ↓reduceDIte]
  rfl

theorem toByteArray_of_fromUTF8? {b : ByteArray} {s : String}
    (h : String.fromUTF8? b = some s) : s.toByteArray = b := by
  simp only [String.fromUTF8?] at h
  split at h
  · cases h
    rfl
  · cases h

variable {S}

theorem RoundTripOn.utf8 {P : T → Prop} (h : S.RoundTripOn P) : S.utf8.RoundTripOn P := by
  intro t ht
  simp [TreeSyntax.utf8, fromUTF8?_toByteArray, h t ht]

theorem Canonical.utf8 (h : S.Canonical) : S.utf8.Canonical := by
  intro b t hb
  simp only [TreeSyntax.utf8, Option.bind_eq_bind, Option.bind_eq_some_iff] at hb
  obtain ⟨s, hs, ht⟩ := hb
  show (S.print t).toByteArray = b
  rw [h s t ht]
  exact toByteArray_of_fromUTF8? hs

end TreeSyntax

end Silmaril.Formats
