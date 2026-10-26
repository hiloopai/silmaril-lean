module

public import Silmaril.X86.Features.Transport

/-!
# Restricted extensions and canonical decoders

Two generic constructions for extension lanes, both additive over
`Features.Extension`:

* `canonicalDecoder parse encode` turns a parser that reads back every encoding
  (`parse (encode x ++ rest) = some x`) into a `Machine.Decoder` that accepts
  exactly the byte strings beginning with a canonical encoding, the policy
  `Ext.decode` follows. The five decoder laws hold for any such parser
  (`canonicalDecoder_decode_iff`).
* `Extension.union e₁ e₂ hd` joins two disjoint extensions into one whose
  syntax is the sum; both embed into it (`Embeds.union_left`,
  `Embeds.union_right`). It is how two lanes that overlap are reconciled into
  one extension that each of them embeds into (`IntMerged`).
* `Extension.restrict e p` keeps the instructions of `e` satisfying `p`. It
  embeds into `e` (`Embeds.restrict`), and into `e.restrict q` whenever `p`
  implies `q` (`Embeds.restrict_mono`); restrictions to disjoint predicates are
  disjoint (`Disjoint.restrict`), and a restriction inherits disjointness from
  `e` (`Disjoint.restrict_left`).

A lane that publishes its forms as one extension `e` with restrictions
`e.restrict p` for its sub-families is in lattice form: whatever is proved
about a run under a smaller restriction holds under every larger one and under
`e` itself, by `run_conservative` (`Included.restrict`).
-/

@[expose] public section

namespace Silmaril.X86.Features

open Silmaril.X86 (Byte)

/-! ## Canonical decoders -/

section Canonical

variable {α : Type} (parse : List Byte → Option α) (encode : α → List Byte)

/-- Accept the bytes when the parsed instruction's canonical encoding is a
prefix of them. -/
def canonicalDecode (bytes : List Byte) : Option (α × Nat) :=
  match parse bytes with
  | some x => if bytes.take (encode x).length = encode x then some (x, (encode x).length) else none
  | none => none

variable {parse encode}

theorem canonicalDecode_sound {bytes : List Byte} {x : α} {n : Nat}
    (h : canonicalDecode parse encode bytes = some (x, n)) :
    n = (encode x).length ∧ bytes = encode x ++ bytes.drop n := by
  unfold canonicalDecode at h
  split at h
  · rename_i y _
    split_ifs at h with hp
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨rfl, ?_⟩
    conv_lhs => rw [← List.take_append_drop (encode y).length bytes]
    rw [hp]
  · cases h

theorem canonicalDecode_encode_append (hparse : ∀ x rest, parse (encode x ++ rest) = some x)
    (x : α) (rest : List Byte) :
    canonicalDecode parse encode (encode x ++ rest) = some (x, (encode x).length) := by
  simp [canonicalDecode, hparse]

theorem canonicalDecode_iff (hparse : ∀ x rest, parse (encode x ++ rest) = some x)
    {bytes : List Byte} {x : α} {n : Nat} :
    canonicalDecode parse encode bytes = some (x, n) ↔ n = (encode x).length ∧ encode x <+: bytes := by
  constructor
  · intro h
    obtain ⟨hn, hb⟩ := canonicalDecode_sound h
    exact ⟨hn, ⟨_, hb.symm⟩⟩
  · rintro ⟨rfl, rest, rfl⟩
    exact canonicalDecode_encode_append hparse x rest

/-- The canonical decoder of a parser that reads back every encoding. -/
def canonicalDecoder (parse : List Byte → Option α) (encode : α → List Byte)
    (hparse : ∀ x rest, parse (encode x ++ rest) = some x) (hne : ∀ x, encode x ≠ []) :
    Machine.Decoder α where
  decode := canonicalDecode parse encode
  encode := encode
  decode_length_pos h := by
    obtain ⟨rfl, -⟩ := canonicalDecode_sound h
    exact List.length_pos_of_ne_nil (hne _)
  decode_length_le h := by
    obtain ⟨rfl, hb⟩ := canonicalDecode_sound h
    have := congrArg List.length hb
    simp only [List.length_append, List.length_drop] at this
    omega
  decode_append extra h := by
    obtain ⟨hn, rest, rfl⟩ := (canonicalDecode_iff hparse).mp h
    rw [List.append_assoc, canonicalDecode_encode_append hparse, hn]
  decode_take {bytes x n} h := by
    obtain ⟨rfl, rest, hb⟩ := (canonicalDecode_iff hparse).mp h
    subst hb
    rw [List.take_left, ← List.append_nil (encode x), canonicalDecode_encode_append hparse]
    simp
  decode_encode_append x rest := canonicalDecode_encode_append hparse x rest

@[simp] theorem canonicalDecoder_decode (hparse : ∀ x rest, parse (encode x ++ rest) = some x)
    (hne : ∀ x, encode x ≠ []) :
    (canonicalDecoder parse encode hparse hne).decode = canonicalDecode parse encode := rfl

theorem canonicalDecoder_decode_iff (hparse : ∀ x rest, parse (encode x ++ rest) = some x)
    (hne : ∀ x, encode x ≠ []) {bytes : List Byte} {x : α} {n : Nat} :
    (canonicalDecoder parse encode hparse hne).decode bytes = some (x, n) ↔
      n = (encode x).length ∧ encode x <+: bytes :=
  canonicalDecode_iff hparse

end Canonical

/-! ## Restricted decoders and extensions -/

namespace Machine

variable {α : Type}

/-- The instructions of `d` satisfying `p`. -/
def restrictDecode (d : Silmaril.Machine.Decoder α) (p : α → Bool) (bytes : List Byte) :
    Option ({x // p x = true} × Nat) :=
  match d.decode bytes with
  | some (x, n) => if h : p x = true then some (⟨x, h⟩, n) else none
  | none => none

theorem restrictDecode_eq_some {d : Silmaril.Machine.Decoder α} {p : α → Bool}
    {bytes : List Byte} {x : {x // p x = true}} {n : Nat} :
    restrictDecode d p bytes = some (x, n) ↔ d.decode bytes = some (x.1, n) := by
  unfold restrictDecode
  constructor
  · intro h
    split at h
    · rename_i y k hy
      split at h
      · cases h; exact hy
      · cases h
    · cases h
  · intro h
    rw [h]
    simp [x.2]

theorem restrictDecode_eq_none {d : Silmaril.Machine.Decoder α} {p : α → Bool}
    {bytes : List Byte} (h : d.decode bytes = none) : restrictDecode d p bytes = none := by
  simp [restrictDecode, h]

/-- `d` restricted to the instructions satisfying `p`. -/
def restrictDecoder (d : Silmaril.Machine.Decoder α) (p : α → Bool) :
    Silmaril.Machine.Decoder {x // p x = true} where
  decode := restrictDecode d p
  encode x := d.encode x.1
  decode_length_pos h := d.decode_length_pos (restrictDecode_eq_some.mp h)
  decode_length_le h := d.decode_length_le (restrictDecode_eq_some.mp h)
  decode_append extra h :=
    restrictDecode_eq_some.mpr (d.decode_append extra (restrictDecode_eq_some.mp h))
  decode_take h := restrictDecode_eq_some.mpr (d.decode_take (restrictDecode_eq_some.mp h))
  decode_encode_append x rest := restrictDecode_eq_some.mpr (d.decode_encode_append x.1 rest)

end Machine

namespace Extension

/-- The instructions of `e` satisfying `p`, with the same requirements and
semantics. -/
def restrict (e : Extension) (p : e.Syntax → Bool) : Extension where
  name := e.name
  Syntax := {x // p x = true}
  decoder := Machine.restrictDecoder e.decoder p
  requires x := e.requires x.1
  exec x := e.exec x.1

theorem restrict_decode_eq_some {e : Extension} {p : e.Syntax → Bool} {bytes : List Byte}
    {x : (e.restrict p).Syntax} {n : Nat} :
    (e.restrict p).decoder.decode bytes = some (x, n) ↔ e.decoder.decode bytes = some (x.1, n) :=
  Machine.restrictDecode_eq_some

/-- A restriction embeds into the whole extension. -/
theorem Embeds.restrict (e : Extension) (p : e.Syntax → Bool) : (e.restrict p).Embeds e :=
  ⟨Subtype.val, fun _ _ _ h => restrict_decode_eq_some.mp h, fun _ => rfl, fun _ _ _ _ => rfl⟩

/-- A smaller restriction embeds into a larger one. -/
theorem Embeds.restrict_mono (e : Extension) {p q : e.Syntax → Bool}
    (hpq : ∀ x, p x = true → q x = true) : (e.restrict p).Embeds (e.restrict q) :=
  ⟨fun x => ⟨x.1, hpq x.1 x.2⟩,
    fun _ _ _ h => restrict_decode_eq_some.mpr (restrict_decode_eq_some (p := p).mp h),
    fun _ => rfl, fun _ _ _ _ => rfl⟩

theorem Disjoint.symm {e e' : Extension} (h : e.Disjoint e') : e'.Disjoint e :=
  fun bytes => (h bytes).symm

/-- Restrictions to predicates with no common instruction are disjoint. -/
theorem Disjoint.restrict (e : Extension) {p q : e.Syntax → Bool}
    (hpq : ∀ x, p x = true → q x = false) : (e.restrict p).Disjoint (e.restrict q) := by
  intro bytes
  cases hd : e.decoder.decode bytes with
  | none =>
    exact .inl (Machine.restrictDecode_eq_none hd)
  | some r =>
    obtain ⟨x, n⟩ := r
    by_cases hp : p x = true
    · right
      have hq := hpq x hp
      simp [Extension.restrict, Machine.restrictDecoder, Machine.restrictDecode, hd, hq]
    · left
      simp [Extension.restrict, Machine.restrictDecoder, Machine.restrictDecode, hd, hp]

/-- A restriction keeps the disjointness of the extension it restricts. -/
theorem Disjoint.restrict_left {e e' : Extension} (h : e.Disjoint e') (p : e.Syntax → Bool) :
    (e.restrict p).Disjoint e' := by
  intro bytes
  rcases h bytes with h | h
  · exact .inl (Machine.restrictDecode_eq_none h)
  · exact .inr h

end Extension

/-- A list of restrictions of `e` is included in any list containing `e`. -/
theorem Included.restrict {e : Extension} {exts : List Extension} (he : e ∈ exts)
    (ps : List (e.Syntax → Bool)) : Included (ps.map e.restrict) exts := by
  intro e' he'
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp he'
  exact ⟨e, he, Extension.Embeds.restrict e p⟩

/-- Inclusion is transitive. -/
theorem Included.trans {exts₁ exts₂ exts₃ : List Extension} (h₁ : Included exts₁ exts₂)
    (h₂ : Included exts₂ exts₃) : Included exts₁ exts₃ := by
  intro e he
  obtain ⟨e', he', hee'⟩ := h₁ e he
  obtain ⟨e'', he'', he'e''⟩ := h₂ e' he'
  exact ⟨e'', he'', hee'.trans he'e''⟩

/-! ## Unions of disjoint extensions -/

namespace Machine

variable {α β : Type}

/-- Decode with `d₁`, or else with `d₂`. -/
def unionDecode (d₁ : Silmaril.Machine.Decoder α) (d₂ : Silmaril.Machine.Decoder β)
    (bytes : List Byte) : Option ((α ⊕ β) × Nat) :=
  match d₁.decode bytes with
  | some (x, n) => some (.inl x, n)
  | none => (d₂.decode bytes).map fun r => (.inr r.1, r.2)

variable {d₁ : Silmaril.Machine.Decoder α} {d₂ : Silmaril.Machine.Decoder β}

theorem unionDecode_inl {bytes : List Byte} {x : α} {n : Nat} :
    unionDecode d₁ d₂ bytes = some (.inl x, n) ↔ d₁.decode bytes = some (x, n) := by
  unfold unionDecode
  constructor
  · intro h
    split at h
    · cases h; assumption
    · simp at h
  · intro h; rw [h]

theorem unionDecode_inr {bytes : List Byte} {y : β} {n : Nat} :
    unionDecode d₁ d₂ bytes = some (.inr y, n) ↔
      d₁.decode bytes = none ∧ d₂.decode bytes = some (y, n) := by
  unfold unionDecode
  constructor
  · intro h
    split at h
    · cases h
    · rename_i hn
      obtain ⟨⟨y', n'⟩, h', he⟩ := Option.map_eq_some_iff.mp h
      cases he
      exact ⟨hn, h'⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    rfl

/-- The union of two decoders that never accept the same bytes. -/
def unionDecoder (d₁ : Silmaril.Machine.Decoder α) (d₂ : Silmaril.Machine.Decoder β)
    (hd : ∀ bytes, d₁.decode bytes = none ∨ d₂.decode bytes = none) :
    Silmaril.Machine.Decoder (α ⊕ β) where
  decode := unionDecode d₁ d₂
  encode
    | .inl x => d₁.encode x
    | .inr y => d₂.encode y
  decode_length_pos {bytes z n} h := by
    cases z with
    | inl x => exact d₁.decode_length_pos (unionDecode_inl.mp h)
    | inr y => exact d₂.decode_length_pos (unionDecode_inr.mp h).2
  decode_length_le {bytes z n} h := by
    cases z with
    | inl x => exact d₁.decode_length_le (unionDecode_inl.mp h)
    | inr y => exact d₂.decode_length_le (unionDecode_inr.mp h).2
  decode_append {bytes z n} extra h := by
    cases z with
    | inl x => exact unionDecode_inl.mpr (d₁.decode_append extra (unionDecode_inl.mp h))
    | inr y =>
      have h2 := d₂.decode_append extra (unionDecode_inr.mp h).2
      refine unionDecode_inr.mpr ⟨?_, h2⟩
      rcases hd (bytes ++ extra) with h1 | h1
      · exact h1
      · rw [h1] at h2; cases h2
  decode_take {bytes z n} h := by
    cases z with
    | inl x => exact unionDecode_inl.mpr (d₁.decode_take (unionDecode_inl.mp h))
    | inr y =>
      have h2 := d₂.decode_take (unionDecode_inr.mp h).2
      refine unionDecode_inr.mpr ⟨?_, h2⟩
      rcases hd (bytes.take n) with h1 | h1
      · exact h1
      · rw [h1] at h2; cases h2
  decode_encode_append z rest := by
    cases z with
    | inl x => exact unionDecode_inl.mpr (d₁.decode_encode_append x rest)
    | inr y =>
      have h2 := d₂.decode_encode_append y rest
      refine unionDecode_inr.mpr ⟨?_, h2⟩
      rcases hd (d₂.encode y ++ rest) with h1 | h1
      · exact h1
      · rw [h1] at h2; cases h2

end Machine

namespace Extension

/-- The union of two disjoint extensions: an instruction of either, with its
requirements and semantics. -/
def union (e₁ e₂ : Extension) (hd : e₁.Disjoint e₂) : Extension where
  name := e₁.name ++ " + " ++ e₂.name
  Syntax := e₁.Syntax ⊕ e₂.Syntax
  decoder := Machine.unionDecoder e₁.decoder e₂.decoder hd
  requires
    | .inl x => e₁.requires x
    | .inr y => e₂.requires y
  exec
    | .inl x => e₁.exec x
    | .inr y => e₂.exec y

/-- The left summand embeds into the union. -/
theorem Embeds.union_left (e₁ e₂ : Extension) (hd : e₁.Disjoint e₂) : e₁.Embeds (e₁.union e₂ hd) :=
  ⟨Sum.inl, fun _ _ _ h => Machine.unionDecode_inl.mpr h, fun _ => rfl, fun _ _ _ _ => rfl⟩

/-- The right summand embeds into the union. -/
theorem Embeds.union_right (e₁ e₂ : Extension) (hd : e₁.Disjoint e₂) :
    e₂.Embeds (e₁.union e₂ hd) := by
  refine ⟨Sum.inr, fun bytes y n h => Machine.unionDecode_inr.mpr ⟨?_, h⟩, fun _ => rfl,
    fun _ _ _ _ => rfl⟩
  rcases hd bytes with h1 | h1
  · exact h1
  · rw [h1] at h; cases h

/-- A union is disjoint from every extension both summands are disjoint from. -/
theorem Disjoint.union {e₁ e₂ e : Extension} (hd : e₁.Disjoint e₂) (h₁ : e₁.Disjoint e)
    (h₂ : e₂.Disjoint e) : (e₁.union e₂ hd).Disjoint e := by
  intro bytes
  rcases h₁ bytes with h | h
  · rcases h₂ bytes with h' | h'
    · left
      show Machine.unionDecode e₁.decoder e₂.decoder bytes = none
      simp [Machine.unionDecode, h, h']
    · exact .inr h'
  · exact .inr h

end Extension

end Silmaril.X86.Features
