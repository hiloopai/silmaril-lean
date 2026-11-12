module

public import Silmaril.Net.Hpack.Block.Defs
public import Silmaril.Proofs.Net.Hpack.Integer
public import Silmaril.Proofs.Net.Hpack.Table

/-!
# HPACK field representations: proofs

For `Silmaril.Net.Hpack.Block.Thms` (RFC 7541 §6).
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Hpack

open Silmaril.Net.Hpack

theorem encodeInt_split {n hi : Nat} (hn8 : n ≤ 8) (hhi : hi % 2 ^ n = 0) (hhi' : hi < 256)
    (i : Nat) (rest : List UInt8) : ∃ b tl, encodeInt n hi i ++ rest = b :: tl ∧
      hi ≤ b.toNat ∧ b.toNat < hi + 2 ^ n ∧ decodeInt n (b :: tl) = some (i, rest) := by
  obtain ⟨tl, he, hlt, hv⟩ := encodeInt_head hn8 hhi hhi' i
  have hd := decodeInt_encodeInt hn8 hhi hhi' i rest
  rw [he] at hd
  refine ⟨_, tl ++ rest, by rw [he]; rfl, ?_, ?_, hd⟩ <;>
    simp only [toNat_toUInt8, Nat.mod_eq_of_lt hlt] <;> omega

theorem decodeLiteral_encode (ix : Indexing) (nr : NameRef) (v rest : List UInt8)
    (hwf : (Rep.literal ix nr v).WellFormed) (b : UInt8) (tl : List UInt8)
    (hb : encodeRep (.literal ix nr v) ++ rest = b :: tl)
    (hd : ∀ i rest', encodeInt ix.prefixBits ix.flagBits i ++ rest' = b :: tl →
      decodeInt ix.prefixBits (b :: tl) = some (i, rest')) :
    decodeLiteral ix (b :: tl) = some (.literal ix nr v, rest) := by
  cases nr with
  | indexed i =>
    have hi : i ≠ 0 := hwf
    simp only [encodeRep, List.append_assoc] at hb
    simp only [decodeLiteral, hd i _ hb, hi, ↓reduceIte, decodeString_encodeString]
  | literal n =>
    simp only [encodeRep, List.append_assoc] at hb
    simp only [decodeLiteral, hd 0 _ hb, ↓reduceIte, decodeString_encodeString, Option.map_some]

theorem decodeInt_of_eq {n hi : Nat} (hn8 : n ≤ 8) (hhi : hi % 2 ^ n = 0) (hhi' : hi < 256)
    {b : UInt8} {tl : List UInt8} (i : Nat) (rest' : List UInt8)
    (h : encodeInt n hi i ++ rest' = b :: tl) : decodeInt n (b :: tl) = some (i, rest') := by
  rw [← h]; exact decodeInt_encodeInt hn8 hhi hhi' i rest'

theorem decodeRep_encodeRep (r : Rep) (hwf : r.WellFormed) (rest : List UInt8) :
    decodeRep (encodeRep r ++ rest) = some (r, rest) := by
  cases r with
  | indexed i =>
    obtain ⟨b, tl, he, h1, h2, hd⟩ :=
      encodeInt_split (n := 7) (hi := 0x80) (by decide) (by decide) (by decide) i rest
    simp only [encodeRep, he, decodeRep, show 128 ≤ b.toNat by omega, ↓reduceIte, hd,
      Option.map_some]
  | sizeUpdate m =>
    obtain ⟨b, tl, he, h1, h2, hd⟩ :=
      encodeInt_split (n := 5) (hi := 0x20) (by decide) (by decide) (by decide) m rest
    simp only [encodeRep, he, decodeRep, show ¬ 128 ≤ b.toNat by omega,
      show ¬ 64 ≤ b.toNat by omega, show 32 ≤ b.toNat by omega, ↓reduceIte, hd, Option.map_some]
  | literal ix nr v =>
    -- the first octet of a literal is the first octet of its name index
    have hfirst : ∃ b tl, encodeRep (.literal ix nr v) ++ rest = b :: tl ∧
        ix.flagBits ≤ b.toNat ∧ b.toNat < ix.flagBits + 2 ^ ix.prefixBits := by
      have hix : ix.prefixBits ≤ 8 ∧ ix.flagBits % 2 ^ ix.prefixBits = 0 ∧ ix.flagBits < 256 := by
        cases ix <;> decide
      cases nr with
      | indexed i =>
        obtain ⟨b, tl, he, h1, h2, -⟩ :=
          encodeInt_split hix.1 hix.2.1 hix.2.2 i (encodeString v ++ rest)
        exact ⟨b, tl, by simp only [encodeRep, List.append_assoc, he], h1, h2⟩
      | literal n =>
        obtain ⟨b, tl, he, h1, h2, -⟩ :=
          encodeInt_split hix.1 hix.2.1 hix.2.2 0 (encodeString n ++ encodeString v ++ rest)
        exact ⟨b, tl, by simp only [encodeRep, List.append_assoc] at he ⊢; exact he, h1, h2⟩
    obtain ⟨b, tl, he, h1, h2⟩ := hfirst
    rw [he]
    cases ix with
    | incremental =>
      simp only [Indexing.flagBits, Indexing.prefixBits] at h1 h2
      simp only [decodeRep, show ¬ 128 ≤ b.toNat by omega, show 64 ≤ b.toNat by omega,
        ↓reduceIte]
      exact decodeLiteral_encode _ _ _ _ hwf b tl he
        (decodeInt_of_eq (by decide) (by decide) (by decide))
    | never =>
      simp only [Indexing.flagBits, Indexing.prefixBits] at h1 h2
      simp only [decodeRep, show ¬ 128 ≤ b.toNat by omega, show ¬ 64 ≤ b.toNat by omega,
        show ¬ 32 ≤ b.toNat by omega, show 16 ≤ b.toNat by omega, ↓reduceIte]
      exact decodeLiteral_encode _ _ _ _ hwf b tl he
        (decodeInt_of_eq (by decide) (by decide) (by decide))
    | without =>
      simp only [Indexing.flagBits, Indexing.prefixBits] at h1 h2
      simp only [decodeRep, show ¬ 128 ≤ b.toNat by omega, show ¬ 64 ≤ b.toNat by omega,
        show ¬ 32 ≤ b.toNat by omega, show ¬ 16 ≤ b.toNat by omega, ↓reduceIte]
      exact decodeLiteral_encode _ _ _ _ hwf b tl he
        (decodeInt_of_eq (by decide) (by decide) (by decide))

theorem encodeRep_length_pos (r : Rep) : 0 < (encodeRep r).length := by
  have h : ∀ n hi i, 0 < (encodeInt n hi i).length := by
    intro n hi i; unfold encodeInt; split <;> simp
  cases r with
  | indexed i => exact h _ _ _
  | sizeUpdate m => exact h _ _ _
  | literal ix nr v =>
    cases nr <;> simp only [encodeRep, List.length_append] <;>
      have := h ix.prefixBits ix.flagBits <;> grind

theorem decodeRepsFuel_encodeReps (rs : List Rep) (hwf : ∀ r ∈ rs, r.WellFormed) (k : Nat)
    (hk : (encodeReps rs).length ≤ k) : decodeRepsFuel k (encodeReps rs) = some rs := by
  induction rs generalizing k with
  | nil => cases k <;> rfl
  | cons r rs ih =>
    have hpos := encodeRep_length_pos r
    have hlen : (encodeReps (r :: rs)).length =
        (encodeRep r).length + (encodeReps rs).length := by
      simp [encodeReps]
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨b, tl, hbt⟩ : ∃ b tl, encodeReps (r :: rs) = b :: tl := by
      cases h : encodeReps (r :: rs) with
      | nil => rw [h] at hlen; simp at hlen; omega
      | cons b tl => exact ⟨b, tl, rfl⟩
    have hdec := decodeRep_encodeRep r (hwf r (by simp)) (encodeReps rs)
    have hcat : encodeReps (r :: rs) = encodeRep r ++ encodeReps rs := by
      simp [encodeReps]
    rw [hbt]
    simp only [decodeRepsFuel]
    rw [← hbt, hcat, hdec]
    simp only
    rw [ih (fun x hx => hwf x (by simp [hx])) k (by omega)]

theorem decodeReps_encodeReps (rs : List Rep) (hwf : ∀ r ∈ rs, r.WellFormed) :
    decodeReps (encodeReps rs) = some rs :=
  decodeRepsFuel_encodeReps rs hwf _ (Nat.le_refl _)

theorem processRep_valid {t : DynTable} (ht : t.Valid) {r : Rep} {e? : Option Entry}
    {t' : DynTable} (h : processRep t r = some (e?, t')) : t'.Valid := by
  cases r with
  | indexed i =>
    simp only [processRep, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, _, _, rfl⟩ := h; exact ht
  | sizeUpdate m =>
    simp only [processRep, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨t'', h1, _, rfl⟩ := h; exact setMaxSize_valid h1
  | literal ix nr v =>
    simp only [processRep] at h
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      split
      · exact insert_valid ht _
      · exact ht

theorem processRepsFrom_valid {seen : Bool} {t : DynTable} (ht : t.Valid) {rs : List Rep}
    {es : List Entry} {t' : DynTable} (h : processRepsFrom seen t rs = some (es, t')) :
    t'.Valid := by
  induction rs generalizing seen t es with
  | nil => simp only [processRepsFrom, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact ht
  | cons r rs ih =>
    unfold processRepsFrom at h
    split at h
    · split at h
      · cases h
      · split at h
        · cases h
        · next hp => exact ih (processRep_valid ht hp) h
    · split at h
      · cases h
      · next hp =>
        split at h
        · cases h
        · next hq =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact ih (processRep_valid ht hp) hq

/-- Literals without indexing and never-indexed literals leave the dynamic table alone. -/
theorem processRep_literal_noindex {t : DynTable} {ix : Indexing} (hix : ix ≠ .incremental)
    {nr : NameRef} {v : List UInt8} {e? : Option Entry} {t' : DynTable}
    (h : processRep t (.literal ix nr v) = some (e?, t')) : t' = t := by
  simp only [processRep] at h
  split at h
  · cases h
  · simp only [Option.some.injEq, Prod.mk.injEq, hix, ↓reduceIte] at h
    exact h.2.symm

end Silmaril.Proofs.Net.Hpack
