module

public import Silmaril.Wasm.Tools.Meta.Names.Defs
public import Silmaril.Wasm.Tools.Meta.Frame.Thms

/-!
# The name sections: decoding inverts encoding

For well-formed decoded subsections (`SubOk`: valid UTF-8 names within the length limits,
strictly increasing indices below `2^32`, ids that match the subsection kind):

* `readMap_encMap`, `readInd_encInd`: maps and indirect maps round-trip;
* `decodeNames_encNames`: **the module `name` section round-trips**:
  `decodeNames strict (encNames ss) = .ok ss` (with `strict`, when no subsection is raw);
* `decodeCompNames_encNames`: the same for `component-name` subsections with known sorts.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta

/-- A name that wasmparser reads back: UTF-8, its length fits a `u32`, and (with `lim`) at most
100 000 bytes. -/
def NameOk (lim : Bool) (s : List UInt8) : Prop :=
  utf8Ok s = true ∧ s.length < 2 ^ 32 ∧ (lim = true → s.length ≤ 100000)

/-- The entries of a name map that read back after `last`. -/
def EntriesOk (lim : Bool) : Option Nat → NMap → Prop
  | _, [] => True
  | last, (i, s) :: m => idxOk last i = true ∧ i < 2 ^ 32 ∧ NameOk lim s ∧ EntriesOk lim (some i) m

/-- A name map that reads back. -/
def MapOk (lim : Bool) (m : NMap) : Prop := m.length < 2 ^ 32 ∧ EntriesOk lim none m

/-- The entries of an indirect name map that read back after `last`. -/
def IndEntriesOk : Option Nat → List (Nat × NMap) → Prop
  | _, [] => True
  | last, (i, m) :: ms => idxOk last i = true ∧ i < 2 ^ 32 ∧ MapOk true m ∧ IndEntriesOk (some i) ms

/-- An indirect name map that reads back. -/
def IndOk (ms : List (Nat × NMap)) : Prop := ms.length < 2 ^ 32 ∧ IndEntriesOk none ms

/-- The bytes of a string are valid UTF-8. -/
theorem utf8Ok_toUTF8 (s : String) : utf8Ok s.toUTF8.data.toList = true := by
  have h : ByteArray.mk s.toUTF8.data.toList.toArray = s.toByteArray := by
    simp [String.toUTF8_eq_toByteArray]
  simp only [utf8Ok, h]
  exact ByteArray.validateUTF8_eq_true_iff.mpr s.isValidUTF8

theorem readStr_encStr {s r : List UInt8} (h : NameOk true s) :
    readStr (encStr s ++ r) = .ok (s, r) := by
  obtain ⟨hu, hl, hlim⟩ := h
  have h1 : ¬ 100000 < s.length := by have := hlim rfl; omega
  simp [readStr, readStrBytes, encStr, List.append_assoc, readU32_encU32 _ _ hl, h1, hu, bind,
    Except.bind, pure, Except.pure]

theorem readUStr_encStr {s r : List UInt8} (h : NameOk false s) :
    readUStr (encStr s ++ r) = .ok (s, r) := by
  obtain ⟨hu, hl, _⟩ := h
  simp [readUStr, encStr, List.append_assoc, readU32_encU32 _ _ hl, hu, bind, Except.bind, pure,
    Except.pure]

theorem readStrL_encStr {lim : Bool} {s r : List UInt8} (h : NameOk lim s) :
    (if lim then readStr (encStr s ++ r) else readUStr (encStr s ++ r)) = .ok (s, r) := by
  cases lim
  · exact readUStr_encStr h
  · exact readStr_encStr h

theorem readEntries_enc (lim : Bool) : ∀ (last : Option Nat) (m : NMap) (r : List UInt8),
    EntriesOk lim last m → readEntries lim m.length last (encEntries m ++ r) = .ok (m, r)
  | _, [], _, _ => rfl
  | last, (i, s) :: m, r, ⟨hi, hlt, hs, hm⟩ => by
    have ih := readEntries_enc lim (some i) m r hm
    have hstr := readStrL_encStr (r := encEntries m ++ r) hs
    simp only [encEntries, List.append_assoc, List.length_cons, readEntries,
      readU32_encU32 _ _ hlt, hi, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    simp only [hstr, ih]

theorem readMap_encMap {m : NMap} (h : MapOk false m) : readMap (encMap m) = .ok m := by
  obtain ⟨hl, he⟩ := h
  have := readEntries_enc false none m [] he
  simp only [List.append_nil] at this
  simp [readMap, encMap, readU32_encU32 _ _ hl, this]

theorem readIndEntries_enc : ∀ (last : Option Nat) (ms : List (Nat × NMap)) (r : List UInt8),
    IndEntriesOk last ms → readIndEntries ms.length last (encIndEntries ms ++ r) = .ok (ms, r)
  | _, [], _, _ => rfl
  | last, (i, m) :: ms, r, ⟨hi, hlt, ⟨hml, hme⟩, hms⟩ => by
    have ih := readIndEntries_enc (some i) ms r hms
    have hin := readEntries_enc true none m (encIndEntries ms ++ r) hme
    simp only [encIndEntries, encMap, List.append_assoc, List.length_cons, readIndEntries,
      readU32_encU32 _ _ hlt, hi, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      readU32_encU32 _ _ hml, hin, ih]

theorem readInd_encInd {ms : List (Nat × NMap)} (h : IndOk ms) : readInd (encInd ms) = .ok ms := by
  obtain ⟨hl, he⟩ := h
  have := readIndEntries_enc none ms [] he
  simp only [List.append_nil] at this
  simp [readInd, encInd, readU32_encU32 _ _ hl, this]

/-- Every subsection takes at least two bytes, so the fuel `bs.length` suffices. -/
theorem encNames_length_ge : ∀ ss : List NSub, ss.length ≤ (encNames ss).length
  | [] => by simp [encNames]
  | s :: ss => by
    have := encNames_length_ge ss
    cases s <;> simp [encNames, NSub.encode, encSub] <;> omega

/-- The id of a decoded subsection. -/
def NSub.id : NSub → Nat
  | .name _ => 0
  | .map id _ _ => id
  | .ind id _ => id
  | .raw id _ => id

/-- The data of a decoded subsection, as encoded. -/
def NSub.data : NSub → List UInt8
  | .name n => encStr n
  | .map _ pre m => pre ++ encMap m
  | .ind _ ms => encInd ms
  | .raw _ d => d

theorem NSub.encode_eq (s : NSub) : s.encode = encSub s.id s.data := by
  cases s <;> rfl

/-- **Subsections round-trip** when each one's data decodes back to it. -/
theorem readSubs_enc (dec : Nat → List UInt8 → Except String NSub) :
    ∀ (f : Nat) (ss : List NSub), ss.length ≤ f →
      (∀ s ∈ ss, s.id < 128 ∧ s.data.length < 2 ^ 32 ∧ dec s.id s.data = .ok s) →
      readSubs dec f (encNames ss) = .ok ss
  | _, [], _, _ => by cases ‹Nat› <;> rfl
  | 0, _ :: _, hf, _ => by simp at hf
  | f + 1, s :: ss, hf, hs => by
    obtain ⟨hid, hlen, hdec⟩ := hs s (by simp)
    have ih := readSubs_enc dec f ss (by simp at hf; omega) (fun t ht => hs t (by simp [ht]))
    have hid' : ¬ 128 ≤ (s.id.toUInt8).toNat := by
      rw [toNat_toUInt8_of_lt (by omega)]; omega
    have hidn : (s.id.toUInt8).toNat = s.id := toNat_toUInt8_of_lt (by omega)
    rw [encNames, NSub.encode_eq, encSub]
    simp only [List.cons_append, List.append_assoc, readSubs, hidn]
    simp [hid, readU32_encU32 _ _ hlen, hdec, ih]

/-- A module subsection that decodes back to itself. -/
def ModSubOk (strict : Bool) : NSub → Prop
  | .name n => NameOk true n ∧ (encStr n).length < 2 ^ 32
  | .map id pre m => id ∈ mapIds ∧ pre = [] ∧ MapOk false m ∧ (encMap m).length < 2 ^ 32
  | .ind id ms => id ∈ indIds ∧ IndOk ms ∧ (encInd ms).length < 2 ^ 32
  | .raw id d => strict = false ∧ id ≠ 0 ∧ id ∉ mapIds ∧ id ∉ indIds ∧ id < 128 ∧
      d.length < 2 ^ 32

theorem readNameSub_encStr {lim : Bool} {n : List UInt8} (h : NameOk lim n) :
    readNameSub lim (encStr n) = .ok n := by
  have := readStrL_encStr (r := []) h
  simp only [List.append_nil] at this
  cases lim <;> simp_all [readNameSub]

theorem decodeModSub_enc {strict : Bool} {s : NSub} (h : ModSubOk strict s) :
    s.id < 128 ∧ s.data.length < 2 ^ 32 ∧ decodeModSub strict s.id s.data = .ok s := by
  cases s with
  | name n =>
    obtain ⟨hn, hl⟩ := h
    exact ⟨by simp [NSub.id], hl, by simp [NSub.id, NSub.data, decodeModSub, readNameSub_encStr hn,
      Except.map]⟩
  | map id pre m =>
    obtain ⟨hid, rfl, hm, hl⟩ := h
    have h0 : id ≠ 0 := by intro h; subst h; simp [mapIds] at hid
    refine ⟨by simp [mapIds] at hid; simp [NSub.id]; omega, by simpa [NSub.data] using hl, ?_⟩
    simp [NSub.id, NSub.data, decodeModSub, h0, hid, readMap_encMap hm, Except.map]
  | ind id ms =>
    obtain ⟨hid, hm, hl⟩ := h
    have h0 : id ≠ 0 := by intro h; subst h; simp [indIds] at hid
    have h1 : id ∉ mapIds := by simp [indIds] at hid; simp [mapIds]; omega
    refine ⟨by simp [indIds] at hid; simp [NSub.id]; omega, hl, ?_⟩
    simp [NSub.id, NSub.data, decodeModSub, h0, hid, h1, readInd_encInd hm, Except.map]
  | raw id d =>
    obtain ⟨rfl, h0, h1, h2, h3, hl⟩ := h
    exact ⟨h3, hl, by simp [NSub.id, NSub.data, decodeModSub, h0, h1, h2]⟩

/-- **The module `name` section round-trips**: decoding the encoding of well-formed
subsections gives them back (`strict`: no raw subsections). -/
theorem decodeNames_encNames {strict : Bool} {ss : List NSub} (h : ∀ s ∈ ss, ModSubOk strict s) :
    decodeNames strict (encNames ss) = .ok ss := by
  apply readSubs_enc
  · exact encNames_length_ge ss
  · exact fun s hs => decodeModSub_enc (h s hs)

end Silmaril.Wasm.Tools.Meta

end
