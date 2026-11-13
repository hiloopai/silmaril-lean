module

public import Silmaril.Data.BytesTrie.Defs
import Silmaril.Proofs.Data.BytesTrie.Basic

/-!
# Byte tries: theorems and the canonical map type

* `find?_alter`: the pointwise specification of `alter` (hence `insert` and
  `erase`) on sorted tries (`WF`); raw tries need no further invariant.
* `canon_alter`: `alter` preserves canonical form.
* `eq_of_find?_eq`: **canonical tries with the same lookups are equal**, so
  canonical tries are in bijection with finitely supported functions
  (`exists_of_finite` gives surjectivity).
* `BytesMap`: the subtype of canonical tries, with extensional equality
  (`BytesMap.ext_iff`) and structural, kernel-decidable `DecidableEq`.
-/

@[expose] public section

universe u

namespace Silmaril.Data.BytesTrie

variable {α : Type u}

theorem Trie.beq_iff [DecidableEq α] {s t : Trie α} : s.beq t = true ↔ s = t :=
  Proofs.Data.BytesTrie.Trie.beq_iff

/-- Structural equality of tries, through `Trie.beq` (fast in the kernel). -/
instance Trie.instDecidableEq [DecidableEq α] : DecidableEq (Trie α) := fun _ _ =>
  decidable_of_iff _ Trie.beq_iff

instance instDecidableEq [DecidableEq α] : DecidableEq (BytesTrie α) := fun s t =>
  if h : s.root = t.root ∧ s.kids = t.kids then isTrue (by cases s; cases t; simp_all)
  else isFalse fun e => h (e ▸ ⟨rfl, rfl⟩)

theorem canonB_iff {t : BytesTrie α} : t.canonB = true ↔ t.Canon :=
  Proofs.Data.BytesTrie.Trie.canonB_iff

instance (t : BytesTrie α) : Decidable t.Canon := decidable_of_iff _ canonB_iff

theorem Canon.wf {t : BytesTrie α} (h : t.Canon) : t.WF := Proofs.Data.BytesTrie.Canon.wf h

/-- **The `alter` specification**: only the key `ks` changes, to `f` of its old value. -/
theorem find?_alter {t : BytesTrie α} (h : t.WF) (ks : List UInt8) (f : Option α → Option α)
    (js : List UInt8) :
    (t.alter ks f).find? js = if js = ks then f (t.find? ks) else t.find? js :=
  Proofs.Data.BytesTrie.find?_alter h ks f js

theorem wf_alter {t : BytesTrie α} (h : t.WF) (ks : List UInt8) (f : Option α → Option α) :
    (t.alter ks f).WF :=
  Proofs.Data.BytesTrie.wf_alter h ks f

theorem canon_alter {t : BytesTrie α} (h : t.Canon) (ks : List UInt8) (f : Option α → Option α) :
    (t.alter ks f).Canon :=
  Proofs.Data.BytesTrie.canon_alter h ks f

theorem canon_empty : (empty : BytesTrie α).Canon := trivial

theorem find?_empty (ks : List UInt8) : (empty : BytesTrie α).find? ks = none :=
  Proofs.Data.BytesTrie.find?_empty ks

/-- **Uniqueness of canonical forms.** Raw tries are not unique (see `Equiv`);
canonical ones are. -/
theorem eq_of_find?_eq {s t : BytesTrie α} (hs : s.Canon) (ht : t.Canon)
    (h : ∀ ks, s.find? ks = t.find? ks) : s = t :=
  Proofs.Data.BytesTrie.eq_of_find?_eq hs ht h

theorem find?_alterAll {t : BytesTrie α} (h : t.WF) (keys : List (List UInt8))
    (f : List UInt8 → Option α) (js : List UInt8) :
    (t.alterAll keys f).find? js = if js ∈ keys then f js else t.find? js :=
  Proofs.Data.BytesTrie.find?_alterAll h keys f js

theorem canon_alterAll {t : BytesTrie α} (h : t.Canon) (keys : List (List UInt8))
    (f : List UInt8 → Option α) : (t.alterAll keys f).Canon :=
  Proofs.Data.BytesTrie.canon_alterAll h keys f

/-- Every finitely supported function is the lookup of a canonical trie. -/
theorem exists_of_finite (f : List UInt8 → Option α) (keys : List (List UInt8))
    (hf : ∀ ks, ks ∉ keys → f ks = none) :
    ∃ t : BytesTrie α, t.Canon ∧ ∀ ks, t.find? ks = f ks :=
  Proofs.Data.BytesTrie.exists_of_finite f keys hf

theorem find?_insert {t : BytesTrie α} (h : t.WF) (ks : List UInt8) (a : α) (js : List UInt8) :
    (t.insert ks a).find? js = if js = ks then some a else t.find? js :=
  find?_alter h ks _ js

theorem find?_erase {t : BytesTrie α} (h : t.WF) (ks : List UInt8) (js : List UInt8) :
    (t.erase ks).find? js = if js = ks then none else t.find? js :=
  find?_alter h ks _ js

end Silmaril.Data.BytesTrie

namespace Silmaril.Data.BytesMap

variable {α : Type u}

/-- The empty map. -/
def empty : BytesMap α := ⟨.empty, BytesTrie.canon_empty⟩

/-- The value at a key. -/
def find? (m : BytesMap α) (ks : List UInt8) : Option α := m.1.find? ks

/-- Replace the value `x` at `ks` by `f x`. -/
def alter (m : BytesMap α) (ks : List UInt8) (f : Option α → Option α) : BytesMap α :=
  ⟨m.1.alter ks f, BytesTrie.canon_alter m.2 ks f⟩

/-- Bind `ks` to `a`. -/
def insert (m : BytesMap α) (ks : List UInt8) (a : α) : BytesMap α := m.alter ks fun _ => some a

/-- Remove `ks`. -/
def erase (m : BytesMap α) (ks : List UInt8) : BytesMap α := m.alter ks fun _ => none

/-- **Certificate validation**: accept a raw trie (for example a literal term
produced outside the kernel) after the kernel evaluates `canonB`. -/
def ofCanonB (t : BytesTrie α) (h : t.canonB = true := by decide +kernel) : BytesMap α :=
  ⟨t, BytesTrie.canonB_iff.mp h⟩

/-- Check a raw trie: `some` exactly when it is canonical. -/
def ofRaw? (t : BytesTrie α) : Option (BytesMap α) :=
  if h : t.canonB = true then some (ofCanonB t h) else none

/-- Insert a list of bindings; later bindings win. -/
def ofList (l : List (List UInt8 × α)) : BytesMap α :=
  l.foldl (fun m p => m.insert p.1 p.2) empty

/-- All entries, in lexicographic key order. -/
def toList (m : BytesMap α) : List (List UInt8 × α) := m.1.toList

/-- The number of entries. -/
def size (m : BytesMap α) : Nat := m.1.size

instance [DecidableEq α] : DecidableEq (BytesMap α) := fun a b =>
  if h : a.1 = b.1 then isTrue (Subtype.ext h) else isFalse fun e => h (congrArg Subtype.val e)

theorem find?_empty (ks : List UInt8) : (empty : BytesMap α).find? ks = none :=
  BytesTrie.find?_empty ks

theorem find?_alter (m : BytesMap α) (ks : List UInt8) (f : Option α → Option α)
    (js : List UInt8) :
    (m.alter ks f).find? js = if js = ks then f (m.find? ks) else m.find? js :=
  BytesTrie.find?_alter m.2.wf ks f js

theorem find?_insert (m : BytesMap α) (ks : List UInt8) (a : α) (js : List UInt8) :
    (m.insert ks a).find? js = if js = ks then some a else m.find? js :=
  find?_alter m ks _ js

theorem find?_erase (m : BytesMap α) (ks : List UInt8) (js : List UInt8) :
    (m.erase ks).find? js = if js = ks then none else m.find? js :=
  find?_alter m ks _ js

/-- **Extensionality**: maps are equal exactly when their lookups agree. -/
theorem ext_iff {m m' : BytesMap α} : m = m' ↔ ∀ ks, m.find? ks = m'.find? ks :=
  ⟨fun h _ => h ▸ rfl, fun h => Subtype.ext (BytesTrie.eq_of_find?_eq m.2 m'.2 h)⟩

theorem ext {m m' : BytesMap α} (h : ∀ ks, m.find? ks = m'.find? ks) : m = m' := ext_iff.mpr h

/-- **Completeness**: every finitely supported function is a map. With
`ext_iff`, `find?` is a bijection from `BytesMap α` onto the finitely
supported functions `List UInt8 → Option α`. -/
theorem exists_of_finite (f : List UInt8 → Option α) (keys : List (List UInt8))
    (hf : ∀ ks, ks ∉ keys → f ks = none) : ∃ m : BytesMap α, ∀ ks, m.find? ks = f ks :=
  let ⟨t, ht, h⟩ := BytesTrie.exists_of_finite f keys hf
  ⟨⟨t, ht⟩, h⟩

end Silmaril.Data.BytesMap
