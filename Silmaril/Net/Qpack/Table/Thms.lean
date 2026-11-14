module

public import Silmaril.Net.Qpack.Table.Defs
import Silmaril.Proofs.Net.Qpack.Table

@[expose] public section

/-!
# QPACK dynamic table: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Qpack/Table.lean`), RFC 9204 §3.2:

* `insert_valid`, `setCapacity_valid`: the invariant `DynTable.Valid` (size ≤ capacity ≤
  maximum capacity, entries ≤ insertions) holds after every accepted insertion and capacity
  change (§3.2.2, §3.2.3); `empty_valid`: initially;
* `insert_eq_none_iff`: an insertion fails exactly when the entry is larger than the capacity
  (§3.2.2, an encoder stream error);
* `insert_insertCount`, `insert_lookup_new`: an insertion takes the next absolute index
  (§3.2.4);
* `insert_lookup_old`, `setCapacity_lookup`: eviction never moves an entry: an entry that
  survives keeps its absolute index (§3.2.4);
* `lookupAbs_isSome_iff`, `insert_dropped`, `setCapacity_dropped`: the live entries are exactly
  the absolute indices `[dropped, insertCount)`, and eviction only advances `dropped`, never
  past the previous insert count (FIFO, §3.2);
* `lookupRel_eq`: encoder-stream relative index `r` is position `r` of the newest-first list
  (§3.2.5);
* `relToAbs_absToRel`, `absToRel_relToAbs`, `postBaseToAbs_absToPostBase`: the Base-relative
  and post-Base index conversions are mutually inverse on their domains (§3.2.5, §3.2.6);
* `length_le_maxEntries`: a valid table holds at most `MaxEntries = maxCapacity / 32` entries
  (§4.5.1.1).
-/

namespace Silmaril.Net.Qpack

open Silmaril.Net.Hpack (Entry Entry.ofStrings tableSize fitPrefix)

namespace DynTable

theorem empty_valid (m : Nat) : (empty m).Valid :=
  ⟨Nat.le_refl _, Nat.zero_le _, Nat.le_refl _⟩

theorem insert_valid {t t' : DynTable} {e : Entry} (ht : t.Valid) (h : t.insert e = some t') :
    t'.Valid :=
  Silmaril.Proofs.Net.Qpack.DynTable.insert_valid ht h

theorem setCapacity_valid {t t' : DynTable} {c : Nat} (ht : t.Valid)
    (h : t.setCapacity c = some t') : t'.Valid :=
  Silmaril.Proofs.Net.Qpack.DynTable.setCapacity_valid ht h

theorem insert_eq_none_iff {t : DynTable} {e : Entry} : t.insert e = none ↔ t.capacity < e.size :=
  Silmaril.Proofs.Net.Qpack.DynTable.insert_eq_none_iff

theorem insert_insertCount {t t' : DynTable} {e : Entry} (h : t.insert e = some t') :
    t'.insertCount = t.insertCount + 1 :=
  Silmaril.Proofs.Net.Qpack.DynTable.insert_insertCount h

theorem insert_maxCapacity {t t' : DynTable} {e : Entry} (h : t.insert e = some t') :
    t'.maxCapacity = t.maxCapacity :=
  Silmaril.Proofs.Net.Qpack.DynTable.insert_maxCapacity h

theorem insert_lookup_new {t t' : DynTable} {e : Entry} (h : t.insert e = some t') :
    t'.lookupAbs t.insertCount = some e :=
  Silmaril.Proofs.Net.Qpack.DynTable.insert_lookup_new h

theorem insert_lookup_old {t t' : DynTable} {e : Entry} (h : t.insert e = some t') {a : Nat}
    (ha : a < t.insertCount) {x : Entry} (hx : t'.lookupAbs a = some x) :
    t.lookupAbs a = some x :=
  Silmaril.Proofs.Net.Qpack.DynTable.insert_lookup_old h ha hx

theorem setCapacity_lookup {t t' : DynTable} {c : Nat} (h : t.setCapacity c = some t') {a : Nat}
    {x : Entry} (hx : t'.lookupAbs a = some x) : t.lookupAbs a = some x :=
  Silmaril.Proofs.Net.Qpack.DynTable.setCapacity_lookup h hx

theorem setCapacity_insertCount {t t' : DynTable} {c : Nat} (h : t.setCapacity c = some t') :
    t'.insertCount = t.insertCount := by
  obtain ⟨-, rfl⟩ := Silmaril.Proofs.Net.Qpack.DynTable.setCapacity_eq h; rfl

theorem setCapacity_maxCapacity {t t' : DynTable} {c : Nat} (h : t.setCapacity c = some t') :
    t'.maxCapacity = t.maxCapacity := by
  obtain ⟨-, rfl⟩ := Silmaril.Proofs.Net.Qpack.DynTable.setCapacity_eq h; rfl

theorem lookupAbs_isSome_iff (t : DynTable) (a : Nat) :
    (t.lookupAbs a).isSome ↔ t.dropped ≤ a ∧ a < t.insertCount :=
  Silmaril.Proofs.Net.Qpack.DynTable.lookupAbs_isSome_iff t a

theorem insert_dropped {t t' : DynTable} {e : Entry} (h : t.insert e = some t') :
    t.dropped ≤ t'.dropped ∧ t'.dropped ≤ t.insertCount :=
  Silmaril.Proofs.Net.Qpack.DynTable.insert_dropped h

theorem setCapacity_dropped {t t' : DynTable} {c : Nat} (h : t.setCapacity c = some t') :
    t.dropped ≤ t'.dropped ∧ t'.dropped ≤ t.insertCount :=
  Silmaril.Proofs.Net.Qpack.DynTable.setCapacity_dropped h

theorem lookupRel_eq {t : DynTable} (ht : t.entries.length ≤ t.insertCount) (r : Nat) :
    t.lookupRel r = t.entries[r]? :=
  Silmaril.Proofs.Net.Qpack.DynTable.lookupRel_eq ht r

theorem length_le_maxEntries {t : DynTable} (ht : t.Valid) : t.entries.length ≤ t.maxEntries :=
  Silmaril.Proofs.Net.Qpack.DynTable.length_le_maxEntries ht

end DynTable

theorem relToAbs_absToRel {base a : Nat} (h : a < base) :
    relToAbs base (absToRel base a) = some a :=
  Silmaril.Proofs.Net.Qpack.relToAbs_absToRel h

theorem absToRel_relToAbs {base r a : Nat} (h : relToAbs base r = some a) :
    a < base ∧ absToRel base a = r :=
  Silmaril.Proofs.Net.Qpack.absToRel_relToAbs h

theorem postBaseToAbs_absToPostBase {base a : Nat} (h : base ≤ a) :
    postBaseToAbs base (absToPostBase base a) = a := by
  simp only [postBaseToAbs, absToPostBase]; omega

theorem absToPostBase_postBaseToAbs (base p : Nat) :
    absToPostBase base (postBaseToAbs base p) = p := by
  simp only [postBaseToAbs, absToPostBase]; omega

/-! RFC 9204 §3.2 and §4.5.1.2, checked by evaluation. -/

/-- §4.5.1.2: with Base 6, relative index 1 is the fifth entry added (absolute 4) and post-Base
index 1 the eighth (absolute 7). -/
example : relToAbs 6 1 = some 4 ∧ postBaseToAbs 6 1 = 7 := by decide
/-- §4.5.1.1: a 100-byte maximum table holds at most 3 entries. -/
example : (DynTable.empty 100).maxEntries = 3 := by decide
/-- §3.2.2: an insert into the initial table (capacity zero) fails. -/
example : (DynTable.empty 4096).insert (Entry.ofStrings "a" "b") = none := by decide +kernel

end Silmaril.Net.Qpack
