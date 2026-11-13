module

public import Silmaril.Net.Hpack.Table.Defs
import Silmaril.Proofs.Net.Hpack.Table

@[expose] public section

/-!
# HPACK indexing tables: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Hpack/Table.lean`), RFC 7541 §4:

* `tableSize_fitPrefix`, `fitPrefix_prefix`, `fitPrefix_of_le`, `fitPrefix_maximal`: eviction
  keeps the longest prefix (newest entries) that fits, and evicts nothing when the table
  already fits;
* `insert_valid`, `setMaxSize_valid`: the invariant `DynTable.Valid` (size within the maximum,
  maximum within the limit) holds after every insertion and every accepted size update, so a
  peer cannot make a decoder hold more than its advertised limit (the memory bound of §7.3);
* `insert_newest`: a fitting inserted entry is at index 62 (§2.3.3); `insert_empty`: an
  oversize entry empties the table (§4.4); `insert_shift`: older surviving entries move up by
  one index.
-/

namespace Silmaril.Net.Hpack

theorem tableSize_fitPrefix (cap : Nat) (es : List Entry) : tableSize (fitPrefix cap es) ≤ cap :=
  Silmaril.Proofs.Net.Hpack.tableSize_fitPrefix cap es

theorem fitPrefix_prefix (cap : Nat) (es : List Entry) : fitPrefix cap es <+: es :=
  Silmaril.Proofs.Net.Hpack.fitPrefix_prefix cap es

theorem fitPrefix_of_le (cap : Nat) (es : List Entry) (h : tableSize es ≤ cap) :
    fitPrefix cap es = es :=
  Silmaril.Proofs.Net.Hpack.fitPrefix_of_le cap es h

theorem fitPrefix_maximal (cap : Nat) (es : List Entry) (e : Entry)
    (h : fitPrefix cap es ++ [e] <+: es) : cap < tableSize (fitPrefix cap es ++ [e]) :=
  Silmaril.Proofs.Net.Hpack.fitPrefix_maximal cap es e h

namespace DynTable

theorem empty_valid (n : Nat) : (empty n).Valid := ⟨Nat.zero_le _, Nat.le_refl _⟩

theorem insert_valid {t : DynTable} (ht : t.Valid) (e : Entry) : (t.insert e).Valid :=
  Silmaril.Proofs.Net.Hpack.insert_valid ht e

theorem setMaxSize_valid {t t' : DynTable} {m : Nat} (h : t.setMaxSize m = some t') : t'.Valid :=
  Silmaril.Proofs.Net.Hpack.setMaxSize_valid h

theorem insert_newest {t : DynTable} {e : Entry} (h : e.size ≤ t.maxSize) :
    (t.insert e).lookup (staticLength + 1) = some e :=
  Silmaril.Proofs.Net.Hpack.insert_newest h

theorem insert_empty {t : DynTable} {e : Entry} (h : t.maxSize < e.size) :
    (t.insert e).entries = [] :=
  Silmaril.Proofs.Net.Hpack.insert_empty h

theorem insert_shift {t : DynTable} {e : Entry} (i : Nat) (x : Entry)
    (hi : (t.insert e).lookup (staticLength + 2 + i) = some x) :
    t.lookup (staticLength + 1 + i) = some x :=
  Silmaril.Proofs.Net.Hpack.insert_shift i x hi

end DynTable

/-! Appendix A and §4.1, checked by evaluation. -/

example : staticTable.length = staticLength := by decide +kernel
example : (DynTable.empty 4096).lookup 2 = some (Entry.ofStrings ":method" "GET") := by decide +kernel
example : (DynTable.empty 4096).lookup 61 = some (Entry.ofStrings "www-authenticate" "") := by
  decide +kernel
example : (DynTable.empty 4096).lookup 0 = none := by decide +kernel
example : (DynTable.empty 4096).lookup 62 = none := by decide +kernel
/-- RFC 7541 C.3.1: `custom-key: custom-header` has size 55. -/
example : (Entry.ofStrings "custom-key" "custom-header").size = 55 := by decide +kernel

end Silmaril.Net.Hpack
