module

public import Silmaril.Net.Hpack.Table.Defs

@[expose] public section

/-!
# QPACK dynamic table (RFC 9204 §3.2)

"The dynamic table consists of a list of field lines maintained in first-in, first-out order.
A QPACK encoder and decoder share a dynamic table that is initially empty" (§3.2). Duplicate
entries are allowed (§3.2).

**Size (§3.2.1).** As in HPACK: `|name| + |value| + 32` per entry (`Hpack.Entry.size`), summed
over the table (`Hpack.tableSize`).

**Capacity and eviction (§3.2.2, §3.2.3).** "The initial capacity of the dynamic table is
zero." "Before a new entry is added to the dynamic table, entries are evicted from the end of
the dynamic table until the size of the dynamic table is less than or equal to (table capacity
- size of new entry)." "It is an error if the encoder attempts to add an entry that is larger
than the dynamic table capacity" (unlike HPACK, which empties the table): `insert` returns
`none`, which the decoder reports as `QPACK_ENCODER_STREAM_ERROR`. Reducing the capacity evicts
from the end until the table fits; the capacity may not exceed the maximum table capacity
(`SETTINGS_QPACK_MAX_TABLE_CAPACITY` in HTTP/3): `setCapacity` returns `none` above it.
Eviction from the end until the table fits is HPACK's `fitPrefix` (the longest fitting prefix of
the newest-first entry list).

**Indexing (§3.2.4–§3.2.6).** Unlike HPACK, entries are addressed by an **absolute index**,
"fixed for the lifetime of that entry. The first entry inserted has an absolute index of 0;
indices increase by one with each insertion." The table therefore records the **insert count**
`n` (all insertions so far); with the entries newest first, position `k` holds absolute index
`n - 1 - k`, and the `d = n - |entries|` oldest entries have been dropped.

* In encoder instructions, "a relative index of 0 refers to the most recently inserted value"
  (§3.2.5): relative index `r` is absolute `n - 1 - r` (`encoderRelToAbs`).
* In field line representations, relative indices are taken from the **Base**: "a relative
  index of 0 refers to the entry with absolute index equal to Base - 1" (§3.2.5,
  `relToAbs`), and post-Base index `p` is absolute `Base + p` (§3.2.6, `postBaseToAbs`).
-/

namespace Silmaril.Net.Qpack

open Silmaril.Net.Hpack (Entry Entry.ofStrings tableSize fitPrefix)

/-- A QPACK dynamic table (§3.2): entries newest first, the insert count (§3.2.4), the current
capacity (§3.2.2) and the maximum table capacity set by the decoder (§3.2.3). -/
structure DynTable where
  entries : List Entry
  insertCount : Nat
  capacity : Nat
  maxCapacity : Nat
  deriving DecidableEq, Repr

namespace DynTable

/-- The initial table: empty, no insertions, capacity zero (§3.2.2), maximum `m` (§3.2.3). -/
def empty (m : Nat) : DynTable := ⟨[], 0, 0, m⟩

/-- The invariant: the size is within the capacity, the capacity within the maximum, and there
are no more entries than insertions. -/
def Valid (t : DynTable) : Prop :=
  tableSize t.entries ≤ t.capacity ∧ t.capacity ≤ t.maxCapacity ∧ t.entries.length ≤ t.insertCount

/-- The size of the table (§3.2.1). -/
def size (t : DynTable) : Nat := tableSize t.entries

/-- The number of dropped (evicted) entries, `d` of Figure 2. -/
def dropped (t : DynTable) : Nat := t.insertCount - t.entries.length

/-- `MaxEntries = floor(MaxTableCapacity / 32)` (§4.5.1.1): the most entries the table can
hold, since every entry has size at least 32. -/
def maxEntries (t : DynTable) : Nat := t.maxCapacity / 32

/-- The entry with absolute index `a` (§3.2.4), if it was inserted and not evicted. -/
def lookupAbs (t : DynTable) (a : Nat) : Option Entry :=
  if a < t.insertCount then t.entries[t.insertCount - 1 - a]? else none

/-- Encoder-stream relative index to absolute index (§3.2.5): `n - 1 - r`. -/
def encoderRelToAbs (t : DynTable) (r : Nat) : Option Nat :=
  if r < t.insertCount then some (t.insertCount - 1 - r) else none

/-- The entry with encoder-stream relative index `r` (§3.2.5). -/
def lookupRel (t : DynTable) (r : Nat) : Option Entry :=
  (t.encoderRelToAbs r).bind t.lookupAbs

/-- Insert an entry (§3.2.2): evict from the end until the size is at most
`capacity - size e`, then add `e` with absolute index `insertCount`. `none` (an encoder stream
error) if the entry is larger than the capacity. -/
def insert (t : DynTable) (e : Entry) : Option DynTable :=
  if e.size ≤ t.capacity then
    some { t with entries := e :: fitPrefix (t.capacity - e.size) t.entries,
                  insertCount := t.insertCount + 1 }
  else none

/-- Set the capacity (§3.2.2, §4.3.1): evict from the end until the table fits. `none` (an
encoder stream error) above the maximum table capacity (§3.2.3). -/
def setCapacity (t : DynTable) (c : Nat) : Option DynTable :=
  if c ≤ t.maxCapacity then some { t with entries := fitPrefix c t.entries, capacity := c }
  else none

end DynTable

/-! ## Indices relative to a Base (§3.2.5, §3.2.6) -/

/-- Field-line relative index to absolute index (§3.2.5): `Base - 1 - r`, defined for
`r < Base`. -/
def relToAbs (base r : Nat) : Option Nat := if r < base then some (base - 1 - r) else none

/-- Absolute index to field-line relative index (§3.2.5), for `a < Base`. -/
def absToRel (base a : Nat) : Nat := base - 1 - a

/-- Post-Base index to absolute index (§3.2.6): `Base + p`. -/
def postBaseToAbs (base p : Nat) : Nat := base + p

/-- Absolute index to post-Base index (§3.2.6), for `Base ≤ a`. -/
def absToPostBase (base a : Nat) : Nat := a - base

end Silmaril.Net.Qpack
