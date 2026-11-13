module

@[expose] public section

/-!
# HPACK indexing tables (RFC 7541 §2.3, §4, Appendix A)

HPACK associates header fields with indices in two tables (§2.3):

* the **static table** (§2.3.1, Appendix A): 61 predefined entries, indices `1..61`;
* the **dynamic table** (§2.3.2): a FIFO of entries the encoder chose to index; "the first and
  newest entry is at the lowest index, and the oldest entry … at the highest index". Its
  entries follow the static ones in a single **index address space** (§2.3.3): index
  `62` is the newest dynamic entry.

**Size (§4.1).** "The size of an entry is the sum of its name's length in octets …, its value's
length in octets, and 32"; the size of the table is the sum of its entries' sizes.

**Eviction (§4.3, §4.4).** On a change of maximum size, or before inserting, entries are evicted
from the end until the table fits. "If the size of the new entry is less than or equal to the
maximum size, that entry is added to the table. It is not an error to attempt to add an entry
that is larger than the maximum size; an attempt to add an entry larger than the maximum size
causes the table to be emptied of all existing entries and results in an empty table."

Here the dynamic table is its list of entries, newest first, and its maximum size. Evicting
from the end until the table fits is `fitPrefix`, the longest prefix whose size fits: since
every entry has positive size, the two agree. `insert` is `fitPrefix` applied to the new entry
consed on the front, which also gives the empty table for an oversize entry.

**Limit (§4.2).** The decoder's maximum is bounded by a limit fixed by the protocol (in HTTP/2,
`SETTINGS_HEADER_TABLE_SIZE`); `setMaxSize` refuses a value above the limit (a decoding error,
§6.3).
-/

namespace Silmaril.Net.Hpack

/-- A header field: a name and a value, as octets. -/
structure Entry where
  name : List UInt8
  value : List UInt8
  deriving DecidableEq, Repr, Inhabited

/-- The size of an entry (§4.1): `|name| + |value| + 32`. -/
def Entry.size (e : Entry) : Nat := e.name.length + e.value.length + 32

/-- The size of a list of entries (§4.1). -/
def tableSize (es : List Entry) : Nat := (es.map Entry.size).sum

/-- The octets of an ASCII string. -/
def ascii (s : String) : List UInt8 := s.toList.map (fun c => c.toNat.toUInt8)

/-- An entry from ASCII strings. -/
def Entry.ofStrings (n v : String) : Entry := ⟨ascii n, ascii v⟩

/-- The static table (Appendix A), index `i + 1` at position `i`. -/
def staticTable : List Entry :=
  [(":authority", ""), (":method", "GET"), (":method", "POST"), (":path", "/"),
   (":path", "/index.html"), (":scheme", "http"), (":scheme", "https"), (":status", "200"),
   (":status", "204"), (":status", "206"), (":status", "304"), (":status", "400"),
   (":status", "404"), (":status", "500"), ("accept-charset", ""),
   ("accept-encoding", "gzip, deflate"), ("accept-language", ""), ("accept-ranges", ""),
   ("accept", ""), ("access-control-allow-origin", ""), ("age", ""), ("allow", ""),
   ("authorization", ""), ("cache-control", ""), ("content-disposition", ""),
   ("content-encoding", ""), ("content-language", ""), ("content-length", ""),
   ("content-location", ""), ("content-range", ""), ("content-type", ""), ("cookie", ""),
   ("date", ""), ("etag", ""), ("expect", ""), ("expires", ""), ("from", ""), ("host", ""),
   ("if-match", ""), ("if-modified-since", ""), ("if-none-match", ""), ("if-range", ""),
   ("if-unmodified-since", ""), ("last-modified", ""), ("link", ""), ("location", ""),
   ("max-forwards", ""), ("proxy-authenticate", ""), ("proxy-authorization", ""),
   ("range", ""), ("referer", ""), ("refresh", ""), ("retry-after", ""), ("server", ""),
   ("set-cookie", ""), ("strict-transport-security", ""), ("transfer-encoding", ""),
   ("user-agent", ""), ("vary", ""), ("via", ""), ("www-authenticate", "")].map
    fun (n, v) => Entry.ofStrings n v

/-- The number of static entries (61). -/
def staticLength : Nat := 61

/-- The longest prefix of `es` (newest first) whose size is at most `cap`: the table left by
evicting the oldest entries until it fits (§4.3, §4.4). -/
def fitPrefix (cap : Nat) : List Entry → List Entry
  | [] => []
  | e :: es => if e.size ≤ cap then e :: fitPrefix (cap - e.size) es else []

/-- A decoder's dynamic table (§2.3.2): its entries, newest first, its maximum size (§4.2) and
the protocol limit on that maximum (§4.2; `SETTINGS_HEADER_TABLE_SIZE` in HTTP/2). -/
structure DynTable where
  entries : List Entry
  maxSize : Nat
  limit : Nat
  deriving DecidableEq, Repr

namespace DynTable

/-- The empty table with maximum size and limit `n` (HTTP/2's default is 4096, RFC 9113 §6.5.2). -/
def empty (n : Nat) : DynTable := ⟨[], n, n⟩

/-- The invariant: the table fits its maximum, which is within the limit. -/
def Valid (t : DynTable) : Prop := tableSize t.entries ≤ t.maxSize ∧ t.maxSize ≤ t.limit

/-- Insert an entry (§4.4): the new entry first, then evict until the table fits. -/
def insert (t : DynTable) (e : Entry) : DynTable :=
  { t with entries := fitPrefix t.maxSize (e :: t.entries) }

/-- A dynamic table size update (§4.3, §6.3): `none` (a decoding error) above the limit. -/
def setMaxSize (t : DynTable) (m : Nat) : Option DynTable :=
  if m ≤ t.limit then some { t with entries := fitPrefix m t.entries, maxSize := m } else none

/-- The entry at an index of the shared address space (§2.3.3): `1..61` static, then dynamic,
newest first. Index 0 and indices past the end are decoding errors (`none`, §2.3.3, §6.1). -/
def lookup (t : DynTable) (i : Nat) : Option Entry :=
  if i = 0 then none
  else if i ≤ staticLength then staticTable[i - 1]?
  else t.entries[i - staticLength - 1]?

end DynTable

end Silmaril.Net.Hpack
