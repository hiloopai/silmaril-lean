module

public import Silmaril.Libc.Ptmalloc.Chunk.Defs

/-!
# ptmalloc component: the tcache (thread-local)

State `TcacheSt` (one thread's `tcache_perthread_struct`), invariant `TcacheWF`, operations
`get` (`tcache_get`) and `put` (`tcache_put`). The tcache holds `client` chunks of arenas (lent
out), so its invariant mentions no arena; that each entry is a client chunk of some arena and
parked once is the world-level link (`WorldWF.parked`).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

/-- **A thread's tcache**: the struct's payload address and, per bin, the chunks in list order
(head first) as (chunk address, chunk size). -/
structure TcacheSt where
  addr : Nat
  bins : Nat → List (Nat × Nat)

namespace TcacheSt

variable (C : Config) (tc : TcacheSt)

/-- **`tcache_get (i)`**: pop the head of bin `i` (its payload address). -/
def get (i : Nat) : Option (Nat × TcacheSt) :=
  match tc.bins i with
  | [] => none
  | c :: rest => some (c.1 + C.hdr, { tc with bins := fun j => if j = i then rest else tc.bins j })

/-- **`tcache_put (c, i)`**: push the chunk `c = (addr, size)` on bin `i`. -/
def put (c : Nat × Nat) (i : Nat) : TcacheSt :=
  { tc with bins := fun j => if j = i then c :: tc.bins j else tc.bins j }

/-- The payloads parked in the tcache, as (payload, usable size). -/
def payloads : List (Nat × Nat) :=
  ((List.range C.tcacheBins).flatMap tc.bins).map fun c => (c.1 + C.hdr, c.2 - C.sizeSz)

end TcacheSt

/-- **The tcache's invariant**: bins in range, at most `tcacheCount` chunks each, no duplicates,
chunk sizes of the bin, aligned non-null chunks, the struct allocated. -/
structure TcacheWF (C : Config) (tc : TcacheSt) : Prop where
  bins : ∀ i, C.tcacheBins ≤ i → tc.bins i = []
  nodup : ∀ i, (tc.bins i).Nodup ∧ (tc.bins i).length ≤ C.tcacheCount
  size : ∀ i c, c ∈ tc.bins i → C.tidx c.2 = i ∧ c.2 % C.align = 0 ∧ C.minSize ≤ c.2
  nonNull : ∀ i c, c ∈ tc.bins i → c.1 ≠ 0 ∧ c.1 % C.align = 0
  struct : tc.addr ≠ 0

end Silmaril.Libc.Ptmalloc
