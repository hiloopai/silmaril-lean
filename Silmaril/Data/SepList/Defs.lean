module

public import Silmaril.Data.Cells.Defs

/-!
# List-segment fragments: doubly linked lists, rings, encoded singly linked lists, skip lists

Generic over the link layout (`Links`: the two link fields' offsets and the word width) and,
for singly linked lists, the **pointer encoding** (`SLinks.enc pos ptr`: what is stored at
position `pos` for the successor `ptr`; the identity, or glibc's safe-linking
`PROTECT_PTR (pos, ptr) = (pos >> 12) ^ ptr`). Lists are given as lists of node addresses.

The primitive is the separation-logic **list segment** `dseg K p l n`: the nodes `l` linked
through `K.fd`/`K.bk`, the first node's `bk` holding `p` and the last node's `fd` holding `n`.
Every doubly linked list below is a segment closed in some way:

* `dll K s l`: a circular doubly linked list through `K.fd`/`K.bk` with the sentinel node `s`
  (glibc's bins, Linux's `list_head`, …) = the sentinel's two cells and `dseg K s l s`.
* `ring K l`: a circular doubly linked list without a sentinel (glibc's large bins'
  `fd_nextsize`/`bk_nextsize` over the first chunk of each size).
* `slist K l`: a singly linked list through `K.link`, the last node storing `enc pos K.nil`.
* `skip K sz l`: over a list sorted by decreasing key `sz`, the `ring` of the first node of each
  run of equal keys (`leadersFrom`), the other nodes (`followersFrom`) holding 0 in both fields.

A list's possible locations are its **slots** (`Links.slots`, `SLinks.slots`): separation
hypotheses are stated as `(slots …).Sep` (decidable). The insertion/removal lemmas are proved
once (`Silmaril.Data.SepList.Thms`) and instantiated by each data structure using these lists.
-/

@[expose] public section

namespace Silmaril.Data.SepList

open Silmaril.Data

/-- **The links of a doubly linked node**: offsets of the forward and backward fields, and the
word width. -/
structure Links where
  fd : Nat
  bk : Nat
  ws : Nat := 8
  deriving DecidableEq, Repr

/-- **The link of a singly linked node**, its width, its encoding and the terminator. -/
structure SLinks where
  link : Nat
  ws : Nat := 8
  enc : Nat → Nat → Nat := fun _ p => p
  nil : Nat := 0

/-- The two link cells of a doubly linked node `x` holding `f` and `b`. -/
def Links.node (K : Links) (x f b : Nat) : Frag := [⟨x + K.fd, K.ws, f⟩, ⟨x + K.bk, K.ws, b⟩]

/-- **The slots of nodes `N`**: where their link fields live (values irrelevant, 0). -/
def Links.slots (K : Links) (N : List Nat) : Frag := N.flatMap fun x => K.node x 0 0

/-- **A doubly linked list segment**: nodes `l`, the first's `bk` = `p`, the last's `fd` = `n`. -/
def dseg (K : Links) : Nat → List Nat → Nat → Frag
  | _, [], _ => []
  | p, x :: xs, n => ⟨x + K.fd, K.ws, xs.headD n⟩ :: ⟨x + K.bk, K.ws, p⟩ :: dseg K x xs n

/-- **A circular doubly linked list** `l` (head first) with the sentinel `s`. -/
def dll (K : Links) (s : Nat) (l : List Nat) : Frag :=
  ⟨s + K.fd, K.ws, l.headD s⟩ :: ⟨s + K.bk, K.ws, l.getLastD s⟩ :: dseg K s l s

/-- **A circular doubly linked list without sentinel** (head first). -/
def ring (K : Links) : List Nat → Frag
  | [] => []
  | x :: xs => dseg K (xs.getLastD x) (x :: xs) x

/-- The slots of an encoded singly linked list's nodes. -/
def SLinks.slots (K : SLinks) (N : List Nat) : Frag := N.map fun x => ⟨x + K.link, K.ws, 0⟩

/-- **An encoded singly linked list** `l` (head first). -/
def slist (K : SLinks) : List Nat → Frag
  | [] => []
  | x :: xs => ⟨x + K.link, K.ws, K.enc (x + K.link) (xs.headD K.nil)⟩ :: slist K xs

/-- The nodes of `l` that start a run of equal keys, given the previous node's key. -/
def leadersFrom (sz : Nat → Nat) : Option Nat → List Nat → List Nat
  | _, [] => []
  | p, x :: xs => (if p = some (sz x) then [] else [x]) ++ leadersFrom sz (some (sz x)) xs

/-- The nodes of `l` that continue a run of equal keys, given the previous node's key. -/
def followersFrom (sz : Nat → Nat) : Option Nat → List Nat → List Nat
  | _, [] => []
  | p, x :: xs => (if p = some (sz x) then [x] else []) ++ followersFrom sz (some (sz x)) xs

/-- **A skip list** over `l`, sorted by decreasing `sz`, through `K.fd`/`K.bk`: the run leaders
form a `ring`, the followers hold 0 in both fields. -/
def skip (K : Links) (sz : Nat → Nat) (l : List Nat) : Frag :=
  ring K (leadersFrom sz none l) ++ (followersFrom sz none l).flatMap fun x => K.node x 0 0

/-- `l` is sorted by decreasing `sz` (the skip list's shape condition). -/
def SortedDesc (sz : Nat → Nat) (l : List Nat) : Prop :=
  ∀ j, j + 1 < l.length → sz (l.getD (j + 1) 0) ≤ sz (l.getD j 0)

instance (sz : Nat → Nat) (l : List Nat) : Decidable (SortedDesc sz l) :=
  decidable_of_iff (∀ j < l.length - 1, sz (l.getD (j + 1) 0) ≤ sz (l.getD j 0))
    ⟨fun h j hj => h j (by omega), fun h j hj => h j (by omega)⟩

/-! ## Store lists of the operations (what the code writes, in order) -/

/-- `ring` insertion of `a` before `succ`, after `pred` (four stores; glibc's large-bin
insertion of a new size, and a leader's replacement in `unlink_chunk`). -/
def ringInsertStores (K : Links) (a succ pred : Nat) : List Cell :=
  [⟨a + K.fd, K.ws, succ⟩, ⟨a + K.bk, K.ws, pred⟩, ⟨succ + K.bk, K.ws, a⟩, ⟨pred + K.fd, K.ws, a⟩]

/-- Insertion into the ring `M` (rotated so that the new node goes last): self-links into an
empty ring, else `ringInsertStores` before `M`'s head, after its last node. -/
def ringInsertInto (K : Links) (a : Nat) (M : List Nat) : List Cell :=
  if M = [] then [⟨a + K.fd, K.ws, a⟩, ⟨a + K.bk, K.ws, a⟩]
  else ringInsertStores K a (M.headD 0) (M.getLastD 0)

/-- `ring` removal between `succ` and `pred` (two stores; `unlink_chunk`'s nextsize repair). -/
def ringRemoveStores (K : Links) (succ pred : Nat) : List Cell :=
  [⟨succ + K.bk, K.ws, pred⟩, ⟨pred + K.fd, K.ws, succ⟩]

/-! ## Obligations (owned by `seplist`; discharged in `Silmaril.Data.SepList.Thms`)

Revised by `seplist`: the separation hypothesis is now `(slots …).Sep` (the first-cut statements'
`Nodup`/`Disjoint` hypotheses do not exclude nodes whose link fields overlap). -/

/-- **`Task.seplist.dllPushFront`**: inserting `a` at the head (`fwd = s->fd; a->fd = fwd;
a->bk = s; s->fd = a; fwd->bk = a`) turns `dll K s l` into `dll K s (a :: l)`, given `a`'s link
fields are writable, all nodes' link fields are separated, and the nodes fit the word. -/
def Task.seplist.dllPushFront : Prop :=
  ∀ (K : Links) (v : MemView) (s a : Nat) (l : List Nat), 0 < K.ws →
    (dll K s l).Holds v → (K.slots (a :: s :: l)).Sep → (∀ x ∈ s :: a :: l, x < 256 ^ K.ws) →
    (∀ i < K.ws, v.writable (a + K.fd + i) = true ∧ v.writable (a + K.bk + i) = true) →
    (dll K s (a :: l)).Holds (v.storeAll
      [⟨a + K.fd, K.ws, l.headD s⟩, ⟨a + K.bk, K.ws, s⟩,
       ⟨s + K.fd, K.ws, a⟩, ⟨l.headD s + K.bk, K.ws, a⟩])

/-- **`Task.seplist.dllUnlink`**: the two stores of an unlink (`fd->bk = bk; bk->fd = fd`) turn
`dll K s (l₁ ++ a :: l₂)` into `dll K s (l₁ ++ l₂)`. -/
def Task.seplist.dllUnlink : Prop :=
  ∀ (K : Links) (v : MemView) (s a : Nat) (l₁ l₂ : List Nat), 0 < K.ws →
    (dll K s (l₁ ++ a :: l₂)).Holds v → (K.slots (s :: (l₁ ++ a :: l₂))).Sep →
    (∀ x ∈ s :: (l₁ ++ a :: l₂), x < 256 ^ K.ws) →
    (dll K s (l₁ ++ l₂)).Holds
      (v.storeAll [⟨l₂.headD s + K.bk, K.ws, l₁.getLastD s⟩, ⟨l₁.getLastD s + K.fd, K.ws, l₂.headD s⟩])

/-- **`Task.seplist.slistPush`**: one store of `enc pos head` at the new node (the caller writes
the head) turns `slist K l` into `slist K (a :: l)`. -/
def Task.seplist.slistPush : Prop :=
  ∀ (K : SLinks) (v : MemView) (a : Nat) (l : List Nat), (slist K l).Holds v → a ∉ l →
    (∀ i < K.ws, v.writable (a + K.link + i) = true) →
    Frag.Disjoint [⟨a + K.link, K.ws, 0⟩] (slist K l) →
    K.enc (a + K.link) (l.headD K.nil) < 256 ^ K.ws →
    (slist K (a :: l)).Holds (v.store ⟨a + K.link, K.ws, K.enc (a + K.link) (l.headD K.nil)⟩)

/-- **`Task.seplist.slistPop`**: popping needs no store: `slist K (a :: l)` contains
`slist K l`. -/
def Task.seplist.slistPop : Prop :=
  ∀ (K : SLinks) (v : MemView) (a : Nat) (l : List Nat), (slist K (a :: l)).Holds v →
    (slist K l).Holds v

/-- **`Task.seplist.skipInsert`**: inserting `a` into a skip list where glibc's large-bin sort
puts it. Either `a` joins an existing run as a follower, right after a node of its key (no
store: its fields are already 0, glibc clears them when a large chunk enters the unsorted
list), or it starts a new run (its neighbours have other keys) and enters the leaders' ring
between the next leader (circularly) and the previous one: `ringInsertInto` the rotated ring
`L₂ ++ L₁`. -/
def Task.seplist.skipInsert : Prop :=
  ∀ (K : Links) (sz : Nat → Nat) (v : MemView) (l₁ l₂ : List Nat) (a : Nat), 0 < K.ws →
    SortedDesc sz (l₁ ++ a :: l₂) → (K.slots (a :: (l₁ ++ l₂))).Sep →
    (∀ x ∈ a :: (l₁ ++ l₂), x < 256 ^ K.ws) →
    (skip K sz (l₁ ++ l₂)).Holds v →
    if l₁.getLast?.map sz = some (sz a) then
      (K.node a 0 0).Holds v → (skip K sz (l₁ ++ a :: l₂)).Holds v
    else
      l₂.head?.map sz ≠ some (sz a) →
      (∀ i < K.ws, v.writable (a + K.fd + i) = true ∧ v.writable (a + K.bk + i) = true) →
      (skip K sz (l₁ ++ a :: l₂)).Holds (v.storeAll
        (ringInsertInto K a (leadersFrom sz none l₂ ++ leadersFrom sz none l₁)))

/-- **`Task.seplist.skipRemove`**: removing `p` from a skip list (`unlink_chunk`'s nextsize
repair). A follower: no store. A leader whose run continues with `q`: `q` takes `p`'s place in
the ring (`ringInsertInto` the other leaders, rotated). A leader alone in its run: ring removal
(two stores; self-links of `p` when it was the only leader). -/
def Task.seplist.skipRemove : Prop :=
  ∀ (K : Links) (sz : Nat → Nat) (v : MemView) (l₁ l₂ : List Nat) (p : Nat), 0 < K.ws →
    SortedDesc sz (l₁ ++ p :: l₂) → (K.slots (l₁ ++ p :: l₂)).Sep →
    (∀ x ∈ l₁ ++ p :: l₂, x < 256 ^ K.ws) →
    (skip K sz (l₁ ++ p :: l₂)).Holds v →
    if l₁.getLast?.map sz = some (sz p) then (skip K sz (l₁ ++ l₂)).Holds v
    else
      let M := leadersFrom sz (some (sz p)) l₂ ++ leadersFrom sz none l₁
      if l₂.head?.map sz = some (sz p) then
        (skip K sz (l₁ ++ l₂)).Holds (v.storeAll (ringInsertInto K (l₂.headD 0) M))
      else
        (skip K sz (l₁ ++ l₂)).Holds (v.storeAll (ringRemoveStores K (M.headD p) (M.getLastD p)))

end Silmaril.Data.SepList
