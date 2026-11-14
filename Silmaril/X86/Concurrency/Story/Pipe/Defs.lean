module

public import Silmaril.X86.Concurrency.Cir.Csl.Rel.Defs
public import Silmaril.X86.Concurrency.Cir.Mutex.Defs

/-!
# A producer-consumer pipeline: a channel and a mutex-protected result (definitions)

Two threads:

* the **producer** sends the values `vs` over a one-slot channel, then adds `|vs|` to the shared
  result `acc` under a mutex;
* the **consumer** receives the `|vs|` messages, stores message `k` in its cell `out k`, keeps
  their sum in its cell `sm`, then adds the sum to `acc` under the same mutex.

The goal (`Goal vs`): at the end `out k = vs[k]` for every `k` and `acc = |vs| + Σ vs` (mod
`2 ^ 64`).

## The channel

A stop-and-wait channel with sequence numbers (the mailbox protocol, `Cir.Chan.Mailbox`, with
the values as payloads), on three 8-byte cells: `cseq` (messages published), `cack` (messages
acknowledged) and the payload `cdat`.

* `send k v`: `mfence`; spin until `cack = k`; `cdat := v` (plain); `cseq := k + 1` (release store).
* `recv k`: `mfence`; spin until `cseq = k + 1`; `rcx := cdat` (plain); `out k := rcx`;
  `rbx := rbx + rcx`; `sm := rbx`; `cack := k + 1` (release store).

Every spin compares with a **literal** message number, so a thread proceeds only when the value it
reads pins down the channel's state. The `mfence` before each spin is needed by the logic (that
x86 does not need it is argued, not proved): `SafeR`'s side condition forbids a thread to read a
cell it does not own between a release store and its next draining label (`Csl.Rel`, triangular
race freedom in the strong form), and a spin read right after the previous message's release store
would be such a read.

## The channel's invariant (`Chan vs`)

A state is `(s, a, cP, cC)`: `s` messages published, `a` acknowledged, `cP` claimed by the
producer (it owns `cdat` while `cP = s + 1`) and `cC` claimed by the consumer (it owns `cdat` while
`cC = a + 1`). `Ok` lists the constraints. The physical part (`chanH`) holds `cseq ↦ s`, `cack ↦ a`
and, when nobody has claimed it, `cdat` (any value when empty, message `a` when full).

The ghost part (`invG`) pins the state down for each thread. CSL's ghost cells are exclusive
tokens; a thread learns a fact about the invariant only from the disjointness of its own tokens
with the invariant's. Six token families (`tok f i`), each indexed by message number:

* `C i`/`U i` (family 0/1): the invariant holds `C i` for `i < cP` and `U i` for `i ≥ cP`; the
  producer holds the rest. A claim swaps `C k` for `U k`, so the producer knows `cP` exactly.
* `P i` (family 2): the invariant holds `P i` for `i < s`; the producer gives `P k` when it
  publishes message `k`, so it knows `s ≤ k` before.
* `Q i`/`V i`, `A i` (families 3/4, 5): the same for the consumer's `cC` and `a`.

A release store can only give resources away, so after its own release a thread cannot rule out
the state just before it. That is harmless here: the next thing each thread does is a spin read
whose literal comparison rules it out. -/

@[expose] public section

namespace Silmaril.X86.Concurrency.Story.Pipe

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Rel

/-! ## Cells -/

/-- The mutex (an 8-byte slot). -/
def m : Nat := 0x100
/-- The channel's published count. -/
def cseq : Nat := 0x200
/-- The channel's acknowledged count. -/
def cack : Nat := 0x208
/-- The channel's payload. -/
def cdat : Nat := 0x210
/-- The shared result. -/
def acc : Nat := 0x218
/-- The first receipt (a token cell no code accesses). -/
def r0 : Nat := 0x220
/-- The second receipt (a token cell no code accesses). -/
def r1 : Nat := 0x228
/-- The producer's permit (a token cell no code accesses). -/
def pP : Nat := 0x230
/-- The consumer's permit (a token cell no code accesses). -/
def pC : Nat := 0x238
/-- The consumer's running sum. -/
def sm : Nat := 0x240
/-- The base of the consumer's output cells. -/
def ob : Nat := 0x10000
/-- The consumer's output cell for message `k`. -/
def out (k : Nat) : Nat := ob + 8 * k

/-! ## Ghost tokens -/

/-- The ghost cells of the channel live at `Nat.pair gbase _` (the mutex's ghost cells live at
`Nat.pair m _`, `IfaceG.gdom`). -/
def gbase : Nat := 0x200

/-- **Token `i` of family `f`** (`f < 6`). -/
def tok (f i : Nat) : Nat := Nat.pair gbase (6 * i + f)

/-- The ghost heap of the tokens `(f, i)` with `T f i`. -/
def gh (T : Nat → Nat → Bool) : Heap := fun x =>
  if (Nat.unpair x).1 = gbase ∧ T ((Nat.unpair x).2 % 6) ((Nat.unpair x).2 / 6) = true then some 0
  else none

/-- The producer's tokens: `C i` for `i ≥ c`, `U i` for `i < c`, `P i` for `i ≥ p`. -/
def prodG (c p : Nat) : Heap :=
  gh fun f i => (f == 0 && decide (c ≤ i)) || (f == 1 && decide (i < c)) ||
    (f == 2 && decide (p ≤ i))

/-- The consumer's tokens: `Q i` for `i ≥ c`, `V i` for `i < c`, `A i` for `i ≥ a`. -/
def consG (c a : Nat) : Heap :=
  gh fun f i => (f == 3 && decide (c ≤ i)) || (f == 4 && decide (i < c)) ||
    (f == 5 && decide (a ≤ i))

/-- The invariant's tokens in state `(s, a, cP, cC)`. -/
def invG (s a cP cC : Nat) : Heap :=
  gh fun f i => (f == 0 && decide (i < cP)) || (f == 1 && decide (cP ≤ i)) ||
    (f == 2 && decide (i < s)) || (f == 3 && decide (i < cC)) || (f == 4 && decide (cC ≤ i)) ||
    (f == 5 && decide (i < a))

/-! ## The channel invariant -/

/-- **The constraints on a channel state.** -/
def Ok (s a cP cC : Nat) : Prop :=
  a ≤ s ∧ s ≤ a + 1 ∧ (cP = s ∨ (cP = s + 1 ∧ s = a)) ∧ (cC = a ∨ (cC = a + 1 ∧ s = a + 1))

/-- The channel's physical cells in state `(s, a, cP, cC)`; `w` is the payload of an empty,
unclaimed channel. -/
def chanH (vs : List Nat) (s a cP cC w : Nat) : Heap := fun x =>
  if x = cseq then some s
  else if x = cack then some a
  else if x = cdat then
    (if s = a ∧ cP = s then some w else if s = a + 1 ∧ cC = a then some (vs.getD a 0) else none)
  else none

/-- **The channel's invariant.** -/
def Chan (vs : List Nat) : GProp := fun h g =>
  ∃ s a cP cC w, Ok s a cP cC ∧ h = chanH vs s a cP cC w ∧ g = invG s a cP cC

/-! ## Code -/

/-- **A spin**: `rax := [a]` (acquire) until `rax = k`, with at most `B` retries. -/
def spin (B a k : Nat) : Stmt :=
  .seq (.load .rax .acq 8 .wb (.lit a))
    (.loop B (.bin .ne (.reg .rax) (.lit k)) (.load .rax .acq 8 .wb (.lit a)))

/-- The tail of `send k v` after its spin: `cdat := v` (plain), then the release `cseq := k + 1`. -/
def sendPub (k v : Nat) : Stmt :=
  .seq (.store .na 8 .wb (.lit cdat) (.lit v)) (.store .rel 8 .wb (.lit cseq) (.lit (k + 1)))

/-- **`send k v`**: `mfence`; spin until `cack = k`; `cdat := v`; `cseq := k + 1` (release). -/
def send (B k v : Nat) : Stmt := .seq (.fence .mfence) (.seq (spin B cack k) (sendPub k v))

/-- The tail of `recv k` after its spin. -/
def recvTake (k : Nat) : Stmt :=
  .seq (.load .rcx .na 8 .wb (.lit cdat))
    (.seq (.store .na 8 .wb (.lit (out k)) (.reg .rcx))
      (.seq (.assign .rbx (.bin .add (.reg .rbx) (.reg .rcx)))
        (.seq (.store .na 8 .wb (.lit sm) (.reg .rbx))
          (.store .rel 8 .wb (.lit cack) (.lit (k + 1))))))

/-- **`recv k`**: `mfence`; spin until `cseq = k + 1`; `rcx := cdat`; `out k := rcx`;
`rbx := rbx + rcx`; `sm := rbx`; `cack := k + 1` (release). -/
def recv (B k : Nat) : Stmt := .seq (.fence .mfence) (.seq (spin B cseq (k + 1)) (recvTake k))

/-- Send the values `vs` as messages `k, k + 1, …`, then run `t`. -/
def sends (B : Nat) : Nat → List Nat → Stmt → Stmt
  | _, [], t => t
  | k, v :: vs, t => .seq (send B k v) (sends B (k + 1) vs t)

/-- Receive `r` messages from message `k` on, then run `t`. -/
def recvs (B : Nat) : Nat → Nat → Stmt → Stmt
  | _, 0, t => t
  | k, r + 1, t => .seq (recv B k) (recvs B (k + 1) r t)

/-- The producer's critical section: `acc := acc + c` (plain accesses). -/
def prodCs (c : Nat) : Stmt :=
  .seq (.load .rax .na 8 .wb (.lit acc))
    (.store .na 8 .wb (.lit acc) (.bin .add (.reg .rax) (.lit c)))

/-- The consumer's critical section: `acc := acc + sm` (plain accesses). -/
def consCs : Stmt :=
  .seq (.load .rax .na 8 .wb (.lit acc))
    (.seq (.load .rcx .na 8 .wb (.lit sm))
      (.store .na 8 .wb (.lit acc) (.bin .add (.reg .rax) (.reg .rcx))))

/-- The producer with holes `lk`, `ul`. -/
def prod (vs : List Nat) (B : Nat) (lk ul : Expr → Stmt) : Stmt :=
  sends B 0 vs (.seq (lk (.lit m)) (.seq (prodCs vs.length) (ul (.lit m))))

/-- The consumer with holes `lk`, `ul`. -/
def cons (n B : Nat) (lk ul : Expr → Stmt) : Stmt :=
  recvs B 0 n (.seq (lk (.lit m)) (.seq consCs (ul (.lit m))))

/-- Thread `0` is the producer, thread `1` the consumer. -/
def body (vs : List Nat) (B : Nat) (lk ul : Expr → Stmt) (t : Nat) : Stmt :=
  if t = 0 then prod vs B lk ul else cons vs.length B lk ul

/-- An output cell of a client with `n` messages. -/
def isOut (n x : Nat) : Prop := ob ≤ x ∧ x < ob + 8 * n ∧ (x - ob) % 8 = 0

instance (n x : Nat) : Decidable (isOut n x) := by unfold isOut; infer_instance

/-- The client's cells, all `0`: the channel, the result, the four token cells, the running sum
and the outputs. -/
def mem (n : Nat) : Heap := fun x =>
  if x = cseq ∨ x = cack ∨ x = cdat ∨ x = acc ∨ x = r0 ∨ x = r1 ∨ x = pP ∨ x = pC ∨ x = sm ∨
    isOut n x
  then some 0 else none

/-- **The pipeline** for the values `vs`, spin bound `B`: two threads, one mutex at `m`. -/
def client (vs : List Nat) (B : Nat) : Mutex.Client := ⟨2, body vs B, mem vs.length, [m], 8⟩

/-- **The pipeline's goal**: every message arrived, in order, and the result is
`|vs| + Σ vs` (mod `2 ^ 64`). -/
def Goal (vs : List Nat) (mem : Heap) : Prop :=
  mem acc = some ((vs.length + vs.sum) % 2 ^ 64) ∧ ∀ k < vs.length, mem (out k) = some (vs.getD k 0)

end Silmaril.X86.Concurrency.Story.Pipe
