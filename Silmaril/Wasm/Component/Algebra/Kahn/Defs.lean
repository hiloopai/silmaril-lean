module

public import Silmaril.Games.LTS.Defs
public import Silmaril.Wasm.Component.Iface.Defs

/-!
# The pull game of a stream: Kahn strategies

The game semantics of a **readable stream end** in the component algebra's universal signature
`sigU`. A stream component has one function (index `0`) at each interface: its **export** is the
readable end of its output stream, its **import** the readable end of its input stream.

| move | Component Model reading |
|---|---|
| question `(0, p)` at the export | the consumer's `stream.read` on our output (pending, i.e. the consumer's `waitable-set.wait`, until answered) |
| answer `some (.vals [v])` | a rendezvous of one item `v` (our `stream.write [v]` meets the read: `COMPLETED`, count 1) |
| any other answer `a` (incl. a trap `none`) | the end of the stream (`stream.drop-writable`: `DROPPED`), carried verbatim |
| question `(0, p)` at the import | our `stream.read` on the input stream, with the consumer's request `p` |
| question `(i, p)`, `i ≠ 0` | out of range: trap (`none`) at once, as `maskH 1` |

Plugging two stream components (`Algebra.seq`) hides the channel between them: the hidden
interface is the `stream.new` pair whose writable end the upstream holds and whose readable end
the downstream reads.

A component's behaviour on this game is a **stream function on answers**: `F h` is the list of
answers it has produced after receiving the answers `h` from upstream. `kahn F` is the strategy
of the canonical deterministic machine for `F` (`kahnL F`):

* between questions it holds `(h, k)`: the answers `h` received and the number `k` delivered;
* on a question `(0, p)` it answers `(F h)[k]` if `F` has produced it, and otherwise pulls
  `(0, p)` from upstream, appends the answer to `h` and tries again;
* other questions trap.

It pulls only when every produced answer has been delivered (no read-ahead), so equal stream
functions give equal strategies, and, for monotone stream functions (`Mono`), composition of
strategies is composition of stream functions (`Kahn.Thms`: `kahn_comp`, `kahn_id`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Algebra.Kahn

open Silmaril.Games Silmaril.Wasm.Component

/-- An answer of the stream game: an item, the end of the stream or a trap. -/
abbrev Ans : Type := Option Payload

/-- A stream function on answers is **monotone**: what has been produced is never retracted. -/
def Mono (F : List Ans → List Ans) : Prop := ∀ h h', F h <+: F (h ++ h')

/-- States of the Kahn machine. -/
inductive KState where
  /-- Between questions: `h` received, `k` delivered. -/
  | idle (h : List Ans) (k : Nat)
  /-- Answering the question `q`. -/
  | run (h : List Ans) (k : Nat) (q : sigU.Op)
  /-- Answering `q`, waiting for upstream. -/
  | wait (h : List Ans) (k : Nat) (q : sigU.Op)

/-- Transitions of the Kahn machine of `F`. -/
inductive KStep (F : List Ans → List Ans) : KState → Option (Move sigU sigU) → KState → Prop
  /-- Accept a question. -/
  | ask (h : List Ans) (k : Nat) (q : sigU.Op) :
      KStep F (.idle h k) (some (.inr (.ask q))) (.run h k q)
  /-- A question out of range traps. -/
  | trap (h : List Ans) (k : Nat) (q : sigU.Op) : q.1 ≠ 0 →
      KStep F (.run h k q) (some (.inr (.ans q none))) (.idle h k)
  /-- Deliver the next produced answer. -/
  | out (h : List Ans) (k : Nat) (q : sigU.Op) (a : Ans) : q.1 = 0 → (F h)[k]? = some a →
      KStep F (.run h k q) (some (.inr (.ans q a))) (.idle h (k + 1))
  /-- Nothing to deliver: pull from upstream. -/
  | pull (h : List Ans) (k : Nat) (q : sigU.Op) : q.1 = 0 → (F h)[k]? = none →
      KStep F (.run h k q) (some (.inl (.ask (0, q.2)))) (.wait h k q)
  /-- Receive an answer from upstream. -/
  | recv (h : List Ans) (k : Nat) (q : sigU.Op) (a : Ans) :
      KStep F (.wait h k q) (some (.inl (.ans (0, q.2) a))) (.run (h ++ [a]) k q)

/-- The Kahn machine of `F`. -/
@[reducible] def kahnL (F : List Ans → List Ans) : LTS sigU sigU := ⟨KState, .idle [] 0, KStep F⟩

/-- **The Kahn strategy** of the stream function `F`. -/
def kahn (F : List Ans → List Ans) : Strategy sigU sigU := Strategy.ofLTS (kahnL F)

/-- The game position of a state of the Kahn machine. -/
def kpos : KState → Pos sigU sigU
  | .idle _ _ => .idle
  | .run _ _ q => .run q
  | .wait _ _ q => .wait q (0, q.2)

end Silmaril.Wasm.Component.Algebra.Kahn
