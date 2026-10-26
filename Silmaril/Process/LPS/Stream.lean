module

public import Silmaril.Process.LPS.Basic
public import Silmaril.Process.Syscall

/-!
# LPS in Lean: input streams, network streams and the connection queue

Translation of the stream section of LPS `State.v` (lines 1793-2366, upstream commit
`f1006fe8`).

LPS uses Rocq coinductive types (`InputStream := IEof | ICons b rest`, `NetStream`, and the
nil-free `NetQueue`). Lean has no primitive coinductive types, so each is represented by its
observations:

* `InputStream` **is** Silmaril's existing `Process.Syscall.InputStream`: a function
  `byteAt : ℕ → Option Byte` whose end of file is stable. `IEof` is `InputStream.eof`,
  `ICons b s` is `InputStream.cons b s`. This identification is the first point of contact
  between the two process models (see `Silmaril.Process.LPS.Lattice`).
* `NetStream` is a stable sequence of items, each a byte or one of the three endings
  `NFin`, `NRst`, `NTimedOut`.
* `NetQueue` is an infinite sequence of connections (peer, script).
-/

@[expose] public section

namespace Silmaril.Process.LPS

/-- LPS `State.v:1793` `InputStream`, as Silmaril's stable byte stream. -/
abbrev InputStream := Silmaril.Process.Syscall.InputStream

namespace InputStream

/-- `IEof`. -/
def eof : InputStream where
  byteAt _ := none
  eof_stable _ _ _ _ := rfl

/-- The stream after its first `k` positions. -/
def drop (s : InputStream) (k : Nat) : InputStream where
  byteAt i := s.byteAt (k + i)
  eof_stable first later le h := s.eof_stable _ _ (by omega) h

/-- `ICons b s`. -/
def cons (b : Byte) (s : InputStream) : InputStream where
  byteAt
    | 0 => some b
    | i + 1 => s.byteAt i
  eof_stable first later le h := by
    cases first with
    | zero => simp at h
    | succ f =>
      cases later with
      | zero => omega
      | succ l => exact s.eof_stable f l (by omega) h

/-- The bytes at positions `start, start+1, …` up to `k` of them, stopping at end of file. -/
def takeFrom (s : InputStream) (start : Nat) : Nat → List Byte
  | 0 => []
  | k + 1 =>
    match s.byteAt start with
    | none => []
    | some b => b :: takeFrom s (start + 1) k

/-- LPS `State.v:1806` `stream_take`: at most `k` bytes, and the rest of the stream. -/
def take (s : InputStream) (k : Nat) : List Byte × InputStream :=
  let bs := takeFrom s 0 k
  (bs, s.drop bs.length)

/-- LPS `State.v:1817` `stream_bytes`. -/
def bytes (s : InputStream) (k : Nat) : List Byte := (s.take k).1
/-- LPS `State.v:1821` `stream_rest`. -/
def rest (s : InputStream) (k : Nat) : InputStream := (s.take k).2

/-- LPS `State.v:1915` `stream_take_z`: the binary-recursion form of `stream_take`; LPS
proves it equal to `stream_take` on non-negative counts, and the translation uses that form. -/
def takeZ (s : InputStream) (n : Int) : List Byte × InputStream :=
  if 0 < n then s.take n.toNat else ([], s)

/-- `match s with IEof => … | ICons _ _ => …`: whether the stream is at end of file. -/
def atEof (s : InputStream) : Bool := (s.byteAt 0).isNone

/-- LPS `State.v:1989` `stream_infinite`. -/
def Infinite (s : InputStream) : Prop := ∀ n, (s.byteAt n).isSome

/-- LPS `State.v:2040` `stream_const`. -/
def const (b : Byte) : InputStream where
  byteAt _ := some b
  eof_stable _ _ _ h := by simp at h

/-- LPS `State.v:2076` `default_urandom`: zero bytes forever. -/
def defaultUrandom : InputStream := const 0

/-- LPS `EquivalenceDefinition/FinInput.v:161` `stream_of_list`. -/
def ofList (l : List Byte) : InputStream := Silmaril.Process.Syscall.InputStream.ofList l

/-- LPS `EquivalenceDefinition/FinInput.v:191` `stream_of_list_then`. -/
def ofListThen (l : List Byte) (s : InputStream) : InputStream := l.foldr cons s

end InputStream

/-- The end of a network stream: LPS `NFin`, `NRst`, `NTimedOut`. -/
inductive NetEnd where
  | fin | rst | timedOut
  deriving DecidableEq, Repr

/-- LPS `State.v:2127` `NetStream`: a sequence of bytes ended (or not) by a `NetEnd`. Once an
ending is reached it stays. -/
structure NetStream where
  item : Nat → Byte ⊕ NetEnd
  stable : ∀ i j, i ≤ j → (item i).isRight → item j = item i

namespace NetStream

/-- A stream that has ended with `e`. -/
def ended (e : NetEnd) : NetStream where
  item _ := .inr e
  stable _ _ _ _ := rfl

/-- The stream after `k` positions. -/
def drop (s : NetStream) (k : Nat) : NetStream where
  item i := s.item (k + i)
  stable i j le h := s.stable _ _ (by omega) h

/-- Bytes from position `start`, at most `k` of them, stopping at the ending. -/
def takeFrom (s : NetStream) (start : Nat) : Nat → List Byte
  | 0 => []
  | k + 1 =>
    match s.item start with
    | .inr _ => []
    | .inl b => b :: takeFrom s (start + 1) k

/-- LPS `State.v:2141` `net_take`. -/
def take (s : NetStream) (k : Nat) : List Byte × NetStream :=
  let bs := takeFrom s 0 k
  (bs, s.drop bs.length)

/-- LPS `State.v:2236` `net_ended`. -/
def isEnded (s : NetStream) : Bool := (s.item 0).isRight

/-- LPS `State.v:2260` `net_take_z`. -/
def takeZ (s : NetStream) (n : Int) : List Byte × NetStream :=
  if 0 < n then s.take n.toNat else ([], s)

end NetStream

/-- LPS `State.v:2318` `PeerAddr`. -/
structure PeerAddr where
  addr : BitVec 32
  port : BitVec 16
  deriving DecidableEq, Repr

/-- LPS `State.v:2343` `NetQueue`: an infinite queue of incoming connections. It is never
empty, which keeps `accept` receptive (SCOPE.md: the model has no environment in which no
peer ever connects). -/
abbrev NetQueue := Nat → PeerAddr × NetStream

/-- LPS `State.v:2357` `net_silent`. -/
def netSilent : NetQueue := fun _ => (⟨0, 0⟩, NetStream.ended .fin)
/-- LPS `State.v:2361` `nq_peer`. -/
def nqPeer (q : NetQueue) : PeerAddr := (q 0).1
/-- LPS `State.v:2363` `nq_script`. -/
def nqScript (q : NetQueue) : NetStream := (q 0).2
/-- LPS `State.v:2365` `nq_rest`. -/
def nqRest (q : NetQueue) : NetQueue := fun n => q (n + 1)

end Silmaril.Process.LPS
