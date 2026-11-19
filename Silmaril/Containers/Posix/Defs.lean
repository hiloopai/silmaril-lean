module

public import Silmaril.Containers.Env.Defs
public import Silmaril.Games.Sig.Defs

/-! # Experimental typed read/write protocol

These are abstract POSIX-subset requests, not an x86 ABI or a claim about Linux. The existing
`Ev.read/write(path, bytes)` remain coarse effects. They do not encode descriptor identity,
offsets, attempted versus accepted bytes, errno, or interruption. Here responses depend on
the request, and descriptor aliases share an open description's offset. -/

@[expose] public section
namespace Silmaril.Containers.Posix
abbrev Bytes := List UInt8

inductive Errno where
  | badfd | io | intr | again
  deriving DecidableEq, Repr

inductive Req where
  | read (fd count : Nat)
  | write (fd : Nat) (attempt : Bytes)
  deriving DecidableEq, Repr

inductive ReadReply (count : Nat) where
  | bytes (data : Bytes) (bound : data.length ≤ count)
  | eof
  | error (errno : Errno)

inductive WriteReply (attempt : Bytes) where
  | accepted (count : Nat) (bound : count ≤ attempt.length)
  | error (errno : Errno)

def Response : Req → Type
  | .read _ n => ReadReply n
  | .write _ bs => WriteReply bs

/-- Calls and returns are separate letters; a signal may arrive in between them. -/
inductive Event where
  | call (req : Req)
  | returned (req : Req) (reply : Response req)

/-- An open description names a stable file identity, not its current pathname. -/
structure Description where
  file : Nat
  offset : Nat
  deriving DecidableEq, Repr

structure State where
  descriptors : Nat → Option Nat
  descriptions : Nat → Option Description
  files : Nat → Bytes

/-- Aliased descriptors look up the same description. -/
def State.lookup (s : State) (fd : Nat) : Option Description :=
  (s.descriptors fd).bind s.descriptions

/-- Advance an *open description*, so all its descriptor aliases observe the new offset. -/
def State.advance (s : State) (id count : Nat) : State :=
  { s with descriptions := fun j => if j = id then
      (s.descriptions j).map fun d => { d with offset := d.offset + count }
    else s.descriptions j }

/-- A bounded read response can still lie about the file. This checker additionally checks
that the returned bytes are a prefix of the contents at the shared offset. -/
def readStep (s : State) (fd count : Nat) : ReadReply count → Option State
  | .error _ => some s
  | .eof => do
    let d ← s.lookup fd
    if (s.files d.file).drop d.offset = [] then some s else none
  | .bytes bs _ => do
    let id ← s.descriptors fd
    let d ← s.descriptions id
    if bs <+: (s.files d.file).drop d.offset then some (s.advance id bs.length) else none

/-- Accepted bytes are a prefix of the attempt; the remainder has not been written. -/
def acceptedBytes (attempt : Bytes) (reply : WriteReply attempt) : Bytes :=
  match reply with
  | .accepted n _ => attempt.take n
  | .error _ => []

/-- Update bytes at an offset, filling a gap with zeroes. -/
def writeAt (old : Bytes) (offset : Nat) (data : Bytes) : Bytes :=
  old.take offset ++ List.replicate (offset - old.length) 0 ++ data ++
    old.drop (offset + data.length)

/-- The descriptor/open-description/file adapter, not an `fd → path` renaming. -/
def writeStep (s : State) (fd : Nat) (attempt : Bytes) : WriteReply attempt → Option State
  | .error _ => some s
  | .accepted n _ => do
    let id ← s.descriptors fd
    let d ← s.descriptions id
    let data := attempt.take n
    let s' := s.advance id n
    if n = 0 then pure s else pure { s' with files := fun f => (if f = d.file then writeAt (s.files f) d.offset data else s.files f) }

/-- The same typed protocol can be supplied as a dependent game signature. Mapping an ABI or
WIT resource into this protocol must also preserve its descriptor and resource state. -/
def interrupted : (req : Req) → Response req
  | .read _ _ => .error .intr
  | .write _ _ => .error .intr

/-- Requests are program questions; answers are host choices in the existing game API. -/
def signature : Silmaril.Games.Sig := ⟨Req, Response⟩

/-- Offset-aware effects. A response is not a whole-file replacement or a pathname lookup. -/
inductive Effect where
  | read (file offset : Nat) (bytes : Bytes)
  | eof (file offset : Nat)
  | write (file offset : Nat) (accepted : Bytes)
  | failed (request : Req) (errno : Errno)
  deriving DecidableEq, Repr

/-- A stateful adapter from a completed typed request/response to a file effect. Interruption
is assembled at the split call/return layer; it is not simulated by renaming an fd to a path. -/
def respond (s : State) : (req : Req) → Response req → Option (State × Effect)
  | .read fd n, .error e => some (s, .failed (.read fd n) e)
  | .read fd n, .bytes bs bound => do
    let d ← s.lookup fd
    let next ← readStep s fd n (.bytes bs bound)
    pure (next, .read d.file d.offset bs)
  | .read fd n, .eof => do
    let d ← s.lookup fd
    let next ← readStep s fd n .eof
    pure (next, .eof d.file d.offset)
  | .write fd attempt, .error e => some (s, .failed (.write fd attempt) e)
  | .write fd attempt, .accepted n bound => do
    let d ← s.lookup fd
    let next ← writeStep s fd attempt (.accepted n bound)
    pure (next, .write d.file d.offset (attempt.take n))

end Silmaril.Containers.Posix
