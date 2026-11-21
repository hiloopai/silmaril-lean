module

public import Init.Data.BitVec.Basic

/-! An executable read contract independent of ISA state, backing storage, and image policy. -/

@[expose] public section

namespace Silmaril.Process.ImageAccess

inductive Kind where
  | data | fetch
  deriving DecidableEq, Repr

structure Read where
  kind : Kind
  address : Nat
  size : Nat
  deriving DecidableEq, Repr

/-- Route only if the whole span is inside a single specified interval. -/
def Read.within (request : Read) (base size : Nat) : Bool :=
  decide (base ≤ request.address ∧ request.address + request.size ≤ base + size)

inductive Stop where
  /-- A concrete backing or permission failure, not an exception-delivery model. -/
  | fault
  /-- This view provides no answer; this need not fault in a fuller image. -/
  | unavailable
  /-- A read outside the domain promised by the simple model's client. -/
  | ub
  deriving DecidableEq, Repr

abbrev Reader := Read → Except Stop (List (BitVec 8))

/-- Read-only effects; continuations may choose the next request from an answer. -/
inductive Program (α : Type) where
  | done (value : α)
  | read (request : Read) (next : List (BitVec 8) → Program α)

def Program.bind {α β : Type} (program : Program α) (next : α → Program β) : Program β :=
  match program with
  | .done value => next value
  | .read request resume => .read request fun bytes => (resume bytes).bind next

def Program.run {α : Type} (reader : Reader) : Program α → Except Stop α
  | .done value => .ok value
  | .read request next =>
    match reader request with
    | .error stop => .error stop
    | .ok bytes => (next bytes).run reader

/-- A total-correctness WP for this deterministic fragment. Each request on the
chosen path must succeed, ruling out UB, unavailable answers and faults. -/
def Program.wp {α : Type} (reader : Reader) (post : α → Prop) : Program α → Prop
  | .done value => post value
  | .read request next => ∃ bytes, reader request = .ok bytes ∧ (next bytes).wp reader post

/-- A read-model morphism on the source's good domain. It does not identify different
failures and cannot be used to conclude anything where the source fails. -/
def Reader.Refines (target source : Reader) : Prop :=
  ∀ request bytes, source request = .ok bytes → target request = .ok bytes

end Silmaril.Process.ImageAccess
