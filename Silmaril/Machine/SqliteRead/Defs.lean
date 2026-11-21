module

public import Silmaril.Semantics.Behaviour.Thms

/-! A single SQLite VFS-file `xRead` request. Dispatch is independent of the
handler's response, file snapshot and buffer-write semantics. -/

@[expose] public section

namespace Silmaril.Machine.SqliteRead

open Behaviour

structure Request where
  file : BitVec 64
  buffer : BitVec 64
  amount : BitVec 32
  offset : BitVec 64
  deriving DecidableEq, Repr

inductive Status where
  | ok
  | shortRead
  | other (code : BitVec 32)
  deriving DecidableEq, Repr

def Status.ofCode (code : BitVec 32) : Status :=
  if code = 0#32 then .ok else if code = 522#32 then .shortRead else .other code

def Status.code : Status → BitVec 32
  | .ok => 0
  | .shortRead => 522
  | .other code => code

structure Context where
  liveWithRead : BitVec 64 → Prop
  /-- Exclusive writable access to the requested span for the duration of the call. -/
  ownsBuffer : BitVec 64 → Nat → Prop

/-- Positive signed `int` count and nonnegative signed `sqlite3_int64` range;
no overflow at the end even for a handler that adds the count to the offset. -/
def Context.Admits (env : Context) (req : Request) : Prop :=
  req.file ≠ 0#64 ∧ env.liveWithRead req.file ∧ req.buffer ≠ 0#64 ∧
    0 < req.amount.toNat ∧ req.amount.toNat < 2 ^ 31 ∧
    req.offset.toNat + req.amount.toNat < 2 ^ 63 ∧
    req.buffer.toNat + req.amount.toNat ≤ 2 ^ 64 ∧ env.ownsBuffer req.buffer req.amount.toNat

inductive Boundary where
  | handlerEntry
  deriving DecidableEq, Repr

inductive Failure where
  | data | fetch | divide | undefinedFlag | unsupported | validation
  deriving DecidableEq, Repr

/-- Here the successful ending is **entry to the handler**, not its response. -/
abbrev Obs := Observable Request Boundary Empty Unit Failure

def dispatch (req : Request) : Obs := ⟨[req], .returned .handlerEntry⟩

def contract (env : Context) : Observable.Contract Request Request Boundary Empty Unit Failure where
  pre := env.Admits
  post req obs := obs = dispatch req

abbrev BufferView := Nat → Option (BitVec 8)

def available (snapshot : List (BitVec 8)) (req : Request) : List (BitVec 8) :=
  (snapshot.drop req.offset.toNat).take req.amount.toNat

def Framed (req : Request) (before after : BufferView) : Prop :=
  ∀ addr, addr < req.buffer.toNat ∨ req.buffer.toNat + req.amount.toNat ≤ addr →
    after addr = before addr

def Writes (req : Request) (after : BufferView) (bytes : List (BitVec 8)) : Prop :=
  ∀ index < bytes.length, after (req.buffer.toNat + index) = bytes[index]?

/-- A returning handler for the stable-snapshot pilot, not a theorem about
SQLite's Unix backend. The frame is on the caller-visible buffer view, not on
all handler-private memory. Other errors leave the in-span bytes unspecified. -/
def Handler (snapshot : List (BitVec 8)) (req : Request) (before after : BufferView)
    (status : Status) : Prop :=
  let bytes := available snapshot req
  Framed req before after ∧
    match status with
    | .ok => bytes.length = req.amount.toNat ∧ Writes req after bytes
    | .shortRead => bytes.length < req.amount.toNat ∧
        Writes req after (bytes ++ List.replicate (req.amount.toNat - bytes.length) 0)
    | .other code => code ≠ 0#32 ∧ code ≠ 522#32

end Silmaril.Machine.SqliteRead
