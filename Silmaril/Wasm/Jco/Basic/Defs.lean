module

public import Silmaril.Wasm.Component.ABI.Defs

/-!
# jco-style toolchain: the common layer

The jco part (`docs/projects/wasm-components.md`) turns a core module plus WIT metadata into a component. This
module fixes what every later construction is stated over:

* `RM σ α`: a **relational state monad**. A computation relates a start state to its terminating
  outcomes `Out σ α` (`ok a s'` or `trap`). No outcome at all is divergence (or a stuck
  configuration); divergence is not otherwise observed. Equality of `RM` computations is
  equality of these relations, so "same behaviour" theorems are equations.
* `Mem`: a linear memory as a list of bytes, with bounds-checked `read`/`write`, and
  little-endian `u32` reads (`Mem.readU32`).
* `CoreInst`: an abstract **core instance**: a state type, its (single) linear memory with an
  update, and the behaviour of each core export `call name args` over flat values. Any core
  module instantiated by any core engine gives one; nothing here depends on a particular Wasm
  semantics.
* `PTy`/`PVal`: the component value types of the first FFI fragment: memory-free types (`ValTy`
  of `Silmaril.Wasm.Component.ABI`: scalars, records, variants), `string` (UTF-8) and
  `list<u8>` (`bytes`); `Sig`: a world function (name, parameters, optional result).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat ValTy Val)
open Silmaril.Wasm (NumType)

/-! ## The relational state monad -/

/-- A terminating outcome: a value with the final state, or a trap. -/
inductive Out (σ α : Type) where
  | ok (a : α) (s : σ)
  | trap

/-- Relational state computations: the terminating outcomes of a computation from a state. -/
def RM (σ α : Type) : Type := σ → Out σ α → Prop

namespace RM

variable {σ α β : Type}

/-- Return a value, keeping the state. -/
protected def pure (a : α) : RM σ α := fun s o => o = .ok a s

/-- Sequencing: run `m`; on a value continue with `k`, on a trap trap. -/
protected def bind (m : RM σ α) (k : α → RM σ β) : RM σ β := fun s o =>
  (∃ a s', m s (.ok a s') ∧ k a s' o) ∨ (m s .trap ∧ o = .trap)

instance : Monad (RM σ) where
  pure := RM.pure
  bind := RM.bind

/-- Trap. -/
def fail : RM σ α := fun _ o => o = .trap

/-- Read the state. -/
def get : RM σ σ := fun s o => o = .ok s s

/-- Replace the state. -/
def set (s' : σ) : RM σ Unit := fun _ o => o = .ok () s'

/-- Trap unless `b`. -/
def check (b : Bool) : RM σ Unit := if b then RM.pure () else fail

/-- A value, or a trap on `none`. -/
def ofOption : Option α → RM σ α
  | some a => RM.pure a
  | none => fail

/-- Every value `m` returns satisfies `P`. -/
def Returns (m : RM σ α) (P : α → Prop) : Prop := ∀ s a s', m s (.ok a s') → P a

end RM

/-! ## Linear memory -/

/-- A linear memory: byte `i` at index `i`. -/
abbrev Mem := List UInt8

namespace Mem

/-- The `n` bytes from address `a`; out of bounds is `none` (a trap). -/
def read (m : Mem) (a n : Nat) : Option (List UInt8) :=
  if a + n ≤ m.length then some ((m.drop a).take n) else none

/-- Store `bs` at address `a`; out of bounds is `none`. -/
def write (m : Mem) (a : Nat) (bs : List UInt8) : Option Mem :=
  if a + bs.length ≤ m.length then some (m.take a ++ bs ++ m.drop (a + bs.length)) else none

end Mem

/-- A little-endian `u32` from four bytes. -/
def ofLe32 : List UInt8 → Option (BitVec 32)
  | [a, b, c, d] =>
    some (BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat))
  | _ => none

/-- The `i32` payload of a single flat result. -/
def single32? : List Flat → Option (BitVec 32)
  | [⟨.int .i32, x⟩] => some x
  | _ => none

/-- The `i32` payload of a flat value. -/
def asI32? : Flat → Option (BitVec 32)
  | ⟨.int .i32, x⟩ => some x
  | _ => none

/-- The `i32` flat value of a natural number (taken modulo `2^32`). -/
abbrev i32n (n : Nat) : Flat := Flat.i32 (BitVec.ofNat 32 n)

/-! ## Core instances -/

/-- An abstract core instance: its state, its linear memory, and its exports' behaviour. -/
structure CoreInst where
  /-- Instance states (store, globals, tables, memory, …). -/
  St : Type
  /-- The exported linear memory. -/
  mem : St → Mem
  /-- Replace the memory (stores through the exported memory). -/
  setMem : St → Mem → St
  /-- Calling a core export by name on flat arguments. -/
  call : String → List Flat → RM St (List Flat)

namespace CoreInst

variable (M : CoreInst)

/-- Read `n` bytes at `a` of the instance's memory (trap out of bounds). -/
def load (a n : Nat) : RM M.St (List UInt8) := do
  let s ← RM.get
  RM.ofOption ((M.mem s).read a n)

/-- Store bytes at `a` of the instance's memory (trap out of bounds). -/
def store (a : Nat) (bs : List UInt8) : RM M.St Unit := do
  let s ← RM.get
  let m ← RM.ofOption ((M.mem s).write a bs)
  RM.set (M.setMem s m)

end CoreInst

/-! ## Types and values of the fragment -/

/-- Parameter and result types of the first fragment. -/
inductive PTy where
  /-- A memory-free type (scalars, records, variants), passed flat. -/
  | val (t : ValTy)
  /-- `string`, UTF-8 encoded. -/
  | string
  /-- `list<u8>`. -/
  | bytes
  deriving Repr, Inhabited, DecidableEq

/-- Values of the fragment. -/
inductive PVal where
  | val (v : Val)
  | string (s : String)
  | bytes (bs : List UInt8)
  deriving Repr, Inhabited

/-- A function of a world: its name, parameters and optional result. -/
structure Sig where
  name : String
  params : List PTy
  result : Option PTy := none
  deriving Repr, Inhabited, DecidableEq

/-- The core type `i32`. -/
abbrev i32T : NumType := .int .i32

/-- Canonical-ABI flattening of a fragment type: strings and lists are `(ptr, len)`. -/
def PTy.flat : PTy → List NumType
  | .val t => t.flat
  | .string | .bytes => [i32T, i32T]

/-- The flattened parameter list. -/
def flatParams : List PTy → List NumType
  | [] => []
  | t :: ts => t.flat ++ flatParams ts

/-- Whether a result is passed through memory (a `(ptr, len)` pair behind a pointer). -/
def inMem : Option PTy → Bool
  | some .string | some .bytes => true
  | _ => false

/-- The UTF-8 bytes of a string. -/
def utf8 (s : String) : List UInt8 := s.toUTF8.data.toList

/-- The canonical ABI's `MAX_STRING_BYTE_LENGTH`. -/
def maxStringBytes : Nat := 2 ^ 31 - 1

/-- The largest byte length of a `list<u8>` (`byte_length < 2^32`). -/
def maxListBytes : Nat := 2 ^ 32 - 1

/-- `MAX_FLAT_PARAMS`. -/
def maxFlatParams : Nat := 16

/-- A signature inside the fragment the constructions treat faithfully: at most
`MAX_FLAT_PARAMS` flat parameters (no spilling), and a result that is absent, flattens to at most
one core value, or is a string or list (returned through memory). -/
def Sig.Ok (s : Sig) : Bool :=
  decide ((flatParams s.params).length ≤ maxFlatParams) &&
  match s.result with
  | none | some .string | some .bytes => true
  | some (.val t) => decide (t.flat.length ≤ 1)

end Silmaril.Wasm.Jco

namespace Silmaril.Wasm.Jco.RM

/-- `m` is deterministic from `s`, with the single outcome `o`. -/
def Det {σ α : Type} (m : RM σ α) (s : σ) (o : Out σ α) : Prop := ∀ o', m s o' ↔ o' = o

end Silmaril.Wasm.Jco.RM
