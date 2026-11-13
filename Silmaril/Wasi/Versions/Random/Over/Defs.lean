module

public import Silmaril.Wasi.Versions.Random.Defs
public import Silmaril.Wasi.Versions.Stateful.Defs

@[expose] public section

/-!
# `wasi:random` across versions: 0.3 over 0.2 and 0.2 over 0.3

Two components between the `wasi:random` slices of `Silmaril.Wasi.Versions.Random` (complete
interfaces: `random`, `insecure`, `insecure-seed`).

* **`p3OverP2R`** (relation (b), 0.3 over 0.2): imports the 0.2 functions, exports the 0.3 ones.
  Each 0.3 call is forwarded to the 0.2 function of the same meaning (`to2`; `get-insecure-seed`
  to `insecure-seed`) with the same arguments, and the answer is returned unchanged. An exact
  0.2 answer is an admissible 0.3 short read.
* **`p2OverP3R`** (the reverse direction): imports 0.3, exports 0.2. A byte call
  `get-random-bytes(len)` / `get-insecure-random-bytes(len)` runs `fill`: it asks 0.3 for the
  bytes still missing, appends each answer and repeats until `len` bytes are accumulated, as the
  0.3 text requires of callers that need exactly `max-len` bytes. The component checks each
  answer (a `list<u8>` of `1 … missing` bytes) and traps otherwise; `fill` has fuel `len`, enough
  because every admissible 0.3 answer to a positive request carries at least one byte. The
  other calls are forwarded (`to3`).

Neither component keeps state (`Unit`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Random

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)

/-! ## 0.3 over 0.2 -/

/-- The 0.2 function behind a 0.3 function. -/
def to2 (f : FnName) : FnName :=
  if f = randBytes3 then randBytes2
  else if f = insBytes3 then insBytes2
  else if f = randU64_3 then randU64_2
  else if f = insU64_3 then insU64_2
  else insSeed2

/-- `to2` lands in the 0.2 functions. -/
theorem to2_mem (f : FnName) : to2 f ∈ rand2Fns := by
  unfold to2
  split_ifs <;> simp [rand2Fns_eq]

/-- The 0.2 call behind a 0.3 call. -/
def op2 (q : (nsig rand3Fns).Op) : (nsig rand2Fns).Op := (⟨to2 q.1.1, to2_mem _⟩, q.2)

/-- **`wasi:random` 0.3 over 0.2**: forward each call and return the answer. -/
def p3OverP2R : SBody Unit rand2Fns rand3Fns := fun _ q =>
  .call (op2 q) fun n => .pure ((), n)

/-! ## 0.2 over 0.3 -/

/-- The 0.3 function behind a 0.2 function. -/
def to3 (f : FnName) : FnName :=
  if f = randBytes2 then randBytes3
  else if f = insBytes2 then insBytes3
  else if f = randU64_2 then randU64_3
  else if f = insU64_2 then insU64_3
  else insSeed3

/-- `to3` lands in the 0.3 functions. -/
theorem to3_mem (f : FnName) : to3 f ∈ rand3Fns := by
  unfold to3
  split_ifs <;> simp [rand3Fns_eq]

/-- The 0.3 function behind a 0.2 function, as an import. -/
def fn3 (f : FnName) : {g // g ∈ rand3Fns} := ⟨to3 f, to3_mem f⟩

/-- An answer of the 0.3 byte function that `fill` accepts while `need` bytes are missing. -/
def chunkOk (need : Nat) (v : Val) : Bool :=
  allU8 v && decide (0 < (bytesOf v).length) && decide ((bytesOf v).length ≤ need)

/-- **Accumulate `need` more bytes** with the 0.3 byte function `g`, after `acc`. -/
def fill (g : {g // g ∈ rand3Fns}) : Nat → Nat → List (BitVec 8) → SProg Unit rand3Fns
  | 0, need, acc => if need = 0 then .pure ((), some [bytesV acc]) else .pure ((), none)
  | fuel + 1, need, acc =>
    if need = 0 then .pure ((), some [bytesV acc])
    else
      .call (g, [.u64 (BitVec.ofNat 64 need)]) fun r =>
        match r with
        | some [v] =>
          if chunkOk need v then fill g fuel (need - (bytesOf v).length) (acc ++ bytesOf v)
          else .pure ((), none)
        | _ => .pure ((), none)

/-- A 0.2 byte call with its length. -/
def bytesCall (f : FnName) (a : List Val) : Option Nat :=
  if f = randBytes2 ∨ f = insBytes2 then
    (match a with | [.u64 n] => some n.toNat | _ => none)
  else none

/-- **`wasi:random` 0.2 over 0.3**: byte calls accumulate short reads; others are forwarded. -/
def p2OverP3R : SBody Unit rand3Fns rand2Fns := fun _ q =>
  match bytesCall q.1.1 q.2 with
  | some n => fill (fn3 q.1.1) n n []
  | none => .call (fn3 q.1.1, q.2) fun r => .pure ((), r)

end Silmaril.Wasi.Versions.Random
