module

public import Silmaril.Wasi.Theory.Defs
public import Silmaril.Wasi.Host.Defs
public import Silmaril.Machine.Process.IoSpec.Defs
public import Silmaril.Wasi.Versions.WitImport.Tables.Defs
public import Silmaril.Wasi.Versions.WitImport.RTables3.Defs

@[expose] public section

/-!
# `wasi:random` in WASI 0.2 and 0.3 as theories

Checked against the vendored WIT (`vendor/wasi/0.2.12/random/{random,insecure,insecure-seed}.wit`,
the same signatures in `vendor/wasi/v0.2.9/random`, and `vendor/wasi/0.3.2/random/*.wit`):

| Lean | WIT 0.2 | WIT 0.3 |
| --- | --- | --- |
| `randBytes2` / `randBytes3` | `random.get-random-bytes: func(len: u64) -> list<u8>` | `random.get-random-bytes: func(max-len: u64) -> list<u8>` |
| `randU64_2` / `randU64_3` | `random.get-random-u64: func() -> u64` | the same |
| `insBytes2` / `insBytes3` | `insecure.get-insecure-random-bytes: func(len: u64) -> list<u8>` | `…(max-len: u64) -> list<u8>` |
| `insU64_2` / `insU64_3` | `insecure.get-insecure-random-u64: func() -> u64` | the same |
| `insSeed2` / `insSeed3` | `insecure-seed.insecure-seed: func() -> tuple<u64, u64>` | `insecure-seed.get-insecure-seed: func() -> tuple<u64, u64>` (renamed) |

These are all the functions of `wasi:random` in both versions: the interface is complete here.

## The semantic difference

0.2: "Return `len` cryptographically-secure random or pseudo-random bytes." 0.3 (`random.wit`):
"Implementations MAY return fewer bytes than requested (a short read). Callers that require
exactly `max-len` bytes MUST call this function in a loop until the desired number of bytes has
been accumulated. Implementations MUST return at least 1 byte when `max-len` is greater than
zero. When `max-len` is zero, implementations MUST return an empty list without trapping." The
same text is in `insecure.wit` for `get-insecure-random-bytes`.

* `randTh2` (`pointwise ok2`): a `get-random-bytes(len)` / `get-insecure-random-bytes(len)`
  answer is a `list<u8>` of **exactly** `len` bytes; the `u64` functions answer a `u64`, the
  seed a `tuple<u64, u64>`; no traps on well-typed calls.
* `randTh3` (`pointwise ok3`): the byte functions answer `k` bytes with `k ≤ max-len` and
  `0 < k` when `0 < max-len` (`shortOk`); the rest as in 0.2.

Calls whose arguments are not the WIT arguments (the canonical ABI lifts only well-typed
values) are unconstrained. Freshness and unpredictability ("must always return fresh data") are
not expressible on single traces and are not part of the theories.

## Hosts and the OS image

`rand2Impl src` and `rand3Impl src c` answer the secure byte functions from a **device**
`src : Nat → BitVec 8` (think `/dev/urandom`), read sequentially: the next bytes after those
already delivered (`drawn`). `rand3Impl` delivers at most `c + 1` bytes per call (short reads).
The insecure functions answer zeros, the `u64` functions a counter, the seed `(0, 0)`.

`osEvR ch` reads a secure byte answer (0.2 or 0.3) as LPS `readEv ch b` events: the bytes a
process reads from the device's channel `ch` (the `read` arm of `Silmaril.Machine.Process.IoSpec`,
`readArm`). `osTraceR ch t` is the image of an event list. There is no LPS event for the other
functions.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Random

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Function names -/

/-- `wasi:random/random.get-random-bytes` (0.2). -/
def randBytes2 : FnName := ⟨"wasi:random/random", "get-random-bytes"⟩
/-- `wasi:random/random.get-random-u64` (0.2). -/
def randU64_2 : FnName := ⟨"wasi:random/random", "get-random-u64"⟩
/-- `wasi:random/insecure.get-insecure-random-bytes` (0.2). -/
def insBytes2 : FnName := ⟨"wasi:random/insecure", "get-insecure-random-bytes"⟩
/-- `wasi:random/insecure.get-insecure-random-u64` (0.2). -/
def insU64_2 : FnName := ⟨"wasi:random/insecure", "get-insecure-random-u64"⟩
/-- `wasi:random/insecure-seed.insecure-seed` (0.2). -/
def insSeed2 : FnName := ⟨"wasi:random/insecure-seed", "insecure-seed"⟩

/-- `wasi:random/random@0.3.2.get-random-bytes`. -/
def randBytes3 : FnName := ⟨"wasi:random/random@0.3.2", "get-random-bytes"⟩
/-- `wasi:random/random@0.3.2.get-random-u64`. -/
def randU64_3 : FnName := ⟨"wasi:random/random@0.3.2", "get-random-u64"⟩
/-- `wasi:random/insecure@0.3.2.get-insecure-random-bytes`. -/
def insBytes3 : FnName := ⟨"wasi:random/insecure@0.3.2", "get-insecure-random-bytes"⟩
/-- `wasi:random/insecure@0.3.2.get-insecure-random-u64`. -/
def insU64_3 : FnName := ⟨"wasi:random/insecure@0.3.2", "get-insecure-random-u64"⟩
/-- `wasi:random/insecure-seed@0.3.2.get-insecure-seed`. -/
def insSeed3 : FnName := ⟨"wasi:random/insecure-seed@0.3.2", "get-insecure-seed"⟩

/-- The `wasi:random` functions of 0.2, **read from the vendored WIT**
(`vendor/wasi/0.2.12/random`, `Silmaril.Wasi.Versions.WitImport.rand2T`). -/
def rand2Fns : Set FnName := {f | f ∈ WitImport.names WitImport.rand2T}

/-- The `wasi:random` functions of 0.3, **read from the vendored WIT**
(`vendor/wasi/0.3.2/random`, `Silmaril.Wasi.Versions.WitImport.rand3T`). -/
def rand3Fns : Set FnName := {f | f ∈ WitImport.names WitImport.rand3T}

/-- **The imported 0.2 functions are the hand-written five.** Proofs that need the members
rewrite with this equation instead of unfolding `rand2Fns`. -/
theorem rand2Fns_eq : rand2Fns = {randBytes2, randU64_2, insBytes2, insU64_2, insSeed2} := by
  have h : WitImport.names WitImport.rand2T = [insSeed2, insBytes2, insU64_2, randBytes2, randU64_2] := by
    decide +kernel
  ext f
  show f ∈ WitImport.names WitImport.rand2T ↔ _
  rw [h]
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- **The imported 0.3 functions are the hand-written five.** -/
theorem rand3Fns_eq : rand3Fns = {randBytes3, randU64_3, insBytes3, insU64_3, insSeed3} := by
  have h : WitImport.names WitImport.rand3T = [insSeed3, insBytes3, insU64_3, randBytes3, randU64_3] := by
    decide +kernel
  ext f
  show f ∈ WitImport.names WitImport.rand3T ↔ _
  rw [h]
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- The `wasi:random` world of 0.2 (imports only). -/
def rand2World : World := ⟨rand2Fns, ∅⟩

/-- The `wasi:random` world of 0.3 (imports only). -/
def rand3World : World := ⟨rand3Fns, ∅⟩

/-! ## Answers -/

/-- An encoded `list<u8>`: a record of `u8`s. -/
def allU8 : Val → Bool
  | .record vs => vs.all fun | .u8 _ => true | _ => false
  | _ => false

/-- A `list<u8>` answer whose length satisfies `P`. -/
def bytesAns (P : Nat → Bool) : Option (List Val) → Bool
  | some [v] => allU8 v && P (bytesOf v).length
  | _ => false

/-- A `u64` answer. -/
def u64Ans : Option (List Val) → Bool
  | some [.u64 _] => true
  | _ => false

/-- A `tuple<u64, u64>` answer. -/
def seedAns : Option (List Val) → Bool
  | some [.record [.u64 _, .u64 _]] => true
  | _ => false

/-- A byte call `(u64 n)` answered `r`, checked by `P n`; other arguments are unconstrained. -/
def bytesM (P : Nat → Nat → Bool) (a : List Val) (r : Option (List Val)) : Bool :=
  match a with
  | [.u64 n] => bytesAns (P n.toNat) r
  | _ => true

/-- A call without arguments answered `r`, checked by `ans`; other arguments are unconstrained. -/
def nullM (ans : Option (List Val) → Bool) (a : List Val) (r : Option (List Val)) : Bool :=
  match a with
  | [] => ans r
  | _ => true

/-- 0.2: exactly `n` bytes. -/
def exactOk (n k : Nat) : Bool := k == n

/-- 0.3: at most `n` bytes, and at least one when `0 < n`. -/
def shortOk (n k : Nat) : Bool := decide (k ≤ n) && (n == 0 || decide (0 < k))

/-! ## The theories -/

/-- The answers of 0.2 `wasi:random`, as written by hand (`ok2_eq_hand`: equal to `ok2`). -/
def ok2H : WEv → Bool
  | .imp f a r =>
    if f = randBytes2 ∨ f = insBytes2 then
      bytesM exactOk a r
    else if f = randU64_2 ∨ f = insU64_2 then nullM u64Ans a r
    else if f = insSeed2 then nullM seedAns a r
    else true
  | _ => true

/-- The answers of 0.3 `wasi:random`, as written by hand (`ok3_eq_hand`: equal to `ok3`). -/
def ok3H : WEv → Bool
  | .imp f a r =>
    if f = randBytes3 ∨ f = insBytes3 then
      bytesM shortOk a r
    else if f = randU64_3 ∨ f = insU64_3 then nullM u64Ans a r
    else if f = insSeed3 then nullM seedAns a r
    else true
  | _ => true

end Silmaril.Wasi.Versions.Random

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasi.Versions.Random

/-- The length condition `P n k` of a byte call `(u64 n)` answered by one value. -/
def lenM (P : Nat → Nat → Bool) (a : List Val) (r : Option (List Val)) : Bool :=
  match a, r with
  | [.u64 n], some [v] => P n.toNat (bytesOf v).length
  | _, _ => true

/-- The length part of `Random.ok2`. -/
def len2 : WEv → Bool
  | .imp f a r => if f = randBytes2 ∨ f = insBytes2 then lenM exactOk a r else true
  | _ => true

/-- The length part of `Random.ok3`. -/
def len3 : WEv → Bool
  | .imp f a r => if f = randBytes3 ∨ f = insBytes3 then lenM shortOk a r else true
  | _ => true

end Silmaril.Wasi.Versions.WitImport

namespace Silmaril.Wasi.Versions.Random

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- The answers of 0.2 `wasi:random`: **the resolved WIT typing of the imported
`vendor/wasi/0.2.12/random` package** plus the exact-length condition, which the WIT does not
express (`len2`). -/
def ok2 (e : WEv) : Bool := WitImport.witROk WitImport.rand2P e && WitImport.len2 e

/-- The answers of 0.3 `wasi:random`: **the resolved WIT typing of the imported
`vendor/wasi/0.3.2/random` package** plus the short-read condition (`len3`). -/
def ok3 (e : WEv) : Bool := WitImport.witROk WitImport.rand3P e && WitImport.len3 e

/-- **The `wasi:random` theory of WASI 0.2**: exact lengths. -/
def randTh2 : Protocol Unit WEv := pointwise ok2

/-- **The `wasi:random` theory of WASI 0.3**: short reads, at least one byte. -/
def randTh3 : Protocol Unit WEv := pointwise ok3

/-! ## Concrete hosts over a device -/

/-- The device bytes an event delivered: a secure byte answer of either version. -/
def drawnEv : WEv → Nat
  | .imp f _ (some [v]) => if f = randBytes2 ∨ f = randBytes3 then (bytesOf v).length else 0
  | _ => 0

/-- The device bytes delivered by an event list. -/
def drawn (t : List WEv) : Nat := (t.map drawnEv).sum

/-- The next `n` bytes of the device after the answers `p`. -/
def devBytes (src : Nat → BitVec 8) (p : List WEv) (n : Nat) : List (BitVec 8) :=
  (List.range n).map fun i => src (drawn p + i)

/-- **The concrete 0.2 host over the device `src`**: `get-random-bytes(len)` reads the next
`len` device bytes; insecure bytes are zeros; the `u64`s count the answers; the seed is
`(0, 0)`. -/
def rand2Impl (src : Nat → BitVec 8) : Impl := fun p f a =>
  if f = randBytes2 then
    (match a with | [.u64 n] => some [bytesV (devBytes src p n.toNat)] | _ => none)
  else if f = insBytes2 then
    (match a with | [.u64 n] => some [bytesV (List.replicate n.toNat 0)] | _ => none)
  else if f = randU64_2 ∨ f = insU64_2 then some [.u64 (BitVec.ofNat 64 p.length)]
  else if f = insSeed2 then some [.record [.u64 0, .u64 0]]
  else none

/-- **The concrete 0.3 host over the device `src`**, with short reads: each byte call delivers
`min max-len (c + 1)` bytes. -/
def rand3Impl (src : Nat → BitVec 8) (c : Nat) : Impl := fun p f a =>
  if f = randBytes3 then
    (match a with | [.u64 n] => some [bytesV (devBytes src p (min n.toNat (c + 1)))] | _ => none)
  else if f = insBytes3 then
    (match a with | [.u64 n] => some [bytesV (List.replicate (min n.toNat (c + 1)) 0)] | _ => none)
  else if f = randU64_3 ∨ f = insU64_3 then some [.u64 (BitVec.ofNat 64 p.length)]
  else if f = insSeed3 then some [.record [.u64 0, .u64 0]]
  else none

/-! ## The OS image -/

/-- The OS image of an event: a secure byte answer read from the device channel `ch`. -/
def osEvR (ch : Silmaril.Process.LPS.Word) : WEv → List Silmaril.Process.LPS.Event
  | .imp f _ (some [v]) =>
    if f = randBytes2 ∨ f = randBytes3 then (bytesOf v).map (.readEv ch) else []
  | _ => []

/-- **The OS image** of an event list: the device bytes read. -/
def osTraceR (ch : Silmaril.Process.LPS.Word) (t : List WEv) : List Silmaril.Process.LPS.Event :=
  t.flatMap (osEvR ch)

/-- The first `n` bytes of the device, read on `ch`. -/
def devTrace (ch : Silmaril.Process.LPS.Word) (src : Nat → BitVec 8) (n : Nat) :
    List Silmaril.Process.LPS.Event :=
  (List.range n).map fun i => .readEv ch (src i)

end Silmaril.Wasi.Versions.Random
