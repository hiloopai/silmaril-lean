module

public import Silmaril.Wasm.Wat
public import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Wasm.Verify.FnSpec.Defs
public import Silmaril.Wasm.Examples.Wat.Defs

/-!
# Verified Wasm functions: examples of `FnSpec` and `wasm_vc`

Six small functions in one module `prog` (quoted with silmaril-lean's `wat3!`), each with a
`FnSpec`; the proofs are in `Silmaril.Proofs.Wasm.Examples.Verified.Basic`:

| function | spec | shape |
|---|---|---|
| `double x` | `x + x` | `FnSpec.pure` |
| `abs x` | `|x|` (as integers, `x ≠ intMin`) | `FnSpec.pure`, `if` |
| `max x y` | signed maximum | `FnSpec.pure`, `select` |
| `sum n` | `0 + 1 + ⋯ + n` (mod `2³²`) | `FnSpec.pure`, loop with invariant |
| `store_load p x` | writes `x` at `p`, returns it | `FnSpec.mem` with `write` |
| `get base len i` | `base[i]` if `i < len`, else `-1` | `FnSpec.mem`, bounds check |

and one binary: `doubleBytes` is the 43-byte `double.wasm` of the silmaril project demo
(`wasm-tools parse double.wat`, stripped); it decodes to `doubleWat`
(`Silmaril.Proofs.Wasm.Examples.Verified.Basic.doubleBytes_decode`, by kernel evaluation of
silmaril-lean's decoder), whose function is verified against `doubleSpec`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.Verified

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Verify Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Examples.Wat (triangle)

/-- The module. -/
def prog : Module := wat3! r#"
(module
  (memory 1)
  (func $double (export "double") (param $x i32) (result i32)
    local.get $x
    local.get $x
    i32.add)
  (func $abs (export "abs") (param $x i32) (result i32)
    (if (result i32) (i32.lt_s (local.get $x) (i32.const 0))
      (then (i32.sub (i32.const 0) (local.get $x)))
      (else (local.get $x))))
  (func $max (export "max") (param $x i32) (param $y i32) (result i32)
    (select (local.get $x) (local.get $y) (i32.gt_s (local.get $x) (local.get $y))))
  (func $sum (export "sum") (param $n i32) (result i32) (local $i i32) (local $acc i32)
    (block $done
      (loop $next
        (br_if $done (i32.eq (local.get $i) (local.get $n)))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (local.set $acc (i32.add (local.get $acc) (local.get $i)))
        (br $next)))
    (local.get $acc))
  (func $store_load (export "store_load") (param $p i32) (param $x i32) (result i32)
    (i32.store (local.get $p) (local.get $x))
    (i32.load (local.get $p)))
  (func $get (export "get") (param $base i32) (param $len i32) (param $i i32) (result i32)
    (if (result i32) (i32.lt_u (local.get $i) (local.get $len))
      (then (i32.load (i32.add (local.get $base) (i32.shl (local.get $i) (i32.const 2)))))
      (else (i32.const -1)))))
"#

/-! ## Specifications -/

/-- `double x = x + x`. -/
def doubleSpec : FnSpec (BitVec 32) :=
  .pure (fun x => [.i32 x]) fun x res => res = [.i32 (x + x)]

/-- `abs x = |x|` as integers, for `x ≠ intMin`. -/
def absSpec : FnSpec (BitVec 32) :=
  .pure (fun x => [.i32 x]) (pre := fun x => x ≠ BitVec.intMin 32)
    fun x res => ∃ r : BitVec 32, res = [.i32 r] ∧ r.toInt = x.toInt.natAbs

/-- `max x y` is the signed maximum. -/
def maxSpec : FnSpec (BitVec 32 × BitVec 32) :=
  .pure (fun (x, y) => [.i32 x, .i32 y])
    fun (x, y) res => ∃ r : BitVec 32, res = [.i32 r] ∧ r.toInt = max x.toInt y.toInt

/-- `sum n = 0 + 1 + ⋯ + n` (mod `2³²`); the loop invariant: store unchanged, no loop
parameters, locals `n, i, acc` with `i ≤ n` and `acc = 0 + ⋯ + i`. -/
def sumSpec : FnSpec (BitVec 32) :=
  .pure (fun n => [.i32 n]) (fun n res => res = [.i32 (BitVec.ofNat 32 (triangle n.toNat))])
    (inv := fun n _ s₀ _ s f a => s = s₀ ∧ a = [] ∧ ∃ i acc : BitVec 32,
      f.locals = [some (.i32 n), some (.i32 i), some (.i32 acc)] ∧ i.toNat ≤ n.toNat ∧
      acc = BitVec.ofNat 32 (triangle i.toNat))

/-- `store_load p x` writes `x` at byte `p` of memory `0` and returns it. -/
def storeLoadSpec : FnSpec (BitVec 32 × BitVec 32) :=
  .mem (fun (p, x) => [.i32 p, .i32 x]) (pre := fun (p, _) B => p.toNat + 4 ≤ B.size)
    (write := fun (p, x) B => wr B p.toNat x)
    fun (_, x) _ res => res = [.i32 x]

/-- `get base len i` reads the `i`-th word of the array of `len` words at `base`, or answers
`-1` out of bounds; memory is unchanged. -/
def getSpec : FnSpec (BitVec 32 × BitVec 32 × BitVec 32) :=
  .mem (fun (b, n, i) => [.i32 b, .i32 n, .i32 i])
    (pre := fun (b, n, _) B => b.toNat + 4 * n.toNat ≤ B.size ∧ b.toNat + 4 * n.toNat < 2 ^ 32)
    fun (b, n, i) B res =>
      res = [.i32 (if i.toNat < n.toNat then wd B (b.toNat + 4 * i.toNat) else -1)]

/-! ## A binary -/

/-- `double.wasm` of the silmaril project demo (43 bytes). -/
def doubleBytes : ByteArray := ⟨#[0, 97, 115, 109, 1, 0, 0, 0, 1, 6, 1, 96, 1, 127, 1, 127, 3, 2,
  1, 0, 7, 10, 1, 6, 100, 111, 117, 98, 108, 101, 0, 0, 10, 9, 1, 7, 0, 32, 0, 32, 0, 106, 11]⟩

/-- The source of `double.wasm`. -/
def doubleWat : Module := wat3! r#"
(module
  (func $double (export "double") (param i32) (result i32)
    local.get 0
    local.get 0
    i32.add))
"#

end Silmaril.Wasm.Examples.Verified
