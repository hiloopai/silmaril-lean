module

public import Silmaril.WasmSpec.InsertionSort.Defs
public import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun
public import Silmaril.Wasm.Logic.Words.Thms
public import Silmaril.Wasm.Verify.Refute.Defs
public import Silmaril.Wasm.Binaryen.Exe.Encode
public meta import Silmaril.WasmSpec.InsertionSort.Defs
public meta import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun
public meta import Silmaril.Wasm.Logic.Words.Thms
public meta import Silmaril.Wasm.Verify.Refute.Defs
public meta import Silmaril.Wasm.Binaryen.Exe.Encode

@[expose] public section

/-!
# `insertion_sort`: tests

**Executed** (`#guard`, not a proof): the instantiated module is run with silmaril-lean's
verified interpreter (`Silmaril.Wasm.SingleThreaded.Exec.runInvoke?`, whose runs are Core runs)
on arrays written into its memory between two sentinel words. A run passes if it returns no
values, the segment holds `List.mergeSort` of the input (signed order), and the whole memory
outside the segment, including the sentinels, is unchanged. The interpreter copies the 64 KiB
memory on every store, so only a few cases run here; the property test over thousands of
pseudo-random arrays runs on `wasmi` (`tools/wasm-spec-fuzz`, `cargo test`) against
`wasmBytes`, the encoding of `program` checked below.

A Silmaril addition.
-/

namespace Silmaril.WasmSpec.InsertionSort

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Words Silmaril.Wasm.Verify

/-- The bytes of memory `0` of a store. -/
def mem0 (s : Store Nat) : ByteArray := (s.mems.head?.map (·.bytes)).getD ByteArray.empty

/-- The store with the words `xs` at `p` in memory `0`, between sentinels at `p - 4` and
`p + 4 |xs|`. -/
def storeWith (p : Nat) (xs : List (BitVec 32)) : Store Nat :=
  match store₀.mems with
  | mi :: rest =>
    { store₀ with mems :=
        { mi with bytes := writeWords mi.bytes (p - 4) (0x5a5a5a5a :: xs ++ [0xa5a5a5a5]) } :: rest }
  | [] => store₀

/-- Run `insertion_sort(p, |xs|)`: the result and the final memory. -/
def run (p : Nat) (xs : List (BitVec 32)) : Option (Option Result × ByteArray) :=
  (Silmaril.Wasm.SingleThreaded.Exec.runInvoke? refOracle refFuel (storeWith p xs) 0
    [.i32 (BitVec.ofNat 32 p), .i32 (BitVec.ofNat 32 xs.length)]).map fun (c, _, r) =>
      (r, mem0 c.store)

/-- The specification's sort, executably. -/
def sortS (xs : List (BitVec 32)) : List (BitVec 32) :=
  xs.mergeSort fun x y => decide (x.toInt ≤ y.toInt)

/-- The run returns, sorts the segment and leaves every other byte unchanged. -/
def agrees (p : Nat) (xs : List (BitVec 32)) : Bool :=
  match run p xs with
  | some (some (.values []), B') =>
    let B := mem0 (storeWith p xs)
    words B' p xs.length == sortS xs && B'.size == B.size &&
      (List.range B.size).all fun i =>
        (p ≤ i && i < p + 4 * xs.length) || B'.data[i]! == B.data[i]!
  | _ => false

/-- A linear congruential generator. -/
def lcg (x : Nat) : Nat := (1103515245 * x + 12345) % 2 ^ 31

/-- `k` pseudo-random words in `[-r, r)` from the seed `x`. -/
def randWords (x r : Nat) : Nat → List (BitVec 32)
  | 0 => []
  | k + 1 => BitVec.ofInt 32 ((lcg x % (2 * r) : Nat) - (r : Int)) :: randWords (lcg x) r k

/-- The `j`-th random array: length `j % 16`, values in `[-r, r)` with `r` from `2` to `2^20`. -/
def randArray (j : Nat) : List (BitVec 32) := randWords (j * 7919 + 1) (2 ^ (1 + j % 20)) (j % 16)

#guard agrees 16 []
#guard agrees 16 [3, 1, 2]
#guard agrees 100 [0x7fffffff, BitVec.ofInt 32 (-1), 0, BitVec.ofInt 32 (-2147483648)]
#guard (List.range 3).all fun j => agrees (4 + 4 * j) (randArray (j + 7))

/-- The binary encoding of `program` (silmaril-lean's `encodeModule?`), as run by the `wasmi`
property tests in `tools/wasm-spec-fuzz` (which check their `.wasm` file against this list). -/
def wasmBytes : List UInt8 := [
  0, 97, 115, 109, 1, 0, 0, 0, 1, 6, 1, 96, 2, 127, 127, 0, 3, 2, 1, 0, 5, 3, 1, 0, 1, 7, 27, 2,
  6, 109, 101, 109, 111, 114, 121, 2, 0, 14, 105, 110, 115, 101, 114, 116, 105, 111, 110, 95,
  115, 111, 114, 116, 0, 0, 10, 126, 1, 124, 1, 3, 127, 65, 1, 33, 2, 2, 64, 3, 64, 32, 2, 32,
  1, 79, 13, 1, 32, 0, 32, 2, 65, 4, 108, 106, 40, 2, 0, 33, 4, 32, 2, 33, 3, 2, 64, 3, 64, 32,
  3, 69, 13, 1, 32, 0, 32, 3, 65, 1, 107, 65, 4, 108, 106, 40, 2, 0, 32, 4, 76, 13, 1, 32, 0,
  32, 3, 65, 4, 108, 106, 32, 0, 32, 3, 65, 1, 107, 65, 4, 108, 106, 40, 2, 0, 54, 2, 0, 32, 3,
  65, 1, 107, 33, 3, 12, 0, 11, 11, 32, 0, 32, 3, 65, 4, 108, 106, 32, 4, 54, 2, 0, 32, 2, 65,
  1, 106, 33, 2, 12, 0, 11, 11, 11]

#guard (Silmaril.Wasm.Binaryen.Exe.encodeModule? program).toOption == some wasmBytes

end Silmaril.WasmSpec.InsertionSort
