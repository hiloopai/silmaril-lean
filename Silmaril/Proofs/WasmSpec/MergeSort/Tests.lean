module

public import Silmaril.WasmSpec.MergeSort.Defs
public import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun
public import Silmaril.Wasm.Logic.Words.Thms
public import Silmaril.Wasm.Verify.Refute.Defs
public import Silmaril.Wasm.Binaryen.Exe.Encode
public meta import Silmaril.WasmSpec.MergeSort.Defs
public meta import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun
public meta import Silmaril.Wasm.Logic.Words.Thms
public meta import Silmaril.Wasm.Verify.Refute.Defs
public meta import Silmaril.Wasm.Binaryen.Exe.Encode

@[expose] public section

/-!
# `merge_sort`: tests

**Executed** (`#guard`, not a proof): the instantiated module is run with silmaril-lean's
verified interpreter (`Silmaril.Wasm.SingleThreaded.Exec.runInvoke?`) on a few arrays written
into its memory; a run passes if it returns no values, the array holds `List.mergeSort` of the
input (signed order), and every byte outside the array and the scratch buffer is unchanged. The
interpreter copies the 64 KiB memory on every store, so only a few cases run here; the property
test over thousands of pseudo-random arrays runs on `wasmi` (`tools/wasm-spec-fuzz`,
`cargo test`) against `wasmBytes`, the encoding of `program` checked below.

A Silmaril addition.
-/

namespace Silmaril.WasmSpec.MergeSort

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Words Silmaril.Wasm.Verify

/-- The bytes of memory `0` of a store. -/
def mem0 (s : Store Nat) : ByteArray := (s.mems.head?.map (·.bytes)).getD ByteArray.empty

/-- The store with the words `xs` at `p` in memory `0`. -/
def storeWith (p : Nat) (xs : List (BitVec 32)) : Store Nat :=
  match store₀.mems with
  | mi :: rest => { store₀ with mems := { mi with bytes := writeWords mi.bytes p xs } :: rest }
  | [] => store₀

/-- Run `merge_sort(p, |xs|, t)`: the result and the final memory. -/
def run (p t : Nat) (xs : List (BitVec 32)) : Option (Option Result × ByteArray) :=
  (Silmaril.Wasm.SingleThreaded.Exec.runInvoke? refOracle refFuel (storeWith p xs) 1
    [.i32 (BitVec.ofNat 32 p), .i32 (BitVec.ofNat 32 xs.length), .i32 (BitVec.ofNat 32 t)]).map
    fun (c, _, r) => (r, mem0 c.store)

/-- The run returns, sorts the array and leaves every byte outside the array and the buffer
(`t > p`) unchanged. -/
def agrees (p t : Nat) (xs : List (BitVec 32)) : Bool :=
  match run p t xs with
  | some (some (.values []), B') =>
    let B := mem0 (storeWith p xs)
    let n := xs.length
    words B' p n == xs.mergeSort (fun x y => decide (x.toInt ≤ y.toInt)) && B'.size == B.size &&
      (B'.extract 0 p).data == (B.extract 0 p).data &&
      (B'.extract (p + 4 * n) t).data == (B.extract (p + 4 * n) t).data &&
      (B'.extract (t + 4 * n) B.size).data == (B.extract (t + 4 * n) B.size).data
  | _ => false

#guard agrees 16 400 []
#guard agrees 16 400 [3, 1, 2]
#guard agrees 100 600 [0x7fffffff, BitVec.ofInt 32 (-1), 0, BitVec.ofInt 32 (-2147483648), 5]

/-- The binary encoding of `program` (silmaril-lean's `encodeModule?`), as run by the `wasmi`
property tests in `tools/wasm-spec-fuzz` (which check their `.wasm` file against this list). -/
def wasmBytes : List UInt8 := [
  0, 97, 115, 109, 1, 0, 0, 0, 1, 14, 2, 96, 4, 127, 127, 127, 127, 0, 96, 3, 127, 127, 127, 0,
  3, 3, 2, 0, 1, 5, 3, 1, 0, 1, 7, 31, 3, 6, 109, 101, 109, 111, 114, 121, 2, 0, 5, 109, 101,
  114, 103, 101, 0, 0, 10, 109, 101, 114, 103, 101, 95, 115, 111, 114, 116, 0, 1, 10, 253, 1, 2,
  193, 1, 1, 4, 127, 32, 1, 33, 5, 2, 64, 3, 64, 32, 6, 32, 2, 79, 13, 1, 32, 5, 32, 2, 79, 4,
  64, 65, 1, 33, 7, 5, 32, 4, 32, 1, 79, 4, 64, 65, 0, 33, 7, 5, 32, 0, 32, 4, 65, 4, 108, 106,
  40, 2, 0, 32, 0, 32, 5, 65, 4, 108, 106, 40, 2, 0, 76, 33, 7, 11, 11, 32, 7, 4, 64, 32, 3, 32,
  6, 65, 4, 108, 106, 32, 0, 32, 4, 65, 4, 108, 106, 40, 2, 0, 54, 2, 0, 32, 4, 65, 1, 106, 33,
  4, 5, 32, 3, 32, 6, 65, 4, 108, 106, 32, 0, 32, 5, 65, 4, 108, 106, 40, 2, 0, 54, 2, 0, 32, 5,
  65, 1, 106, 33, 5, 11, 32, 6, 65, 1, 106, 33, 6, 12, 0, 11, 11, 65, 0, 33, 6, 2, 64, 3, 64,
  32, 6, 32, 2, 79, 13, 1, 32, 0, 32, 6, 65, 4, 108, 106, 32, 3, 32, 6, 65, 4, 108, 106, 40, 2,
  0, 54, 2, 0, 32, 6, 65, 1, 106, 33, 6, 12, 0, 11, 11, 11, 56, 1, 1, 127, 2, 64, 32, 1, 65, 2,
  73, 13, 0, 32, 1, 65, 1, 118, 33, 3, 32, 0, 32, 3, 32, 2, 16, 1, 32, 0, 32, 3, 65, 4, 108,
  106, 32, 1, 32, 3, 107, 32, 2, 16, 1, 32, 0, 32, 3, 32, 1, 32, 2, 16, 0, 11, 11]

#guard (Silmaril.Wasm.Binaryen.Exe.encodeModule? program).toOption == some wasmBytes

end Silmaril.WasmSpec.MergeSort
