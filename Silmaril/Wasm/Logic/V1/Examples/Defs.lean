module

public import Silmaril.Wasm.Logic.V1.Derived.Thms

/-!
# Abstract predicates for the Wasm Logic case studies

The data-structure predicates of §4 and Appendix B of Watt, Maksimović,
Krishnaswami and Gardner: array segments, bounded arrays, ordered bounded
arrays with and without duplicates, and the memory pages a B-tree is laid out
in. In a separation logic these are just notation for a particular assertion,
and they are here too.

Addresses are natural numbers rather than i32, which is why the explicit
`x + 4 · (n + 1) ≤ INT32_MAX` bounds of the paper's definitions are kept: they
are what rules out a layout whose addresses would have wrapped.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1.Examples

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Logic.V1

/-- The largest positive i32. -/
def INT32_MAX : Nat := 2 ^ 31 - 1

/-- The i32 cell assertion, the paper's `τ₁ ↦_i32 τ₂`. -/
abbrev cell32 (a : Term Nat) (v : Term (BitVec 32)) : HAssert :=
  HAssert.cellNum (.int .i32) a v

/-- An i32 cell of unspecified contents, the paper's `τ ↦_i32 −`. -/
abbrev cell32Any (a : Term Nat) : HAssert := HAssert.cellNumAny (.int .i32) a

/-- `Aseg(x, α)`: the contents of `α` laid out as consecutive i32 cells from `x`. -/
def Aseg (x : Term Nat) (α : Term (List (BitVec 32))) : HAssert := fun ρ =>
  HAssert.iterRange 0 (α ρ).length
    (fun i => cell32 (fun ρ' => x ρ' + 4 * i) (fun ρ' => (α ρ')[i]!)) ρ

/-- The over-allocated tail of a bounded array of capacity `n` holding `α`. -/
def Aspare (x : Term Nat) (n : Term Nat) (α : Term (List (BitVec 32))) : HAssert := fun ρ =>
  HAssert.iterRange ((α ρ).length + 1) (n ρ + 1)
    (fun i => cell32Any (fun ρ' => x ρ' + 4 * i)) ρ

/-- `BA(x, n, α)`: a bounded array at `x` of capacity `n` holding `α`, with its
length in the leading i32 cell. -/
def BA (x : Term Nat) (n : Term Nat) (α : Term (List (BitVec 32))) : HAssert :=
  HAssert.and
    (HAssert.star (cell32 x (fun ρ => BitVec.ofNat 32 (α ρ).length))
      (HAssert.star (Aseg (fun ρ => x ρ + 4) α) (Aspare x n α)))
    (HAssert.pure fun ρ => (α ρ).length ≤ n ρ ∧ x ρ + 4 * (n ρ + 1) ≤ INT32_MAX)

/-- `Ordered(α)`: ascending order, as unsigned i32. -/
def Ordered (α : List (BitVec 32)) : Prop :=
  ∀ i j, j < α.length → i < j → (α[i]!).toNat ≤ (α[j]!).toNat

/-- `OBA(x, n, α)`: an ordered bounded array. -/
def OBA (x : Term Nat) (n : Term Nat) (α : Term (List (BitVec 32))) : HAssert :=
  HAssert.and (BA x n α) (HAssert.pure fun ρ => Ordered (α ρ))

/-- `OBA_nd(x, n, α)`: an ordered bounded array without duplicates. -/
def OBAnd (x : Term Nat) (n : Term Nat) (α : Term (List (BitVec 32))) : HAssert :=
  HAssert.and (OBA x n α) (HAssert.pure fun ρ => (α ρ).Nodup)

/-- `Page(a)`: ownership of the whole of memory page `a`, byte by byte.

The paper writes `⊛_{a·64k ≤ i < (a+1)·64k} (i ↦_i32 −)`, but `↦_i32` is four
consecutive byte cells, so as printed that is 65536 mutually overlapping
four-byte cells — unsatisfiable, and three bytes past the end of the page. Byte
ownership is the only satisfiable reading, and the one every use of `Page`
requires, since `Keys`, `Ptrs` and `Node` carve i32 arrays out of the page. -/
def Page (a : Term Nat) : HAssert :=
  HAssert.and
    (fun ρ => HAssert.iterRange (a ρ * Memory.pageSize) ((a ρ + 1) * Memory.pageSize)
      (fun i => HAssert.cellAny (fun _ => i)) ρ)
    (HAssert.pure fun ρ => (a ρ + 1) * Memory.pageSize ≤ INT32_MAX)

/-- The length of a bounded array's free-page list, chosen in the paper so that
it cannot overflow the metadata page: `64k / 4 - 3`. -/
def freeCapacity : Nat := 16381

/-- `Free(φ)`: the list of free pages, together with ownership of each of them. -/
def Free (φ : Term (List (BitVec 32))) : HAssert :=
  HAssert.star (OBAnd (fun _ => 8) (fun _ => freeCapacity) φ)
    (fun ρ => HAssert.iterRange 0 (φ ρ).length
      (fun i => Page (fun ρ' => ((φ ρ')[i]!).toNat)) ρ)

/-- `Meta(t, r, µ, φ)`: the B-tree metadata page — branching factor, root
address, memory size in pages, and free-page list. -/
def Meta (t r : Term (BitVec 32)) (μ : Term Nat) (φ : Term (List (BitVec 32))) : HAssert :=
  HAssert.star (cell32 (fun _ => 0) t)
    (HAssert.star (cell32 (fun _ => 4) r)
      (HAssert.star (HAssert.size μ) (Free φ)))

/-- The maximum number of keys a B-tree node can hold.

The paper gives two capacities and neither is consistent with its own statement
that "a B-tree node takes up an entire WebAssembly page in memory": §4.2 says
8090 keys and 8091 pointers, Appendix B.4 says 4095 and 4096. A `BA` of capacity
`n` owns `4 · (n + 1)` bytes, so with the paper's offsets — the leaf indicator at
`x · 64k`, the keys at `x · 64k + 4`, the pointers at `x · 64k + 32k` — a node
owns `4 + 4(K+1) + 4(P+1)` bytes, which is 64736 for §4.2's figures and 32776
for Appendix B.4's, against a page of 65536. The unique pair that fills a page
exactly, and that puts the end of the key array exactly at the `32k` the pointer
array starts from, is 8190 and 8191. We use those; §4.2's figures look like a
transcription slip for them.

The correction vindicates §4.2's *conclusion*: it says "the maximal branching
factor of our B-trees is 4095", and `2 · 4095 - 1 = 8189 ≤ 8190` while
`2 · 4096 - 1 = 8191 > 8190`, so 4095 is exactly the bound 8190 keys give. -/
def keyCapacity : Nat := 8190

/-- The maximum number of child pointers a B-tree node can hold. -/
def ptrCapacity : Nat := 8191

/-- The largest branching factor a node of this layout supports: a node holds at
most `2t - 1` keys, so `t ≤ 4095`, which is §4.2's figure. -/
def maxBranching : Nat := (keyCapacity + 1) / 2

/-- `Keys(x, κ)`: the key array of the node on page `x`. -/
def Keys (x : Term Nat) (κ : Term (List (BitVec 32))) : HAssert :=
  OBAnd (fun ρ => x ρ * Memory.pageSize + 4) (fun _ => keyCapacity) κ

/-- `Ptrs(x, π)`: the child-pointer array of the node on page `x`; unordered. -/
def Ptrs (x : Term Nat) (π : Term (List (BitVec 32))) : HAssert :=
  BA (fun ρ => x ρ * Memory.pageSize + 32768) (fun _ => ptrCapacity) π

/-- `Node(x, λ, κ, π)`: a B-tree node occupying the whole of page `x`, with leaf
indicator `λ`, keys `κ` and child pointers `π`. -/
def Node (x : Term Nat) (lf : Term (BitVec 32)) (κ π : Term (List (BitVec 32))) : HAssert :=
  HAssert.star (cell32 (fun ρ => x ρ * Memory.pageSize) lf)
    (HAssert.star (Keys x κ) (Ptrs x π))

end Silmaril.Wasm.Logic.V1.Examples
