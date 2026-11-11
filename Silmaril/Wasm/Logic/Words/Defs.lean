module

public import Silmaril.Wasm.Logic.Memory.Defs
public import Silmaril.Wasm.Logic.Total.Defs

/-!
# `i32` words, arrays and an `i32` view of frames: definitions

Program proofs about code that keeps `i32` values in its locals and an array of `i32` words in
linear memory (sorting, searching, scanning) want to talk about **words**, not bytes. This file
gives the view; the lemmas and the every-run rules over it are in `Silmaril.Wasm.Logic.Words.Thms`.

* `wd B a`: the little-endian `i32` at byte `a` of the memory bytes `B` (`0` out of bounds);
  `wr B a v`: the bytes after writing `v` at `a`;
* `words B p n`: the `n` words at `p, p + 4, …` as a list (an `i32` array segment);
* `SameOutside B B' p len`: `B'` has the size of `B` and the same bytes outside `[p, p + len)`;
* `fr mi L`: a frame of module instance `mi` whose locals are the `i32` values `L`; `loc f k`
  the `i32` local `k` as a natural number (for loop variants);
* `MemAt s mi ma mt B`: memory `0` of `mi` is the store's memory at address `ma`, of type `mt`,
  holding the bytes `B`;
* `SortedS`: a list of words sorted by signed (`i32.lt_s`) order.

`wd`, `wr` and `words` are generalised from the LRAT example
(`Silmaril.Wasm.Examples.LRAT.Defs`, where they are fixed to one 64 KiB memory). A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Words

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core

/-- The `i32` word at byte `a` (little-endian; `0` out of bounds). -/
def wd (B : ByteArray) (a : Nat) : BitVec 32 := (Memory.load B a 4).getD 0

/-- Write the `i32` word `v` at byte `a`. -/
def wr (B : ByteArray) (a : Nat) (v : BitVec 32) : ByteArray :=
  Silmaril.Wasm.Logic.Core.storeLE B a 4 v.toNat

/-- The `n` words at `p, p + 4, …, p + 4 (n - 1)`. -/
def words (B : ByteArray) (p n : Nat) : List (BitVec 32) :=
  (List.range n).map fun k => wd B (p + 4 * k)

/-- Write the words `xs` at `p, p + 4, …` (for tests and initial memories). -/
def writeWords (B : ByteArray) (p : Nat) : List (BitVec 32) → ByteArray
  | [] => B
  | x :: xs => writeWords (wr B p x) (p + 4) xs

/-- `B'` has the size of `B` and the same bytes outside `[p, p + len)`. -/
def SameOutside (B B' : ByteArray) (p len : Nat) : Prop :=
  B'.size = B.size ∧ ∀ i, i < p ∨ p + len ≤ i → B'.data.toList[i]? = B.data.toList[i]?

/-- `B'` has the size of `B` and the same bytes outside `[p, p + len) ∪ [q, q + len')` (an
array and a scratch buffer). -/
def SameOutside2 (B B' : ByteArray) (p len q len' : Nat) : Prop :=
  B'.size = B.size ∧ ∀ i, i < p ∨ p + len ≤ i → i < q ∨ q + len' ≤ i →
    B'.data.toList[i]? = B.data.toList[i]?

/-- A frame of module instance `mi` whose locals are the `i32` values `L`. -/
def fr (mi : ModuleInst) (L : List (BitVec 32)) : Frame :=
  ⟨L.map fun v => some (Val.i32 v), mi⟩

/-- The `i32` local `k` of a frame as a natural number (`0` if it is not an `i32`): for
variants of loops. -/
def loc (f : Frame) (k : Nat) : Nat :=
  match f.locals[k]? with
  | some (some (.num ⟨.int .i32, v⟩)) => v.toNat
  | _ => 0

/-- Memory `0` of `mi` is the store's memory at address `ma`, of type `mt`, with bytes `B`. -/
def MemAt {H : Type} (s : Store H) (mi : ModuleInst) (ma : Nat) (mt : MemoryType)
    (B : ByteArray) : Prop :=
  mi.mems[0]? = some ma ∧ s.mems[ma]? = some ⟨mt, B⟩

/-! ## Instruction shorthands

Program proofs state the code they verify with these and check it against the quoted module
by `rfl` (`wat3!` produces the same terms). -/

/-- `i32.const n`. -/
abbrev c32 (n : Nat) : Instr := .intConst .i32 (BitVec.ofNat 32 n)
/-- `local.get k`. -/
abbrev lget (k : Nat) : Instr := .localGet ⟨⟨k % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩
/-- `local.set k`. -/
abbrev lset (k : Nat) : Instr := .localSet ⟨⟨k % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩
/-- `local.tee k`. -/
abbrev ltee (k : Nat) : Instr := .localTee ⟨⟨k % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩
/-- `br l`. -/
abbrev br (l : Nat) : Instr := .br ⟨⟨l % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩
/-- `br_if l`. -/
abbrev brIf (l : Nat) : Instr := .brIf ⟨⟨l % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩
/-- `call x`. -/
abbrev call (x : Nat) : Instr := .call ⟨⟨x % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩
/-- `i32.add`, `i32.sub`, `i32.mul`, `i32.shr_u`. -/
abbrev iadd : Instr := .intBinOp .i32 .add
abbrev isub : Instr := .intBinOp .i32 .sub
abbrev imul : Instr := .intBinOp .i32 .mul
abbrev ishru : Instr := .intBinOp .i32 (.shr .unsigned)
/-- `i32` comparisons. -/
abbrev ieqz : Instr := .intTestOp .i32 .eqz
abbrev iltu : Instr := .intRelOp .i32 (.lt .unsigned)
abbrev igeu : Instr := .intRelOp .i32 (.ge .unsigned)
abbrev ilts : Instr := .intRelOp .i32 (.lt .signed)
abbrev iles : Instr := .intRelOp .i32 (.le .signed)
abbrev igts : Instr := .intRelOp .i32 (.gt .signed)
/-- `i32.load` and `i32.store` (memory `0`, alignment `2`, offset `0`). -/
abbrev iload : Instr := .intLoad .i32 none ⟨0⟩ ⟨2, 0⟩
abbrev istore : Instr := .intStore .i32 none ⟨0⟩ ⟨2, 0⟩
/-- `block (loop body)`, both of empty block type. -/
abbrev while_ (body : List Instr) : Instr := .block .empty [.loop .empty body]

/-- `i32` comparisons, stated on `BitVec 32` (silmaril-lean's `Numerics.intRelOp .i32` is
stated on `BitVec IntType.i32.width`, which `simp` does not see through). -/
def relOp32 : IntRelOp → BitVec 32 → BitVec 32 → BitVec 32
  | .eq, x, y => Numerics.bool32 (x == y)
  | .ne, x, y => Numerics.bool32 (x != y)
  | .lt .unsigned, x, y => Numerics.bool32 (decide (x.toNat < y.toNat))
  | .le .unsigned, x, y => Numerics.bool32 (decide (x.toNat ≤ y.toNat))
  | .gt .unsigned, x, y => Numerics.bool32 (decide (y.toNat < x.toNat))
  | .ge .unsigned, x, y => Numerics.bool32 (decide (y.toNat ≤ x.toNat))
  | .lt .signed, x, y => Numerics.bool32 (decide (x.toInt < y.toInt))
  | .le .signed, x, y => Numerics.bool32 (decide (x.toInt ≤ y.toInt))
  | .gt .signed, x, y => Numerics.bool32 (decide (y.toInt < x.toInt))
  | .ge .signed, x, y => Numerics.bool32 (decide (y.toInt ≤ x.toInt))

/-- Sorted (non-decreasing) in signed `i32` order. -/
def SortedS (l : List (BitVec 32)) : Prop := l.Pairwise fun x y => x.toInt ≤ y.toInt

instance (l : List (BitVec 32)) : Decidable (SortedS l) :=
  inferInstanceAs (Decidable (l.Pairwise fun x y => x.toInt ≤ y.toInt))

end Silmaril.Wasm.Logic.Words
