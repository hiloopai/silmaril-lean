module

public import Silmaril.Wasm.Wat
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce
public import Silmaril.Wasm.Logic.Words.Defs

/-!
# `insertion_sort`: sorting an `i32` array segment in place (program and specification)

`program` (quoted from `insertion_sort.wat`) is a Core 3.0 module whose function
`insertion_sort(p, n)` sorts the `n` words at `p, p + 4, …` of memory `0` in signed order by
insertion: for `i = 1, …, n - 1` it saves `key = a[i]`, shifts the larger elements of the sorted
prefix `a[0..i)` one place up (`a[j] := a[j - 1]` while `j > 0` and `a[j - 1] > key`) and stores
`key` at `a[j]`.

`sortSpec a fi` (`Silmaril.Wasm.Logic.Hoare.FSpec`), read with `TFSpecAt` (every-run total
correctness): if `fi` is at `a`, the arguments are `p, n`, memory `0` of `fi`'s module (at store
address `ma`, of type `mt`) holds the bytes `B` with `p + 4 n ≤ |B|` and `p + 4 n < 2^32`, then
every run of the call terminates and returns no values, and the final store is the initial one
with memory `ma` replaced by bytes `B'` such that

* `B'` agrees with `B` outside `[p, p + 4 n)` (and has its size): `SameOutside`;
* `words B' p n` is sorted (`SortedS`, signed) and a permutation of `words B p n`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.InsertionSort

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Hoare (FSpec)

/-- **The module.** -/
def program := wat3! r#"
(module
  (memory (export "memory") 1)
  (func $insertion_sort (export "insertion_sort") (param $p i32) (param $n i32)
    (local $i i32) (local $j i32) (local $key i32)
    (local.set $i (i32.const 1))
    (block $done
      (loop $outer
        (br_if $done (i32.ge_u (local.get $i) (local.get $n)))
        (local.set $key
          (i32.load (i32.add (local.get $p) (i32.mul (local.get $i) (i32.const 4)))))
        (local.set $j (local.get $i))
        (block $placed
          (loop $inner
            (br_if $placed (i32.eqz (local.get $j)))
            (br_if $placed (i32.le_s
              (i32.load (i32.add (local.get $p)
                (i32.mul (i32.sub (local.get $j) (i32.const 1)) (i32.const 4))))
              (local.get $key)))
            (i32.store (i32.add (local.get $p) (i32.mul (local.get $j) (i32.const 4)))
              (i32.load (i32.add (local.get $p)
                (i32.mul (i32.sub (local.get $j) (i32.const 1)) (i32.const 4)))))
            (local.set $j (i32.sub (local.get $j) (i32.const 1)))
            (br $inner)))
        (i32.store (i32.add (local.get $p) (i32.mul (local.get $j) (i32.const 4)))
          (local.get $key))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $outer)))))
"#

/-- The store after instantiating the module against no imports; the sort is function `0`. -/
def store₀ : Store Nat :=
  match instantiateOnce? ({} : Store Nat) program [] with
  | some (s, _, _) => s
  | none => {}

/-- The function `insertion_sort`. -/
def sortFunc : Func := program.funcs[0]

/-- The comparison of the inner loop: leave when `a[j - 1] ≤ key`. -/
def innerCmp : List Instr :=
  [lget 0, lget 3, c32 1, isub, c32 4, imul, iadd, iload, lget 4, iles, brIf 1]

/-- The test of the inner loop: leave when `j = 0` or `a[j - 1] ≤ key`. -/
def innerTest : List Instr := [lget 3, ieqz, brIf 1] ++ innerCmp

/-- The shift: `a[j] := a[j - 1]`, `j := j - 1`, repeat. -/
def innerShift : List Instr :=
  [lget 0, lget 3, c32 4, imul, iadd,
   lget 0, lget 3, c32 1, isub, c32 4, imul, iadd, iload, istore,
   lget 3, c32 1, isub, lset 3, br 0]

/-- The inner loop (shift the larger elements up), as abstract syntax. -/
def innerBody : List Instr := innerTest ++ innerShift

/-- After the inner loop: store `key` at `a[j]`, `i := i + 1`, repeat. -/
def placeKey : List Instr :=
  [lget 0, lget 3, c32 4, imul, iadd, lget 4, istore, lget 2, c32 1, iadd, lset 2, br 0]

/-- The outer loop body. -/
def outerBody : List Instr :=
  [lget 2, lget 1, igeu, brIf 1,
   lget 0, lget 2, c32 4, imul, iadd, iload, lset 4, lget 2, lset 3,
   while_ innerBody] ++ placeKey

/-- The function body, as abstract syntax (checked equal to the quoted one by `rfl`). -/
def body : List Instr := [c32 1, lset 2, while_ outerBody]

variable {H : Type}

/-- The precondition: `fi` is at `a`; the arguments are `p, n`; memory `0` of `fi`'s module
holds `B`, which contains the segment, and the segment's addresses do not wrap. -/
def Pre (a : Nat) (fi : FuncInst H) (s : Store H) (args : List Val) : Prop :=
  s.funcs[a]? = some fi ∧ ∃ (p n : BitVec 32) (ma : Nat) (mt : MemoryType) (B : ByteArray),
    args = [.i32 p, .i32 n] ∧ MemAt s fi.module ma mt B ∧ p.toNat + 4 * n.toNat ≤ B.size ∧
    p.toNat + 4 * n.toNat < 2 ^ 32

/-- What a sort of the segment `[p, p + 4 n)` of `B` may leave: `B'` equals `B` outside the
segment, and the segment's words are sorted and a permutation of the original ones. -/
def Sorts (B B' : ByteArray) (p n : Nat) : Prop :=
  SameOutside B B' p (4 * n) ∧ SortedS (words B' p n) ∧ (words B' p n).Perm (words B p n)

/-- **The specification of `insertion_sort`.** -/
def sortSpec (a : Nat) (fi : FuncInst H) : FSpec H where
  pre := Pre a fi
  post s args s' o := ∀ (p n : BitVec 32) (ma : Nat) (mt : MemoryType) (B : ByteArray),
    args = [.i32 p, .i32 n] → MemAt s fi.module ma mt B →
    o = .normal [] ∧ ∃ B', s' = s.setMem ma ⟨mt, B'⟩ ∧ Sorts B B' p.toNat n.toNat

open Silmaril.Wasm.Numerics Silmaril.Wasm.Validation in
/-- **Specification**: every function instance running `insertion_sort` (two parameters, no
results), at any address, meets `sortSpec` for total correctness, at every profile and for
every host relation. -/
def Spec : Prop :=
  ∀ {H : Type} (P : Profile) (host : HostSemantics H) (a : Nat) (fi : FuncInst H)
    (ps rs : Ty (.list .val)), fi.code = .wasm sortFunc → Expand fi.type (.func ps rs) →
    ps.length = 2 → rs.length = 0 → Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (sortSpec a fi)

open Silmaril.Wasm.Numerics in
/-- **The instantiated program**: function `0` of `store₀` meets `sortSpec`. -/
def SpecStore : Prop :=
  ∃ fi : FuncInst Nat, store₀.funcs[0]? = some fi ∧
    ∀ (P : Profile) (host : HostSemantics Nat), Silmaril.Wasm.Logic.Hoare.TFSpecAt P host 0 (sortSpec 0 fi)

end Silmaril.WasmSpec.InsertionSort
