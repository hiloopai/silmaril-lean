module

public import Silmaril.Wasm.Wat
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce
public import Silmaril.Wasm.Logic.Words.Defs

/-!
# `merge_sort`: recursive merge sort of an `i32` array segment (program and specification)

`program` (quoted from `merge_sort.wat`) is a Core 3.0 module with two functions:

* `merge(p, m, n, t)` (function `0`): the words `a[0..m)` and `a[m..n)` at `p` are sorted;
  merge them into the scratch buffer `t[0..n)` (taking the left element on ties), then copy
  the buffer back to `a[0..n)`;
* `merge_sort(p, n, t)` (function `1`): if `n ≥ 2`, sort `a[0..m)` and `a[m..n)` (with
  `m = n / 2`) by recursive calls, then `merge(p, m, n, t)`.

Specifications (`Silmaril.Wasm.Logic.Hoare.FSpec`, read with `TFSpecAt`: every-run total
correctness): `mergeSpec` and `sortSpec`. Both require the array `[p, p + 4 n)` and the buffer
`[t, t + 4 n)` to be disjoint, inside memory `0` and without address wrap-around; both
guarantee that the call returns no values (never traps) and that the final store is the
initial one with memory `0` replaced by bytes `B'` that agree with the input bytes `B` outside
the array and the buffer, where the array's words are sorted (signed) and a permutation of the
input's (for `merge`: of the two sorted halves). `sortSpec` also requires the module's function
indices `0` and `1` to resolve to `merge` and to the function itself (`Linked`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.WasmSpec.MergeSort

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Hoare (FSpec)

/-- **The module.** -/
def program := wat3! r#"
(module
  (memory (export "memory") 1)
  (func $merge (export "merge") (param $p i32) (param $m i32) (param $n i32) (param $t i32)
    (local $i i32) (local $j i32) (local $k i32) (local $l i32)
    (local.set $j (local.get $m))
    (block $done
      (loop $step
        (br_if $done (i32.ge_u (local.get $k) (local.get $n)))
        (if (i32.ge_u (local.get $j) (local.get $n))
          (then (local.set $l (i32.const 1)))
          (else
            (if (i32.ge_u (local.get $i) (local.get $m))
              (then (local.set $l (i32.const 0)))
              (else
                (local.set $l (i32.le_s
                  (i32.load (i32.add (local.get $p) (i32.mul (local.get $i) (i32.const 4))))
                  (i32.load (i32.add (local.get $p) (i32.mul (local.get $j) (i32.const 4))))))))))
        (if (local.get $l)
          (then
            (i32.store (i32.add (local.get $t) (i32.mul (local.get $k) (i32.const 4)))
              (i32.load (i32.add (local.get $p) (i32.mul (local.get $i) (i32.const 4)))))
            (local.set $i (i32.add (local.get $i) (i32.const 1))))
          (else
            (i32.store (i32.add (local.get $t) (i32.mul (local.get $k) (i32.const 4)))
              (i32.load (i32.add (local.get $p) (i32.mul (local.get $j) (i32.const 4)))))
            (local.set $j (i32.add (local.get $j) (i32.const 1)))))
        (local.set $k (i32.add (local.get $k) (i32.const 1)))
        (br $step)))
    (local.set $k (i32.const 0))
    (block $copied
      (loop $copy
        (br_if $copied (i32.ge_u (local.get $k) (local.get $n)))
        (i32.store (i32.add (local.get $p) (i32.mul (local.get $k) (i32.const 4)))
          (i32.load (i32.add (local.get $t) (i32.mul (local.get $k) (i32.const 4)))))
        (local.set $k (i32.add (local.get $k) (i32.const 1)))
        (br $copy))))
  (func $merge_sort (export "merge_sort") (param $p i32) (param $n i32) (param $t i32)
    (local $m i32)
    (block $done
      (br_if $done (i32.lt_u (local.get $n) (i32.const 2)))
      (local.set $m (i32.shr_u (local.get $n) (i32.const 1)))
      (call $merge_sort (local.get $p) (local.get $m) (local.get $t))
      (call $merge_sort (i32.add (local.get $p) (i32.mul (local.get $m) (i32.const 4)))
        (i32.sub (local.get $n) (local.get $m)) (local.get $t))
      (call $merge (local.get $p) (local.get $m) (local.get $n) (local.get $t)))))
"#

/-- The store after instantiating the module against no imports; `merge` is function `0`,
`merge_sort` function `1`. -/
def store₀ : Store Nat :=
  match instantiateOnce? ({} : Store Nat) program [] with
  | some (s, _, _) => s
  | none => {}

/-- The function `merge`. -/
def mergeFunc : Func := program.funcs[0]

/-- The function `merge_sort`. -/
def sortFunc : Func := program.funcs[1]

/-! ## The code as abstract syntax (checked equal to the quoted one by `rfl`)

Locals of `merge`: `0 p, 1 m, 2 n, 3 t, 4 i, 5 j, 6 k, 7 l`. -/

/-- `l := (a[i] ≤ a[j])`. -/
def cmpCode : List Instr :=
  [lget 0, lget 4, c32 4, imul, iadd, iload, lget 0, lget 5, c32 4, imul, iadd, iload, iles,
   lset 7]

/-- Decide which side to take: `l := 1` if the right side is exhausted, `l := 0` if the left
one is, else `l := (a[i] ≤ a[j])`. -/
def chooseCode : List Instr :=
  [lget 5, lget 2, igeu,
   .if_ .empty [c32 1, lset 7]
     [lget 4, lget 1, igeu, .if_ .empty [c32 0, lset 7] cmpCode]]

/-- `t[k] := a[i]; i := i + 1`. -/
def takeLeft : List Instr :=
  [lget 3, lget 6, c32 4, imul, iadd, lget 0, lget 4, c32 4, imul, iadd, iload, istore,
   lget 4, c32 1, iadd, lset 4]

/-- `t[k] := a[j]; j := j + 1`. -/
def takeRight : List Instr :=
  [lget 3, lget 6, c32 4, imul, iadd, lget 0, lget 5, c32 4, imul, iadd, iload, istore,
   lget 5, c32 1, iadd, lset 5]

/-- After choosing: take a side, `k := k + 1`, repeat. -/
def takeCode : List Instr :=
  [lget 7, .if_ .empty takeLeft takeRight, lget 6, c32 1, iadd, lset 6, br 0]

/-- The merge loop body. -/
def mergeBody : List Instr := [lget 6, lget 2, igeu, brIf 1] ++ chooseCode ++ takeCode

/-- The copy loop body: `a[k] := t[k]`. -/
def copyBody : List Instr :=
  [lget 6, lget 2, igeu, brIf 1,
   lget 0, lget 6, c32 4, imul, iadd, lget 3, lget 6, c32 4, imul, iadd, iload, istore,
   lget 6, c32 1, iadd, lset 6, br 0]

/-- The copy loop and what follows it. -/
def copyCode : List Instr := [c32 0, lset 6, while_ copyBody]

/-- The body of `merge`. -/
def mergeCode : List Instr := [lget 1, lset 5, while_ mergeBody] ++ copyCode

/-- The recursive calls and the merge (locals of `merge_sort`: `0 p, 1 n, 2 t, 3 m`). -/
def callsCode : List Instr :=
  [lget 1, c32 1, ishru, lset 3,
   lget 0, lget 3, lget 2, call 1,
   lget 0, lget 3, c32 4, imul, iadd, lget 1, lget 3, isub, lget 2, call 1,
   lget 0, lget 3, lget 1, lget 2, call 0]

/-- The body of `merge_sort`. -/
def sortCode : List Instr := [.block .empty ([lget 1, c32 2, iltu, brIf 0] ++ callsCode)]

/-! ## Specifications -/

variable {H : Type}

/-- The common layout: memory `0` of `mi` holds `B`; the array `[p, p + 4 n)` and the buffer
`[t, t + 4 n)` are disjoint, inside `B`, and do not wrap. -/
def Layout {H : Type} (s : Store H) (mi : ModuleInst) (ma : Nat) (mt : MemoryType) (B : ByteArray)
    (p n t : BitVec 32) : Prop :=
  MemAt s mi ma mt B ∧ p.toNat + 4 * n.toNat ≤ B.size ∧ t.toNat + 4 * n.toNat ≤ B.size ∧
    p.toNat + 4 * n.toNat < 2 ^ 32 ∧ t.toNat + 4 * n.toNat < 2 ^ 32 ∧
    (p.toNat + 4 * n.toNat ≤ t.toNat ∨ t.toNat + 4 * n.toNat ≤ p.toNat)

/-- What `merge` and `merge_sort` may leave: `B'` agrees with `B` outside the array and the
buffer, and the array's words are sorted and a permutation of `B`'s. -/
def Sorts (B B' : ByteArray) (p n t : Nat) : Prop :=
  SameOutside2 B B' p (4 * n) t (4 * n) ∧ SortedS (words B' p n) ∧
    (words B' p n).Perm (words B p n)

/-- The postcondition shared by both functions. -/
def Post (fi : FuncInst H) (s : Store H) (args : List Val) (s' : Store H)
    (o : Silmaril.Wasm.Logic.Core.Outcome) : Prop :=
  ∀ (p m n t : BitVec 32) (ma : Nat) (mt : MemoryType) (B : ByteArray),
    (args = [.i32 p, .i32 m, .i32 n, .i32 t] ∨ (args = [.i32 p, .i32 n, .i32 t] ∧ m = 0)) →
    MemAt s fi.module ma mt B →
    o = .normal [] ∧ ∃ B', s' = s.setMem ma ⟨mt, B'⟩ ∧ Sorts B B' p.toNat n.toNat t.toNat

/-- **The specification of `merge`**: both halves sorted, `m ≤ n`. -/
def mergeSpec (a : Nat) (fi : FuncInst H) : FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ ∃ (p m n t : BitVec 32) (ma : Nat) (mt : MemoryType)
    (B : ByteArray), args = [.i32 p, .i32 m, .i32 n, .i32 t] ∧ Layout s fi.module ma mt B p n t ∧
    m.toNat ≤ n.toNat ∧ SortedS (words B p.toNat m.toNat) ∧
    SortedS (words B (p.toNat + 4 * m.toNat) (n.toNat - m.toNat))
  post := Post fi

open Silmaril.Wasm.Validation in
/-- The module's function indices `0` and `1` resolve to `merge` (at `aM`, the instance `fiM`
of the same module instance, of type `[i32 i32 i32 i32] → []`) and to the function at `a`. -/
def Linked (a : Nat) (fi : FuncInst H) (aM : Nat) (fiM : FuncInst H) : Prop :=
  fi.module.funcs[0]? = some aM ∧ fi.module.funcs[1]? = some a ∧ fiM.code = .wasm mergeFunc ∧
    fiM.module = fi.module ∧
    ∃ ps rs : Ty (.list .val), Expand fiM.type (.func ps rs) ∧ ps.length = 4 ∧ rs.length = 0

/-- **The specification of `merge_sort`.** -/
def sortSpec (a : Nat) (fi : FuncInst H) (aM : Nat) (fiM : FuncInst H) : FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ s.funcs[aM]? = some fiM ∧
    ∃ (p n t : BitVec 32) (ma : Nat) (mt : MemoryType) (B : ByteArray),
      args = [.i32 p, .i32 n, .i32 t] ∧ Layout s fi.module ma mt B p n t
  post := Post fi

open Silmaril.Wasm.Numerics Silmaril.Wasm.Validation in
/-- **Specification of `merge`**, for every instance running it (four parameters, no
results), at every profile and host relation. -/
def MergeSpec : Prop :=
  ∀ {H : Type} (P : Profile) (host : HostSemantics H) (a : Nat) (fi : FuncInst H)
    (ps rs : Ty (.list .val)), fi.code = .wasm mergeFunc → Expand fi.type (.func ps rs) →
    ps.length = 4 → rs.length = 0 → Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (mergeSpec a fi)

open Silmaril.Wasm.Numerics Silmaril.Wasm.Validation in
/-- **Specification of `merge_sort`**, for every instance running it (three parameters, no
results) linked to a `merge`, at every profile and host relation. -/
def Spec : Prop :=
  ∀ {H : Type} (P : Profile) (host : HostSemantics H) (a : Nat) (fi : FuncInst H) (aM : Nat)
    (fiM : FuncInst H) (ps rs : Ty (.list .val)), fi.code = .wasm sortFunc →
    Expand fi.type (.func ps rs) → ps.length = 3 → rs.length = 0 → Linked a fi aM fiM →
    Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (sortSpec a fi aM fiM)

open Silmaril.Wasm.Numerics in
/-- **The instantiated program**: function `1` of `store₀` meets `sortSpec` with `merge` at
`0`. -/
def SpecStore : Prop :=
  ∃ fiM fi : FuncInst Nat, store₀.funcs = [fiM, fi] ∧
    ∀ (P : Profile) (host : HostSemantics Nat),
      Silmaril.Wasm.Logic.Hoare.TFSpecAt P host 1 (sortSpec 1 fi 0 fiM)

end Silmaril.WasmSpec.MergeSort
