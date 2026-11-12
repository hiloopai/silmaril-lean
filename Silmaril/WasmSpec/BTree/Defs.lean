module

public import Silmaril.Wasm.Wat
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce
public import Silmaril.Wasm.Logic.Words.Defs

/-!
# The B-tree library of Wasm Logic (Watt et al., ECOOP 2019): program and specifications

The paper's verified example (its §4) is a B-tree
library over **ordered, bounded arrays** (OBAs). This entry states the paper's predicates and
specifications over silmaril-lean's Core 3.0 semantics and the `i32` view of
`Silmaril.Wasm.Logic.Words`, with Silmaril's every-run logic (`TFSpecAt`, total correctness, where
the paper's triples are partial correctness), and quotes a program (`btree.wat`) with:

* `oba_get(x, k)` (function `0`, the paper's `OBAGet`, Figure 12): the `k`-th element;
* `oba_find(x, e)` (function `1`, `OBAFind`, Figure 13): the first index whose element is
  not below `e` (the loads of `OBAGet` are inlined; the paper calls it);
* `btree_search(k)` (function `2`, `BTreeSearch`, Figure 14): descend from the root page,
  using `oba_find`/`oba_get` on the node's keys and pointers (CLRS `B-TREE-SEARCH`).

The paper's code for the B-tree operations is in its technical report (arXiv 1811.03479v3,
Appendix B.5, not vendored; hashes in the paper's `notes.md`). `btree_search` here follows the
report's `BTreeSearch`/`BTreeSearchRec` (§B.5.2): the same layout, leaf convention, calls of
`OBAFind` on the keys and the same tests, except that the report descends by a recursive call
of `BTreeSearchRec` and reads keys and pointers through `GetNodeKey`/`GetNodePtr`/`GetNodeLeaf`
wrappers, while this version descends in a loop and calls `oba_get` directly.
`btree_create`, `btree_insert` (with node splitting and page allocation) and `oba_insert`/
`oba_delete` are **not implemented here**; their specifications are stated (`CreateSpec`,
`InsertSpec`) for any implementation.

## Layout (paper §4.1–4.2)

* `OBA B x n α`: the word at `x` is the length of `α`, the next `|α|` words are `α`, ordered
  (`SortedS`, signed), `|α| ≤ n` and `x + 4 + 4 n ≤ INT32_MAX`; `BA` drops the ordering;
  `OBAnd` adds no duplicates. (Ownership of the over-allocated cells is not tracked: this is
  not a separation logic, see `Silmaril.Wasm.Logic.Words`.)
* page `x` of a node: the word at `65536 x` is the leaf indicator (nonzero: a leaf, as in the
  report's `BTreeRec` and `BTreeSearchRec`; the paper's §4.2 text says the opposite), the
  keys are an `OBAnd` at `65536 x + 4` (at most 8090), the child pointers (page numbers) a `BA`
  at `65536 x + 32768` (at most 8091); the metadata page `0` holds the branching factor `t` at
  `0` and the root page `r` at `4` (the paper's free-page list is not modelled).
* `Tree`: abstract B-tree nodes; `Repr B x T`: page `x` represents `T`; `Ordered lo hi T`
  (keys strictly increasing, within bounds, children between keys), `Balanced t d T`
  (key counts `t - 1 ≤ |keys| ≤ 2 t - 1` below the root, all leaves at depth `d`);
  `IsBTree B t κ`: the metadata and a represented, ordered, balanced tree with key set `κ`.

A Silmaril addition (the predicates transcribe the paper's; the code is new).
-/

@[expose] public section

namespace Silmaril.WasmSpec.BTree

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Logic.Hoare (FSpec)

/-- **The module.** -/
def program := wat3! r#"
(module
  (memory (export "memory") 1)
  (func $oba_get (export "oba_get") (param $x i32) (param $k i32) (result i32)
    (i32.load offset=4 (i32.add (local.get $x) (i32.mul (local.get $k) (i32.const 4)))))
  (func $oba_find (export "oba_find") (param $x i32) (param $e i32) (result i32)
    (local $i i32)
    (block $done
      (loop $next
        (br_if $done (i32.ge_u (local.get $i) (i32.load (local.get $x))))
        (br_if $done (i32.ge_s
          (i32.load offset=4 (i32.add (local.get $x) (i32.mul (local.get $i) (i32.const 4))))
          (local.get $e)))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $next)))
    (local.get $i))
  (func $btree_search (export "btree_search") (param $k i32) (result i32)
    (local $x i32) (local $i i32) (local $keys i32)
    (local.set $x (i32.load (i32.const 4)))
    (block $never
      (loop $descend
        (local.set $keys (i32.add (i32.mul (local.get $x) (i32.const 65536)) (i32.const 4)))
        (local.set $i (call $oba_find (local.get $keys) (local.get $k)))
        (if (i32.lt_u (local.get $i) (i32.load (local.get $keys)))
          (then
            (if (i32.eq (call $oba_get (local.get $keys) (local.get $i)) (local.get $k))
              (then (return (i32.const 1))))))
        (if (i32.load (i32.mul (local.get $x) (i32.const 65536)))
          (then (return (i32.const 0))))
        (local.set $x (call $oba_get
          (i32.add (i32.mul (local.get $x) (i32.const 65536)) (i32.const 32768)) (local.get $i)))
        (br $descend)))
    (i32.const 0)))
"#

/-- The store after instantiating the module against no imports. -/
def store₀ : Store Nat :=
  match instantiateOnce? ({} : Store Nat) program [] with
  | some (s, _, _) => s
  | none => {}

/-- `oba_get`. -/
def getFunc : Func := program.funcs[0]

/-- `oba_find`. -/
def findFunc : Func := program.funcs[1]

/-- `btree_search`. -/
def searchFunc : Func := program.funcs[2]

/-! ## Ordered, bounded arrays -/

/-- `INT32_MAX`. -/
abbrev int32Max : Nat := 2 ^ 31 - 1

/-- **A bounded array** at `x` of capacity `n` holding `α`. -/
def BA (B : ByteArray) (x n : Nat) (α : List (BitVec 32)) : Prop :=
  wd B x = BitVec.ofNat 32 α.length ∧ words B (x + 4) α.length = α ∧ α.length ≤ n ∧
    x + 4 + 4 * n ≤ int32Max ∧ x + 4 + 4 * n ≤ B.size

/-- **An ordered, bounded array** (the paper's `OBA(x, n, α)`). -/
def OBA (B : ByteArray) (x n : Nat) (α : List (BitVec 32)) : Prop := BA B x n α ∧ SortedS α

/-- An ordered, bounded array without duplicates (`OBA_nd`). -/
def OBAnd (B : ByteArray) (x n : Nat) (α : List (BitVec 32)) : Prop := OBA B x n α ∧ α.Nodup

variable {H : Type}

/-- **`OBAGet`** (Figure 12): `{[x, k] | OBA(x, n, α) ∧ 0 ≤ k < |α|} oba_get {[α!k] | OBA(x, n, α)}`;
here the store is unchanged and the call terminates in every run. -/
def getSpec (a : Nat) (fi : FuncInst H) : FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ ∃ (x k : BitVec 32) (ma : Nat) (mt : MemoryType)
    (B : ByteArray) (n : Nat) (α : List (BitVec 32)), args = [.i32 x, .i32 k] ∧
    MemAt s fi.module ma mt B ∧ OBA B x.toNat n α ∧ k.toNat < α.length
  post s args s' o := s' = s ∧ ∀ (x k : BitVec 32) (ma : Nat) (mt : MemoryType) (B : ByteArray)
    (n : Nat) (α : List (BitVec 32)), args = [.i32 x, .i32 k] → MemAt s fi.module ma mt B →
    OBA B x.toNat n α → k.toNat < α.length → o = .normal [.i32 (α.getD k.toNat 0)]

/-- What `OBAFind` returns (Figure 13): the first index `i ≤ |α|` with every element before it
below `e` and every element from it on at least `e`. -/
def FindsAt (α : List (BitVec 32)) (e : BitVec 32) (i : Nat) : Prop :=
  i ≤ α.length ∧ (∀ j < i, (α.getD j 0).toInt < e.toInt) ∧
    (∀ j, i ≤ j → j < α.length → e.toInt ≤ (α.getD j 0).toInt)

/-- **`OBAFind`** (Figure 13). -/
def findSpec (a : Nat) (fi : FuncInst H) : FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ ∃ (x e : BitVec 32) (ma : Nat) (mt : MemoryType)
    (B : ByteArray) (n : Nat) (α : List (BitVec 32)), args = [.i32 x, .i32 e] ∧
    MemAt s fi.module ma mt B ∧ OBA B x.toNat n α
  post s args s' o := s' = s ∧ ∀ (x e : BitVec 32) (ma : Nat) (mt : MemoryType) (B : ByteArray)
    (n : Nat) (α : List (BitVec 32)), args = [.i32 x, .i32 e] → MemAt s fi.module ma mt B →
    OBA B x.toNat n α → ∃ i, FindsAt α e i ∧ o = .normal [.i32 (BitVec.ofNat 32 i)]

/-! ## B-trees -/

/-- Abstract B-tree nodes: the leaf flag, the keys and the children. -/
inductive Tree where
  | node (leaf : Bool) (keys : List (BitVec 32)) (children : List Tree)

/-- The bytes per page. -/
abbrev page : Nat := 65536

/-- **Page `x` represents the tree `T`** (the paper's `Node(x, λ, κ, π)` and `BTreeRec`): the
leaf indicator, the keys as an `OBAnd`, and for an inner node the child pages as a `BA`, each
representing its child. -/
inductive Repr (B : ByteArray) : Nat → Tree → Prop where
  | leaf {x : Nat} {ks : List (BitVec 32)} (hl : wd B (page * x) ≠ 0)
      (hk : OBAnd B (page * x + 4) 8090 ks) : Repr B x (.node true ks [])
  | inner {x : Nat} {ks : List (BitVec 32)} {cs : List Tree} {ps : List (BitVec 32)}
      (hl : wd B (page * x) = 0) (hk : OBAnd B (page * x + 4) 8090 ks)
      (hp : BA B (page * x + 32768) 8091 ps) (hlen : ps.length = cs.length)
      (hc : ∀ i (h₁ : i < ps.length) (h₂ : i < cs.length), Repr B ps[i].toNat cs[i]) :
      Repr B x (.node false ks cs)

/-- `k` is a key of the tree. -/
inductive InTree (k : BitVec 32) : Tree → Prop where
  | here {l : Bool} {ks : List (BitVec 32)} {cs : List Tree} (h : k ∈ ks) :
      InTree k (.node l ks cs)
  | child {l : Bool} {ks : List (BitVec 32)} {cs : List Tree} {c : Tree} (hc : c ∈ cs)
      (h : InTree k c) : InTree k (.node l ks cs)

/-- `lo < x < hi`, for optional (signed) bounds. -/
def Within (lo hi : Option (BitVec 32)) (x : BitVec 32) : Prop :=
  (∀ l, lo = some l → l.toInt < x.toInt) ∧ (∀ h, hi = some h → x.toInt < h.toInt)

/-- **Search-tree order**: the keys are strictly increasing and within `(lo, hi)`; an inner
node has one child more than keys, child `i` lying between keys `i - 1` and `i`. -/
inductive Ordered : Option (BitVec 32) → Option (BitVec 32) → Tree → Prop where
  | mk {lo hi : Option (BitVec 32)} {l : Bool} {ks : List (BitVec 32)} {cs : List Tree}
      (hs : ks.Pairwise fun a b => a.toInt < b.toInt) (hw : ∀ k ∈ ks, Within lo hi k)
      (hlen : l = false → cs.length = ks.length + 1)
      (hc : ∀ i (h : i < cs.length), Ordered (if i = 0 then lo else ks[i - 1]?)
        (if i = ks.length then hi else ks[i]?) cs[i]) :
      Ordered lo hi (.node l ks cs)

/-- **Balance** with branching factor `t`: every leaf at depth `d` below this node, and
`t - 1 ≤ |keys| ≤ 2 t - 1` for every node except the root (`root`), which has at most
`2 t - 1` keys. -/
inductive Balanced (t : Nat) : Bool → Nat → Tree → Prop where
  | leaf {root : Bool} {ks : List (BitVec 32)} (hk : (root ∨ t - 1 ≤ ks.length) ∧ ks.length ≤ 2 * t - 1) :
      Balanced t root 0 (.node true ks [])
  | inner {root : Bool} {d : Nat} {ks : List (BitVec 32)} {cs : List Tree}
      (hk : (root ∨ t - 1 ≤ ks.length) ∧ ks.length ≤ 2 * t - 1)
      (hc : ∀ c ∈ cs, Balanced t false d c) : Balanced t root (d + 1) (.node false ks cs)

/-- **`BTree(t, κ)`** (paper §4.2): page `0` holds `t` and the root page `r`; page `r`
represents an ordered, balanced tree whose keys are `κ`; `2 ≤ t ≤ 4095`. -/
def IsBTree (B : ByteArray) (t : Nat) (κ : BitVec 32 → Prop) : Prop :=
  2 ≤ t ∧ t ≤ 4095 ∧ wd B 0 = BitVec.ofNat 32 t ∧ ∃ (T : Tree) (d : Nat),
    Repr B (wd B 4).toNat T ∧ Ordered none none T ∧ Balanced t true d T ∧ ∀ k, InTree k T ↔ κ k

/-- **`BTreeSearch`** (Figure 14): `{[k] | BTree(t, κ)} btree_search {∃ b. [b] | BTree(t, κ) ∧
(k ∈ κ ⇒ b = 1) ∧ (k ∉ κ ⇒ b = 0)}`; here the store is unchanged. -/
def searchSpec (a : Nat) (fi : FuncInst H) : FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ ∃ (k : BitVec 32) (ma : Nat) (mt : MemoryType)
    (B : ByteArray) (t : Nat) (κ : BitVec 32 → Prop), args = [.i32 k] ∧
    MemAt s fi.module ma mt B ∧ IsBTree B t κ
  post s args s' o := s' = s ∧ ∀ (k : BitVec 32) (ma : Nat) (mt : MemoryType) (B : ByteArray)
    (t : Nat) (κ : BitVec 32 → Prop), args = [.i32 k] → MemAt s fi.module ma mt B →
    IsBTree B t κ → ∃ b : BitVec 32, o = .normal [.i32 b] ∧ (κ k → b = 1) ∧ (¬ κ k → b = 0)

/-- **`BTreeInsert`** (Figure 14): `{[k] | BTree(t, κ)} btree_insert {[] | BTree(t, κ ∪ {k})}`,
read as every-run partial correctness (as in the paper); memory `0` may grow. -/
def insertSpec (a : Nat) (fi : FuncInst H) : FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ ∃ (k : BitVec 32) (ma : Nat) (mt : MemoryType)
    (B : ByteArray) (t : Nat) (κ : BitVec 32 → Prop), args = [.i32 k] ∧
    MemAt s fi.module ma mt B ∧ IsBTree B t κ
  post s args s' o := ∀ (k : BitVec 32) (ma : Nat) (mt : MemoryType) (B : ByteArray) (t : Nat)
    (κ : BitVec 32 → Prop), args = [.i32 k] → MemAt s fi.module ma mt B → IsBTree B t κ →
    o = .normal [] ∧ ∃ (mt' : MemoryType) (B' : ByteArray), MemAt s' fi.module ma mt' B' ∧
      IsBTree B' t (fun k' => κ k' ∨ k' = k)

/-- **`BTreeCreate`** (Figure 14): `{[t] | size(0) ∧ 2 ≤ t ≤ 4095} btree_create
{[] | BTree(t, ∅)}`, every-run partial correctness. -/
def createSpec (a : Nat) (fi : FuncInst H) : FSpec H where
  pre s args := s.funcs[a]? = some fi ∧ ∃ (t : BitVec 32) (ma : Nat) (mt : MemoryType),
    args = [.i32 t] ∧ MemAt s fi.module ma mt ByteArray.empty ∧ 2 ≤ t.toNat ∧ t.toNat ≤ 4095
  post _ args s' o := ∀ (t : BitVec 32), args = [.i32 t] →
    o = .normal [] ∧ ∃ (ma : Nat) (mt' : MemoryType) (B' : ByteArray),
      MemAt s' fi.module ma mt' B' ∧ IsBTree B' t.toNat (fun _ => False)

open Silmaril.Wasm.Numerics Silmaril.Wasm.Validation in
/-- **Specification of `oba_get` and `oba_find`** (proved): every instance running them meets
`getSpec`/`findSpec` for total correctness, at every profile and host relation. -/
def OBASpec : Prop :=
  ∀ {H : Type} (P : Profile) (host : HostSemantics H) (a : Nat) (fi : FuncInst H)
    (ps rs : Ty (.list .val)), Expand fi.type (.func ps rs) → ps.length = 2 → rs.length = 1 →
    (fi.code = .wasm getFunc → Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (getSpec a fi)) ∧
    (fi.code = .wasm findFunc → Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (findSpec a fi))

open Silmaril.Wasm.Numerics Silmaril.Wasm.Validation in
/-- **Specification of `btree_search`** (stated, not proved): every instance running it, whose
function indices `0` and `1` resolve to `oba_get` and `oba_find` instances of its module
(addresses `aG`, `aF`), meets `searchSpec` for total correctness. -/
def SearchSpec : Prop :=
  ∀ {H : Type} (P : Profile) (host : HostSemantics H) (a aG aF : Nat) (fi fiG fiF : FuncInst H)
    (ps rs : Ty (.list .val)), fi.code = .wasm searchFunc → Expand fi.type (.func ps rs) →
    ps.length = 1 → rs.length = 1 → fi.module.funcs[0]? = some aG →
    fi.module.funcs[1]? = some aF → Silmaril.Wasm.Logic.Hoare.TFSpecAt P host aG (getSpec aG fiG) →
    Silmaril.Wasm.Logic.Hoare.TFSpecAt P host aF (findSpec aF fiF) → fiG.module = fi.module →
    fiF.module = fi.module →
    (∀ s args, (searchSpec a fi).pre s args → s.funcs[aG]? = some fiG ∧ s.funcs[aF]? = some fiF) →
    Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a (searchSpec a fi)

open Silmaril.Wasm.Numerics in
/-- **The insert and create specifications for a given implementation** `c` (stated; this
entry has no implementation). -/
def InsertCreateSpec (cInsert cCreate : Func) : Prop :=
  ∀ {H : Type} (P : Profile) (host : HostSemantics H) (a : Nat) (fi : FuncInst H),
    (fi.code = .wasm cInsert → Silmaril.Wasm.Logic.Hoare.FSpecValid P host a (insertSpec a fi)) ∧
    (fi.code = .wasm cCreate → Silmaril.Wasm.Logic.Hoare.FSpecValid P host a (createSpec a fi))

end Silmaril.WasmSpec.BTree
