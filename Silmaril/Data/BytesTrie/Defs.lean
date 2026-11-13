module

public import Init.Data.UInt.Basic
public import Init.Data.List.Basic

/-!
# Byte tries: finite maps from byte strings

`BytesTrie α` is a finite map from byte strings (`List UInt8`) to `α`, built for
proofs that the kernel checks by evaluation (`decide`, `rfl`):

* the datatype is a plain (non-nested) inductive, the *left-child right-sibling*
  encoding of a 256-ary trie, so every operation is structural recursion and
  reduces in the kernel without well-founded recursion;
* bytes are compared through `UInt8.toNat`, which the kernel accelerates with
  its built-in `Nat` operations;
* `alter` keeps siblings sorted by byte and prunes nodes holding no value, so a
  trie built from `empty` with `alter`, `insert` and `erase` is in canonical form.

**Semantics.** `find?` gives every raw trie a meaning, a finitely supported
function `List UInt8 → Option α`. Raw tries are *not* canonical: unsorted
siblings, shadowed duplicates and value-free nodes all denote maps that also
have other representations. `Canon` picks one representation per map; the
uniqueness theorem `Silmaril.Data.BytesTrie.eq_of_find?_eq` (in `Thms`) shows
that canonical tries with the same lookups are equal, and `BytesMap α`, the
subtype of canonical tries, is therefore isomorphic to the finitely supported
functions (`BytesMap.ext_iff`, `BytesMap.exists_of_finite`). Its `DecidableEq`
is structural comparison of tries.
-/

@[expose] public section

universe u

namespace Silmaril.Data.BytesTrie

/-- A forest of byte-labelled nodes in left-child right-sibling form:
`node b v child next` is the edge labelled `b`, the value `v` at the end of
that edge, the forest `child` below it, and the remaining siblings `next`. -/
inductive Trie (α : Type u) where
  | nil
  | node (b : UInt8) (v : Option α) (child next : Trie α)
  deriving Repr, Inhabited

namespace Trie

variable {α : Type u}

/-- Look up the key `k :: ks`: the first sibling labelled `k` decides. -/
def find? : Trie α → UInt8 → List UInt8 → Option α
  | nil, _, _ => none
  | node b v c n, k, ks =>
    if k = b then
      match ks with
      | [] => v
      | k' :: ks' => c.find? k' ks'
    else n.find? k ks

/-- `node`, but a node with no value and no children is dropped. -/
def mkNode (b : UInt8) (v : Option α) (c n : Trie α) : Trie α :=
  match v, c with
  | none, nil => n
  | v, c => node b v c n

/-- The single path `k :: ks` holding `v`, in front of the siblings `rest`
(just `rest` when `v = none`). -/
def path (k : UInt8) : List UInt8 → Option α → Trie α → Trie α
  | [], v, rest => mkNode k v nil rest
  | k' :: ks, v, rest => mkNode k none (path k' ks v nil) rest

/-- Replace the value `x` at key `k :: ks` by `f x`, keeping siblings sorted and
pruning nodes left without values. -/
def alter (f : Option α → Option α) : Trie α → UInt8 → List UInt8 → Trie α
  | nil, k, ks => path k ks (f none) nil
  | node b v c n, k, ks =>
    if k = b then
      match ks with
      | [] => mkNode b (f v) c n
      | k' :: ks' => mkNode b v (c.alter f k' ks') n
    else if k.toNat < b.toNat then path k ks (f none) (node b v c n)
    else node b v c (n.alter f k ks)

/-- Siblings are strictly increasing, from at least `lo`, at every level. -/
def WF : Nat → Trie α → Prop
  | _, nil => True
  | lo, node b _ c n => lo ≤ b.toNat ∧ WF 0 c ∧ WF (b.toNat + 1) n

/-- Canonical form: `WF`, and every node holds a value or has children. -/
def Canon : Nat → Trie α → Prop
  | _, nil => True
  | lo, node b v c n => lo ≤ b.toNat ∧ (v.isSome ∨ c ≠ nil) ∧ Canon 0 c ∧ Canon (b.toNat + 1) n

/-- `Canon` as a `Bool`: the check a certificate (a trie given as a literal
term) passes to become a `BytesMap` (`Thms`: `canonB_iff`). -/
def canonB : Nat → Trie α → Bool
  | _, nil => true
  | lo, node b v c n =>
    Nat.ble lo b.toNat && (v.isSome || (match c with | nil => false | node .. => true)) &&
      canonB 0 c && canonB (b.toNat + 1) n

/-- All entries, in lexicographic key order when the trie is `WF`; `pre` is the
reversed key prefix. -/
def toList : Trie α → List UInt8 → List (List UInt8 × α)
  | nil, _ => []
  | node b v c n, pre =>
    let here := match v with
      | some a => [((b :: pre).reverse, a)]
      | none => []
    here ++ c.toList (b :: pre) ++ n.toList pre

/-- Structural equality as a `Bool`. `Thms` builds `DecidableEq` from it: the
kernel evaluates this much faster than a derived `DecidableEq` instance. -/
def beq [DecidableEq α] : Trie α → Trie α → Bool
  | nil, nil => true
  | node b v c n, node b' v' c' n' =>
    Nat.beq b.toNat b'.toNat &&
      (match v, v' with
        | none, none => true
        | some x, some y => decide (x = y)
        | _, _ => false) &&
      c.beq c' && n.beq n'
  | _, _ => false

/-- The number of stored values. -/
def size : Trie α → Nat
  | nil => 0
  | node _ v c n => (if v.isSome then 1 else 0) + c.size + n.size

end Trie

end Silmaril.Data.BytesTrie

namespace Silmaril.Data

open BytesTrie

/-- A raw byte trie: the value at the empty key and the forest below it.
See the module documentation for its semantics and canonical form. -/
structure BytesTrie (α : Type u) where
  root : Option α
  kids : BytesTrie.Trie α
  deriving Repr, Inhabited

namespace BytesTrie

variable {α : Type u}

/-- The empty trie. -/
def empty : BytesTrie α := ⟨none, .nil⟩

/-- The value at a key. -/
def find? (t : BytesTrie α) : List UInt8 → Option α
  | [] => t.root
  | k :: ks => t.kids.find? k ks

/-- Replace the value `x` at `ks` by `f x`. -/
def alter (t : BytesTrie α) (ks : List UInt8) (f : Option α → Option α) : BytesTrie α :=
  match ks with
  | [] => ⟨f t.root, t.kids⟩
  | k :: ks => ⟨t.root, t.kids.alter f k ks⟩

/-- Bind `ks` to `a`. -/
def insert (t : BytesTrie α) (ks : List UInt8) (a : α) : BytesTrie α := t.alter ks fun _ => some a

/-- Remove `ks`. -/
def erase (t : BytesTrie α) (ks : List UInt8) : BytesTrie α := t.alter ks fun _ => none

/-- Canonical form (see `Trie.Canon`). -/
def Canon (t : BytesTrie α) : Prop := t.kids.Canon 0

/-- `Canon` as a `Bool`. -/
def canonB (t : BytesTrie α) : Bool := t.kids.canonB 0

/-- Sorted siblings (see `Trie.WF`); weaker than `Canon`, enough for the
`alter` specification. -/
def WF (t : BytesTrie α) : Prop := t.kids.WF 0

/-- All entries; in lexicographic key order when `WF`. -/
def toList (t : BytesTrie α) : List (List UInt8 × α) :=
  (match t.root with | some a => [([], a)] | none => []) ++ t.kids.toList []

/-- The number of stored values. -/
def size (t : BytesTrie α) : Nat := (if t.root.isSome then 1 else 0) + t.kids.size

/-- Bind each `ks ∈ keys` to `f ks`, starting from `t`. -/
def alterAll (t : BytesTrie α) (keys : List (List UInt8)) (f : List UInt8 → Option α) :
    BytesTrie α :=
  keys.foldl (fun t ks => t.alter ks fun _ => f ks) t

/-- Insert a list of bindings; later bindings win. -/
def ofList (l : List (List UInt8 × α)) : BytesTrie α :=
  l.foldl (fun t p => t.insert p.1 p.2) empty

/-- Two raw tries are equivalent when they have the same lookups. -/
def Equiv (s t : BytesTrie α) : Prop := ∀ ks, s.find? ks = t.find? ks

end BytesTrie

/-- Finite maps from byte strings to `α`: canonical byte tries. Equality is
extensional (`BytesMap.ext_iff`) and decided by comparing tries. -/
def BytesMap (α : Type u) : Type u := { t : BytesTrie α // t.Canon }

end Silmaril.Data
