module

public import Silmaril.Elf.Lookup.Defs

/-! # The lookup index: a kernel-friendly table derived from the parse

`Index.build A` precomputes, from a file's AST, everything a lookup compares, as numbers:

* for every hashed `.dynsym` entry (`i ≥ symoffset`): its name as a **key** `(length,
  little-endian value)` (one `Nat` comparison instead of a list walk), its raw symbol, its
  version index and the `l_versions` entry of that index (hash and name key);
* for every defined global or weak function of `.symtab`: its key and definition.

`Index.lookup ix r plt` and `Index.symtabFind ix n` answer from the table alone. A binding fact
is then `Index.build A = some ix ∧ ix.lookup r plt = some (some d)`, closed by `decide +kernel`
on the index literal (the emitter prints `ix`; `Index.build A = some ix` is checked once per
file).

**Soundness** (the index builder's deliverables, `Task`s below):

* `Task.index_lookup_sound`: `ix.lookup = A.scanLookup`-based `lookupDef` (by construction the
  same scan, with keys for names);
* `Task.index_symtab_sound`: `ix.symtabFind = A.symtabFind`;
* with `Task.gnu_eq_scan` (proved in `Index.Thms`), the index answers what ld.so's hash walk does.

The index layout (a list in symbol order) is the simplest sound one; a bucket-ordered or sorted
layout is a refinement with the same `lookup` (`Index.Tree`).
-/

@[expose] public section

namespace Silmaril.Elf

open Silmaril.Formats.ELF (Symbol NameBytes ObjectSymbol)
open Silmaril.X86.Link (Blob)

/-- **The key of a name**: its length and its little-endian value. Injective on names. -/
def nameKey (n : NameBytes) : Nat × Nat := (n.length, Blob.valueLE n)

/-- A hashed dynamic symbol, precomputed. -/
structure Index.Entry where
  index : Nat
  key : Nat × Nat
  sym : Symbol
  /-- `.gnu.version[index]`, if the file has versions. -/
  versym : Option Nat
  /-- `l_versions[versym & 0x7fff]`: hash and name key. -/
  verdef : Option (Nat × (Nat × Nat))
  deriving DecidableEq, Repr

/-- Lexicographic order on name keys (length first). -/
def keyLt (a b : Nat × Nat) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

/-- **A binary search tree over name keys**: each node holds the entries with its key, in
symbol order. Built by insertion in symbol order (`Index.Tree.ofList`); a lookup follows one
path (depth 28 for libc 2.39's 3,136 hashed symbols). `find` is `List.filter` on the keys
(`Index.Tree.find_ofList`), whatever the shape, so no balance or order invariant is needed. -/
inductive Index.Tree where
  | leaf
  | node (l : Index.Tree) (k : Nat × Nat) (es : List Index.Entry) (r : Index.Tree)
  deriving DecidableEq, Repr

namespace Index.Tree

/-- Insert an entry (after the entries already there with its key). -/
def insert (e : Entry) : Tree → Tree
  | .leaf => .node .leaf e.key [e] .leaf
  | .node l k es r =>
    if e.key == k then .node l k (es ++ [e]) r
    else if keyLt e.key k then .node (l.insert e) k es r else .node l k es (r.insert e)

/-- The tree of a list of entries, inserted in order. -/
def ofList (es : List Entry) : Tree := es.foldl (fun t e => t.insert e) .leaf

/-- The entries with key `k`, in insertion order. -/
def find (k : Nat × Nat) : Tree → List Entry
  | .leaf => []
  | .node l k' es r => if k == k' then es else if keyLt k k' then l.find k else r.find k

/-- The depth of a tree. -/
def depth : Tree → Nat
  | .leaf => 0
  | .node l _ _ r => max l.depth r.depth + 1

end Index.Tree

/-- **The lookup index of a file.** -/
structure Index where
  /-- Whether the file has a GNU hash table (else every dynamic lookup has no answer). -/
  hashed : Bool
  /-- Whether the file has `.gnu.version`. -/
  versioned : Bool
  entries : List Index.Entry
  /-- Whether the file has `.symtab`. -/
  hasSymtab : Bool
  /-- The defined global or weak functions of `.symtab`, in order: key and definition. -/
  funcs : List ((Nat × Nat) × Def)
  /-- `entries` as a search tree (`Tree.ofList entries`): what `lookup` reads. -/
  tree : Index.Tree
  deriving DecidableEq, Repr

namespace Index

/-- The index entry of `.dynsym` symbol `i` (`s`), with version index `vs`. -/
def entryOf (A : File) (i : Nat) (s : ObjectSymbol) (vs : Option Nat) : Entry :=
  ⟨i, nameKey s.name, s.raw, vs,
    vs.bind fun ndx => (A.verdefOf (ndx % 0x8000)).map fun (h, n) => (h, nameKey n)⟩

/-- The index entry of `.dynsym` symbol `i` (`none` past the end of the table). -/
def entryAt (A : File) (i : Nat) : Option Entry := do
  let s ← A.dynsyms[i]?
  pure (entryOf A i s (A.versyms.bind (·[i]?)))

/-- The entries of the symbols `ss` from index `i`, with the versions `vs` from `i`: one pass,
no indexing (what `build` computes; `entryAt` pointwise). -/
def entriesFrom (A : File) : Nat → List ObjectSymbol → Option (List Nat) → List Entry
  | _, [], _ => []
  | i, s :: ss, vs => entryOf A i s (vs.bind (·.head?)) :: entriesFrom A (i + 1) ss (vs.map (·.tail))

/-- The `.symtab` entry `(s, i)` as an index function: its key and `File.funcDef`. -/
def funcOf (si : ObjectSymbol × Nat) : Option ((Nat × Nat) × Def) :=
  (File.funcDef si).map fun d => (nameKey si.1.name, d)

/-- **The index of `A`** (`none` when a table it reads is malformed). -/
def build (A : File) : Option Index := do
  let g := A.gnuHashTab
  let off := (g.map (·.symoffset)).getD A.dynsyms.length
  let entries := entriesFrom A off (A.dynsyms.drop off) (A.versyms.map (·.drop off))
  let funcs := (A.symbols .symtab).zipIdx.filterMap funcOf
  pure ⟨g.isSome, A.versyms.isSome, entries, (A.sectionOfType SHT_SYMTAB).isSome, funcs,
    Tree.ofList entries⟩

/-- `check_match` on an entry (as `File.checkMatch`, names by key). The name is compared first:
the other tests only reject, so the order does not change the answer, and a lookup then spends
one `Nat` comparison on each entry with another name. -/
def Entry.checkMatch (versioned : Bool) (e : Entry) (r : Ref) (plt : Bool) : Option Bool := do
  if e.key ≠ nameKey r.name then return false
  let raw := e.sym
  if (raw.value = 0 ∧ raw.sectionIndex ≠ 0xfff1 ∧ raw.kind ≠ 6) ∨ (plt ∧ raw.sectionIndex = 0) then
    return false
  if raw.kind ∉ [0, 1, 2, 5, 6, 10] then return false
  if !versioned then return true
  let ndx ← e.versym
  match r.ver with
  | some v =>
    let same := match e.verdef with
      | some (h, k) => h == v.hash && k == nameKey v.name
      | none => false
    let dh := match e.verdef with
      | some (h, _) => h
      | none => 0
    if !same ∧ (v.hidden ∨ dh ≠ 0 ∨ ndx / 0x8000 % 2 = 1) then return false
    return true
  | none => if 3 ≤ ndx % 0x8000 then none else return true

/-- The first entry `check_match` accepts. -/
def firstEntry (versioned : Bool) (r : Ref) (plt : Bool) : List Entry → Option (Option Entry)
  | [] => some none
  | e :: es => do if ← e.checkMatch versioned r plt then pure (some e) else firstEntry versioned r plt es

/-- **The dynamic lookup, from the index** (`File.lookupDef` on a well-formed hash table): the
entries with the reference's name, from the tree, then `check_match` on them in symbol order. -/
def lookup (ix : Index) (r : Ref) (plt : Bool) : Option (Option Def) := do
  guard ix.hashed
  match ← firstEntry ix.versioned r plt (ix.tree.find (nameKey r.name)) with
  | none => pure none
  | some e =>
    guard (e.sym.binding = 1 ∨ e.sym.binding = 2)
    pure (some ⟨e.index, e.sym.value, e.sym.size, e.sym.kind == 10, e.sym.sectionIndex == 0xfff1⟩)

/-- **Static selection, from the index** (`File.symtabFind`). -/
def symtabFind (ix : Index) (n : NameBytes) : Option (Option Def) := do
  guard ix.hasSymtab
  pure ((ix.funcs.find? (·.1 == nameKey n)).map (·.2))

end Index

/-! ## Soundness (index builder) -/

/-- **The index answers the declarative lookup.** -/
def Task.index_lookup_sound : Prop :=
  ∀ (A : File) (ix : Index), Index.build A = some ix → ∀ r plt,
    ix.lookup r plt = (do
      match ← A.scanLookup r plt with
      | none => pure none
      | some i => some <$> A.defAt i)

/-- **The index answers static selection.** -/
def Task.index_symtab_sound : Prop :=
  ∀ (A : File) (ix : Index), Index.build A = some ix → ∀ n, ix.symtabFind n = A.symtabFind n

/-- **On a well-formed GNU hash table, the hash walk computes the declarative lookup.** -/
def Task.gnu_eq_scan : Prop :=
  ∀ (A : File), A.GnuHashOk → ∀ r plt, A.gnuLookup r plt = A.scanLookup r plt

end Silmaril.Elf
