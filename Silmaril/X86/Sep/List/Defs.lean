module

public import Silmaril.X86.Sep.Defs
public import Silmaril.X86.Ext.Semantics

/-!
# Linked lists in the shallow separation logic

Heap predicates for singly linked lists of 64-bit values, over the machine fragments of
`Silmaril.X86.Sep` (ladder rung 06, `examples/elf-ladder/06-list-sep-logic`).

* `nodePt p v n`: the C object `struct node { u64 val; struct node *next; }` at `p`, as gcc
  13.3 lays it out on x86-64: 16 bytes, `val` at offset 0 and `next` at offset 8 (both
  little-endian words, readable and writable). The offsets were checked against the `-O2`
  code (`list_sum`: `add (%rdi),%rax`; `list_length`: `mov 0x8(%rdi),%rdi`) and against
  the DWARF of a `-g` build (`DW_AT_data_member_location` 0 and 8).
* `lseg p q xs`: a list segment from `p` to `q` holding `xs`, defined by recursion on `xs`
  (the inductive definition of the textbook): empty iff `p = q`; otherwise a non-null node at
  `p` holding the head and pointing at some `n`, separately from the segment from `n`.
* `llist p xs`: a null-terminated list, `lseg p 0 xs`.

Every assertion here owns memory locations only (`MemOnly`). For such a fragment `d`,
`memFrag d mem` re-reads its locations in another memory; loop invariants of the list
functions are stated as `P (memFrag d mem)`, where `d` is the fragment owned at entry and
`mem` the current memory.

The `rem` measure (the length of the list from a pointer in a machine state) is used to
prove termination of pointer-chasing loops; it is well-defined because a list is determined
by its head pointer and the memory (`llist_unique`).
-/

@[expose] public section

namespace Silmaril.X86.Sep

open Silmaril.X86 (MState Word Byte)
open Silmaril.Process (Memory)

/-- A list node at `p`: `val = v` at offset 0, `next = n` at offset 8. -/
def nodePt (p v n : Word) : SProp := wordPt p.toNat v ∗ wordPt (p.toNat + 8) n

/-- **A list segment** from `p` to `q` holding `xs`. -/
def lseg : Word → Word → List Word → SProp
  | p, q, [] => ⌜p = q⌝
  | p, q, x :: xs => sexists fun n : Word => ⌜p ≠ 0⌝ ∗ nodePt p x n ∗ lseg n q xs

/-- **A null-terminated list** at `p` holding `xs`. -/
def llist (p : Word) (xs : List Word) : SProp := lseg p 0 xs

/-- A fragment owns memory locations only. -/
def MemOnly (d : Frag) : Prop := ∀ l, (d l).isSome → ∃ a, l = .mem a

/-- The memory locations owned by `d`, as addresses. -/
def memDom (d : Frag) (a : Nat) : Prop := (d (.mem a)).isSome = true

/-- The memory locations of `d`, read in the memory `mem`. -/
def memFrag (d : Frag) (mem : Memory) : Frag
  | .mem a => if (d (.mem a)).isSome then some (.cell ⟨mem.bytes.get? a, permsAt mem a⟩) else none
  | _ => none

/-- One eight-byte little-endian store of `v` at `a`, as an explicit memory (what a
successful `storeN mem a 8 v` produces). -/
def store8 (mem : Memory) (a : Nat) (v : Word) : Memory :=
  { mem with bytes := Memory.install mem.bytes a (Silmaril.X86.Ext.leBytes v 8) }

open Classical in
/-- The length of the list at `p` in the state `m` (0 if there is none). -/
noncomputable def rem (m : MState) (p : Word) : Nat :=
  if h : ∃ zs : List Word, ∃ f, llist p zs f ∧ Frag.Le f (toFrag m) then
    (Classical.choose h).length
  else 0

end Silmaril.X86.Sep
