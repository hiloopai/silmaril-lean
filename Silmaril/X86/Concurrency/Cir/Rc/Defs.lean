module

public import Silmaril.X86.Concurrency.Cir.Csl.Defs

/-!
# Reference counting as derived CIR ops

A reference-counted object (`rc_t` of
`examples/litmus-c/rc/rc.c`) is a 4-byte count cell at `l` and a payload. The library's three
operations are **derived CIR ops**: CIR itself is unchanged.

* `rcInc d a` (`rc_clone`, C11 `fetch_add(1, relaxed)`): `rmw d rlx 4 (op add) a 1`. gcc
  `-O2` emits `lock add DWORD PTR [rdi], 1`; CIR's `rmw` names a destination register `d` that
  x86 does not write, so `d` is a **clobbered** scratch register of the translation.
* `rcDec d a` (C11 `fetch_sub(1, release)`): `rmw d rel 4 (op sub) a 1` (`lock sub`), and
  `rcDrop d a slow`: `rcDec d a; if d == 1 then slow`. gcc folds the test into the zero flag of
  `lock sub` and a `je` to the **outlined cold path** `slow` (C11: `fence(acquire)` then
  `rc_drop_slow`, which frees). The acquire fence compiles to no x86 instruction: the locked
  `sub` is already a full barrier, and in the logic a draining RMW may take ownership, so CIR
  needs no fence either.

## Counting ghost tokens, in cells

The logic has one resource invariant and no ghost state. Ghost state comes for free from the
**cell heap**: CIR addresses are values of 64-bit expressions, so no CIR access of these
programs touches a cell at or above `2^64`, and such cells are ghost cells that only ownership
transfers move. Each object `l` has a **ledger** of `M = 2^32 - 1` index slots `k`, each with two
ghost cells, `gA l k` and `gB l k`:

* `tok l k` (a **token**, one counted reference): the thread owns `gA l k`;
* `blank l k` (an **unused slot**, one unit of clone budget): the thread owns `gB l k`;
* the invariant `rcInv l P` owns, for every slot, the *other* cell: `gB l k` if the slot is in
  use (`k ∈ S`), `gA l k` if not (`ledger l S`). So a thread holding `tok l k` knows `k ∈ S`
  and one holding `blank l k` knows `k ∉ S`, just by disjointness from the invariant.
* while some token is out (`S ≠ []`) the invariant also owns the count cell `l ↦ |S|` and the
  payload `P`; when no token is out it owns only the ledger, and the count and `P` belong to one
  thread (`uniq l P := l ↦ 1 ∗ P`: just created, or just dropped for the last time).

This is a counting permission (Bornat et al. 2005) whose total is fixed: `M` slots. The count
never exceeds `M < 2^32`, so the 32-bit `lock add` never wraps. Rust's `Arc::clone` instead
aborts when the count passes `isize::MAX`; here a clone needs a blank slot, which is a
precondition a thread can establish locally.

## Allocation

`Alloc` is a CIR allocator interface in the shape of `Sep.Alloc.Iface`'s `free`: an
abstract allocator invariant `mm`, a per-block token `blk l`, and CIR code for
`free(rdi)` with `{blk l ∗ obj l} free {emp}` under every frame invariant. Linking a CIR
`Alloc` to the x86 `Sep.Alloc.Iface` needs call-level translation validation (not done).

## The client `Drop2`

Two threads share one object holding the value `42` (and its allocator token). Thread `t` owns
`tok l t`, the blank `blank l (2 + t)` and an output cell. It clones, reads the payload through
its token (an atomic load), writes the value to its output cell, drops the clone (never the last
reference while it holds `tok l t`), then drops its own reference; the last dropper writes the
payload non-atomically (it owns it again) and frees the object.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Rc

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl

/-! ## Ghost cells -/

/-- The number of ledger slots per object: `2^32 - 1`, so a count never wraps 32 bits. -/
def M : Nat := 2 ^ 32 - 1

/-- The first ghost address: no CIR access of a 64-bit address reaches it. -/
def gbase : Nat := 2 ^ 64

/-- The token cell of slot `k` of object `l`. -/
def gA (l k : Nat) : Nat := gbase * (2 * k + 1) + l

/-- The blank cell of slot `k` of object `l`. -/
def gB (l k : Nat) : Nat := gbase * (2 * k + 2) + l

/-- Decode a ghost cell of object `l`: its slot and whether it is the blank cell. -/
def slot (l x : Nat) : Option (Nat × Bool) :=
  if gbase ≤ x ∧ x % gbase = l then some ((x / gbase - 1) / 2, (x / gbase - 1) % 2 == 1)
  else none

/-- **The ledger** of object `l` with slots `S` in use: the invariant's cell of every slot
(`gB` for a slot in use, `gA` for a free one), each holding `0`. -/
def ledger (l : Nat) (S : List Nat) : Heap := fun x =>
  match slot l x with
  | some (k, b) => if k < M ∧ b = decide (k ∈ S) then some 0 else none
  | none => none

/-- Every ghost cell of object `l` (the ledger and all tokens and blanks), each holding `0`. -/
def ghosts (l : Nat) : Heap := fun x =>
  match slot l x with
  | some (k, _) => if k < M then some 0 else none
  | none => none

/-! ## Tokens -/

/-- **A token**: one counted reference to object `l`, slot `k`. -/
def tok (l k : Nat) : HProp := fun h => k < M ∧ h = Heap.single (gA l k) 0

/-- **A blank**: an unused slot `k` of object `l` (one unit of clone budget). -/
def blank (l k : Nat) : HProp := fun h => k < M ∧ h = Heap.single (gB l k) 0

/-- Some token of `l`. -/
def Tok (l : Nat) : HProp := fun h => ∃ k, tok l k h

/-- Some blank of `l`. -/
def Blank (l : Nat) : HProp := fun h => ∃ k, blank l k h

/-- **Unique ownership**: count `1` and the payload, with no token out. -/
def uniq (l : Nat) (P : HProp) : HProp := pt l 1 ∗ P

/-- A heap is exactly `g`. -/
def exactly (g : Heap) : HProp := fun h => h = g

/-- **The invariant of object `l` with payload `P`**: the slots `S` in use are distinct slots
below `M`; the ledger; and, while some slot is in use, the count `|S|` and the payload. -/
def rcInv (l : Nat) (P : HProp) : HProp := fun h =>
  ∃ S : List Nat, S.Nodup ∧ (∀ k ∈ S, k < M) ∧
    ((S = [] ∧ h = ledger l []) ∨ (S ≠ [] ∧ (exactly (ledger l S) ∗ pt l S.length ∗ P) h))

/-! ## Derived ops -/

/-- **`rc_inc`** (`rc_clone`, C11 `fetch_add(1, relaxed)`, x86 `lock add [a], 1`). -/
def rcInc (d : Reg) (a : Expr) : Stmt := .rmw d .rlx 4 (.op .add) a (.lit 1)

/-- **`rc_dec`** (C11 `fetch_sub(1, release)`, x86 `lock sub [a], 1`); `d` gets the old count. -/
def rcDec (d : Reg) (a : Expr) : Stmt := .rmw d .rel 4 (.op .sub) a (.lit 1)

/-- The zero flag of a 32-bit `lock o [a], c` whose old value is in `d`: the 32-bit result is
`0`. -/
def zfOf (o : BinOp) (d : Reg) (c : Nat) : Expr :=
  .bin .eq (.bin .and (.bin o (.reg d) (.lit c)) (.lit 0xffffffff)) (.lit 0)

/-- The old count was `1`: this was the last reference. It is stated as x86 computes it, the
zero flag of `lock sub [a], 1` (`zfOf .sub d 1`), so the translation validator can match the
`je` against it syntactically (`Rc.isLast_iff`: it holds exactly when the old count is `1`). -/
def isLast (d : Reg) : Expr := zfOf .sub d 1

/-- **`rc_dec_and_test`**: `rc_dec`, then `d := (old == 1)` (as a `0`/`1` value). -/
def rcDecAndTest (d : Reg) (a : Expr) : Stmt := .seq (rcDec d a) (.assign d (isLast d))

/-- **`rc_drop`** with the outlined cold path `slow`: `rc_dec`, and `slow` on the last
reference (x86: `lock sub [a], 1; je slow`). -/
def rcDrop (d : Reg) (a : Expr) (slow : Stmt) : Stmt :=
  .seq (rcDec d a) (.ite (isLast d) slow .skip)

/-! ## A CIR allocator interface (the `free` half of `Sep.Alloc.Iface`) -/

/-- The cells of an object: count at `l`, payload at `l + 4`, any values. -/
def obj (l : Nat) : HProp := fun h =>
  ∃ c v, h = Heap.union (Heap.single l c) (Heap.single (l + 4) v)

/-- **A CIR allocator**: invariant `mm`, block token `blk l`, and `free(rdi)` with
`{blk l ∗ obj l} free {emp}` under every frame invariant. -/
structure Alloc where
  mm : HProp
  blk : Nat → HProp
  freeCode : Stmt
  free_spec : ∀ (l : Nat) (J : HProp) (rs : Regs) (h : Heap), (rs .rdi).toNat = l →
    (blk l ∗ obj l) h → Csl.Safe (mm ∗ J) (fun _ => hemp) freeCode rs h

/-- **Derived op** `free(a)`: `rdi := a; free`. -/
def Alloc.free (A : Alloc) (a : Expr) : Stmt := .seq (.assign .rdi a) A.freeCode

/-! ## The `Drop2` client -/

namespace Drop2

/-- The object. -/
def l : Nat := 0x100

/-- Thread `t`'s output cell. -/
def out (t : Nat) : Nat := 0x200 + 8 * t

/-- The payload: the value `42` at `l + 4`, with the allocator's block token. -/
def P (A : Alloc) : HProp := pt (l + 4) 42 ∗ A.blk l

/-- The last dropper's cold path: `[l + 4] := 0` (`na`: it owns the payload again), then
`free(l)`. -/
def slow (A : Alloc) : Stmt :=
  .seq (.store .na 4 .wb (.lit (l + 4)) (.lit 0)) (A.free (.lit l))

/-- Thread `t`: clone, read the payload through the token, publish it to the output cell, drop
the clone, drop the own reference. -/
def body (A : Alloc) (t : Nat) : Stmt :=
  .seq (rcInc .rax (.lit l))
    (.seq (.load .rbx .rlx 4 .wb (.lit (l + 4)))
      (.seq (.store .na 8 .wb (.lit (out t)) (.reg .rbx))
        (.seq (rcDrop .rax (.lit l) (slow A)) (rcDrop .rax (.lit l) (slow A)))))

/-- The invariant: the object's, next to the allocator's. -/
def inv (A : Alloc) : HProp := rcInv l (P A) ∗ A.mm

/-- Thread `t`'s postcondition: its two blanks back, and `42` in its output cell. -/
def post (t : Nat) : Regs → HProp := fun _ => blank l t ∗ blank l (2 + t) ∗ pt (out t) 42

/-- Thread `t`'s starting heap: its token, its blank and its output cell. -/
def own (t : Nat) : Heap :=
  if t < 2 then
    Heap.union (Heap.single (gA l t) 0) (Heap.union (Heap.single (gB l (2 + t)) 0)
      (Heap.single (out t) 0))
  else Heap.empty

/-- The invariant's starting heap: slots `0` and `1` in use, count `2`, the payload and the
allocator's heaps. -/
def ownI (hmm hblk : Heap) : Heap :=
  Heap.union (Heap.union (ledger l [0, 1]) (Heap.union (Heap.single l 2)
    (Heap.union (Heap.single (l + 4) 42) hblk))) hmm

/-- **The client's start**, given the allocator's heaps (its invariant's and the block
token's): memory is exactly the owned cells (the ghost cells of the ledger and the threads'
tokens and blanks included; they all hold `0`). -/
def start (A : Alloc) (hmm hblk : Heap) : Cfg :=
  ⟨fun t => (if t < 2 then body A t else .skip, Regs.zero),
    Heap.union (ownI hmm hblk) (Heap.union (own 0) (own 1))⟩

/-- The allocator's heaps are away from the client's cells: below `2^64`, and not `l`, `l + 4`
or an output cell. -/
def AllocAway (hmm hblk : Heap) : Prop :=
  Heap.Disjoint hmm hblk ∧ ∀ x, ((hmm x).isSome ∨ (hblk x).isSome) →
    x < gbase ∧ x ≠ l ∧ x ≠ l + 4 ∧ x ≠ out 0 ∧ x ≠ out 1

/-- `Drop2` with the payload read by a plain (`na`) load, as Rust's `&T` through an `Arc<T>`
may compile. -/
def bodyNa (A : Alloc) (t : Nat) : Stmt :=
  .seq (rcInc .rax (.lit l))
    (.seq (.load .rbx .na 4 .wb (.lit (l + 4)))
      (.seq (.store .na 8 .wb (.lit (out t)) (.reg .rbx))
        (.seq (rcDrop .rax (.lit l) (slow A)) (rcDrop .rax (.lit l) (slow A)))))

/-- The start of the `na`-read variant. -/
def startNa (A : Alloc) (hmm hblk : Heap) : Cfg :=
  ⟨fun t => (if t < 2 then bodyNa A t else .skip, Regs.zero), (start A hmm hblk).mem⟩

end Drop2

/-- **Read-only sharing of the payload by plain loads.** In `Drop2` with `na` payload
reads, every finished, drained TSO and XL state still has `42` in both output cells.

PROVED: `Rc.drop2Na` in `Rc.Thms`. The store-buffer machines never look at a load's
mode, so every run of `startNa` is a run of `start` with the same memory and buffers
(`Proofs/…/Rc/Na.lean`), and `drop2_buffered` applies. The implementer's original plan
(fractional permissions) is not needed for this statement. It *is* needed for what is
still open: a CSL certificate of the `na` variant and its race freedom. The logic cannot
certify it (an `na` load must touch an owned cell, and while the object is shared the payload
is in the invariant), and `Race` counts two concurrent `na` reads as a race, so `no_race`
would also need a `Race` that lets reads share. -/
def Task.drop2Na : Prop :=
  ∀ (A : Alloc) (hmm hblk : Heap), Drop2.AllocAway hmm hblk → A.mm hmm → A.blk Drop2.l hblk →
    ∀ (Mo : OModel) (C : OCfg), OReach Mo 2 (Drop2.startNa A hmm hblk).toO C → C.Drained →
      (∀ t < 2, (C.ts t).1 = .skip) → ∀ t < 2, C.mem (Drop2.out t) = some 42

end Silmaril.X86.Concurrency.Cir.Rc
