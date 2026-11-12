module

public import Silmaril.Libc.Contract.Libc.Defs
public import Silmaril.Libc.Contract.Spec.Defs
public import Silmaril.Libc.AllocInst.Defs
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# The allocator hierarchy

Four signatures over one invariant interface, the visible heap `Heap` (the live blocks: start ↦
requested size, `Silmaril.Libc.Alloc`):

| signature | functions |
|---|---|
| `allocSig 1` | `malloc`, `free` |
| `allocSig 2` | `+ calloc` |
| `allocSig 3` | `+ realloc` |
| `allocSig 4` | `+ aligned_alloc`, `posix_memalign`, `malloc_usable_size` |

with the inclusions `allocIncl : allocSig k ⟶ allocSig k'` (`k ≤ k'`; `allocChain : ℕ ⥤ Sig` in
`Thms`). **The contract at every level is one table** (`allocTable`) on the level's functions
(`allocC k`), so the contract of a level is the reduct of every higher level's
(`Thms.allocC_restrict`).

**The table** (C17 7.22.3, POSIX `posix_memalign`, glibc `malloc_usable_size`), from the loose
allocator `allocLoose` where it applies:

* **preconditions are POSIX use only**: `free`, `calloc`, `realloc`: no undefined behaviour in
  `allocLoose` (`free`/`realloc` of a live block or null; no double free); `aligned_alloc`: a
  power-of-two alignment that divides the size (C11's requirement, portable everywhere);
  `malloc_usable_size`: null or a live block; `malloc`, `posix_memalign`: none;
* **postconditions allow failure** everywhere (null, the heap unchanged), and a success is a
  fresh block (`Heap.Fresh`: non-null, disjoint from every live footprint), suitably aligned for
  `aligned_alloc` and `posix_memalign`; `posix_memalign` with an invalid alignment returns `EINVAL`
  (22); `malloc_usable_size` of a live block is at least its requested size, and of null `0`.

The initial abstract state is the empty heap.

**Models.** `bottomAlloc k`: **the bottom allocator** (every allocation fails, `free` and
`realloc (p, 0)` release, `posix_memalign` reports `ENOMEM`), a model at every level
(`Thms.bottom_holds`, `Thms.allocC_nonVacuous`). `absModel A k`: an abstract allocator of
`Silmaril.Libc.AllocInst` (`AbsAlloc`) as a model of the levels `k ≤ 3`;
`Thms.absModel_sat`: an `AbsAlloc` that is `Safe` on the whole API meets `allocC 3` (and, through
the reduct, every lower level), and one that is `Safe` on `Frag.mf` meets `allocC 1`.
-/

@[expose] public section

namespace Silmaril.Libc.Contracts

open CategoryTheory

/-- The functions of allocator level `1 … k`. -/
def allocF (k : Nat) : Set LFn := LFn.setOf (allocList k)

/-- **The allocator signature at level `k`.** -/
def allocSig (k : Nat) : Sig libcApi := Sig.mk' (A := libcApi) (allocF k) Heap

theorem mem_allocF {k : Nat} {f : LFn} : f ∈ allocF k ↔ 0 < f.allocLevel ∧ f.allocLevel ≤ k := by
  cases f <;> simp [allocF, LFn.setOf, allocList, LFn.all, LFn.allocLevel] <;>
    exact ⟨of_decide_eq_true, decide_eq_true⟩

theorem allocF_mono {k k' : Nat} (h : k ≤ k') : allocF k ⊆ allocF k' := fun _ hf => by
  rw [mem_allocF] at hf ⊢; omega

/-- **The inclusion** of the allocator at level `k` into the one at level `k' ≥ k`. -/
def allocIncl {k k' : Nat} (h : k ≤ k') : Sig.Hom (allocSig k) (allocSig k') :=
  Sig.incl (A := libcApi) (allocF_mono h)

/-- **The allocator chain** `allocSig 0 ⟶ allocSig 1 ⟶ allocSig 2 ⟶ …`, as a functor from the
order `ℕ`. -/
def allocChain : ℕ ⥤ Sig libcApi where
  obj := allocSig
  map f := allocIncl (CategoryTheory.leOfHom f)
  map_id _ := Sig.Hom.ext' rfl
  map_comp _ _ := Sig.Hom.ext' rfl

/-- `n` is a power of two. -/
def PowTwo (n : Nat) : Prop := ∃ j, n = 2 ^ j

/-- A valid `posix_memalign` alignment: a power of two and a multiple of `sizeof (void *)`. -/
def MemalignOk (al : Nat) : Prop := PowTwo al ∧ 8 ∣ al

/-- **The allocator's function contracts** (module doc). -/
def allocTable : (f : LFn) → FnSpec libcApi Heap f
  | .malloc => ⟨fun _ _ => True, fun h (n : Nat) (r : Nat) h' => allocLoose h (.malloc n) (.ok h' r)⟩
  | .free => ⟨fun h (p : Nat) => ¬ allocLoose h (.free p) .ub,
      fun h (p : Nat) _ h' => ∃ r, allocLoose h (.free p) (.ok h' r)⟩
  | .calloc => ⟨fun h (a : Nat × Nat) => ¬ allocLoose h (.calloc a.1 a.2) .ub,
      fun h (a : Nat × Nat) (r : Nat) h' => allocLoose h (.calloc a.1 a.2) (.ok h' r)⟩
  | .realloc => ⟨fun h (a : Nat × Nat) => ¬ allocLoose h (.realloc a.1 a.2) .ub,
      fun h (a : Nat × Nat) (r : Nat) h' => allocLoose h (.realloc a.1 a.2) (.ok h' r)⟩
  | .aligned_alloc => ⟨fun _ (a : Nat × Nat) => PowTwo a.1 ∧ a.1 ∣ a.2,
      fun h (a : Nat × Nat) (r : Nat) h' =>
        (r = 0 ∧ h' = h) ∨ (h.Fresh r a.2 ∧ r % a.1 = 0 ∧ h' = h.add r a.2)⟩
  | .posix_memalign => ⟨fun _ _ => True,
      fun h (a : Nat × Nat) (r : Nat × Nat) h' =>
        (MemalignOk a.1 →
          (r.1 = 0 ∧ h.Fresh r.2 a.2 ∧ r.2 % a.1 = 0 ∧ h' = h.add r.2 a.2) ∨ (r.1 ≠ 0 ∧ h' = h)) ∧
        (¬ MemalignOk a.1 → r.1 = 22 ∧ h' = h)⟩
  | .malloc_usable_size => ⟨fun h (p : Nat) => p = 0 ∨ (h p).isSome,
      fun h (p : Nat) (r : Nat) h' =>
        h' = h ∧ (p = 0 → r = 0) ∧ (p ≠ 0 → ∀ n, h p = some n → n ≤ r)⟩
  | .putchar | .puts | .printf | .scanf | .getchar => ⟨fun _ _ => False, fun _ _ _ _ => False⟩

/-- **The allocator contract at level `k`**: the table on the level's functions, from the empty
heap. -/
def allocC (k : Nat) : Contract (allocSig k) :=
  Contract.ofTable (A := libcApi) (allocF k) Heap (fun h => h = Heap.empty) allocTable

/-! ## The bottom allocator -/

/-- The calls of the bottom allocator. -/
def bottomStep : (f : LFn) → Heap → f.Arg → Option (Heap × f.Ret) → Prop
  | .malloc, h, _, o => o = some (h, (0 : Nat))
  | .free, h, (p : Nat), o => match o with
    | none => allocNever h (.free p) .ub
    | some (h', _) => ∃ r, allocNever h (.free p) (.ok h' r)
  | .calloc, h, _, o => o = some (h, (0 : Nat))
  | .realloc, h, (a : Nat × Nat), o => match o with
    | none => allocNever h (.realloc a.1 a.2) .ub
    | some (h', (r : Nat)) => allocNever h (.realloc a.1 a.2) (.ok h' r)
  | .aligned_alloc, h, _, o => o = some (h, (0 : Nat))
  | .posix_memalign, h, (a : Nat × Nat), o =>
    (MemalignOk a.1 → o = some (h, ((12 : Nat), (0 : Nat)))) ∧
      (¬ MemalignOk a.1 → o = some (h, ((22 : Nat), (0 : Nat))))
  | .malloc_usable_size, h, (p : Nat), o => o = some (h, if p = 0 then 0 else (h p).getD 0)
  | .putchar, _, _, o | .puts, _, _, o | .printf, _, _, o | .scanf, _, _, o
  | .getchar, _, _, o => o = none

/-- **The bottom allocator** at level `k`: its state is its visible heap. -/
def bottomAlloc (k : Nat) : Model (allocSig k) :=
  ⟨Heap, fun h => h = Heap.empty, fun f _ => bottomStep f⟩

/-! ## Abstract allocators of `AllocInst` as models -/

/-- The function of the abstract allocator API (`AFn`) a C function is. -/
def LFn.toAFn : LFn → Option AFn
  | .malloc => some .malloc
  | .free => some .free
  | .calloc => some .calloc
  | .realloc => some .realloc
  | _ => none

/-- The calls of an abstract allocator (`AbsAlloc`) at the allocator levels `1 … 3`. -/
def absStep (A : AbsAlloc) : (f : LFn) → A.St → f.Arg → Option (A.St × f.Ret) → Prop
  | .malloc, s, (n : Nat), o => A.step s (.malloc n) o
  | .free, s, (p : Nat), o => ∃ o', A.step s (.free p) o' ∧ o = o'.map fun x => (x.1, ())
  | .calloc, s, (a : Nat × Nat), o => A.step s (.calloc a.1 a.2) o
  | .realloc, s, (a : Nat × Nat), o => A.step s (.realloc a.1 a.2) o
  | .aligned_alloc, _, _, o | .posix_memalign, _, _, o | .malloc_usable_size, _, _, o
  | .putchar, _, _, o | .puts, _, _, o | .printf, _, _, o | .scanf, _, _, o
  | .getchar, _, _, o => o = none

/-- **An abstract allocator as a model** of the allocator signature at level `k` (meaningful for
`k ≤ 3`: it has no `aligned_alloc`, `posix_memalign`, `malloc_usable_size`). -/
def absModel (A : AbsAlloc) (k : Nat) : Model (allocSig k) :=
  ⟨A.St, fun s => s = A.init, fun f _ => absStep A f⟩

end Silmaril.Libc.Contracts
