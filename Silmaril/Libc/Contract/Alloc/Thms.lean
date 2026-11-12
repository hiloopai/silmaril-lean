module

public import Silmaril.Libc.Contract.Alloc.Defs
public import Silmaril.Libc.Contract.Spec.Thms
public import Silmaril.Libc.AllocInst.Thms

/-!
# The allocator hierarchy: reducts, the bottom allocator at every level, `AllocInst` models

PROVED (standard axioms), names in `Silmaril.Libc.Contracts`:

* **the hierarchy is a chain of reducts**: `allocC_restrict` (the reduct of the level-`k'`
  contract to level `k ≤ k'` is the level-`k` contract), `allocChain` (`Defs`, a functor
  `ℕ ⥤ Sig`);
* **the bottom allocator is a model at every level**: `bottom_holds`, `bottom_returns`,
  `bottom_sat`, `allocC_nonVacuous` (the contract of every level is non-vacuous), and the same
  through the machinery of reducts: `bottom_reduct` (the level-`k` bottom allocator is the reduct
  of the level-4 one), `bottom_sat_reduct` (the reduct of the level-4 bottom allocator meets
  every level, from `Sat.restrict` and `allocC_restrict`);
* **the abstract allocators of `AllocInst`**: `absModel_holds` (an `AbsAlloc` meeting `allocLoose`
  on a fragment, as `SatOn`, meets the contract of every level `k ≤ 3` whose functions are in the
  fragment, relative to its invariant and its visible heap), `absModel_sat` (`Safe Frag.all`:
  levels `1 … 3`), `absModel_sat_mf` (`Safe Frag.mf`, the x86 ladder: level 1), and
  `never_absModel_sat` (`AbsAlloc.never`, the bottom allocator of `AllocInst`, meets level 3).
-/

@[expose] public section

namespace Silmaril.Libc.Contracts

/-- **The reduct of a level's contract to a lower level is the lower level's contract.** -/
theorem allocC_restrict {k k' : Nat} (h : k ≤ k') :
    (allocC k').restrict (allocIncl h) = allocC k :=
  Contract.restrict_ofTable (A := libcApi) (allocF_mono h) _ _

/-! ## The bottom allocator -/

theorem bottom_holds (k : Nat) : Holds (bottomAlloc k) (allocC k) (fun g s => g = s) := by
  refine ⟨fun s hs => ⟨s, hs, rfl⟩, ?_, ?_⟩
  · intro f hf g s a hI hp hs
    subst hI
    cases f with
    | malloc => cases hs
    | free => exact hp hs
    | calloc => cases hs
    | realloc => exact hp (allocNever_le_loose _ _ _ hs)
    | aligned_alloc => cases hs
    | posix_memalign =>
      obtain ⟨h1, h2⟩ := hs
      by_cases hm : MemalignOk (a : Nat × Nat).1
      · have h := h1 hm; simp at h
      · have h := h2 hm; simp at h
    | malloc_usable_size => cases hs
    | putchar | puts | printf | scanf | getchar => exact (hp : False)
  · intro f hf g s a t r hI hp hs
    subst hI
    cases f with
    | malloc => cases hs; exact ⟨_, rfl, allocNever_le_loose _ (.malloc (a : Nat)) _ rfl⟩
    | free =>
      obtain ⟨r', hr⟩ := hs
      exact ⟨t, rfl, r', allocNever_le_loose _ _ _ hr⟩
    | calloc =>
      cases hs
      exact ⟨_, rfl, allocNever_le_loose _ (.calloc (a : Nat × Nat).1 (a : Nat × Nat).2) _ rfl⟩
    | realloc =>
      have hs' : allocNever g (.realloc (a : Nat × Nat).1 (a : Nat × Nat).2) (.ok t r) := hs
      exact ⟨t, rfl, allocNever_le_loose _ _ _ hs'⟩
    | aligned_alloc => cases hs; exact ⟨_, rfl, Or.inl ⟨rfl, rfl⟩⟩
    | posix_memalign =>
      obtain ⟨h1, h2⟩ := hs
      by_cases hm : MemalignOk (a : Nat × Nat).1
      · cases h1 hm
        exact ⟨_, rfl, fun _ => Or.inr ⟨by decide, rfl⟩, fun hn => absurd hm hn⟩
      · cases h2 hm
        exact ⟨_, rfl, fun h => absurd h hm, fun _ => ⟨rfl, rfl⟩⟩
    | malloc_usable_size =>
      cases hs
      refine ⟨_, rfl, rfl, fun h0 => by simp [h0], fun h0 n hn => by simp [h0, hn]⟩
    | putchar | puts | printf | scanf | getchar => exact (hp : False).elim

theorem bottom_returns (k : Nat) : Returns (bottomAlloc k) (allocC k) (fun g s => g = s) := by
  intro f hf g s a hI hp
  subst hI
  cases f with
  | malloc => exact ⟨_, _, rfl⟩
  | free =>
    obtain ⟨o, ho⟩ := allocNever_progress g (.free (a : Nat))
    cases o with
    | ub => exact absurd ho hp
    | ok h' r => exact ⟨h', (), r, ho⟩
  | calloc => exact ⟨_, _, rfl⟩
  | realloc =>
    obtain ⟨o, ho⟩ := allocNever_progress g (.realloc (a : Nat × Nat).1 (a : Nat × Nat).2)
    cases o with
    | ub => exact absurd (allocNever_le_loose _ _ _ ho) hp
    | ok h' r => exact ⟨h', r, ho⟩
  | aligned_alloc => exact ⟨_, _, rfl⟩
  | posix_memalign =>
    by_cases hm : MemalignOk (a : Nat × Nat).1
    · exact ⟨g, ((12 : Nat), (0 : Nat)), fun _ => rfl, fun hn => absurd hm hn⟩
    · exact ⟨g, ((22 : Nat), (0 : Nat)), fun h => absurd h hm, fun _ => rfl⟩
  | malloc_usable_size => exact ⟨_, _, rfl⟩
  | putchar | puts | printf | scanf | getchar => exact (hp : False).elim

theorem bottom_sat (k : Nat) : Sat (bottomAlloc k) (allocC k) := ⟨_, bottom_holds k⟩

/-- **The allocator contract of every level is non-vacuous**: the bottom allocator meets it,
from the empty heap, and every valid call returns. -/
theorem allocC_nonVacuous (k : Nat) : (allocC k).NonVacuous :=
  ⟨bottomAlloc k, _, bottom_holds k, bottom_returns k, Heap.empty, rfl⟩

theorem bottom_reduct {k k' : Nat} (h : k ≤ k') :
    (bottomAlloc k').reduct (allocIncl h) = bottomAlloc k := rfl

/-- The reduct of the level-4 bottom allocator meets every lower level, by the reduct machinery. -/
theorem bottom_sat_reduct {k : Nat} (h : k ≤ 4) :
    Sat ((bottomAlloc 4).reduct (allocIncl h)) (allocC k) := by
  rw [← allocC_restrict h]
  exact (bottom_sat 4).restrict (allocIncl h)

/-! ## The abstract allocators of `AllocInst` -/

set_option linter.unusedTactic false in
/-- **An abstract allocator meeting `allocLoose` on a fragment meets the contract of every level
`k ≤ 3` whose functions are in the fragment**, relative to its invariant and its visible heap. -/
theorem absModel_holds {A : AbsAlloc} {F : Frag} {Inv : A.St → Prop} {k : Nat} (hk : k ≤ 3)
    (hF : ∀ f, f ∈ allocF k → ∀ g, f.toAFn = some g → g ∈ F)
    (h : A.SatOn F (fun _ => True) Inv allocLoose) :
    Holds (absModel A k) (allocC k) (fun g s => Inv s ∧ A.heap s = g) := by
  have hin : ∀ f, f ∈ allocF k → ∀ c : ACall, c.fn = f.toAFn → c.In F := by
    intro f hf c hc g hg
    exact hF f hf g (hc ▸ hg)
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · subst hs; exact ⟨Heap.empty, rfl, h.init, h.empty⟩
  · intro f hf g s a hI hp hs
    obtain ⟨hInv, hh⟩ := hI
    subst hh
    cases f with
    | malloc =>
      have := h.rel s _ none hInv (hin _ hf (.malloc a) rfl) trivial hs
      simp [AbsAlloc.out, allocLoose, allocate] at this
    | free =>
      obtain ⟨o', hs, ho⟩ := hs
      cases o' with
      | none => exact hp (h.rel s _ none hInv (hin _ hf (.free a) rfl) trivial hs)
      | some x => cases ho
    | calloc =>
      exact hp (h.rel s _ none hInv (hin _ hf (.calloc (a : Nat × Nat).1 (a : Nat × Nat).2) rfl)
        trivial hs)
    | realloc =>
      exact hp (h.rel s _ none hInv (hin _ hf (.realloc (a : Nat × Nat).1 (a : Nat × Nat).2) rfl)
        trivial hs)
    | aligned_alloc | posix_memalign | malloc_usable_size | putchar | puts | printf | scanf
    | getchar =>
      exact absurd (mem_allocF.1 hf) (by simp [LFn.allocLevel] <;> omega)
  · intro f hf g s a t r hI hp hs
    obtain ⟨hInv, hh⟩ := hI
    subst hh
    cases f with
    | malloc =>
      have hc := hin _ hf (.malloc a) rfl
      exact ⟨_, ⟨h.inv s _ t r hInv hc trivial hs, rfl⟩, h.rel s _ _ hInv hc trivial hs⟩
    | free =>
      obtain ⟨o', hs, ho⟩ := hs
      cases o' with
      | none => cases ho
      | some x =>
        obtain ⟨t', r'⟩ := x
        cases ho
        have hc := hin _ hf (.free a) rfl
        exact ⟨_, ⟨h.inv s _ t' r' hInv hc trivial hs, rfl⟩, r', h.rel s _ _ hInv hc trivial hs⟩
    | calloc =>
      have hc := hin _ hf (.calloc (a : Nat × Nat).1 (a : Nat × Nat).2) rfl
      exact ⟨_, ⟨h.inv s _ t r hInv hc trivial hs, rfl⟩, h.rel s _ _ hInv hc trivial hs⟩
    | realloc =>
      have hc := hin _ hf (.realloc (a : Nat × Nat).1 (a : Nat × Nat).2) rfl
      exact ⟨_, ⟨h.inv s _ t r hInv hc trivial hs, rfl⟩, h.rel s _ _ hInv hc trivial hs⟩
    | aligned_alloc | posix_memalign | malloc_usable_size | putchar | puts | printf | scanf
    | getchar =>
      exact absurd (mem_allocF.1 hf) (by simp [LFn.allocLevel] <;> omega)

/-- **An abstract allocator that is `Safe` on the whole API meets every level `k ≤ 3`.** -/
theorem absModel_sat {A : AbsAlloc} (hA : A.Safe Frag.all) {k : Nat} (hk : k ≤ 3) :
    Sat (absModel A k) (allocC k) := by
  obtain ⟨Inv, h⟩ := hA
  refine ⟨_, absModel_holds hk (fun _ _ g _ => ?_) h⟩
  cases g <;> simp [Frag.all]

/-- **An abstract allocator that is `Safe` on `malloc`/`free` (the x86 ladder's fragment) meets
level 1.** -/
theorem absModel_sat_mf {A : AbsAlloc} (hA : A.Safe Frag.mf) : Sat (absModel A 1) (allocC 1) := by
  obtain ⟨Inv, h⟩ := hA
  refine ⟨_, absModel_holds (by omega) (fun f hf g hg => ?_) h⟩
  have := mem_allocF.1 hf
  cases f <;> simp [LFn.allocLevel] at this <;> simp [LFn.toAFn] at hg <;> subst hg <;>
    simp [Frag.mf]

/-- **`AllocInst`'s bottom allocator** `AbsAlloc.never` meets the level-3 contract. -/
theorem never_absModel_sat : Sat (absModel AbsAlloc.never 3) (allocC 3) :=
  absModel_sat (never_safe) le_rfl

end Silmaril.Libc.Contracts
