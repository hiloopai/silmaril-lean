module

public import Silmaril.Libc.Contract.Stdio.Defs
public import Silmaril.Libc.Contract.Spec.Thms

/-!
# `stdio` contracts: reducts, format subsets, the stream model

PROVED (standard axioms), names in `Silmaril.Libc.Contracts`:

* **reducts**: `stdioC_restrict` (the reduct of a bigger signature's contract is the smaller
  one's), e.g. `putsC_restrict` (`outSig` to `putsSig`);
* **format subsets**: `stdioC_mono` (a bigger subset of conversions, for `printf` or `scanf`, is
  a stronger contract);
* **non-vacuity**: `stream_holds`, `stream_returns`, `stdioC_nonVacuous` (the stream model meets
  the contract of every catalogue list for every format subset, and every valid call returns).
-/

@[expose] public section

namespace Silmaril.Libc.Contracts

open Silmaril.Libc.Formats (Conv Piece parseFmt convCount SVal ScanOut scanPieces)

/-- **The reduct of a `stdio` contract** along an inclusion of catalogue lists. -/
theorem stdioC_restrict {l l' : List LFn} (h : ∀ f ∈ l, f ∈ l') (K L : FmtSet) :
    (stdioC l' K L).restrict (stdioIncl h) = stdioC l K L :=
  Contract.restrict_ofTable (A := libcApi) (F := LFn.setOf l) (F' := LFn.setOf l')
    (fun f hf => h f hf) _ _

theorem putsC_restrict (K L : FmtSet) :
    (stdioC outList K L).restrict putsIncl = stdioC putsList K L :=
  stdioC_restrict _ K L

/-- **A bigger format subset is a stronger contract.** -/
theorem stdioC_mono (l : List LFn) {K K' L L' : FmtSet} (hK : K ⊆ K') (hL : L ⊆ L') :
    (stdioC l K L).Le (stdioC l K' L') := by
  refine ⟨fun _ h => h, ?_, fun f _ g a r g' _ hq => ?_⟩
  · intro f _ g a hp
    cases f with
    | printf =>
      obtain ⟨ps, out, h1, h2, h3⟩ := hp
      exact ⟨ps, out, h1, fun k hk => hK (h2 k hk), h3⟩
    | scanf =>
      obtain ⟨ps, h1, h2, h3⟩ := hp
      exact ⟨ps, h1, fun k hk => hL (h2 k hk), h3⟩
    | malloc | free | calloc | realloc | aligned_alloc | posix_memalign | malloc_usable_size
    | putchar | puts | getchar => exact hp
  · cases f <;> exact hq

/-- **The stream model meets the `stdio` contract**, relative to the identity invariant. -/
theorem stream_holds (l : List LFn) (K L : FmtSet) :
    Holds (streamModel l) (stdioC l K L) (fun g s => g = s) := by
  refine ⟨fun s hs => ⟨s, hs, rfl⟩, ?_, ?_⟩
  · intro f hf g s a hI hp hs
    subst hI
    have hs' : none = streamRun f g a := hs
    cases f with
    | putchar => simp [streamRun] at hs'
    | puts => simp [streamRun] at hs'
    | printf =>
      obtain ⟨ps, out, hps, -, hout⟩ := hp
      simp [streamRun, hps, hout] at hs'
    | scanf =>
      obtain ⟨ps, hps, -, hub⟩ := hp
      cases hsc : scanPieces ps g.inp with
      | ok vs rest => simp [streamRun, hps, hsc] at hs'
      | fail vs rest => simp [streamRun, hps, hsc] at hs'
      | ub => exact hub hsc
    | getchar =>
      cases hg : g.inp with
      | nil => simp [streamRun, hg] at hs'
      | cons c rest => simp [streamRun, hg] at hs'
    | malloc | free | calloc | realloc | aligned_alloc | posix_memalign | malloc_usable_size =>
      exact (hp : False)
  · intro f hf g s a t r hI hp hs
    subst hI
    have hs' : some (t, r) = streamRun f g a := hs
    cases f with
    | putchar =>
      simp [streamRun] at hs'
      obtain ⟨rfl, rfl⟩ := hs'
      exact ⟨_, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
    | puts =>
      simp [streamRun] at hs'
      obtain ⟨rfl, rfl⟩ := hs'
      exact ⟨_, rfl, rfl, Or.inl ⟨rfl, by omega⟩⟩
    | printf =>
      obtain ⟨ps, out, hps, -, hout⟩ := hp
      simp [streamRun, hps, hout] at hs'
      obtain ⟨rfl, rfl⟩ := hs'
      refine ⟨_, rfl, rfl, fun ps' out' hps' hout' => ?_⟩
      rw [hps] at hps'
      cases hps'
      rw [hout] at hout'
      cases hout'
      exact Or.inl ⟨rfl, rfl⟩
    | scanf =>
      obtain ⟨ps, hps, -, hub⟩ := hp
      cases hsc : scanPieces ps g.inp with
      | ok vs rest =>
        simp [streamRun, hps, hsc] at hs'
        obtain ⟨rfl, rfl⟩ := hs'
        refine ⟨_, rfl, rfl, fun ps' hps' => ?_⟩
        rw [hps] at hps'
        cases hps'
        unfold ScanPost
        rw [hsc]
        exact ⟨rfl, rfl⟩
      | fail vs rest =>
        simp [streamRun, hps, hsc] at hs'
        obtain ⟨rfl, rfl⟩ := hs'
        refine ⟨_, rfl, rfl, fun ps' hps' => ?_⟩
        rw [hps] at hps'
        cases hps'
        unfold ScanPost
        rw [hsc]
        exact ⟨rfl, by omega, List.suffix_refl _⟩
      | ub => exact absurd hsc hub
    | getchar =>
      cases hg : g.inp with
      | nil =>
        simp [streamRun, hg] at hs'
        obtain ⟨rfl, rfl⟩ := hs'
        exact ⟨_, rfl, rfl, Or.inr (Or.inl ⟨hg, rfl, hg⟩)⟩
      | cons c rest =>
        simp [streamRun, hg] at hs'
        obtain ⟨rfl, rfl⟩ := hs'
        exact ⟨_, rfl, rfl, Or.inl ⟨c, hg, rfl⟩⟩
    | malloc | free | calloc | realloc | aligned_alloc | posix_memalign | malloc_usable_size =>
      exact (hp : False).elim

theorem stream_returns (l : List LFn) (K L : FmtSet) :
    Returns (streamModel l) (stdioC l K L) (fun g s => g = s) := by
  intro f hf g s a hI hp
  cases h : streamRun f s a with
  | none => exact absurd h.symm ((stream_holds l K L).safe f hf g s a hI hp)
  | some x => exact ⟨x.1, x.2, h.symm⟩

/-- **Every `stdio` contract of the catalogue is non-vacuous**, for every format subset. -/
theorem stdioC_nonVacuous (l : List LFn) (K L : FmtSet) : (stdioC l K L).NonVacuous :=
  ⟨streamModel l, _, stream_holds l K L, stream_returns l K L, ⟨[], []⟩, rfl⟩

end Silmaril.Libc.Contracts
