module

public import Silmaril.Libc.Contract.Diagram.Defs
public meta import Silmaril.Libc.Contract.Diagram.Defs
public import Silmaril.Libc.Contract.Alloc.Thms
public import Silmaril.Libc.Contract.Stdio.Thms
public import Silmaril.Libc.Contract.Inst.Thms

/-!
# The C library as a tensor; clients of the allocator and of `stdio`; the diagram

PROVED (standard axioms), names in `Silmaril.Libc.Contracts`:

* **the tensor**: `alloc_stdio_disjoint` (no allocator function is a `stdio` one),
  `libc_holds`, `libc_sat`, `libc_nonVacuous` (the bottom allocator beside the stream model
  meets the tensor contract, and every valid call returns), `libc_alloc_factor`,
  `libc_stdio_factor` (every model of the tensor contract meets each factor's contract through
  the injections), `libcSig_F` (the tensor's functions are the catalogue's);
* **clients**: `mallocFree` (`p = malloc (16); free (p)`) is verified against level 1 for the
  postcondition "the heap is empty again" (`mallocFree_verified`), so it is correct on every
  model of level 1 (`mallocFree_correct`) and on every model of the whole C library through the
  reducts (`mallocFree_on_libc`); `hello` (`puts ("hi")`) is verified against `putsSig` for
  "on success, `hi\n` was written" (`hello_verified`, `hello_on_libc`);
* **the diagram**: `#guard` checks that `Diagram.mermaid` is the expected text
  (`Diagram.expected`).
-/

@[expose] public section

namespace Silmaril.Libc.Contracts

open Silmaril.Libc.Formats (SVal)

/-! ## The tensor -/

theorem stdioList_noalloc : ∀ f ∈ stdioList, f.allocLevel = 0 := by decide

/-- **The allocator and `stdio` have no function in common.** -/
theorem alloc_stdio_disjoint (k : Nat) {l : List LFn} (hl : ∀ f ∈ l, f.allocLevel = 0) :
    ∀ f, f ∈ (allocSig k).F → f ∉ (stdioSigOf l).F := fun f hf hl' => by
  have h1 := (mem_allocF.1 hf).1
  have h2 := hl f hl'
  omega

theorem libc_holds (k : Nat) {l : List LFn} (hl : ∀ f ∈ l, f.allocLevel = 0) (K L : FmtSet) :
    Holds (libcModel k l) (libcC k l K L) (fun g s => g.1 = s.1 ∧ g.2 = s.2) :=
  (bottom_holds k).tensor (alloc_stdio_disjoint k hl) (stream_holds l K L)

theorem libc_sat (k : Nat) {l : List LFn} (hl : ∀ f ∈ l, f.allocLevel = 0) (K L : FmtSet) :
    Sat (libcModel k l) (libcC k l K L) :=
  ⟨_, libc_holds k hl K L⟩

/-- **The C library's contract is non-vacuous.** -/
theorem libc_nonVacuous (k : Nat) {l : List LFn} (hl : ∀ f ∈ l, f.allocLevel = 0)
    (K L : FmtSet) : (libcC k l K L).NonVacuous :=
  (allocC_nonVacuous k).tensor (alloc_stdio_disjoint k hl) (stdioC_nonVacuous l K L)

/-- **The allocator factor**: a model of the C library, seen through the allocator, meets the
allocator's contract. -/
theorem libc_alloc_factor {k : Nat} {l : List LFn} (hl : ∀ f ∈ l, f.allocLevel = 0)
    {K L : FmtSet} {X : Model (libcSig k l)} (h : Sat X (libcC k l K L)) :
    Sat (X.reduct (Sig.inl _ _)) (allocC k) :=
  Sat.tensor_inl (alloc_stdio_disjoint k hl) h

/-- **The `stdio` factor.** -/
theorem libc_stdio_factor {k : Nat} {l : List LFn} (hl : ∀ f ∈ l, f.allocLevel = 0)
    {K L : FmtSet} {X : Model (libcSig k l)} (h : Sat X (libcC k l K L)) :
    Sat (X.reduct (Sig.inr _ _)) (stdioC l K L) :=
  Sat.tensor_inr (alloc_stdio_disjoint k hl) h

theorem libcSig_F (k : Nat) (l : List LFn) :
    (libcSig k l).F = LFn.setOf (allocList k ++ l) := by
  ext f
  show f ∈ allocList k ∨ f ∈ l ↔ f ∈ allocList k ++ l
  exact List.mem_append.symm

/-! ## Clients -/

/-- `p = malloc (16); free (p)`. -/
def mallocFree : Prog (allocSig 1) Unit :=
  .call .malloc (mem_allocF.2 ⟨by decide, by decide⟩) (16 : Nat) fun p =>
    .call .free (mem_allocF.2 ⟨by decide, by decide⟩) (show Nat from p) fun _ => .ret ()

/-- **`malloc` then `free` leaves the heap empty**, whatever the allocator returns. -/
theorem mallocFree_verified : mallocFree.Verified (allocC 1) (fun _ g => g = Heap.empty) := by
  intro g hg
  subst hg
  simp only [mallocFree, Prog.WP]
  refine ⟨trivial, fun r g' hm => ?_⟩
  change allocate Heap.empty 16 (.ok g' r) at hm
  rcases hm with hm | ⟨p, hp, hm⟩
  · cases hm
    refine ⟨fun h => ?_, fun _ g'' ⟨r'', h⟩ => ?_⟩
    · simp [allocLoose] at h
    · simp [allocLoose] at h
      injection h
  · cases hm
    have hp0 : @Ne Nat r 0 := hp.1
    have hlive : Heap.add Heap.empty r 16 r = some 16 := ite_eq_left rfl
    have hsome : (Heap.add Heap.empty r 16 r).isSome = true := by rw [hlive]; rfl
    refine ⟨fun h => ?_, fun _ g'' ⟨r'', h⟩ => ?_⟩
    · simp only [allocLoose] at h
      rw [ite_eq_right hp0, ite_eq_left hsome] at h
      cases h
    · simp only [allocLoose] at h
      rw [ite_eq_right hp0, ite_eq_left hsome] at h
      injection h with h1
      rw [h1]
      funext a
      by_cases ha : a = r <;> simp [Heap.remove, Heap.add, Heap.empty, ha]

/-- **On every model of level 1**, from every valid start: no crash, and the heap is empty
again. -/
theorem mallocFree_correct {M : Model (allocSig 1)} (hM : Sat M (allocC 1)) {s : M.St}
    (hs : M.init s) {o : Outcome M.St Unit} (hr : Prog.Run M mallocFree s o) :
    ∃ t, o = .done () t ∧ ∃ g : Heap, g = Heap.empty := by
  obtain ⟨_, t, ho, g, hg⟩ := client_correct hM mallocFree_verified hs hr
  exact ⟨t, ho, g, hg⟩

/-- The allocator level 1 inside the C library: level 1 into level `k`, then the left factor. -/
def allocInLibc {k : Nat} (h : 1 ≤ k) (l : List LFn) : Sig.Hom (allocSig 1) (libcSig k l) :=
  (allocIncl h).comp (Sig.inl _ _)

/-- **On every model of the C library's contract** (any allocator level `k ≥ 1`, any `stdio`
list and format subsets), through the reducts. -/
theorem mallocFree_on_libc {k : Nat} (h : 1 ≤ k) {l : List LFn}
    (hl : ∀ f ∈ l, f.allocLevel = 0) {K L : FmtSet} {X : Model (libcSig k l)}
    (hX : Sat X (libcC k l K L)) {s : X.St} (hs : X.init s) {o : Outcome X.St Unit}
    (hr : Prog.Run X (mallocFree.map (allocInLibc h l)) s o) :
    ∃ t, o = .done () t := by
  have h1 : Sat ((X.reduct (Sig.inl _ _)).reduct (allocIncl h)) (allocC 1) := by
    rw [← allocC_restrict h]
    exact (libc_alloc_factor hl hX).restrict _
  obtain ⟨_, t, ho, _⟩ := client_reduct' (allocInLibc h l) h1 mallocFree_verified hs hr
  exact ⟨t, ho⟩

/-- The bytes of `"hi"`. -/
def hiBytes : List Byte := [104, 105]

/-- `puts ("hi")`. -/
def hello : Prog putsSig Int :=
  .call .puts (by decide : LFn.puts ∈ putsList) (hiBytes) fun r => .ret r

/-- **`puts ("hi")`: on success, `hi\n` was written.** -/
theorem hello_verified (K L : FmtSet) :
    hello.Verified (stdioC putsList K L)
      (fun r g => 0 ≤ r → g.out = hiBytes ++ [10]) := by
  intro g hg
  simp only [hello, Prog.WP]
  refine ⟨(by decide : (0 : Byte) ∉ hiBytes), fun r g' ⟨_, h⟩ hr => ?_⟩
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h, show g.out = [] from hg]; rfl
  · omega

/-- The `puts` signature inside the C library. -/
def putsInLibc (k : Nat) : Sig.Hom putsSig (libcSig k stdioList) :=
  (stdioIncl (by decide : ∀ f ∈ putsList, f ∈ stdioList)).comp (Sig.inr _ _)

theorem hello_on_libc (k : Nat) {K L : FmtSet} {X : Model (libcSig k stdioList)}
    (hX : Sat X (libcC k stdioList K L)) {s : X.St} (hs : X.init s) {o : Outcome X.St Int}
    (hr : Prog.Run X (hello.map (putsInLibc k)) s o) :
    ∃ r t, o = .done r t ∧ (0 ≤ r → ∃ g : Streams, g.out = hiBytes ++ [10]) := by
  have h1 : Sat ((X.reduct (Sig.inr _ _)).reduct (stdioIncl (by decide)))
      (stdioC putsList K L) := by
    rw [← stdioC_restrict (by decide : ∀ f ∈ putsList, f ∈ stdioList) K L]
    exact (libc_stdio_factor stdioList_noalloc hX).restrict _
  obtain ⟨r, t, ho, g, hg⟩ := client_reduct' (putsInLibc k) h1 (hello_verified K L) hs hr
  exact ⟨r, t, ho, fun h => ⟨g, hg h⟩⟩

/-! ## The diagram -/

/-- The expected diagram text. -/
def Diagram.expected : String :=
  "graph BT
  A1[\"allocSig 1<br/>allocC 1<br/><small>malloc, free</small>\"]
  A2[\"allocSig 2<br/>allocC 2<br/><small>malloc, free, calloc</small>\"]
  A3[\"allocSig 3<br/>allocC 3<br/><small>malloc, free, calloc, realloc</small>\"]
  A4[\"allocSig 4<br/>allocC 4<br/><small>malloc, free, calloc, realloc, aligned_alloc, posix_memalign, malloc_usable_size</small>\"]
  P[\"putsSig<br/>stdioC putsList K L<br/><small>putchar, puts</small>\"]
  O[\"outSig<br/>stdioC outList K L<br/><small>putchar, puts, printf</small>\"]
  I[\"inSig<br/>stdioC inList K L<br/><small>getchar, scanf</small>\"]
  S[\"stdioSig<br/>stdioC stdioList K L<br/><small>putchar, puts, printf, getchar, scanf</small>\"]
  L[\"libcSig 4 stdioList<br/>libcC 4 stdioList K L<br/><small>malloc, free, calloc, realloc, aligned_alloc, posix_memalign, malloc_usable_size, putchar, puts, printf, getchar, scanf</small>\"]
  A1 --> A2
  A2 --> A3
  A3 --> A4
  A4 -- ⊗ --> L
  P --> O
  O --> S
  I --> S
  S -- ⊗ --> L
"

end Silmaril.Libc.Contracts

#guard Silmaril.Libc.Contracts.Diagram.mermaid == Silmaril.Libc.Contracts.Diagram.expected
