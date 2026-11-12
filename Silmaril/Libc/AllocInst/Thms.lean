module

public import Silmaril.Libc.AllocInst.Defs
public import Silmaril.Libc.Alloc.Thms

/-!
# The allocator institution, abstract level: orders, the bottom allocator, the ladder

PROVED (standard axioms), names in `Silmaril.Libc`:

* the orders: `AbsAlloc.SatOn.mono_rel` (a looser relation), `SatOn.mono_frag` (fewer
  functions), `SatOn.mono_pre` (fewer client calls); `Functional.live` (a functional instance for
  `R` is a live instance for `R.toCap`), `Live.safe`, `Functional.safe`;
* **the bottom allocator**: `never_safe` (an instance of `safe` on the whole API),
  `never_live` (live for the empty capacity model), `never_ret_zero` (every call returns `0`),
  `never_succLe` (below every allocator in the success order);
* **the ladder, through the reference models of its x86 rows**: `ofRef_funSteps` (an allocator
  built from a reference model is functional for it, once safe), `neverMF_safe` and
  `neverMF_functional` (rung 01), `bump_safe` and `bump_functional` (rung 02, on positive
  requests), and **`bump_unsafe_zero`**: rung 02 is *not* safe once `malloc (0)` may be called
  (it returns the same address twice; `allocLoose` gives every live block, even an empty one, a
  footprint of one byte, as C's "as if the size were some nonzero value").
-/

@[expose] public section

namespace Silmaril.Libc

open Silmaril.Libc.X86Alloc (CapModel RefModel)

namespace AbsAlloc

variable {A : AbsAlloc} {F F' : Frag} {P P' : ACall → Prop} {Inv : A.St → Prop} {T T' : AllocRel}

theorem SatOn.mono_rel (h : A.SatOn F P Inv T) (hT : T.Le T') : A.SatOn F P Inv T' :=
  ⟨h.init, h.empty, fun s c o hi hc hp hs => hT _ _ _ (h.rel s c o hi hc hp hs), h.inv, h.progress⟩

theorem SatOn.mono_frag (h : A.SatOn F P Inv T) (hF : ∀ f ∈ F', f ∈ F) : A.SatOn F' P Inv T :=
  have hc : ∀ c : ACall, c.In F' → c.In F := fun _ hc f hf => hF f (hc f hf)
  ⟨h.init, h.empty, fun s c o hi hc' hp hs => h.rel s c o hi (hc c hc') hp hs,
    fun s c t r hi hc' hp hs => h.inv s c t r hi (hc c hc') hp hs,
    fun s c hi hc' hp => h.progress s c hi (hc c hc') hp⟩

theorem SatOn.mono_pre (h : A.SatOn F P Inv T) (hP : ∀ c, P' c → P c) : A.SatOn F P' Inv T :=
  ⟨h.init, h.empty, fun s c o hi hc hp hs => h.rel s c o hi hc (hP c hp) hs,
    fun s c t r hi hc hp hs => h.inv s c t r hi hc (hP c hp) hs,
    fun s c hi hc hp => h.progress s c hi hc (hP c hp)⟩

theorem Live.safe {C : CapModel} {α : A.St → C.St} (h : A.Live F P C α) : A.Safe F P :=
  let ⟨Inv, hs, _⟩ := h; ⟨Inv, hs⟩

theorem Functional.safe {R : RefModel} {α : A.St → R.St} (h : A.Functional F P R α) :
    A.Safe F P :=
  let ⟨Inv, hs, _⟩ := h; ⟨Inv, hs⟩

/-- **Functional implies live**, for the reference model's own capacity model. -/
theorem Functional.live {R : RefModel} {α : A.St → R.St} (h : A.Functional F P R α) :
    A.Live F P R.toCap α := by
  obtain ⟨Inv, hs, hm, hf⟩ := h
  refine ⟨Inv, hs, fun s n t r hi hF hp hst => ?_, hf⟩
  obtain ⟨hr, ha, hz⟩ := hm s n t r hi hF hp hst
  refine ⟨fun h0 hav => hav ?_, fun h0 => ha h0, hz⟩
  apply BitVec.eq_of_toNat_eq
  rw [← hr, h0]; rfl

end AbsAlloc

/-! ## The bottom allocator -/

theorem never_ret_zero {h : Heap} {c : ACall} {t : Heap} {r : Nat}
    (hs : AbsAlloc.never.step h c (some (t, r))) : r = 0 := by
  simp only [AbsAlloc.never] at hs
  cases c with
  | malloc n => cases hs; rfl
  | calloc k m => cases hs; rfl
  | realloc p n =>
    simp only [allocNever] at hs
    split at hs
    · cases hs; rfl
    · split at hs
      · split at hs <;> (cases hs; rfl)
      · cases hs
  | free p =>
    simp only [allocNever, allocLoose] at hs
    split at hs
    · cases hs; rfl
    · split at hs
      · cases hs; rfl
      · cases hs
  | access p =>
    simp only [allocNever, allocLoose] at hs
    rcases hs with ⟨-, hs⟩ | ⟨-, hs⟩ <;> cases hs; rfl

/-- **The bottom allocator is an instance of `safe`** on the whole API, for every client. -/
theorem never_safe (P : ACall → Prop := fun _ => True) : AbsAlloc.never.Safe Frag.all P := by
  refine ⟨fun _ => True, trivial, rfl, fun s c o _ _ _ hs => ?_, fun _ _ _ _ _ _ _ _ => trivial,
    fun s c _ _ _ => ?_⟩
  · cases o with
    | none => exact allocNever_le_loose _ _ _ hs
    | some x => exact allocNever_le_loose _ _ _ hs
  · obtain ⟨o, ho⟩ := allocNever_progress s c
    cases o with
    | ok h r => exact ⟨some (h, r), ho⟩
    | ub => exact ⟨none, ho⟩

/-- The bottom allocator is live for the empty capacity model. -/
theorem never_live (F : Frag) (P : ACall → Prop) :
    AbsAlloc.never.Live F P capNone (fun _ => ()) := by
  obtain ⟨Inv, hs⟩ := never_safe P
  refine ⟨Inv, hs.mono_frag (fun f _ => by cases f <;> decide), ?_, ?_⟩
  · intro s n t r _ _ _ hst
    have := never_ret_zero hst
    exact ⟨fun _ h => h, fun h0 => absurd this h0, fun _ => rfl⟩
  · intro _ _ _ _ _ _ _ _ _ _ _; rfl

/-- **The bottom allocator is least in the success order**: it never succeeds. -/
theorem never_succLe (B : AbsAlloc) : AbsAlloc.never.SuccLe B := by
  rintro s c ⟨t, r, hs, hr⟩
  exact absurd (never_ret_zero hs) hr

/-! ## Allocators of reference models: the ladder -/

/-- **An allocator built from a reference model meets its functional steps**, under every
invariant. -/
theorem ofRef_funSteps (R : RefModel) (s0 : R.St) (F : Frag) (P : ACall → Prop)
    (Inv : (AbsAlloc.ofRef R s0).St → Prop) :
    (AbsAlloc.ofRef R s0).FunSteps F P Inv R Prod.fst := by
  refine ⟨fun s n t r _ _ _ hs => ?_, fun s p n t r _ _ _ hp hp0 hs => ?_⟩
  · simp only [AbsAlloc.ofRef] at hs
    by_cases h0 : R.malloc s.1 n = 0
    · simp only [h0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact ⟨by rw [h0]; rfl, fun h => absurd rfl h, fun _ => rfl⟩
    · simp only [h0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      refine ⟨rfl, fun _ => rfl, fun h => absurd (BitVec.eq_of_toNat_eq (by rw [h]; rfl)) h0⟩
  · have hp' : (AbsAlloc.ofRef R s0).heap s = s.2 := rfl
    rw [hp'] at hp
    simp only [AbsAlloc.ofRef, hp0, ↓reduceIte, hp, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, -⟩ := hs
    rfl

/-- The calls of `malloc`/`free` of an `ofRef` allocator: the `free` and `access` outcomes are
those of `allocLoose`, and keep any invariant of the visible heap that removal keeps. -/
theorem ofRef_free_loose (R : RefModel) (s0 : R.St) {x : R.St × Heap} {p : Nat}
    {o : Option ((AbsAlloc.ofRef R s0).St × Nat)} (hs : (AbsAlloc.ofRef R s0).step x (.free p) o) :
    allocLoose x.2 (.free p) ((AbsAlloc.ofRef R s0).out o) := by
  by_cases h0 : p = 0
  · simp only [h0, ↓reduceIte] at hs; subst hs; simp [allocLoose, h0, AbsAlloc.out]
  · simp only [h0, ↓reduceIte] at hs
    cases hx : x.2 p with
    | none => simp only [hx] at hs; subst hs; simp [allocLoose, h0, hx, AbsAlloc.out]
    | some n => simp only [hx] at hs; subst hs; simp [allocLoose, h0, hx, AbsAlloc.out]

theorem ofRef_access_loose (R : RefModel) (s0 : R.St) {x : R.St × Heap} {p : Nat}
    {o : Option ((AbsAlloc.ofRef R s0).St × Nat)} (hs : (AbsAlloc.ofRef R s0).step x (.access p) o) :
    allocLoose x.2 (.access p) ((AbsAlloc.ofRef R s0).out o) := by
  rcases hs with ⟨ho, rfl⟩ | ⟨ho, rfl⟩
  · exact Or.inl ⟨ho, rfl⟩
  · exact Or.inr ⟨ho, rfl⟩

theorem ofRef_progress_free (R : RefModel) (s0 : R.St) (x : R.St × Heap) (p : Nat) :
    ∃ o, (AbsAlloc.ofRef R s0).step x (.free p) o := by
  simp only [AbsAlloc.ofRef]
  split
  · exact ⟨_, rfl⟩
  · split <;> exact ⟨_, rfl⟩

theorem ofRef_progress_access (R : RefModel) (s0 : R.St) (x : R.St × Heap) (p : Nat) :
    ∃ o, (AbsAlloc.ofRef R s0).step x (.access p) o := by
  by_cases h : x.2.Owns p
  · exact ⟨_, Or.inl ⟨h, rfl⟩⟩
  · exact ⟨_, Or.inr ⟨h, rfl⟩⟩

theorem ofRef_free_some {R : RefModel} {s0 : R.St} {x : R.St × Heap} {p : Nat}
    {t : (AbsAlloc.ofRef R s0).St} {r : Nat} (hs : (AbsAlloc.ofRef R s0).step x (.free p) (some (t, r))) :
    t.2 = x.2 ∨ t.2 = x.2.remove p := by
  simp only [AbsAlloc.ofRef] at hs
  split at hs
  · cases hs; exact Or.inl rfl
  · split at hs
    · cases hs; exact Or.inr rfl
    · cases hs

theorem ofRef_access_some {R : RefModel} {s0 : R.St} {x : R.St × Heap} {p : Nat}
    {t : (AbsAlloc.ofRef R s0).St} {r : Nat} (hs : (AbsAlloc.ofRef R s0).step x (.access p) (some (t, r))) :
    t = x := by
  simp only [AbsAlloc.ofRef] at hs
  rcases hs with ⟨-, hs⟩ | ⟨-, hs⟩
  · cases hs; rfl
  · cases hs

theorem mf_not_calloc {k m : Nat} (h : (ACall.calloc k m).In Frag.mf) : False := by
  have := h .calloc rfl; simp [Frag.mf] at this

theorem mf_not_realloc {p n : Nat} (h : (ACall.realloc p n).In Frag.mf) : False := by
  have := h .realloc rfl; simp [Frag.mf] at this

/-- **Rung 01 is an instance of `safe`** on malloc/free, for every client. -/
theorem neverMF_safe (P : ACall → Prop := fun _ => True) : neverMF.Safe Frag.mf P := by
  refine ⟨fun _ => True, trivial, rfl, fun s c o _ hc _ hs => ?_, fun _ _ _ _ _ _ _ _ => trivial,
    fun s c _ hc _ => ?_⟩
  · cases c with
    | malloc n =>
      simp only [↓reduceIte] at hs
      subst hs
      exact Or.inl rfl
    | free p => exact ofRef_free_loose _ _ hs
    | access p => exact ofRef_access_loose _ _ hs
    | calloc k m => exact (mf_not_calloc hc).elim
    | realloc p n => exact (mf_not_realloc hc).elim
  · cases c with
    | malloc n => exact ⟨_, rfl⟩
    | free p => exact ofRef_progress_free _ _ s p
    | access p => exact ofRef_progress_access _ _ s p
    | calloc k m => exact (mf_not_calloc hc).elim
    | realloc p n => exact (mf_not_realloc hc).elim

/-- Rung 01 is functional for its (never-allocating) reference model. -/
theorem neverMF_functional (P : ACall → Prop := fun _ => True) :
    neverMF.Functional Frag.mf P neverRef Prod.fst :=
  let ⟨Inv, hs⟩ := neverMF_safe P
  ⟨Inv, hs, ofRef_funSteps _ _ _ _ _⟩

open Silmaril.Libc.X86Alloc.Ladder in
theorem bump_arena_word {u : Nat} (hu : u ≤ Bump.size) :
    (BitVec.ofNat 64 (Bump.arena + u)).toNat = Bump.arena + u := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by simp [Bump.arena, Bump.size] at hu ⊢; omega)

open Silmaril.Libc.X86Alloc.Ladder in
/-- `bump`'s `malloc`: the next `n` bytes of the arena when they fit, else failure. -/
theorem bump_malloc {s : bump.St} {n : Nat} {o : Option (bump.St × Nat)}
    (hu : s.1 ≤ Bump.size) (hs : bump.step s (.malloc n) o) :
    (n ≤ Bump.size - s.1 ∧
      o = some (((s.1 + n : Nat), s.2.add (Bump.arena + s.1) n), Bump.arena + s.1)) ∨
    (¬ n ≤ Bump.size - s.1 ∧ o = some (s, 0)) := by
  by_cases hn : n ≤ Bump.size - s.1
  · have hw := bump_arena_word (u := s.1) hu
    have hne : BitVec.ofNat 64 (Bump.arena + s.1) ≠ 0 := by
      intro h; rw [h] at hw; simp [Bump.arena] at hw; omega
    have hm : Bump.ref.malloc s.1 n = BitVec.ofNat 64 (Bump.arena + s.1) := by
      show (if n ≤ Bump.size - s.1 then _ else _) = _
      simp only [hn, ↓reduceIte]
    refine Or.inl ⟨hn, ?_⟩
    have hs' : o = _ := hs
    simp only [hm, hne, ↓reduceIte, hw] at hs'
    rw [hs']; rfl
  · have hm : bumpRef.malloc s.1 n = 0 := by
      show (if n ≤ Bump.size - s.1 then _ else _) = _
      simp only [hn, ↓reduceIte]
    refine Or.inr ⟨hn, ?_⟩
    have hs' : o = _ := hs
    split at hs'
    · exact hs'
    · rename_i hne; exact absurd hm hne

open Silmaril.Libc.X86Alloc.Ladder in
/-- **Rung 02 is an instance of `safe`** on malloc/free, for clients that make positive
requests only, under `bumpInv`. -/
theorem bump_satOn : bump.SatOn Frag.mf PosReq bumpInv allocLoose := by
  refine ⟨⟨Nat.zero_le _, fun a m h => by cases h⟩, rfl, fun s c o hi hc hp hs => ?_,
    fun s c t r hi hc hp hs => ?_, fun s c _ hc _ => ?_⟩
  · cases c with
    | malloc n =>
      rcases bump_malloc hi.1 hs with ⟨hn, rfl⟩ | ⟨-, rfl⟩
      · refine Or.inr ⟨Bump.arena + s.1, ⟨by simp [Bump.arena], ?_, fun a m ha => ?_⟩, rfl⟩
        · have := hi.1; simp [Bump.arena, Bump.size] at this hn ⊢; omega
        · obtain ⟨h1, h2, h3⟩ := hi.2 a m ha
          right; omega
      · exact Or.inl rfl
    | free p => exact ofRef_free_loose _ _ hs
    | access p => exact ofRef_access_loose _ _ hs
    | calloc k m => exact (mf_not_calloc hc).elim
    | realloc p n => exact (mf_not_realloc hc).elim
  · cases c with
    | malloc n =>
      have hp : 0 < n := hp
      rcases bump_malloc hi.1 hs with ⟨hn, he⟩ | ⟨-, he⟩
      · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj he)
        refine ⟨?_, fun a m ha => ?_⟩
        · exact Nat.add_le_of_le_sub' hi.1 hn
        · show Bump.arena ≤ a ∧ a + m ≤ Bump.arena + (s.1 + n) ∧ 0 < m
          simp only [Heap.add] at ha
          split at ha
          · cases ha; rename_i h; subst h; omega
          · obtain ⟨h1, h2, h3⟩ := hi.2 a m ha; omega
      · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj he)
        exact hi
    | free p =>
      simp only [Bump.ref] at hs
      split at hs
      · cases hs; exact hi
      · split at hs
        · cases hs
          refine ⟨hi.1, fun a m ha => ?_⟩
          simp only [Heap.remove] at ha
          split at ha
          · cases ha
          · exact hi.2 a m ha
        · cases hs
    | access p => rw [ofRef_access_some hs]; exact hi
    | calloc k m => exact (mf_not_calloc hc).elim
    | realloc p n => exact (mf_not_realloc hc).elim
  · cases c with
    | malloc n => exact ⟨_, rfl⟩
    | free p => exact ofRef_progress_free _ _ s p
    | access p => exact ofRef_progress_access _ _ s p
    | calloc k m => exact (mf_not_calloc hc).elim
    | realloc p n => exact (mf_not_realloc hc).elim

theorem bump_safe : bump.Safe Frag.mf PosReq := ⟨bumpInv, bump_satOn⟩

/-- **Rung 02 is functional for its reference model** (the model of its x86
functional row), on positive requests. -/
theorem bump_functional :
    bump.Functional Frag.mf PosReq bumpRef Prod.fst :=
  ⟨bumpInv, bump_satOn, ofRef_funSteps _ _ _ _ _⟩

/-- Rung 02 is live for the bump capacity model of its reference model. -/
theorem bump_live :
    bump.Live Frag.mf PosReq bumpRef.toCap Prod.fst :=
  bump_functional.live

open Silmaril.Libc.X86Alloc.Ladder in
/-- **Rung 02 is not safe for a client that calls `malloc (0)`**: two `malloc (0)` return the same
address, while `allocLoose` gives each live block (even an empty one) its own byte. -/
theorem bump_unsafe_zero : ¬ bump.Safe Frag.mf := by
  rintro ⟨Inv, h⟩
  have e : BitVec.ofNat 64 (Bump.arena + 0) ≠ 0 := by decide
  have s1 : bump.step bump.init (.malloc 0)
      (some (((0 : Nat), Heap.empty.add Bump.arena 0), Bump.arena)) := by
    simp only [Bump.ref, Nat.zero_le, ↓reduceIte, e]
    rfl
  have hin : (ACall.malloc 0).In Frag.mf := fun f hf => by cases hf; simp [Frag.mf]
  have i1 := h.inv _ _ _ _ h.init hin trivial s1
  have s2 : bump.step ((0 : Nat), Heap.empty.add Bump.arena 0) (.malloc 0)
      (some (((0 : Nat), (Heap.empty.add Bump.arena 0).add Bump.arena 0), Bump.arena)) := by
    simp only [Bump.ref, Nat.zero_le, ↓reduceIte, e]
    rfl
  have hr := h.rel _ _ _ i1 hin trivial s2
  simp only [AbsAlloc.out, allocLoose, allocate] at hr
  rcases hr with hr | ⟨p, ⟨-, -, hf⟩, hr⟩
  · injection hr with _ h2
    exact absurd h2 (by decide)
  · injection hr with _ h2
    subst h2
    have := hf Bump.arena 0 (by simp [Heap.add])
    simp at this
    omega

end Silmaril.Libc
