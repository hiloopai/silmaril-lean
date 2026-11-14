module

public import Silmaril.X86.Pool.Defs

/-!
# Proofs: the local/shared split of fragments, and pool fragment algebra

* `toFrag_split`: `toFrag m = union (localFrag m.core) (sharedFrag m.memory)`.
* `proj_poolFrag`: thread `t`'s view of the pool fragment is the total fragment of its
  single-thread state.
* `embed`/`embedS`/`proj` and the pool `union`/`Disjoint`/`Le` lemmas used by `Pool/Par`.
* `poolFrag_step`: one SC step of a thread that changes only its fragment `h` changes the pool
  fragment only on `embed t h`, which it re-values.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Pool

open Silmaril.X86 (State MState)
open Silmaril.Process (Memory)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint Le reval)
open Silmaril.X86.MemEvent (ChangesWithin)
open Silmaril.X86.Pool

variable {Tid : Type}

/-! ## The split of `toFrag` -/

theorem toFrag_split (m : MState) :
    toFrag m = Frag.union (localFrag m.core) (sharedFrag m.memory) := by
  funext l
  cases l <;> rfl

theorem toFrag_local {m : MState} {l : Loc} (hl : l.isLocal = true) :
    toFrag m l = localFrag m.core l := by
  cases l <;> simp_all [Loc.isLocal, toFrag, localFrag]

theorem toFrag_shared {m : MState} {l : Loc} (hl : l.isLocal = false) :
    toFrag m l = sharedFrag m.memory l := by
  cases l <;> simp_all [Loc.isLocal, toFrag, sharedFrag]

theorem localFrag_shared {c : State} {l : Loc} (hl : l.isLocal = false) : localFrag c l = none := by
  cases l <;> simp_all [Loc.isLocal, localFrag]

theorem sharedFrag_local {mem : Memory} {l : Loc} (hl : l.isLocal = true) :
    sharedFrag mem l = none := by
  cases l <;> simp_all [Loc.isLocal, sharedFrag]

theorem toFrag_isSome (m : MState) (l : Loc) : (toFrag m l).isSome := by
  cases l <;> simp [toFrag]

/-! ## Single-thread fragments -/

theorem union_of_none {a b : Frag} {l : Loc} (e : a l = none) : union a b l = b l := by
  simp [union, e]

theorem union_of_some {a b : Frag} {l : Loc} {v : Val} (e : a l = some v) :
    union a b l = some v := by
  simp [union, e]

theorem union_empty (h : Frag) : union h Frag.empty = h := by
  funext l; cases e : h l <;> simp [union, e, Frag.empty]

theorem le_union {a b s : Frag} (ha : Le a s) (hb : Le b s) : Le (union a b) s := by
  intro l v e
  cases e' : a l with
  | none => rw [union_of_none e'] at e; exact hb l v e
  | some w => rw [union_of_some e'] at e; cases e; exact ha l _ e'

theorem le_union_left (a b : Frag) : Le a (union a b) := fun _ _ e => union_of_some e

theorem le_union_right {a b : Frag} (hd : Disjoint a b) : Le b (union a b) := by
  intro l v e
  rcases hd l with e' | e'
  · rw [union_of_none e', e]
  · rw [e'] at e; cases e

theorem reval_none {h s : Frag} {l : Loc} (e : h l = none) : reval h s l = none := by
  simp [reval, e]

theorem reval_of_some {h s : Frag} {l : Loc} (e : (h l).isSome) : reval h s l = s l := by
  simp [reval, e]

theorem reval_eq_none {h s : Frag} {l : Loc} (hs : (s l).isSome) :
    reval h s l = none ↔ h l = none := by
  cases e : h l <;> simp_all [reval]
  intro e'; rw [e'] at hs; cases hs

theorem reval_toFrag_none {h : Frag} {m : MState} {l : Loc} :
    reval h (toFrag m) l = none ↔ h l = none :=
  reval_eq_none (toFrag_isSome m l)

theorem disjoint_reval_left {a b : Frag} {m : MState} (hd : Disjoint a b) :
    Disjoint (reval a (toFrag m)) b := by
  intro l
  rcases hd l with e | e
  · exact .inl (reval_none e)
  · exact .inr e

theorem le_reval_toFrag (h : Frag) (m : MState) : Le (reval h (toFrag m)) (toFrag m) := by
  intro l v e
  cases e' : h l with
  | none => rw [reval_none e'] at e; cases e
  | some w => rw [reval_of_some (by simp [e'])] at e; exact e

/-! ## Pool fragments -/

namespace PF

theorem union_of_none {a b : PFrag Tid} {l : PLoc Tid} (e : a l = none) :
    PFrag.union a b l = b l := by
  simp [PFrag.union, e]

theorem union_of_some {a b : PFrag Tid} {l : PLoc Tid} {v : Val} (e : a l = some v) :
    PFrag.union a b l = some v := by
  simp [PFrag.union, e]

theorem union_eq_none {a b : PFrag Tid} {l : PLoc Tid} :
    PFrag.union a b l = none ↔ a l = none ∧ b l = none := by
  cases e : a l <;> simp [PFrag.union, e]

theorem le_union_left (a b : PFrag Tid) : PFrag.Le a (PFrag.union a b) :=
  fun _ _ e => union_of_some e

theorem le_union_right {a b : PFrag Tid} (hd : PFrag.Disjoint a b) :
    PFrag.Le b (PFrag.union a b) := by
  intro l v e
  rcases hd l with e' | e'
  · rw [union_of_none e', e]
  · rw [e'] at e; cases e

theorem le_trans {a b c : PFrag Tid} (h₁ : PFrag.Le a b) (h₂ : PFrag.Le b c) : PFrag.Le a c :=
  fun l v e => h₂ l v (h₁ l v e)

theorem disjoint_symm {a b : PFrag Tid} (h : PFrag.Disjoint a b) : PFrag.Disjoint b a :=
  fun l => (h l).symm

theorem disjoint_union_right {a b c : PFrag Tid} :
    PFrag.Disjoint a (PFrag.union b c) ↔ PFrag.Disjoint a b ∧ PFrag.Disjoint a c := by
  constructor
  · intro h
    refine ⟨fun l => ?_, fun l => ?_⟩
    · rcases h l with e | e
      · exact .inl e
      · exact .inr (union_eq_none.mp e).1
    · rcases h l with e | e
      · exact .inl e
      · exact .inr (union_eq_none.mp e).2
  · rintro ⟨h₁, h₂⟩ l
    rcases h₁ l with e | e
    · exact .inl e
    · rcases h₂ l with e' | e'
      · exact .inl e'
      · exact .inr (union_eq_none.mpr ⟨e, e'⟩)

theorem disjoint_union_left {a b c : PFrag Tid} :
    PFrag.Disjoint (PFrag.union a b) c ↔ PFrag.Disjoint a c ∧ PFrag.Disjoint b c := by
  constructor
  · intro h
    have := disjoint_union_right.mp (disjoint_symm h)
    exact ⟨disjoint_symm this.1, disjoint_symm this.2⟩
  · rintro ⟨h₁, h₂⟩
    exact disjoint_symm (disjoint_union_right.mpr ⟨disjoint_symm h₁, disjoint_symm h₂⟩)

theorem union_left_comm {a b c : PFrag Tid} (hd : PFrag.Disjoint a b) :
    PFrag.union a (PFrag.union b c) = PFrag.union b (PFrag.union a c) := by
  funext l
  rcases hd l with e | e
  · rw [union_of_none e]
    cases e' : b l with
    | none => rw [union_of_none e', union_of_none e', union_of_none e]
    | some v => rw [union_of_some e', union_of_some e']
  · rw [union_of_none e (a := b)]
    cases e' : a l with
    | none => rw [union_of_none e', union_of_none e', union_of_none e]
    | some v => rw [union_of_some e', union_of_some e']

theorem union_assoc (a b c : PFrag Tid) :
    PFrag.union (PFrag.union a b) c = PFrag.union a (PFrag.union b c) := by
  funext l
  cases e : a l with
  | none => simp [PFrag.union, e]
  | some v => simp [PFrag.union, e]

theorem union_comm {a b : PFrag Tid} (hd : PFrag.Disjoint a b) :
    PFrag.union a b = PFrag.union b a := by
  funext l
  rcases hd l with e | e <;> cases e1 : a l <;> cases e2 : b l <;> simp_all [PFrag.union]

theorem empty_union (a : PFrag Tid) : PFrag.union PFrag.empty a = a := by
  funext l; rfl

theorem disjoint_empty (a : PFrag Tid) : PFrag.Disjoint PFrag.empty a := fun _ => .inl rfl

end PF

section Embed
variable [DecidableEq Tid]
set_option linter.unusedSectionVars false

theorem embed_local_self (t : Tid) (h : Frag) {l : Loc} (hl : l.isLocal = true) :
    embed t h (.local t l) = h l := by
  simp [embed, hl]

theorem embed_local_ne {t t' : Tid} (h : Frag) (l : Loc) (ht : t' ≠ t) :
    embed t h (.local t' l) = none := by
  simp [embed, ht]

theorem embed_local_shared (t t' : Tid) (h : Frag) {l : Loc} (hl : l.isLocal = false) :
    embed t h (.local t' l) = none := by
  simp [embed, hl]

theorem embed_shared {t : Tid} (h : Frag) {l : Loc} (hl : l.isLocal = false) :
    embed t h (.shared l) = h l := by
  simp [embed, hl]

theorem embed_shared_local {t : Tid} (h : Frag) {l : Loc} (hl : l.isLocal = true) :
    embed t h (.shared l) = none := by
  simp [embed, hl]

theorem proj_embed (t : Tid) (h : Frag) : proj t (embed t h) = h := by
  funext l
  cases hl : l.isLocal
  · simp [proj, hl, embed_shared h hl]
  · simp [proj, hl, embed_local_self t h hl]

theorem embedS_shared (h : Frag) {l : Loc} (hl : l.isLocal = false) :
    (embedS h : PFrag Tid) (.shared l) = h l := by
  simp [embedS, hl]

theorem proj_embedS (t : Tid) {r : Frag} (hr : SharedOnly r) :
    proj t (embedS r : PFrag Tid) = r := by
  funext l
  cases hl : l.isLocal
  · simp [proj, hl, embedS]
  · simp [proj, hl, embedS, hr l hl]

theorem embed_empty (t : Tid) : embed t Frag.empty = (PFrag.empty : PFrag Tid) := by
  funext l
  cases l <;> simp [embed, Frag.empty, PFrag.empty]

theorem embedS_empty : embedS Frag.empty = (PFrag.empty : PFrag Tid) := by
  funext l
  cases l <;> simp [embedS, Frag.empty, PFrag.empty]

theorem proj_le {t : Tid} {H S : PFrag Tid} (h : PFrag.Le H S) : Le (proj t H) (proj t S) := by
  intro l v e
  unfold proj at e ⊢
  split at e <;> simp_all <;> exact h _ _ e

theorem le_embed_iff {t : Tid} {h : Frag} {S : PFrag Tid} :
    PFrag.Le (embed t h) S → Le h (proj t S) := by
  intro hl
  have := proj_le (t := t) hl
  rwa [proj_embed] at this

/-- Thread `t`'s view of the pool fragment is its total single-thread fragment. -/
theorem proj_poolFrag {p : Pool Tid} {t : Tid} {c : State} (ht : p.threads t = some c) :
    proj t (poolFrag p) = toFrag ⟨c, p.memory⟩ := by
  funext l
  cases hl : l.isLocal
  · simp only [proj, hl, poolFrag]
    rw [toFrag_shared hl]
    rfl
  · simp only [proj, hl, poolFrag, ht, Option.bind_some, ite_true]
    rw [toFrag_local hl]

theorem disjoint_embed_ne {t t' : Tid} (htt : t ≠ t') {h h' : Frag}
    (hs : ∀ l, l.isLocal = false → h l = none ∨ h' l = none) :
    PFrag.Disjoint (embed t h) (embed t' h') := by
  intro L
  cases L with
  | «local» u l =>
    by_cases e : u = t
    · subst e; exact .inr (embed_local_ne h' l htt)
    · exact .inl (embed_local_ne h l e)
  | shared l =>
    cases hl : l.isLocal
    · rcases hs l hl with e | e
      · exact .inl (by rw [embed_shared h hl, e])
      · exact .inr (by rw [embed_shared h' hl, e])
    · exact .inl (embed_shared_local h hl)

theorem disjoint_of_embed {t : Tid} {h : Frag} {r : Frag} (hr : SharedOnly r)
    (hd : PFrag.Disjoint (embed t h) (embedS r : PFrag Tid)) : Disjoint h r := by
  intro l
  cases hl : l.isLocal
  · rcases hd (.shared l) with e | e
    · exact .inl (by rwa [embed_shared h hl] at e)
    · exact .inr (by rwa [embedS_shared r hl] at e)
  · exact .inr (hr l hl)

/-- The shared locations of two embedded fragments are disjoint if the embeddings are. -/
theorem shared_disjoint_of_embed {t t' : Tid} {h h' : Frag}
    (hd : PFrag.Disjoint (embed t h) (embed t' h')) (l : Loc) (hl : l.isLocal = false) :
    h l = none ∨ h' l = none := by
  rcases hd (.shared l) with e | e
  · exact .inl (by rwa [embed_shared h hl] at e)
  · exact .inr (by rwa [embed_shared h' hl] at e)

/-- Re-valuing keeps the domain of an embedded fragment. -/
theorem embed_reval_none {t : Tid} {h : Frag} {m : MState} {L : PLoc Tid} :
    embed t (reval h (toFrag m)) L = none ↔ embed t h L = none := by
  cases L with
  | «local» u l =>
    simp only [embed]
    split
    · exact reval_toFrag_none
    · exact Iff.rfl
  | shared l =>
    simp only [embed]
    split
    · exact Iff.rfl
    · exact reval_toFrag_none

theorem disjoint_embed_reval {t : Tid} {h : Frag} {m : MState} {X : PFrag Tid}
    (hd : PFrag.Disjoint (embed t h) X) : PFrag.Disjoint (embed t (reval h (toFrag m))) X := by
  intro L
  rcases hd L with e | e
  · exact .inl (embed_reval_none.mpr e)
  · exact .inr e

/-- A part of a thread's single-thread state is a part of the pool. -/
theorem embed_le_poolFrag {p : Pool Tid} {t : Tid} {c : State} {h : Frag}
    (ht : p.threads t = some c) (hl : Le h (toFrag ⟨c, p.memory⟩)) :
    PFrag.Le (embed t h) (poolFrag p) := by
  intro L v e
  cases L with
  | «local» u l =>
    simp only [embed] at e
    split at e
    · rename_i hc
      obtain ⟨rfl, hl'⟩ := hc
      have := hl l v e
      rw [toFrag_local hl'] at this
      simp [poolFrag, ht, this]
    · cases e
  | shared l =>
    simp only [embed] at e
    split at e
    · cases e
    · rename_i hc
      have := hl l v e
      rw [toFrag_shared (by simpa using hc)] at this
      exact this

/-- A part of shared locations of a thread's state is a part of the pool. -/
theorem embedS_le_poolFrag {p : Pool Tid} {c : State} {r : Frag}
    (hl : Le r (toFrag ⟨c, p.memory⟩)) : PFrag.Le (embedS r : PFrag Tid) (poolFrag p) := by
  intro L v e
  cases L with
  | «local» u l => cases e
  | shared l =>
    simp only [embedS] at e
    split at e
    · cases e
    · rename_i hc
      have := hl l v e
      rw [toFrag_shared (by simpa using hc)] at this
      exact this

theorem disjoint_embed_embedS {t : Tid} {h r : Frag} (hd : Disjoint h r) :
    PFrag.Disjoint (embed t h) (embedS r : PFrag Tid) := by
  intro L
  cases L with
  | «local» u l => exact .inr rfl
  | shared l =>
    cases hl : l.isLocal
    · rcases hd l with e | e
      · exact .inl (by rw [embed_shared h hl, e])
      · exact .inr (by rw [embedS_shared r hl, e])
    · exact .inl (embed_shared_local h hl)

theorem poolFrag_step_outside {p : Pool Tid} {t : Tid} {c : State} {h : Frag} {m' : MState}
    (ht : p.threads t = some c) (hcw : ChangesWithin h ⟨c, p.memory⟩ m') {L : PLoc Tid}
    (e : embed t h L = none) :
    poolFrag (⟨Function.update p.threads t (some m'.core), m'.memory⟩ : Pool Tid) L =
      poolFrag p L := by
  cases L with
  | «local» u l =>
    by_cases hu : u = t
    · subst hu
      cases hl : l.isLocal
      · simp [poolFrag, ht, localFrag_shared hl]
      · rw [embed_local_self u h hl] at e
        simp only [poolFrag, Function.update_self, Option.bind_some, ht]
        rw [← toFrag_local hl, ← toFrag_local (m := ⟨c, p.memory⟩) hl]
        exact hcw l e
    · simp [poolFrag, Function.update_of_ne hu]
  | shared l =>
    cases hl : l.isLocal
    · rw [embed_shared h hl] at e
      simp only [poolFrag]
      rw [← toFrag_shared (m := m') hl, ← toFrag_shared (m := ⟨c, p.memory⟩) hl]
      exact hcw l e
    · simp [poolFrag, sharedFrag_local hl]

theorem poolFrag_step_inside {p : Pool Tid} {t : Tid} {h : Frag} {m' : MState} {L : PLoc Tid}
    (e : (embed t h L).isSome) :
    poolFrag (⟨Function.update p.threads t (some m'.core), m'.memory⟩ : Pool Tid) L =
      embed t (reval h (toFrag m')) L := by
  cases L with
  | «local» u l =>
    by_cases hu : u = t
    · subst hu
      cases hl : l.isLocal
      · rw [embed_local_shared u u h hl] at e; cases e
      · rw [embed_local_self u h hl] at e
        rw [embed_local_self u _ hl, reval_of_some e]
        simp only [poolFrag, Function.update_self, Option.bind_some]
        rw [← toFrag_local hl]
    · rw [embed_local_ne h l hu] at e; cases e
  | shared l =>
    cases hl : l.isLocal
    · rw [embed_shared h hl] at e
      rw [embed_shared _ hl, reval_of_some e]
      simp only [poolFrag]
      rw [← toFrag_shared (m := m') hl]
    · rw [embed_shared_local h hl] at e; cases e

/-- **One SC step changes the pool fragment only on the stepping thread's fragment.** -/
theorem poolFrag_step {p : Pool Tid} {t : Tid} {c : State} {h : Frag} {X : PFrag Tid}
    {m' : MState} (ht : p.threads t = some c)
    (hsplit : poolFrag p = PFrag.union (embed t h) X)
    (hcw : ChangesWithin h ⟨c, p.memory⟩ m') :
    poolFrag (⟨Function.update p.threads t (some m'.core), m'.memory⟩ : Pool Tid) =
      PFrag.union (embed t (reval h (toFrag m'))) X := by
  funext L
  cases e : embed t h L with
  | none =>
    rw [PF.union_of_none (embed_reval_none.mpr e), poolFrag_step_outside ht hcw e, hsplit,
      PF.union_of_none e]
  | some v =>
    have hs : (embed t h L).isSome := by simp [e]
    rw [poolFrag_step_inside hs]
    have : (embed t (reval h (toFrag m')) L).isSome := by
      cases e' : embed t (reval h (toFrag m')) L with
      | none => rw [embed_reval_none.mp e'] at e; cases e
      | some _ => rfl
    cases e' : embed t (reval h (toFrag m')) L with
    | none => rw [e'] at this; cases this
    | some w => rw [PF.union_of_some e']

end Embed

end Silmaril.Proofs.X86.Pool
