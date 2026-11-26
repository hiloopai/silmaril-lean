module

public import Silmaril.X86.Open.Thms
public import Silmaril.X86.Safe.Stable.Defs
public import Silmaril.X86.Safe.Thms
public import Silmaril.X86.Sep.Extra.Thms

/-!
# Proofs: stable triples

The structural rules of `TripleS` (frame, consequence, sequencing, the empty run,
existential and pure preconditions, refinement of machines), the bridges to `Sep.Triple`
and `STriple`, and `TripleS.of_local`, the entry point for machine proofs: a run that
leaves every location outside the precondition's fragment unchanged, at **every** state
of the run and not only the last, is a stable triple.

The few fragment lemmas needed are re-proved here (they also exist in
`Silmaril.Proofs.X86.Sep.Algebra`, which this topic may not import).

Names are in `Silmaril.X86.Safe`, so that the header `Safe/Stable/Thms.lean` exports
them.
-/

@[expose] public section

namespace Silmaril.X86.Safe

open Silmaril.X86 (MState)
open Silmaril.Machine.Execution (run run_add Reaches)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint Le reval diff)

/-! ## Fragments -/

namespace Stable

theorem toFrag_isSome (m : MState) (l : Loc) : (toFrag m l).isSome := by
  cases l <;> simp [toFrag]

theorem union_of_none {a b : Frag} {l : Loc} (e : a l = none) : union a b l = b l := by
  simp [union, e]

theorem union_of_some {a b : Frag} {l : Loc} {v : Val} (e : a l = some v) :
    union a b l = some v := by
  simp [union, e]

theorem le_union_left (a b : Frag) : Le a (union a b) := by
  intro l v e; exact union_of_some e

theorem le_union_right {a b : Frag} (hd : Disjoint a b) : Le b (union a b) := by
  intro l v e
  rcases hd l with e' | e'
  · rw [union_of_none e', e]
  · rw [e'] at e; cases e

/-- A fragment contained in `s` is the right part of a split of `s`. -/
theorem union_diff_right {b s : Frag} (hl : Le b s) : union (diff s b) b = s := by
  funext l
  cases e : b l with
  | none => simp only [union, diff, e]; cases s l <;> rfl
  | some v => simp [union, diff, e, hl l v e]

theorem diff_disjoint_right (s b : Frag) : Disjoint (diff s b) b := by
  intro l
  cases e : b l with
  | none => right; rfl
  | some v => left; simp [diff, e]

end Stable

open Stable

/-- **Stability from containment**: if the frame holds of a fragment contained in the
state, `strue ∗ F` holds of the state. -/
theorem stable_of_le {F : SProp} {b s : Frag} (hf : F b) (hl : Le b s) : (strue ∗ F) s :=
  ⟨diff s b, b, diff_disjoint_right s b, (union_diff_right hl).symm, trivial, hf⟩

/-- **Stability from locality**: if `P ∗ F` holds of `m` split as `h₁, h₂`, and `mk`
agrees with `m` outside `h₁`, then `strue ∗ F` holds of `mk`. -/
theorem stable_of_unchanged {F : SProp} {h₁ h₂ : Frag} {m mk : MState} (hd : Disjoint h₁ h₂)
    (he : toFrag m = union h₁ h₂) (hf : F h₂) (hu : Unchanged h₁ m mk) :
    (strue ∗ F) (toFrag mk) := by
  refine stable_of_le hf fun l v e => ?_
  have hn : h₁ l = none := by
    rcases hd l with e' | e'
    · exact e'
    · rw [e'] at e; cases e
  rw [hu l hn, he, union_of_none hn, e]

theorem Unchanged.refl (h : Frag) (m : MState) : Unchanged h m m := fun _ _ => rfl

variable {step step' : MState → Option MState} {P Q R P' Q' : SProp}

/-! ## From runs -/

/-- **A stable triple from a run** that leaves every location outside the precondition's
fragment unchanged at every state of the run, and whose final state, re-valued on that
fragment, satisfies the postcondition. -/
theorem TripleS.of_local
    (h : ∀ m h₁, P h₁ → Le h₁ (toFrag m) →
      ∃ n m', run step n m = some m' ∧ Unchanged h₁ m m' ∧ Q (reval h₁ (toFrag m')) ∧
        ∀ k < n, ∀ mk, run step k m = some mk → Unchanged h₁ m mk) :
    TripleS step P Q := by
  intro F m ⟨h₁, h₂, hd, he, hp, hf⟩
  have hl : Le h₁ (toFrag m) := by rw [he]; exact le_union_left h₁ h₂
  obtain ⟨n, m', hr, hsame, hq, hmid⟩ := h m h₁ hp hl
  refine ⟨n, m', hr, ⟨reval h₁ (toFrag m'), h₂, ?_, ?_, hq, hf⟩,
    fun k hk mk hrk => stable_of_unchanged hd he hf (hmid k hk mk hrk)⟩
  · intro l
    rcases hd l with e | e
    · left; simp [reval, e]
    · right; exact e
  · funext l
    cases e : h₁ l with
    | none =>
      rw [hsame l e, he, union_of_none e, union_of_none]
      simp [reval, e]
    | some v =>
      rw [union_of_some (v := (toFrag m' l).get (Sep.toFrag_isSome m' l))]
      · simp
      · simp [reval, e]

/-- A refining machine runs through the same states. -/
theorem run_of_refines (h : Refines step step') :
    ∀ (k : Nat) {a b : MState}, run step k a = some b → run step' k a = some b
  | 0, _, _, hr => hr
  | k + 1, a, b, hr => by
    simp only [run] at hr ⊢
    cases e : step a with
    | none => rw [e] at hr; cases hr
    | some c =>
      rw [e] at hr
      rw [h e]
      exact run_of_refines h k hr

/-! ## Bridges -/

/-- A stable triple on the open machine is a triple. -/
theorem TripleS.toTriple (h : TripleS Silmaril.X86.Open.isa.step P Q) :
    Sep.Triple Silmaril.X86.Open.isa P Q := by
  intro F m _ hm
  obtain ⟨n, m', hr, hq, -⟩ := h F m hm
  exact ⟨m', ⟨n, hr⟩, hq⟩

/-- A stable triple on any machine gives a run to the postcondition. -/
theorem TripleS.reaches (h : TripleS step P Q) {F : SProp} {m : MState}
    (hm : (P ∗ F) (toFrag m)) : ∃ m', Reaches step m m' ∧ (Q ∗ F) (toFrag m') := by
  obtain ⟨n, m', hr, hq, -⟩ := h F m hm
  exact ⟨m', ⟨n, hr⟩, hq⟩

/-- `SafeNS` forgets its state invariant. -/
theorem safeN_of_safeNS {I : Silmaril.X86.SegVC.Isa MState} {S Q : MState → Prop} :
    ∀ {n : Nat} {m : MState}, SafeNS I.step S Q n m → SafeN I Q n m
  | 0, _, _ => trivial
  | _ + 1, _, .inl hq => .inl hq
  | _ + 1, _, .inr ⟨_, m', hs, h⟩ => .inr ⟨m', hs, safeN_of_safeNS h⟩

/-- A stable step-indexed triple is a step-indexed triple. -/
theorem STripleS.toSTriple {n : Nat} (h : STripleS Silmaril.X86.Open.isa.step n P Q) :
    STriple Silmaril.X86.Open.isa n P Q :=
  fun F m _ hm => safeN_of_safeNS (h F m hm)

/-- A run to `Q` whose earlier states satisfy `S` gives `SafeNS` at every index. -/
theorem safeNS_of_run {S Q : MState → Prop} :
    ∀ (k : Nat) {m m' : MState}, run step k m = some m' → Q m' →
      (∀ j < k, ∀ mj, run step j m = some mj → S mj) → ∀ n, SafeNS step S Q n m
  | _, _, _, _, _, _, 0 => trivial
  | 0, m, m', hr, hq, _, _ + 1 => by
    simp only [run] at hr
    cases hr
    exact .inl hq
  | k + 1, m, m', hr, hq, hs, n + 1 => by
    simp only [run] at hr
    cases e : step m with
    | none => rw [e] at hr; cases hr
    | some m₁ =>
      rw [e] at hr
      refine .inr ⟨hs 0 (by omega) m rfl, m₁, e, safeNS_of_run k hr hq (fun j hj mj hrj => ?_) n⟩
      exact hs (j + 1) (by omega) mj (by simp only [run, e]; exact hrj)

/-- A stable total triple gives the stable step-indexed triple at every index. -/
theorem TripleS.toSTripleS (h : TripleS step P Q) (n : Nat) : STripleS step n P Q := by
  intro F m hm
  obtain ⟨k, m', hr, hq, hs⟩ := h F m hm
  exact safeNS_of_run k hr hq hs n

/-! ## Structural rules -/

/-- **The frame rule.** -/
theorem TripleS.frame (h : TripleS step P Q) (R : SProp) : TripleS step (P ∗ R) (Q ∗ R) := by
  intro F m hm
  rw [sep_assoc] at hm
  obtain ⟨n, m', hr, hq, hs⟩ := h (R ∗ F) m hm
  refine ⟨n, m', hr, by rw [sep_assoc]; exact hq, fun k hk mk hrk => ?_⟩
  have := hs k hk mk hrk
  rw [← sep_assoc] at this
  exact sep_mono_left F (entails_strue _) _ this

/-- **Consequence.** -/
theorem TripleS.conseq (hp : P' ⊢ₛ P) (hq : Q ⊢ₛ Q') (h : TripleS step P Q) :
    TripleS step P' Q' := by
  intro F m hm
  obtain ⟨n, m', hr, hQ, hs⟩ := h F m (sep_mono_left F hp _ hm)
  exact ⟨n, m', hr, sep_mono_left F hq _ hQ, hs⟩

theorem TripleS.pre (hp : P' ⊢ₛ P) (h : TripleS step P Q) : TripleS step P' Q :=
  TripleS.conseq hp (entails_refl Q) h

theorem TripleS.post (hq : Q ⊢ₛ Q') (h : TripleS step P Q) : TripleS step P Q' :=
  TripleS.conseq (entails_refl P) hq h

/-- **Sequencing.** The intermediate assertion `R ∗ F` implies `strue ∗ F`, so the state
between the two runs is stable too. -/
theorem TripleS.seq (h₁ : TripleS step P R) (h₂ : TripleS step R Q) : TripleS step P Q := by
  intro F m hm
  obtain ⟨n₁, m₁, hr₁, hR, hs₁⟩ := h₁ F m hm
  obtain ⟨n₂, m₂, hr₂, hQ, hs₂⟩ := h₂ F m₁ hR
  refine ⟨n₁ + n₂, m₂, by rw [run_add, hr₁]; exact hr₂, hQ, fun k hk mk hrk => ?_⟩
  by_cases hlt : k < n₁
  · exact hs₁ k hlt mk hrk
  · obtain ⟨j, rfl⟩ : ∃ j, k = n₁ + j := ⟨k - n₁, by omega⟩
    rw [run_add, hr₁] at hrk
    exact hs₂ j (by omega) mk hrk

/-- The empty run. -/
theorem TripleS.refl (P : SProp) : TripleS step P P :=
  fun _ m hm => ⟨0, m, rfl, hm, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩

/-- **Existential precondition.** -/
theorem TripleS.sexists {α : Sort _} {P : α → SProp} (h : ∀ x, TripleS step (P x) Q) :
    TripleS step (Sep.sexists P) Q := by
  intro F m hm
  rw [sexists_sep] at hm
  obtain ⟨x, hx⟩ := hm
  exact h x F m hx

/-- **Pure precondition.** -/
theorem TripleS.spure {φ : Prop} (h : φ → TripleS step P Q) : TripleS step (⌜φ⌝ ∗ P) Q := by
  intro F m hm
  rw [sep_assoc, spure_sep_apply] at hm
  exact h hm.1 F m hm.2

/-! ## Refinement of machines -/

theorem run_isSome_of_le {k n : Nat} (hk : k ≤ n) {m m' : MState}
    (hr : run step n m = some m') : ∃ mk, run step k m = some mk := by
  obtain ⟨j, rfl⟩ : ∃ j, n = k + j := ⟨n - k, by omega⟩
  rw [run_add] at hr
  cases e : run step k m with
  | none => rw [e] at hr; cases hr
  | some mk => exact ⟨mk, rfl⟩

/-- **Stable triples transport along a refinement of machines** (for example from
`Open.step` to `Open9.step`): the refined machine runs through the same states. -/
theorem TripleS.of_refines (hR : Refines step step') (h : TripleS step P Q) :
    TripleS step' P Q := by
  intro F m hm
  obtain ⟨n, m', hr, hq, hs⟩ := h F m hm
  refine ⟨n, m', run_of_refines hR n hr, hq, fun k hk mk hrk => ?_⟩
  obtain ⟨x, hx⟩ := run_isSome_of_le (Nat.le_of_lt hk) hr
  rw [run_of_refines hR k hx] at hrk
  cases hrk
  exact hs k hk _ hx

end Silmaril.X86.Safe
