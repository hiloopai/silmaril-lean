module

public import Silmaril.Machine.X86.Safe.Defs
public import Silmaril.Machine.X86.Sep.Spec.Thms

/-!
# Proofs: step-indexed safety and triples over any machine

The lemmas of `Silmaril.Proofs.Machine.Link.FnSpec` (`Logic.lean`, `CallSite.lean`), proved once
for every step function `step`, and, where a total triple of the separation-logic layer (`Sep.Triple`, over
`Open.step`) is used, for every `step` that extends the open machine (`ExtendsOpen step`).
The proofs are those , with `Open.step` replaced by `step` and `Reaches Open.step`
transported along `ExtendsOpen.ext` (`reaches_of_refines`).

Names are in `Silmaril.Machine.X86.Safe`, so that the header `Safe/Thms.lean` exports them.
-/

@[expose] public section

namespace Silmaril.Machine.X86.Safe

open Silmaril.X86 (MState Word)
open Silmaril.Machine.Execution (run Reaches)
open Silmaril.Machine.X86.Sep
open Silmaril.Machine.X86.Sep.Frag (Le)

variable {step step' : MState → Option MState} {Q Q₁ Q₂ : MState → Prop}

/-! ## Refinement -/

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

theorem reaches_of_refines (h : Refines step step') {a b : MState} (hr : Reaches step a b) :
    Reaches step' a b :=
  let ⟨k, hk⟩ := hr; ⟨k, run_of_refines h k hk⟩

theorem Refines.refl (step : MState → Option MState) : Refines step step := fun h => h

theorem Refines.trans {step'' : MState → Option MState} (h₁ : Refines step step')
    (h₂ : Refines step' step'') : Refines step step'' := fun h => h₂ (h₁ h)

/-- An open run is a run of every machine that extends the open machine. -/
theorem reaches_of_open [ExtendsOpen step] {a b : MState}
    (h : Reaches Silmaril.Machine.X86.Open.step a b) : Reaches step a b :=
  reaches_of_refines ExtendsOpen.ext h

/-! ## `SafeN` -/

theorem safeN_succ {n : Nat} {m : MState} :
    SafeN step Q (n + 1) m ↔ Q m ∨ ∃ m', step m = some m' ∧ SafeN step Q n m' :=
  Iff.rfl

theorem safeN_mono : ∀ {n : Nat} {m : MState}, SafeN step Q (n + 1) m → SafeN step Q n m
  | 0, _, _ => trivial
  | _ + 1, _, h => by
    rcases safeN_succ.mp h with h | ⟨m', hs, h'⟩
    · exact safeN_succ.mpr (.inl h)
    · exact safeN_succ.mpr (.inr ⟨m', hs, safeN_mono h'⟩)

theorem safeN_le {k n : Nat} {m : MState} (hk : k ≤ n) (h : SafeN step Q n m) :
    SafeN step Q k m := by
  induction n generalizing m with
  | zero => rw [Nat.le_zero.mp hk]; exact h
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · exact ih (by omega) (safeN_mono h)
    · rw [show k = n + 1 by omega]; exact h

theorem safeN_post (hq : ∀ m, Q₁ m → Q₂ m) :
    ∀ {n : Nat} {m : MState}, SafeN step Q₁ n m → SafeN step Q₂ n m
  | 0, _, _ => trivial
  | _ + 1, _, h => by
    rcases safeN_succ.mp h with h | ⟨m', hs, h'⟩
    · exact safeN_succ.mpr (.inl (hq _ h))
    · exact safeN_succ.mpr (.inr ⟨m', hs, safeN_post hq h'⟩)

/-- **Refinement**: safety on a machine is safety on every machine that refines it. -/
theorem safeN_of_refines (hr : Refines step step') :
    ∀ {n : Nat} {m : MState}, SafeN step Q n m → SafeN step' Q n m
  | 0, _, _ => trivial
  | _ + 1, _, h => by
    rcases safeN_succ.mp h with h | ⟨m', hs, h'⟩
    · exact safeN_succ.mpr (.inl h)
    · exact safeN_succ.mpr (.inr ⟨m', hr hs, safeN_of_refines hr h'⟩)

theorem run_succ_some {k : Nat} {m m' : MState} (h : run step (k + 1) m = some m') :
    ∃ m₁, step m = some m₁ ∧ run step k m₁ = some m' := by
  simp only [run] at h
  cases hs : step m with
  | none => simp [hs] at h
  | some m₁ => exact ⟨m₁, rfl, by simpa [hs] using h⟩

/-- A run that reaches `Q` is safe at every index. -/
theorem safeN_of_run : ∀ {k : Nat} {m m' : MState}, run step k m = some m' →
    Q m' → ∀ n, SafeN step Q n m
  | 0, m, m', h, hq, n => by
    simp only [run, Option.some.injEq] at h
    subst h
    cases n with
    | zero => trivial
    | succ n => exact safeN_succ.mpr (.inl hq)
  | k + 1, m, m', h, hq, n => by
    obtain ⟨m₁, hs, hr⟩ := run_succ_some h
    cases n with
    | zero => trivial
    | succ n => exact safeN_succ.mpr (.inr ⟨m₁, hs, safeN_of_run hr hq n⟩)

theorem safeN_of_reaches {m m' : MState} (h : Reaches step m m') (hq : Q m') (n : Nat) :
    SafeN step Q n m :=
  let ⟨_, hk⟩ := h; safeN_of_run hk hq n

/-- `k` steps of a run add `k` to the index. -/
theorem safeN_prefix : ∀ {k n : Nat} {m m' : MState},
    run step k m = some m' → SafeN step Q n m' → SafeN step Q (n + k) m
  | 0, n, m, m', h, hs => by
    simp only [run, Option.some.injEq] at h
    subst h; exact hs
  | k + 1, n, m, m', h, hs => by
    obtain ⟨m₁, hst, hr⟩ := run_succ_some h
    exact safeN_succ.mpr (.inr ⟨m₁, hst, safeN_prefix hr hs⟩)

/-- **Sequencing**: run to `Q₁`, then from every `Q₁` state on. -/
theorem safeN_bind : ∀ {n : Nat} {m : MState}, SafeN step Q₁ n m →
    (∀ m', Q₁ m' → SafeN step Q₂ n m') → SafeN step Q₂ n m
  | 0, _, _, _ => trivial
  | n + 1, m, h, hk => by
    rcases safeN_succ.mp h with h | ⟨m', hs, h'⟩
    · exact hk m h
    · exact safeN_succ.mpr (.inr ⟨m', hs, safeN_bind h' (fun m'' hq => safeN_mono (hk m'' hq))⟩)

/-! ## `STriple` -/

variable {n : Nat} {P P' Q' R : SProp}

theorem STriple.zero (P Q : SProp) : STriple step 0 P Q := fun _ _ _ => trivial

theorem STriple.mono {P Q : SProp} (h : STriple step (n + 1) P Q) : STriple step n P Q :=
  fun F m hm => safeN_mono (h F m hm)

theorem STriple.le {k : Nat} {P Q : SProp} (hk : k ≤ n) (h : STriple step n P Q) :
    STriple step k P Q :=
  fun F m hm => safeN_le hk (h F m hm)

theorem STriple.of_refines {P Q : SProp} (hr : Refines step step') (h : STriple step n P Q) :
    STriple step' n P Q :=
  fun F m hm => safeN_of_refines hr (h F m hm)

theorem STriple.frame {P Q : SProp} (h : STriple step n P Q) (R : SProp) :
    STriple step n (P ∗ R) (Q ∗ R) := by
  intro F m hm
  rw [sep_assoc] at hm
  exact safeN_post (fun m' hq => by rw [sep_assoc]; exact hq) (h (R ∗ F) m hm)

theorem STriple.conseq {P Q : SProp} (hp : P' ⊢ₛ P) (h : STriple step n P Q) (hq : Q ⊢ₛ Q') :
    STriple step n P' Q' := fun F m hm =>
  safeN_post (fun _ h' => sep_mono_left F hq _ h') (h F m (sep_mono_left F hp _ hm))

theorem STriple.of_triple [ExtendsOpen step] {P Q : SProp} (h : Triple P Q) :
    STriple step n P Q := by
  intro F m hm
  obtain ⟨m', hr, hq⟩ := h F m hm
  exact safeN_of_reaches (reaches_of_open hr) hq n

/-- A total triple, then a step-indexed one. -/
theorem STriple.triple_seq [ExtendsOpen step] {P Q : SProp} (h₁ : Triple P R)
    (h₂ : STriple step n R Q) : STriple step n P Q := by
  intro F m hm
  obtain ⟨m', hr, hr'⟩ := h₁ F m hm
  obtain ⟨k, hk⟩ := reaches_of_open (step := step) hr
  exact safeN_le (by omega) (safeN_prefix hk (h₂ F m' hr'))

/-- A step-indexed triple, then a total one. -/
theorem STriple.seq_triple [ExtendsOpen step] {P Q : SProp} (h₁ : STriple step n P R)
    (h₂ : Triple R Q) : STriple step n P Q := by
  intro F m hm
  refine safeN_bind (h₁ F m hm) fun m' hr => ?_
  obtain ⟨m'', hr', hq⟩ := h₂ F m' hr
  exact safeN_of_reaches (reaches_of_open hr') hq n

/-- **One step pays for the index**: a total triple that takes a step, then a triple at `n`,
is a triple at `n + 1`. -/
theorem STriple.progress_seq {P Q : SProp} (h₁ : Progress step P R) (h₂ : STriple step n R Q) :
    STriple step (n + 1) P Q := by
  intro F m hm
  obtain ⟨k, m', hk, hr⟩ := h₁ F m hm
  exact safeN_le (by omega) (safeN_prefix hk (h₂ F m' hr))

theorem STriple.sexists_pre {α : Sort _} {P : α → SProp} {Q : SProp}
    (h : ∀ x, STriple step n (P x) Q) : STriple step n (sexists P) Q := by
  intro F m hm
  rw [sexists_sep] at hm
  obtain ⟨x, hx⟩ := hm
  exact h x F m hx

theorem STriple.spure_pre {φ : Prop} {P Q : SProp} (h : φ → STriple step n P Q) :
    STriple step n (⌜φ⌝ ∗ P) Q := by
  intro F m hm
  rw [sep_assoc, spure_sep_apply] at hm
  exact h hm.1 F m hm.2

/-! ## `Progress` -/

theorem Progress.frame {P R : SProp} (h : Progress step P R) (F : SProp) :
    Progress step (P ∗ F) (R ∗ F) := by
  intro G m hm
  rw [sep_assoc] at hm
  obtain ⟨k, m', hk, hr⟩ := h (F ∗ G) m hm
  exact ⟨k, m', hk, by rw [sep_assoc]; exact hr⟩

theorem Progress.conseq {P P' R R' : SProp} (hp : P' ⊢ₛ P) (h : Progress step P R)
    (hr : R ⊢ₛ R') : Progress step P' R' := by
  intro G m hm
  obtain ⟨k, m', hk, hR⟩ := h G m (sep_mono_left G hp _ hm)
  exact ⟨k, m', hk, sep_mono_left G hr _ hR⟩

theorem le_self' (h : Frag) : Le h h := fun _ _ e => e

/-- The value of `rsp` in a state whose fragment starts with `rsp ↦ s`. -/
theorem rsp_of_sep {s : Word} {P F : SProp} {m : MState}
    (h : ((regPt .rsp s ∗ P) ∗ F) (toFrag m)) : m.core.read .rsp = s := by
  obtain ⟨a, _, ha, _, hla, _⟩ := sep_le h (le_self' _)
  obtain ⟨b, _, hb, _, hlb, _⟩ := sep_le ha hla
  exact regPt_le hb hlb

/-- A total triple that moves `rsp` takes a step. -/
theorem progress_of_rsp [ExtendsOpen step] {s s' : Word} {P Q : SProp} (hne : s ≠ s')
    (h : Triple (regPt .rsp s ∗ P) (regPt .rsp s' ∗ Q)) :
    Progress step (regPt .rsp s ∗ P) (regPt .rsp s' ∗ Q) := by
  intro F m hm
  obtain ⟨m', hr, hq⟩ := h F m hm
  obtain ⟨k, hk⟩ := reaches_of_open (step := step) hr
  cases k with
  | zero =>
    simp only [run, Option.some.injEq] at hk
    subst hk
    exact absurd ((rsp_of_sep hm).symm.trans (rsp_of_sep hq)) hne
  | succ k => exact ⟨k, m', hk, hq⟩

end Silmaril.Machine.X86.Safe
