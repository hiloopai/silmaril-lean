module

public import Silmaril.X86.Safe.Defs
public import Silmaril.X86.Sep.Spec.Thms

/-!
# Proofs: step-indexed safety and triples over any segment-VC machine

Behind `Silmaril/X86/Safe/Thms.lean`: the `SafeN` calculus (index monotonicity, runs,
prefixes, sequencing), the structural rules of `STriple` and `Progress`, the bridges from
total triples (`Sep.Triple`) on the same machine, and the transfers along a machine
extension (`SegVC.Isa.Extends`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Safe

open Silmaril.X86 (MState Word)
open Silmaril.X86.SegVC (Isa)
open Silmaril.Machine.Execution (run Reaches)
open Silmaril.X86.Sep
open Silmaril.X86.Safe
open Silmaril.X86.Sep.Frag (Le)

variable {σ τ : Type} {I : Isa σ} {Q Q₁ Q₂ : σ → Prop}

/-! ## `SafeN` -/

theorem safeN_succ {n : Nat} {m : σ} :
    SafeN I Q (n + 1) m ↔ Q m ∨ ∃ m', I.step m = some m' ∧ SafeN I Q n m' :=
  Iff.rfl

theorem safeN_mono : ∀ {n : Nat} {m : σ}, SafeN I Q (n + 1) m → SafeN I Q n m
  | 0, _, _ => trivial
  | _ + 1, _, h => by
    rcases safeN_succ.mp h with h | ⟨m', hs, h'⟩
    · exact safeN_succ.mpr (.inl h)
    · exact safeN_succ.mpr (.inr ⟨m', hs, safeN_mono h'⟩)

theorem safeN_le {k n : Nat} {m : σ} (hk : k ≤ n) (h : SafeN I Q n m) : SafeN I Q k m := by
  induction n generalizing m with
  | zero => rw [Nat.le_zero.mp hk]; exact h
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · exact ih (by omega) (safeN_mono h)
    · rw [show k = n + 1 by omega]; exact h

theorem safeN_post (hq : ∀ m, Q₁ m → Q₂ m) :
    ∀ {n : Nat} {m : σ}, SafeN I Q₁ n m → SafeN I Q₂ n m
  | 0, _, _ => trivial
  | _ + 1, _, h => by
    rcases safeN_succ.mp h with h | ⟨m', hs, h'⟩
    · exact safeN_succ.mpr (.inl (hq _ h))
    · exact safeN_succ.mpr (.inr ⟨m', hs, safeN_post hq h'⟩)

theorem run_succ_some {k : Nat} {m m' : σ} (h : run I.step (k + 1) m = some m') :
    ∃ m₁, I.step m = some m₁ ∧ run I.step k m₁ = some m' := by
  simp only [run] at h
  cases hs : I.step m with
  | none => simp [hs] at h
  | some m₁ => exact ⟨m₁, rfl, by simpa [hs] using h⟩

theorem safeN_of_run : ∀ {k : Nat} {m m' : σ}, run I.step k m = some m' →
    Q m' → ∀ n, SafeN I Q n m
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

theorem safeN_of_reaches {m m' : σ} (h : Reaches I.step m m') (hq : Q m') (n : Nat) :
    SafeN I Q n m :=
  let ⟨_, hk⟩ := h; safeN_of_run hk hq n

theorem safeN_prefix : ∀ {k n : Nat} {m m' : σ},
    run I.step k m = some m' → SafeN I Q n m' → SafeN I Q (n + k) m
  | 0, n, m, m', h, hs => by
    simp only [run, Option.some.injEq] at h
    subst h; exact hs
  | k + 1, n, m, m', h, hs => by
    obtain ⟨m₁, hst, hr⟩ := run_succ_some h
    exact safeN_succ.mpr (.inr ⟨m₁, hst, safeN_prefix hr hs⟩)

theorem safeN_bind : ∀ {n : Nat} {m : σ}, SafeN I Q₁ n m →
    (∀ m', Q₁ m' → SafeN I Q₂ n m') → SafeN I Q₂ n m
  | 0, _, _, _ => trivial
  | n + 1, m, h, hk => by
    rcases safeN_succ.mp h with h | ⟨m', hs, h'⟩
    · exact hk m h
    · exact safeN_succ.mpr (.inr ⟨m', hs, safeN_bind h' (fun m'' hq => safeN_mono (hk m'' hq))⟩)

theorem safeN_lift {J : Isa τ} (E : I.Extends J) :
    ∀ {n : Nat} {x : τ}, SafeN I Q n (E.view x) → SafeN J (fun y => Q (E.view y)) n x
  | 0, _, _ => trivial
  | _ + 1, x, h => by
    rcases safeN_succ.mp h with h | ⟨s', hs, h'⟩
    · exact safeN_succ.mpr (.inl h)
    · refine safeN_succ.mpr (.inr ⟨E.put x s', E.step hs, safeN_lift E ?_⟩)
      rwa [E.view_put]

/-! ## `STriple` -/

variable {n : Nat} {P P' Q' R : SProp}

theorem striple_frame {P Q : SProp} (h : STriple I n P Q) (R : SProp) :
    STriple I n (P ∗ R) (Q ∗ R) := by
  intro F m hl hm
  rw [sep_assoc] at hm
  exact safeN_post (fun m' hq => by rw [sep_assoc]; exact hq) (h (R ∗ F) m hl hm)

theorem striple_conseq {P Q : SProp} (hp : P' ⊢ₛ P) (h : STriple I n P Q) (hq : Q ⊢ₛ Q') :
    STriple I n P' Q' := fun F m hl hm =>
  safeN_post (fun _ h' => sep_mono_left F hq _ h') (h F m hl (sep_mono_left F hp _ hm))

theorem striple_of_triple {P Q : SProp} (h : Triple I P Q) : STriple I n P Q := by
  intro F m hl hm
  obtain ⟨m', hr, hq⟩ := h F m hl hm
  exact safeN_of_reaches hr hq n

theorem striple_triple_seq {P Q : SProp} (h₁ : Triple I P R) (h₂ : STriple I n R Q) :
    STriple I n P Q := by
  intro F m hl hm
  obtain ⟨m', hr, hr'⟩ := h₁ F m hl hm
  have hl' := Silmaril.X86.SegVC.live_reaches hl hr
  obtain ⟨k, hk⟩ := hr
  exact safeN_le (by omega) (safeN_prefix hk (h₂ F m' hl' hr'))

/-- A `SafeN` run reaches its target from the start state. -/
theorem safeN_reach : ∀ {n : Nat} {m : σ}, SafeN I Q n m →
    SafeN I (fun t => Reaches I.step m t ∧ Q t) n m
  | 0, _, _ => trivial
  | _ + 1, m, h => by
    rcases safeN_succ.mp h with h | ⟨m', hs, h'⟩
    · exact safeN_succ.mpr (.inl ⟨Reaches.refl _ m, h⟩)
    · refine safeN_succ.mpr (.inr ⟨m', hs, safeN_post (fun t ⟨hr, ht⟩ => ⟨?_, ht⟩)
        (safeN_reach h')⟩)
      exact (Silmaril.X86.SegVC.reaches_head (I := I) hs).trans hr

theorem striple_seq_triple {P Q : SProp} (h₁ : STriple I n P R) (h₂ : Triple I R Q) :
    STriple I n P Q := by
  intro F m hl hm
  have h₁' : SafeN I (fun t => I.live t ∧ (R ∗ F) (frag I t)) n m :=
    safeN_post (fun t ⟨hr, ht⟩ => ⟨Silmaril.X86.SegVC.live_reaches hl hr, ht⟩)
      (safeN_reach (h₁ F m hl hm))
  refine safeN_bind h₁' fun m' ⟨hl', hr⟩ => ?_
  obtain ⟨m'', hr', hq⟩ := h₂ F m' hl' hr
  exact safeN_of_reaches hr' hq n

theorem striple_progress_seq {P Q : SProp} (h₁ : Progress I P R) (h₂ : STriple I n R Q) :
    STriple I (n + 1) P Q := by
  intro F m hl hm
  obtain ⟨k, m', hk, hr⟩ := h₁ F m hl hm
  have hl' := Silmaril.X86.SegVC.live_reaches hl ⟨k + 1, hk⟩
  exact safeN_le (by omega) (safeN_prefix hk (h₂ F m' hl' hr))

theorem striple_sexists_pre {α : Sort _} {P : α → SProp} {Q : SProp}
    (h : ∀ x, STriple I n (P x) Q) : STriple I n (sexists P) Q := by
  intro F m hl hm
  rw [sexists_sep] at hm
  obtain ⟨x, hx⟩ := hm
  exact h x F m hl hx

theorem striple_spure_pre {φ : Prop} {P Q : SProp} (h : φ → STriple I n P Q) :
    STriple I n (⌜φ⌝ ∗ P) Q := by
  intro F m hl hm
  rw [sep_assoc, spure_sep_apply] at hm
  exact h hm.1 F m hl hm.2

theorem striple_lift {J : Isa τ} (E : I.Extends J) {P Q : SProp} (h : STriple I n P Q) :
    STriple J n P Q := by
  intro F x hl hm
  rw [frag_view E] at hm
  refine safeN_post (fun y hy => ?_) (safeN_lift E (h F (E.view x) (E.live x hl) hm))
  rwa [frag_view E]

/-! ## `Progress` -/

theorem progress_frame {P R : SProp} (h : Progress I P R) (F : SProp) :
    Progress I (P ∗ F) (R ∗ F) := by
  intro G m hl hm
  rw [sep_assoc] at hm
  obtain ⟨k, m', hk, hr⟩ := h (F ∗ G) m hl hm
  exact ⟨k, m', hk, by rw [sep_assoc]; exact hr⟩

theorem progress_conseq {P P' R R' : SProp} (hp : P' ⊢ₛ P) (h : Progress I P R)
    (hr : R ⊢ₛ R') : Progress I P' R' := by
  intro G m hl hm
  obtain ⟨k, m', hk, hR⟩ := h G m hl (sep_mono_left G hp _ hm)
  exact ⟨k, m', hk, sep_mono_left G hr _ hR⟩

theorem progress_lift {J : Isa τ} (E : I.Extends J) {P R : SProp} (h : Progress I P R) :
    Progress J P R := by
  intro F x hl hm
  rw [frag_view E] at hm
  obtain ⟨k, t, hk, hr⟩ := h F (E.view x) (E.live x hl) hm
  refine ⟨k, E.put x t, E.run (k + 1) hk, ?_⟩
  rwa [frag_view E, E.view_put]

theorem rsp_of_sep {s : Word} {P F : SProp} {m : σ}
    (h : ((regPt .rsp s ∗ P) ∗ F) (frag I m)) : (I.core m).read .rsp = s := by
  obtain ⟨a, _, ha, _, hla, _⟩ := sep_le h (fun _ _ e => e)
  obtain ⟨b, _, hb, _, hlb, _⟩ := sep_le ha hla
  exact regPt_le hb hlb

theorem progress_of_rsp {s s' : Word} {P Q : SProp} (hne : s ≠ s')
    (h : Triple I (regPt .rsp s ∗ P) (regPt .rsp s' ∗ Q)) :
    Progress I (regPt .rsp s ∗ P) (regPt .rsp s' ∗ Q) := by
  intro F m hl hm
  obtain ⟨m', ⟨k, hk⟩, hq⟩ := h F m hl hm
  cases k with
  | zero =>
    simp only [run, Option.some.injEq] at hk
    subst hk
    exact absurd ((rsp_of_sep hm).symm.trans (rsp_of_sep hq)) hne
  | succ k => exact ⟨k, m', hk, hq⟩

end Silmaril.Proofs.X86.Safe
