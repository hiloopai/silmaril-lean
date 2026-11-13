module

public import Silmaril.Machine.X86.RelIsa.Safe.Defs
public import Silmaril.Machine.X86.RelIsa.Thms
public import Silmaril.Machine.X86.Safe.Thms

/-!
# Proofs: demonic step-indexed safety and triples (`SafeNR`, `STripleR`, `TripleR`)

Names are in `Silmaril.Machine.X86.RelIsa`, so that the header `RelIsa/Safe/Thms.lean` exports
them.

* `SafeNR`: `safeNR_succ`, `safeNR_mono`, `safeNR_le`, `safeNR_post`, `safeNR_bind`,
  `SafeNR.of_le` (transfer along `Le`, no progress needed), `safeNR_of_must`.
* The deterministic case: `ofFun_step_iff`, `safeNR_ofFun` (`SafeNR (ofFun step) ↔ SafeN step`),
  `safeNR_ofIsa`, `ofIsa_eq_ofFun`, `safeN_of_safeNR` (back to `SafeN` for any
  `Le (ofFun step) A`).
* Loosening: `safeNR_loosen_of_ofIsa`, `safeNR_loosen_of_safeN` (every `SafeN I.step` is a
  `SafeNR (loosen I ⊤)`), and the mutation witness `not_safeNR_loosen_of_stuck`.
* `STripleR`: `zero`, `mono`, `le`, `frame`, `conseq`, `of_le`, `of_tripleR`,
  `of_striple_loosen`, `sexists_pre`, `spure_pre`.
* `TripleR`: `frame`, `conseq`, `seq`, `of_le`, `of_triple_ext` (from `Sep.Triple` on any
  `I` whose step extends `Open.step`), `of_triple` (at `Open.isa`), `of_triple9`.
-/

@[expose] public section

namespace Silmaril.Machine.X86.RelIsa

open Silmaril.X86 (MState)
open Silmaril.X86.SegVC (Isa)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.Machine.X86.Sep

/-! ## `SafeNR` -/

section
variable {σ : Type} {A C : RelIsa σ} {Q Q₁ Q₂ : σ → Prop}

theorem safeNR_zero (m : σ) : SafeNR A Q 0 m := trivial

theorem safeNR_succ {n : Nat} {m : σ} :
    SafeNR A Q (n + 1) m ↔ Q m ∨ ∀ r, A.step m r → ∃ m', r = .ok m' ∧ SafeNR A Q n m' :=
  Iff.rfl

theorem safeNR_mono : ∀ {n : Nat} {m : σ}, SafeNR A Q (n + 1) m → SafeNR A Q n m
  | 0, _, _ => trivial
  | _ + 1, _, h => by
    rcases safeNR_succ.mp h with h | h
    · exact safeNR_succ.mpr (.inl h)
    · refine safeNR_succ.mpr (.inr fun r hr => ?_)
      obtain ⟨m', e, h'⟩ := h r hr
      exact ⟨m', e, safeNR_mono h'⟩

theorem safeNR_le {k n : Nat} {m : σ} (hk : k ≤ n) (h : SafeNR A Q n m) : SafeNR A Q k m := by
  induction n generalizing m with
  | zero => rw [Nat.le_zero.mp hk]; exact h
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · exact ih (by omega) (safeNR_mono h)
    · rw [show k = n + 1 by omega]; exact h

theorem safeNR_post (hq : ∀ m, Q₁ m → Q₂ m) :
    ∀ {n : Nat} {m : σ}, SafeNR A Q₁ n m → SafeNR A Q₂ n m
  | 0, _, _ => trivial
  | _ + 1, _, h => by
    rcases safeNR_succ.mp h with h | h
    · exact safeNR_succ.mpr (.inl (hq _ h))
    · refine safeNR_succ.mpr (.inr fun r hr => ?_)
      obtain ⟨m', e, h'⟩ := h r hr
      exact ⟨m', e, safeNR_post hq h'⟩

/-- **Sequencing**: safe towards `Q₁`, then safe from every `Q₁` state on. -/
theorem safeNR_bind : ∀ {n : Nat} {m : σ}, SafeNR A Q₁ n m →
    (∀ m', Q₁ m' → SafeNR A Q₂ n m') → SafeNR A Q₂ n m
  | 0, _, _, _ => trivial
  | n + 1, m, h, hk => by
    rcases safeNR_succ.mp h with h | h
    · exact hk m h
    · refine safeNR_succ.mpr (.inr fun r hr => ?_)
      obtain ⟨m', e, h'⟩ := h r hr
      exact ⟨m', e, safeNR_bind h' fun m'' hq => safeNR_mono (hk m'' hq)⟩

/-- **Refinement** (no progress needed): safety on `A` is safety on every `C ≤ A`, from a
live state. -/
theorem SafeNR.of_le (h : Le C A) :
    ∀ {n : Nat} {m : σ}, C.live m → SafeNR A Q n m → SafeNR C Q n m
  | 0, _, _, _ => trivial
  | _ + 1, m, hl, hs => by
    rcases safeNR_succ.mp hs with hq | hs
    · exact safeNR_succ.mpr (.inl hq)
    · refine safeNR_succ.mpr (.inr fun r hr => ?_)
      obtain ⟨m', e, h'⟩ := hs r (h.step hl hr)
      subst e
      exact ⟨m', rfl, SafeNR.of_le h (C.live_step hl hr) h'⟩

/-- A demonic total run is safe at every index. -/
theorem safeNR_of_must {R : σ → Prop} {m : σ} (h : Must A R Q m) : ∀ n, SafeNR A Q n m := by
  induction h with
  | done hq => intro n; cases n with
    | zero => trivial
    | succ n => exact safeNR_succ.mpr (.inl hq)
  | step _ hns _ ih => intro n; cases n with
    | zero => trivial
    | succ n =>
      refine safeNR_succ.mpr (.inr fun r hr => ?_)
      cases r with
      | stop => exact absurd hr hns
      | ok t => exact ⟨t, rfl, ih t hr n⟩

end

/-! ## The deterministic case -/

section
variable {step : MState → Option MState} {Q : MState → Prop}

theorem ofFun_step_iff {m : MState} {r : Res MState} :
    (ofFun step).step m r ↔ match step m with | some t => r = .ok t | none => r = .stop :=
  Iff.rfl

theorem ofFun_step_ok {m t : MState} : (ofFun step).step m (.ok t) ↔ step m = some t := by
  show (match step m with | some t' => _ | none => _) ↔ _
  cases step m with
  | some t' => simp [eq_comm]
  | none => simp

theorem ofFun_step_stop {m : MState} : (ofFun step).step m .stop ↔ step m = none := by
  show (match step m with | some t' => _ | none => _) ↔ _
  cases step m with
  | some t' => simp
  | none => simp

@[simp] theorem ofFun_toViews : (ofFun step).toViews = Views.mstate := rfl

theorem progress_ofFun : Progress (ofFun step) := by
  intro m _
  cases e : step m with
  | some t => exact ⟨.ok t, ofFun_step_ok.mpr e⟩
  | none => exact ⟨.stop, ofFun_step_stop.mpr e⟩

/-- **The D5 bridge**: on a step function, demonic safety is `Safe.SafeN`. -/
theorem safeNR_ofFun : ∀ {n : Nat} {m : MState},
    SafeNR (ofFun step) Q n m ↔ Safe.SafeN step Q n m
  | 0, _ => Iff.rfl
  | n + 1, m => by
    rw [safeNR_succ, Safe.safeN_succ]
    refine or_congr Iff.rfl ⟨fun h => ?_, fun ⟨m', e, h'⟩ r hr => ?_⟩
    · cases e : step m with
      | some t =>
        obtain ⟨m', e', h'⟩ := h (.ok t) (ofFun_step_ok.mpr e)
        cases e'
        exact ⟨t, rfl, safeNR_ofFun.mp h'⟩
      | none =>
        obtain ⟨_, e', _⟩ := h .stop (ofFun_step_stop.mpr e)
        cases e'
    · cases r with
      | stop => rw [ofFun_step_stop, e] at hr; cases hr
      | ok t =>
        rw [ofFun_step_ok, e] at hr
        cases hr
        exact ⟨m', rfl, safeNR_ofFun.mpr h'⟩

/-- A segment-VC machine on `MState` with the `MState` views is `ofFun` of its step. -/
theorem ofIsa_eq_ofFun (I : Isa MState) (hv : Views.ofIsa I = Views.mstate) :
    ofIsa I = ofFun I.step := by
  have h1 : (ofIsa I).toViews = (ofFun I.step).toViews := hv
  have h2 : (ofIsa I).step = (ofFun I.step).step := by
    funext s r
    unfold ofIsa ofFun
    dsimp only
    cases I.step s <;> rfl
  cases e : ofIsa I
  cases e' : ofFun I.step
  rw [e, e'] at h1 h2
  simp only at h1 h2
  subst h1 h2
  rfl

theorem ofIsa_open : ofIsa Silmaril.Machine.X86.Open.isa = ofFun Silmaril.Machine.X86.Open.step :=
  ofIsa_eq_ofFun _ rfl

theorem ofIsa_open9 : ofIsa Silmaril.Machine.X86.Open9.isa = ofFun Silmaril.Machine.X86.Open9.step :=
  ofIsa_eq_ofFun _ rfl

/-- `safeNR_ofFun` for a segment-VC machine. -/
theorem safeNR_ofIsa {I : Isa MState} {n : Nat} {m : MState} :
    SafeNR (ofIsa I) Q n m ↔ Safe.SafeN I.step Q n m := by
  have key : ∀ {n m}, SafeNR (ofIsa I) Q n m ↔ SafeNR (ofFun I.step) Q n m := by
    intro n
    induction n with
    | zero => intro m; exact Iff.rfl
    | succ n ih =>
      intro m
      rw [safeNR_succ, safeNR_succ]
      refine or_congr Iff.rfl (forall_congr' fun r => ?_)
      have hs : (ofIsa I).step m r ↔ (ofFun I.step).step m r := by
        cases r with
        | ok t => rw [ofIsa_step_ok, ofFun_step_ok]
        | stop => rw [ofIsa_step_stop, ofFun_step_stop]
      rw [hs]
      exact imp_congr_right fun _ => exists_congr fun m' => and_congr Iff.rfl ih
  exact key.trans safeNR_ofFun

/-- **Back to the deterministic machine**: demonic safety on any `A` that `ofFun step`
refines is `SafeN step` (progress of `ofFun step` is automatic). -/
theorem safeN_of_safeNR {A : RelIsa MState} (h : Le (ofFun step) A) {n : Nat} {m : MState}
    (hs : SafeNR A Q n m) : Safe.SafeN step Q n m :=
  safeNR_ofFun.mp (SafeNR.of_le h trivial hs)

end

/-! ## Loosening -/

section
variable {σ : Type} {I : Isa σ} {Q : σ → Prop}

/-- Safety of a deterministic machine is safety of its everywhere-loosening. -/
theorem safeNR_loosen_of_ofIsa :
    ∀ {n : Nat} {m : σ}, SafeNR (ofIsa I) Q n m → SafeNR (loosen I (fun _ => True)) Q n m
  | 0, _, _ => trivial
  | _ + 1, m, h => by
    rcases safeNR_succ.mp h with hq | h
    · exact safeNR_succ.mpr (.inl hq)
    · refine safeNR_succ.mpr (.inr fun r hr => ?_)
      cases e : I.step m with
      | none =>
        obtain ⟨_, e', _⟩ := h .stop (ofIsa_step_stop.mpr e)
        cases e'
      | some t =>
        obtain ⟨m', e', h'⟩ := h (.ok t) (ofIsa_step_ok.mpr e)
        cases e'
        cases hr.1 t trivial e
        exact ⟨t, rfl, safeNR_loosen_of_ofIsa h'⟩

/-- **Non-vacuity (mutation witness).** Where `I` is stuck and `Q` fails, the loosening is not
safe even for one step: it may stop. -/
theorem not_safeNR_loosen_of_stuck {P : σ → Prop} {m : σ} (he : I.step m = none) (hq : ¬ Q m) :
    ¬ SafeNR (loosen I P) Q 1 m := by
  intro h
  rcases safeNR_succ.mp h with h | h
  · exact hq h
  · obtain ⟨_, e, _⟩ := h .stop ⟨fun t _ ht => (by rw [he] at ht; cases ht),
      fun _ e => (by cases e)⟩
    cases e

end

/-- **The free bridge for safety**: `SafeN I.step` is `SafeNR` of the everywhere-loosening. -/
theorem safeNR_loosen_of_safeN {I : Isa MState} {Q : MState → Prop} {n : Nat} {m : MState}
    (h : Safe.SafeN I.step Q n m) : SafeNR (loosen I (fun _ => True)) Q n m :=
  safeNR_loosen_of_ofIsa (safeNR_ofIsa.mpr h)

/-! ## `STripleR` -/

section
variable {A C : RelIsa MState} {n : Nat} {P P' Q Q' R : SProp}

theorem STripleR.zero (A : RelIsa MState) (P Q : SProp) : STripleR A 0 P Q :=
  fun _ _ _ => trivial

theorem STripleR.mono (h : STripleR A (n + 1) P Q) : STripleR A n P Q :=
  fun F m hm => safeNR_mono (h F m hm)

theorem STripleR.le {k : Nat} (hk : k ≤ n) (h : STripleR A n P Q) : STripleR A k P Q :=
  fun F m hm => safeNR_le hk (h F m hm)

theorem STripleR.frame (h : STripleR A n P Q) (R : SProp) : STripleR A n (P ∗ R) (Q ∗ R) := by
  intro F m hm
  rw [sep_assoc] at hm
  exact safeNR_post (fun m' hq => by rw [sep_assoc]; exact hq) (h (R ∗ F) m hm)

theorem STripleR.conseq (hp : P' ⊢ₛ P) (h : STripleR A n P Q) (hq : Q ⊢ₛ Q') :
    STripleR A n P' Q' := fun F m hm =>
  safeNR_post (fun _ h' => sep_mono_left F hq _ h') (h F m (sep_mono_left F hp _ hm))

/-- **Refinement**: a triple on `A` is a triple on every `C ≤ A` whose states are all live. -/
theorem STripleR.of_le (h : Le C A) (hl : ∀ m, C.live m) (ht : STripleR A n P Q) :
    STripleR C n P Q :=
  fun F m hm => SafeNR.of_le h (hl m) (ht F m hm)

/-- A total demonic triple is a step-indexed one at every index. -/
theorem STripleR.of_tripleR (h : TripleR A P Q) : STripleR A n P Q :=
  fun F m hm => safeNR_of_must (h F m hm) n

/-- **The free bridge for triples**: a `Safe.STriple` on `I.step` is an `STripleR` on the
everywhere-loosening of `I`. -/
theorem STripleR.of_striple_loosen {I : Isa MState} (h : Safe.STriple I.step n P Q) :
    STripleR (loosen I (fun _ => True)) n P Q :=
  fun F m hm => safeNR_loosen_of_safeN (h F m hm)

theorem STripleR.sexists_pre {α : Sort _} {P : α → SProp}
    (h : ∀ x, STripleR A n (P x) Q) : STripleR A n (sexists P) Q := by
  intro F m hm
  rw [sexists_sep] at hm
  obtain ⟨x, hx⟩ := hm
  exact h x F m hx

theorem STripleR.spure_pre {φ : Prop} (h : φ → STripleR A n P Q) :
    STripleR A n (⌜φ⌝ ∗ P) Q := by
  intro F m hm
  rw [sep_assoc, spure_sep_apply] at hm
  exact h hm.1 F m hm.2

end

/-! ## `TripleR` -/

section
variable {A C : RelIsa MState} {P P' Q Q' R : SProp}

theorem TripleR.frame (h : TripleR A P Q) (R : SProp) : TripleR A (P ∗ R) (Q ∗ R) := by
  intro F m hm
  rw [sep_assoc] at hm
  exact Must.mono (fun _ h => h) (fun m' hq => by rw [sep_assoc]; exact hq) (h (R ∗ F) m hm)

theorem TripleR.conseq (hp : P' ⊢ₛ P) (h : TripleR A P Q) (hq : Q ⊢ₛ Q') : TripleR A P' Q' :=
  fun F m hm =>
    Must.mono (fun _ h => h) (fun _ h' => sep_mono_left F hq _ h') (h F m (sep_mono_left F hp _ hm))

theorem TripleR.seq (h₁ : TripleR A P R) (h₂ : TripleR A R Q) : TripleR A P Q :=
  fun F m hm => Must.bind (h₁ F m hm) fun m' hr => h₂ F m' hr

/-- **Refinement**: a total triple on `A` is one on every `C ≤ A` whose states are all live. -/
theorem TripleR.of_le (h : Le C A) (hl : ∀ m, C.live m) (ht : TripleR A P Q) : TripleR C P Q :=
  fun F m hm => Must.of_le h (hl m) (ht F m hm)

/-- **The separation-logic layer's total triples are demonic triples** of the everywhere-loosening of every
machine `I` that extends the open machine. -/
theorem TripleR.of_triple_ext {I : Isa MState} [Safe.ExtendsOpen I.step] (h : Triple P Q) :
    TripleR (loosen I (fun _ => True)) P Q := by
  intro F m hm
  obtain ⟨m', hr, hq⟩ := h F m hm
  exact must_loosen_of_reaches (Safe.reaches_of_open hr) hq

/-- **`TripleR.of_triple`**: `Sep.Triple P Q` is a demonic triple of `loosen Open.isa ⊤`. -/
theorem TripleR.of_triple (h : Triple P Q) :
    TripleR (loosen Silmaril.Machine.X86.Open.isa (fun _ => True)) P Q :=
  have : Safe.ExtendsOpen Silmaril.Machine.X86.Open.isa.step := Safe.instExtendsOpenOpen
  TripleR.of_triple_ext h

/-- `TripleR.of_triple` on the open machine over `Ext9`. -/
theorem TripleR.of_triple9 (h : Triple P Q) :
    TripleR (loosen Silmaril.Machine.X86.Open9.isa (fun _ => True)) P Q :=
  have : Safe.ExtendsOpen Silmaril.Machine.X86.Open9.isa.step := Safe.instExtendsOpenOpen9
  TripleR.of_triple_ext h

end

end Silmaril.Machine.X86.RelIsa
