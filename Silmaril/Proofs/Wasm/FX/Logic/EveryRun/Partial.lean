module

public import Silmaril.Proofs.Wasm.FX.Logic.EveryRun.Derived

/-!
# The step-indexed partial-correctness rules of the every-run WasmFX logic

The context rules for `Safe` (`Silmaril.Wasm.FX.Logic.EveryRun.Defs`), the step-indexed every-run
predicate, as in `Silmaril.Wasm.Logic.Hoare` with a continuation index `k`: the postcondition of
the inner code continues with code safe for `k` steps (`safeJ P fx Q k`), and the rule holds for
`n ≤ k` steps (`n ≤ k + 1` for the label and the handler, which take one step to reach their
continuation). By induction on `n`, with the same inversions and stopped-outcome lemmas as the
total rules:

* `safe_mono` (fewer steps), `safe_post_mono` (weaker postcondition);
* **`safe_seq`**, **`safe_label`**, **`safe_frame`**, **`safe_handler`** (the handler rule);
* `hwp_seq`, `hwp_frame`: the same for `HWP`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Logic.EveryRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Logic (OutcomeFX PostFX Conts)
open Silmaril.Wasm.FX.Logic.EveryRun (Unhandled Stops Safe HWP Inv seqPost labelPost framePost
  handlerPost safeJ)
open Silmaril.Proofs.Wasm.Models.FXVRuns (fval? fnvF_cases)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX} {Q : PostFX H}

/-! ## Monotonicity -/

/-- **Fewer steps.** -/
theorem safe_mono : ∀ {n m : Nat} {c : ConfigFX H}, m ≤ n → Safe P fx Q n c → Safe P fx Q m c
  | _, 0, _, _, _ => trivial
  | n + 1, m + 1, _, hm, h => ⟨h.1, fun c' hs => safe_mono (by omega) (h.2 c' hs)⟩
  | 0, _ + 1, _, hm, _ => absurd hm (by omega)

/-- **A weaker postcondition.** -/
theorem safe_post_mono {Q' : PostFX H} (hQ : ∀ s K f o, Q s K f o → Q' s K f o) :
    ∀ {n : Nat} {c : ConfigFX H}, Safe P fx Q n c → Safe P fx Q' n c
  | 0, _, _ => trivial
  | _ + 1, _, h => ⟨fun o ho => hQ _ _ _ _ (h.1 o ho), fun c' hs => safe_post_mono hQ (h.2 c' hs)⟩

/-! ## Sequencing -/

section Seq

variable {c₂ : List AdminFX} {k : Nat}

/-- The trap postcondition of code with a trap inside a sequence, safe for two steps. -/
theorem safe_trap_post {Q' : PostFX H} {m : Nat} {c : ConfigFX H} (h : Safe P fx Q' (m + 2) c)
    {V : List FVal} {R : List AdminFX} (hc : c.code = fvals V ++ .core .trap :: R) :
    Q' c.store c.conts c.frame .trap := by
  by_cases hne : V ≠ [] ∨ R ≠ []
  · have hst : StepFX' P noHost fx c ⟨c.store, c.conts, c.frame, [.core .trap]⟩ := by
      have := StepFX'.trapSeq (P := P) (host := noHost) (fx := fx) (s := c.store) (K := c.conts)
        (f := c.frame) hne
      rw [show c = ⟨c.store, c.conts, c.frame, fvals V ++ [.core .trap] ++ R⟩ by
        rw [List.append_assoc, List.singleton_append, ← hc]]
      exact this
    exact (h.2 _ hst).1 .trap rfl
  · have hv : V = [] ∧ R = [] := by simpa only [ne_eq, not_or, not_not] using hne
    exact h.1 .trap (by rw [hc, hv.1, hv.2]; rfl)

/-- The throw postcondition of code with an exception inside a sequence, safe for two steps. -/
theorem safe_throw_post {Q' : PostFX H} {m : Nat} {c : ConfigFX H} (h : Safe P fx Q' (m + 2) c)
    {V : List FVal} {b : Nat} {R : List AdminFX} (hc : c.code = fvals V ++ cthrowing b ++ R) :
    Q' c.store c.conts c.frame (.throw b) := by
  by_cases hne : V ≠ [] ∨ R ≠ []
  · have hst : StepFX' P noHost fx c ⟨c.store, c.conts, c.frame, cthrowing b⟩ := by
      have := StepFX'.throwSeq (P := P) (host := noHost) (fx := fx) (s := c.store) (K := c.conts)
        (f := c.frame) (a := b) hne
      rw [show c = ⟨c.store, c.conts, c.frame, fvals V ++ cthrowing b ++ R⟩ by rw [← hc]]
      exact this
    exact (h.2 _ hst).1 (.throw b) rfl
  · have hv : V = [] ∧ R = [] := by simpa only [ne_eq, not_or, not_not] using hne
    exact h.1 (.throw b) (by
      rw [hc, hv.1, hv.2]; show fvals [] ++ cthrowing b ++ [] = cthrowing b; simp)

/-- A trap cutting into the code after it. -/
theorem safe_seq_cut_trap {n : Nat} {c y : ConfigFX H}
    (h : Safe P fx (seqPost (safeJ P fx Q k) c₂ Q) (n + 1) c) {V : List FVal} {R₁ : List AdminFX}
    (hc : c.code = fvals V ++ .core .trap :: R₁) (hs : y.store = c.store) (hK : y.conts = c.conts)
    (hf : y.frame = c.frame) {ws : List FVal} {r' : List AdminFX}
    (hcode : y.code = fvals ws ++ .core .trap :: r') : Safe P fx Q n y := by
  cases n with
  | zero => trivial
  | succ m =>
    have ht : Q c.store c.conts c.frame .trap :=
      safe_trap_post (Q' := seqPost (safeJ P fx Q k) c₂ Q) h hc
    rw [show y = ⟨c.store, c.conts, c.frame, fvals ws ++ .core .trap :: r'⟩ by
      rw [← hs, ← hK, ← hf, ← hcode]]
    exact safe_trap ht _

/-- An exception cutting into the code after it. -/
theorem safe_seq_cut_throw {n : Nat} {c y : ConfigFX H}
    (h : Safe P fx (seqPost (safeJ P fx Q k) c₂ Q) (n + 1) c) {V : List FVal} {b : Nat}
    {R₁ : List AdminFX} (hc : c.code = fvals V ++ cthrowing b ++ R₁) (hs : y.store = c.store)
    (hK : y.conts = c.conts) (hf : y.frame = c.frame) {ws : List FVal} {r' : List AdminFX}
    (hcode : y.code = fvals ws ++ cthrowing b ++ r') : Safe P fx Q n y := by
  cases n with
  | zero => trivial
  | succ m =>
    have ht : Q c.store c.conts c.frame (.throw b) :=
      safe_throw_post (Q' := seqPost (safeJ P fx Q k) c₂ Q) h hc
    rw [show y = ⟨c.store, c.conts, c.frame, fvals ws ++ cthrowing b ++ r'⟩ by
      rw [← hs, ← hK, ← hf, ← hcode]]
    exact safe_throw ht _

/-- One step of `c₁ ++ c₂` for the sequence rule. -/
theorem safe_seq_step {n : Nat} {c y : ConfigFX H}
    (h : Safe P fx (seqPost (safeJ P fx Q k) c₂ Q) (n + 1) c)
    (ih : ∀ c', StepFX' P noHost fx c c' →
      Safe P fx Q n ⟨c'.store, c'.conts, c'.frame, c'.code ++ c₂⟩)
    {V : List FVal} {a : AdminFX} {R₁ : List AdminFX} (hc : c.code = fvals V ++ a :: R₁)
    (ha : fval? a = none)
    (hy : StepFX' P noHost fx ⟨c.store, c.conts, c.frame, c.code ++ c₂⟩ y) : Safe P fx Q n y := by
  have hc' : c = ⟨c.store, c.conts, c.frame, fvals V ++ a :: R₁⟩ := by rw [← hc]
  rw [hc] at hy
  rcases step_split_app ha hy with ⟨c₁', hst, hcode⟩ | ⟨rfl, hs', hK, hf, ws, r', hcode⟩ |
      ⟨rfl, hs', hK, hf, ws, V', b, r', rfl, hcode⟩
  · have hst' : StepFX' P noHost fx c ⟨y.store, y.conts, y.frame, c₁'⟩ := by rw [hc']; exact hst
    rw [show y = ⟨y.store, y.conts, y.frame, c₁' ++ c₂⟩ by rw [← hcode]]
    exact ih _ hst'
  · exact safe_seq_cut_trap h hc hs' hK hf hcode
  · exact safe_seq_cut_throw h (R₁ := R₁) (by rw [hc, cthrowing_app]) hs' hK hf hcode

/-- **Sequencing** (step-indexed): `c₁ ++ c₂` is safe for `n ≤ k` steps if `c₁` is, with `c₂`
safe for `k` steps after `c₁` falls through. -/
theorem safe_seq (hQ : Inv Q) :
    ∀ {n : Nat} {c : ConfigFX H}, n ≤ k → Safe P fx (seqPost (safeJ P fx Q k) c₂ Q) n c →
      Safe P fx Q n ⟨c.store, c.conts, c.frame, c.code ++ c₂⟩
  | 0, _, _, _ => trivial
  | n + 1, c, hn, h => by
    rcases fnvF_cases c.code with ⟨U, hU⟩ | ⟨V, a, R₁, hc, ha⟩
    · have h1 : Safe P fx Q k ⟨c.store, c.conts, c.frame, fvals U ++ c₂⟩ := h.1 (.normal U) hU
      rw [hU]; exact safe_mono hn h1
    · exact ⟨seq_stops hQ h.1 hc ha, fun y hy => safe_seq_step h
        (fun c' hs => safe_seq hQ (by omega) (h.2 c' hs)) hc ha hy⟩

/-- **Sequencing** for every-run weakest preconditions. -/
theorem hwp_seq (hQ : Inv Q) {s : Store H} {K : Conts} {f : Frame} {c₁ : List AdminFX}
    (h : HWP P fx s K f c₁ (seqPost (fun s K f c => HWP P fx s K f c Q) c₂ Q)) :
    HWP P fx s K f (c₁ ++ c₂) Q := fun n =>
  safe_seq (k := n) hQ le_rfl (safe_post_mono (fun s K f o ho => by
    cases o <;> first | exact ho | exact ho n) (h n))

end Seq

/-! ## Labels, frames and handlers -/

section Wrap

variable {k : Nat}

/-- The `br (l+1)` arm of the label rules: a branch to an outer label. -/
theorem label_succ_post {J : Store H → Conts → Frame → List AdminFX → Prop} {s : Store H}
    {K : Conts} {f : Frame} {N : Nat} {cont : List InstrFX} {us vs : List FVal} {l : LabelIdx}
    {rest : List AdminFX}
    (hq : ∀ o, Stops s f o (fvals vs ++ [.core (.plain (.br l))] ++ rest) →
      labelPost J N cont us Q s K f o) (hl : 0 < l.toNat) :
    Q s K f (.br (labelPred l).toNat (us ++ vs)) := by
  obtain ⟨m, hm⟩ : ∃ m, l.toNat = m + 1 := ⟨l.toNat - 1, by omega⟩
  have h1 := hq (.br l.toNat vs) ⟨l, rest, rfl, by simp⟩
  rw [hm] at h1
  have hp : (labelPred l).toNat = m := by
    have h' : l.toNat - 1 = m := by omega
    simpa [labelPred, Idx.toNat] using h'
  exact hp ▸ h1

theorem safe_label_root {n : Nat} {s : Store H} {K : Conts} {f : Frame} {N : Nat}
    {cont : List InstrFX} {us : List FVal} {b : List AdminFX} {y : ConfigFX H} (hn : n ≤ k)
    (hq : ∀ o, Stops s f o b → labelPost (safeJ P fx Q k) N cont us Q s K f o)
    (ih : ∀ c', StepFX' P noHost fx ⟨s, K, f, b⟩ c' →
      Safe P fx Q n ⟨c'.store, c'.conts, c'.frame, fvals us ++ [.label N cont c'.code]⟩)
    {V₂ : List FVal} (hr : Root P fx s K f V₂ (.label N cont b) y) :
    Safe P fx Q n ⟨y.store, y.conts, y.frame, fvals us ++ y.code⟩ := by
  cases hr with
  | ctxLabel h => exact ih _ h
  | @labelVals _ _ vs => simpa using safe_vals (P := P) (fx := fx) (Q := Q) (hq (.normal vs) rfl) n
  | @brLabelZero _ _ vs' vs l rest hl hn' =>
    have h1 := hq (.br l.toNat (vs' ++ vs)) ⟨l, rest, rfl, by simp⟩
    rw [hl] at h1
    have h2 : Safe P fx Q k ⟨s, K, f, fvals (us ++ vs) ++ cont.map InstrFX.toAdmin⟩ :=
      h1 vs' vs rfl hn'
    simpa using safe_mono hn h2
  | @brLabelSucc _ _ vs l rest hl =>
    simpa using safe_br (P := P) (fx := fx) (Q := Q) (R := []) (label_succ_post hq hl) n
  | @returnLabel _ _ vs rest =>
    simpa using safe_ret (P := P) (fx := fx) (Q := Q) (R := []) (hq (.ret vs) ⟨rest, by simp⟩) n
  | trapLabel => simpa using safe_trap (P := P) (fx := fx) (Q := Q) (ws := us) (r := []) (hq .trap rfl) n
  | @throwLabel _ _ a =>
    simpa using safe_throw (P := P) (fx := fx) (Q := Q) (ws := us) (r := []) (hq (.throw a) rfl) n

/-- **Labels** (step-indexed), with values below. -/
theorem safe_label (hQ : Inv Q) {N : Nat} {cont : List InstrFX} {us : List FVal} :
    ∀ {n : Nat} {c : ConfigFX H}, n ≤ k + 1 →
      Safe P fx (labelPost (safeJ P fx Q k) N cont us Q) n c →
      Safe P fx Q n ⟨c.store, c.conts, c.frame, fvals us ++ [.label N cont c.code]⟩
  | 0, _, _, _ => trivial
  | n + 1, ⟨s, K, f, b⟩, hn, h => by
    refine ⟨label_stops hQ h.1, fun y hy => ?_⟩
    obtain ⟨V₁, V₂, y', hV, hr, rfl⟩ := step_last hy us _ rfl rfl
    obtain ⟨-, rfl⟩ := wrap_root_vals hr trivial hV
    exact safe_label_root (by omega) h.1 (fun c' hs => safe_label hQ (by omega) (h.2 c' hs)) hr

theorem safe_frame_root {n : Nat} {s : Store H} {K : Conts} {f F : Frame} {N : Nat}
    {us : List FVal} {b : List AdminFX} {y : ConfigFX H}
    (hq : ∀ o, Stops s F o b → framePost N f us Q s K F o)
    (ih : ∀ c', StepFX' P noHost fx ⟨s, K, F, b⟩ c' →
      Safe P fx Q n ⟨c'.store, c'.conts, f, fvals us ++ [.frame N c'.frame c'.code]⟩)
    {V₂ : List FVal} (hr : Root P fx s K f V₂ (.frame N F b) y) :
    Safe P fx Q n ⟨y.store, y.conts, y.frame, fvals us ++ y.code⟩ := by
  cases hr with
  | ctxFrame h => exact ih _ h
  | @frameVals _ _ vs hn => simpa using safe_vals (P := P) (fx := fx) (Q := Q) (hq (.normal vs) rfl hn) n
  | @returnFrame _ _ vs' vs rest hn =>
    simpa using safe_vals (P := P) (fx := fx) (Q := Q)
      (hq (.ret (vs' ++ vs)) ⟨rest, by simp⟩ vs' vs rfl hn) n
  | trapFrame => simpa using safe_trap (P := P) (fx := fx) (Q := Q) (ws := us) (r := []) (hq .trap rfl) n
  | @throwFrame _ _ a =>
    simpa using safe_throw (P := P) (fx := fx) (Q := Q) (ws := us) (r := []) (hq (.throw a) rfl) n

/-- **Function frames** (step-indexed), with values below. -/
theorem safe_frame (hQ : Inv Q) {N : Nat} {f : Frame} {us : List FVal} :
    ∀ {n : Nat} {c : ConfigFX H}, Safe P fx (framePost N f us Q) n c →
      Safe P fx Q n ⟨c.store, c.conts, f, fvals us ++ [.frame N c.frame c.code]⟩
  | 0, _, _ => trivial
  | n + 1, ⟨s, K, F, b⟩, h => by
    refine ⟨frame_stops hQ h.1, fun y hy => ?_⟩
    obtain ⟨V₁, V₂, y', hV, hr, rfl⟩ := step_last hy us _ rfl rfl
    obtain ⟨-, rfl⟩ := wrap_root_vals hr trivial hV
    exact safe_frame_root h.1 (fun c' hs => safe_frame hQ (h.2 c' hs)) hr

theorem safe_handler_root {n : Nat} {s : Store H} {K : Conts} {f : Frame} {hs : List HClause}
    {us : List FVal} {b : List AdminFX} {y : ConfigFX H} (hn : n ≤ k)
    (hq : ∀ o, Stops s f o b → handlerPost (safeJ P fx Q k) hs us Q s K f o)
    (ih : ∀ c', StepFX' P noHost fx ⟨s, K, f, b⟩ c' →
      Safe P fx Q n ⟨c'.store, c'.conts, c'.frame, fvals us ++ [.handler hs c'.code]⟩)
    {V₂ : List FVal} (hr : Root P fx s K f V₂ (.handler hs b) y) :
    Safe P fx Q n ⟨y.store, y.conts, y.frame, fvals us ++ y.code⟩ := by
  cases hr with
  | ctxHandler h => exact ih _ h
  | @brHandler _ vs l rest =>
    simpa using safe_br (P := P) (fx := fx) (Q := Q) (R := []) (hq (.br l.toNat vs) ⟨l, rest, rfl, by simp⟩) n
  | @returnHandler _ vs rest =>
    simpa using safe_ret (P := P) (fx := fx) (Q := Q) (R := []) (hq (.ret vs) ⟨rest, by simp⟩) n
  | @handlerVals _ vs => simpa using safe_vals (P := P) (fx := fx) (Q := Q) (hq (.normal vs) rfl) n
  | trapHandler => simpa using safe_trap (P := P) (fx := fx) (Q := Q) (ws := us) (r := []) (hq .trap rfl) n
  | @throwHandler _ a =>
    simpa using safe_throw (P := P) (fx := fx) (Q := Q) (ws := us) (r := []) (hq (.throw a) rfl) n
  | @suspend _ E vs x ta ti l ht hE hc =>
    have h1 : Q s (K ++ [some ⟨E.plug⟩]) f (.br l.toNat (us ++ vs ++ [.cont K.length])) :=
      (hq (.susp E vs x) ⟨rfl, unhandled_of ht hE⟩).1 ta ti l ht hE hc
    simpa [FVal.toAdmin] using safe_br (P := P) (fx := fx) (Q := Q) (R := []) h1 n
  | @switch _ E vs j C ct x ta ti hk ht hE hc =>
    exact safe_mono hn ((hq (.swtch E vs j ct x) ⟨rfl, unhandled_of ht hE⟩).1 C ta ti hk ht hE hc)

/-- **The handler rule** (step-indexed), with values below. -/
theorem safe_handler (hQ : Inv Q) {hs : List HClause} {us : List FVal} :
    ∀ {n : Nat} {c : ConfigFX H}, n ≤ k + 1 →
      Safe P fx (handlerPost (safeJ P fx Q k) hs us Q) n c →
      Safe P fx Q n ⟨c.store, c.conts, c.frame, fvals us ++ [.handler hs c.code]⟩
  | 0, _, _, _ => trivial
  | n + 1, ⟨s, K, f, b⟩, hn, h => by
    refine ⟨handler_stops hQ h.1, fun y hy => ?_⟩
    obtain ⟨V₁, V₂, y', hV, hr, rfl⟩ := step_last hy us _ rfl rfl
    obtain ⟨-, rfl⟩ := wrap_root_vals hr trivial hV
    exact safe_handler_root (by omega) h.1 (fun c' hs => safe_handler hQ (by omega) (h.2 c' hs)) hr

/-- **Function frames** for every-run weakest preconditions. -/
theorem hwp_frame (hQ : Inv Q) {N : Nat} {s : Store H} {K : Conts} {f F : Frame}
    {us : List FVal} {b : List AdminFX} (h : HWP P fx s K F b (framePost N f us Q)) :
    HWP P fx s K f (fvals us ++ [.frame N F b]) Q := fun n =>
  safe_frame hQ (h n)

end Wrap

end Silmaril.Proofs.Wasm.FX.Logic.EveryRun
