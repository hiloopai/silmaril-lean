module

public import Silmaril.X86.Safe.Exc.Defs
public import Silmaril.X86.Safe.Thms
public import Silmaril.X86.Sep.Extra.Thms
public import Silmaril.X86.Sep.SysV.Thms
public import Silmaril.Proofs.X86.Safe.Basic

/-!
# Proofs: two-exit triples

The rules of `STripleX`, for every segment-VC machine `I`.

* Index: `STripleX.zero`, `STripleX.mono`, `STripleX.le`.
* Entry: `STriple.toX` (an ordinary triple is a two-exit triple for every `k`, `E`),
  `STripleX.toSTriple` (with no payload, `E = fun _ => False`, the exceptional exit cannot be
  taken), `STripleX.throw` (a state at the continuation exits exceptionally).
* Structure: `STripleX.conseq`, `STripleX.frameF` (the frame is leaked on the exceptional
  exit), `STripleX.frameG` (the frame survives it, as part of the payload), `STripleX.seq`,
  `STripleX.progress_seq`, `STripleX.triple_seq`, `STripleX.seq_triple`,
  `STripleX.sexists_pre`, `STripleX.spure_pre`, and `STripleX.lift` along a machine extension.
* `xcall_rule`: a `call rel32` to a function with a two-exit triple at the pushed return
  address, on every machine extending `Open.isa`. The call site's code survives the
  exceptional exit (it joins the payload).
* `catch_rule`: a two-exit triple for the protected code, and an ordinary triple for the
  handler from every exceptional state, give an ordinary triple whose postcondition is the
  normal one or the handler's with garbage (`sor Q (Q' ∗ strue)`).
* `stable_iff_strue`: `(strue ∗ F) (toFrag m) ↔ Holds F m`.

Sequencing needs the intermediate state to be live: `safeN_live` threads `I.live` through a
`SafeN` run (`SegVC.live_reaches`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.SafeExc

open Silmaril.X86 (MState Word Insn)
open Silmaril.X86.SegVC (Isa)
open Silmaril.Machine.Execution (run Reaches)
open Silmaril.X86.Sep
open Silmaril.X86.Safe
open Silmaril.X86.Sep.Frag (union Disjoint Le diff)

variable {σ τ : Type} {I : Isa σ} {n : Nat} {k : Cont} {E E' : Word → SProp}
  {P P' Q Q' R : SProp}

/-- A state that meets the target is safe at every index. -/
theorem safeN_now {Q : σ → Prop} {m : σ} (h : Q m) : ∀ n, SafeN I Q n m
  | 0 => trivial
  | _ + 1 => safeN_succ.mpr (.inl h)

/-- Every state a `SafeN` run reaches from a live state is live. -/
theorem safeN_live {Q : σ → Prop} {m : σ} (hl : I.live m) (h : SafeN I Q n m) :
    SafeN I (fun t => I.live t ∧ Q t) n m :=
  safeN_post (fun _ ⟨hr, ht⟩ => ⟨Silmaril.X86.SegVC.live_reaches hl hr, ht⟩)
    (Silmaril.Proofs.X86.Safe.safeN_reach h)

/-! ## `Exc` -/

theorem Exc.mono (he : ∀ v, E v ⊢ₛ E' v) (G : SProp) : Exc k E G ⊢ₛ Exc k E' G :=
  sexists_elim fun v => sexists_intro v
    (sep_mono_right _ (sep_mono_right _ (sep_mono_left _ (he v))))

theorem Exc.frame (R G : SProp) : Exc k E (R ∗ G) = Exc k (fun v => E v ∗ R) G := by
  simp only [Exc, sep_assoc]

theorem exc_of_at (F G : SProp) :
    ((sexists fun v => ⌜v ≠ 0⌝ ∗ AtCont k v ∗ E v) ∗ F ∗ G) ⊢ₛ Exc k E G := by
  rw [sexists_sep]
  refine sexists_elim fun v => sexists_intro v ?_
  refine entails_trans (entails_of_eq
    (by ac_rfl : ((⌜v ≠ 0⌝ ∗ AtCont k v ∗ E v) ∗ F ∗ G) = (⌜v ≠ 0⌝ ∗ AtCont k v ∗ E v ∗ G ∗ F)))
    ?_
  exact sep_mono_right _ (sep_mono_right _ (sep_mono_right _ (sep_mono_right _
    (entails_strue F))))

/-! ## Index -/

theorem STripleX.le {k' : Nat} (hk : k' ≤ n) (h : STripleX I n P Q k E) :
    STripleX I k' P Q k E :=
  fun F G m hl hm => safeN_le hk (h F G m hl hm)

/-! ## Entry -/

theorem STriple.toX (h : STriple I n P Q) (k : Cont) (E : Word → SProp) :
    STripleX I n P Q k E :=
  fun F G m hl hm => safeN_post (fun _ h' => .inl h') (h (F ∗ G) m hl hm)

theorem STripleX.toSTriple (h : STripleX I n P Q k (fun _ => fun _ => False)) :
    STriple I n P Q := by
  intro F m hl hm
  have hm' : (P ∗ F ∗ emp) (frag I m) := by rwa [sep_emp]
  refine safeN_post (fun _ hq => ?_) (h F emp m hl hm')
  rcases hq with hq | ⟨v, hv⟩
  · rwa [sep_emp] at hq
  · obtain ⟨_, _, _, _, -, _, _, _, _, -, _, _, _, _, hE, -⟩ := hv
    exact hE.elim

theorem STripleX.throw (h : P ⊢ₛ sexists fun v => ⌜v ≠ 0⌝ ∗ AtCont k v ∗ E v) (Q : SProp) :
    STripleX I n P Q k E :=
  fun F G _ _ hm => safeN_now (.inr (exc_of_at F G _ (sep_mono_left _ h _ hm))) n

/-! ## Structural rules -/

theorem STripleX.conseq (hp : P' ⊢ₛ P) (h : STripleX I n P Q k E) (hq : Q ⊢ₛ Q')
    (he : ∀ v, E v ⊢ₛ E' v) : STripleX I n P' Q' k E' := fun F G m hl hm =>
  safeN_post (fun _ h' => h'.imp (sep_mono_left _ hq _) (Exc.mono he G _))
    (h F G m hl (sep_mono_left _ hp _ hm))

theorem STripleX.frameF (h : STripleX I n P Q k E) (R : SProp) :
    STripleX I n (P ∗ R) (Q ∗ R) k E := by
  intro F G m hl hm
  rw [show ((P ∗ R) ∗ F ∗ G) = (P ∗ (R ∗ F) ∗ G) by ac_rfl] at hm
  refine safeN_post (fun m' h' => ?_) (h (R ∗ F) G m hl hm)
  rcases h' with h' | h'
  · left; rw [show ((Q ∗ R) ∗ F ∗ G) = (Q ∗ (R ∗ F) ∗ G) by ac_rfl]; exact h'
  · exact .inr h'

theorem STripleX.frameG (h : STripleX I n P Q k E) (R : SProp) :
    STripleX I n (P ∗ R) (Q ∗ R) k (fun v => E v ∗ R) := by
  intro F G m hl hm
  rw [show ((P ∗ R) ∗ F ∗ G) = (P ∗ F ∗ R ∗ G) by ac_rfl] at hm
  refine safeN_post (fun m' h' => ?_) (h F (R ∗ G) m hl hm)
  rcases h' with h' | h'
  · left; rw [show ((Q ∗ R) ∗ F ∗ G) = (Q ∗ F ∗ R ∗ G) by ac_rfl]; exact h'
  · right; rwa [Exc.frame] at h'

theorem STripleX.seq (h₁ : STripleX I n P R k E) (h₂ : STripleX I n R Q k E) :
    STripleX I n P Q k E := by
  intro F G m hl hm
  refine safeN_bind (safeN_live hl (h₁ F G m hl hm)) fun m' ⟨hl', h'⟩ => ?_
  rcases h' with h' | h'
  · exact h₂ F G m' hl' h'
  · exact safeN_now (.inr h') n

theorem STripleX.progress_seq (h₁ : Progress I P R) (h₂ : STripleX I n R Q k E) :
    STripleX I (n + 1) P Q k E := by
  intro F G m hl hm
  obtain ⟨j, m', hj, hr⟩ := h₁ (F ∗ G) m hl hm
  have hl' := Silmaril.X86.SegVC.live_reaches hl ⟨j + 1, hj⟩
  exact safeN_le (by omega) (safeN_prefix hj (h₂ F G m' hl' hr))

theorem STripleX.triple_seq (h₁ : Triple I P R) (h₂ : STripleX I n R Q k E) :
    STripleX I n P Q k E := by
  intro F G m hl hm
  obtain ⟨m', hr, hr'⟩ := h₁ (F ∗ G) m hl hm
  have hl' := Silmaril.X86.SegVC.live_reaches hl hr
  obtain ⟨j, hj⟩ := hr
  exact safeN_le (by omega) (safeN_prefix hj (h₂ F G m' hl' hr'))

theorem STripleX.seq_triple (h₁ : STripleX I n P R k E) (h₂ : Triple I R Q) :
    STripleX I n P Q k E := by
  intro F G m hl hm
  refine safeN_bind (safeN_live hl (h₁ F G m hl hm)) fun m' ⟨hl', h'⟩ => ?_
  rcases h' with h' | h'
  · obtain ⟨m'', hr, hq⟩ := h₂ (F ∗ G) m' hl' h'
    exact safeN_of_reaches hr (.inl hq) n
  · exact safeN_now (.inr h') n

theorem STripleX.sexists_pre {α : Sort _} {P : α → SProp}
    (h : ∀ x, STripleX I n (P x) Q k E) : STripleX I n (sexists P) Q k E := by
  intro F G m hl hm
  rw [sexists_sep] at hm
  obtain ⟨x, hx⟩ := hm
  exact h x F G m hl hx

theorem STripleX.spure_pre {φ : Prop} (h : φ → STripleX I n P Q k E) :
    STripleX I n (⌜φ⌝ ∗ P) Q k E := by
  intro F G m hl hm
  rw [sep_assoc, spure_sep_apply] at hm
  exact h hm.1 F G m hl hm.2

theorem STripleX.lift {J : Isa τ} (Ex : I.Extends J) (h : STripleX I n P Q k E) :
    STripleX J n P Q k E := by
  intro F G x hl hm
  rw [frag_view Ex] at hm
  refine safeN_post (fun y hy => ?_) (SafeN.lift Ex (h F G (Ex.view x) (Ex.live x hl) hm))
  rwa [frag_view Ex]

/-! ## Calls -/

theorem xcall_rule (Ex : Silmaril.X86.Open.isa.Extends I) {pc s f : Word} {rel : BitVec 32}
    (hs : 8 ≤ s.toNat) (hf : pc + 5#64 + rel.signExtend 64 = f)
    (hS : STripleX I n (ripPt f ∗ regPt .rsp (s - 8#64) ∗ wordPt (s.toNat - 8) (pc + 5#64) ∗ P)
      Q k E) :
    STripleX I n
      (codePt pc.toNat (Insn.encode (.call rel)) ∗ ripPt pc ∗ regPt .rsp s ∗
        blockAny (s.toNat - 8) 8 ∗ P)
      (codePt pc.toNat (Insn.encode (.call rel)) ∗ Q) k
      (fun v => E v ∗ codePt pc.toNat (Insn.encode (.call rel))) := by
  have hc := Triple.frame (call_step Ex pc s rel hs) P
  rw [hf] at hc
  refine STripleX.triple_seq (Triple.conseq (entails_of_eq (by ac_rfl)) hc (entails_refl _))
    (STripleX.conseq (entails_of_eq (by ac_rfl)) (STripleX.frameG hS _)
      (entails_of_eq (by ac_rfl)) (fun _ => entails_refl _))

/-! ## Catch -/

theorem catch_rule (h₁ : STripleX I n P Q k E)
    (h₂ : ∀ v, v ≠ 0 → STriple I n (AtCont k v ∗ E v) Q') :
    STriple I n P (sor Q (Q' ∗ strue)) := by
  intro F m hl hm
  have hm' : (P ∗ emp ∗ F) (frag I m) := by rwa [emp_sep]
  refine safeN_bind (safeN_live hl (h₁ emp F m hl hm')) fun m' ⟨hl', h'⟩ => ?_
  rcases h' with hq | ⟨v, hv⟩
  · rw [emp_sep] at hq
    exact safeN_now (by rw [sor_sep]; exact .inl hq) n
  · rw [spure_sep_apply] at hv
    obtain ⟨hne, hv⟩ := hv
    rw [show (AtCont k v ∗ E v ∗ F ∗ strue) = ((AtCont k v ∗ E v) ∗ F ∗ strue) by ac_rfl] at hv
    refine safeN_post (fun m'' hq => ?_) (h₂ v hne (F ∗ strue) m' hl' hv)
    rw [sor_sep]
    right
    rwa [show ((Q' ∗ strue) ∗ F) = (Q' ∗ F ∗ strue) by ac_rfl]

/-! ## `strue` and stability -/

theorem stable_iff_strue (F : SProp) (m : MState) : (strue ∗ F) (toFrag m) ↔ Holds F m := by
  constructor
  · rintro ⟨h₁, h₂, hd, he, -, hf⟩
    refine ⟨h₂, hf, fun l v hv => ?_⟩
    have h1 : h₁ l = none := (hd l).resolve_right (by simp [hv])
    rw [he]
    simp [Frag.union, h1, hv]
  · rintro ⟨h, hf, hle⟩
    refine ⟨diff (toFrag m) h, h, fun l => ?_, ?_, trivial, hf⟩
    · by_cases hs : (h l).isSome
      · left; simp [diff, hs]
      · right; simpa using hs
    · funext l
      simp only [Frag.union, diff]
      cases e : h l with
      | none => simp only [Option.isSome_none, Bool.false_eq_true, ite_false]; cases toFrag m l <;> rfl
      | some v => simp [hle l v e]

end Silmaril.Proofs.X86.SafeExc
