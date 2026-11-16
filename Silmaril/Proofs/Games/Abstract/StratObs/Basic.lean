module

public import Silmaril.Games.Abstract.StratObs.Defs
public import Silmaril.Games.Div.Thms

/-!
# From function observations to divergence-observing strategies: proofs

* Reading the calls of a round (`readCalls`, `readCalls_inv`): from `run q c₀`
  the automaton reads `callMoves c` exactly when every call of `c` is a call
  prefix, and then it is at `run q (c₀ ++ c)`.
* `satP` is closed under call prefixes (`satP_prefix`) and saturation is
  idempotent (`sat_idem`).
* Membership characterisations for completed rounds, pending calls,
  divergence and productive streams, and `toDStrat_eq_iff`.
-/

public section

namespace Silmaril.Proofs.Games.Abstract.StratObs

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-! ## Call moves and streams -/

section Calls

variable {F : Sig.{u}}

@[simp] theorem callMoves_nil : (callMoves [] : List (Move E F)) = [] := rfl

@[simp] theorem callMoves_cons (x : Call E) (c : List (Call E)) :
    (callMoves (x :: c) : List (Move E F)) = .inl (.ask x.1) :: .inl (.ans x.1 x.2) :: callMoves c :=
  rfl

@[simp] theorem callMoves_append (c d : List (Call E)) :
    (callMoves (c ++ d) : List (Move E F)) = callMoves c ++ callMoves d := by
  simp [callMoves]

theorem length_callMoves (c : List (Call E)) :
    (callMoves c : List (Move E F)).length = 2 * c.length := by
  induction c with
  | nil => rfl
  | cons x c ih => simp [ih]; omega

theorem not_inr_mem_callMoves {c : List (Call E)} {y : Ev F} :
    (.inr y : Move E F) ∉ callMoves c := by
  induction c with
  | nil => simp
  | cons x c ih => simp [ih]

theorem prefix_of_callMoves {c d : List (Call E)}
    (h : (callMoves c : List (Move E F)) <+: callMoves d) : c <+: d := by
  induction c generalizing d with
  | nil => exact List.nil_prefix
  | cons x c ih =>
    cases d with
    | nil => simp at h
    | cons y d =>
      obtain ⟨m, n⟩ := x
      obtain ⟨m', n'⟩ := y
      simp only [callMoves_cons, List.cons_prefix_cons, Sum.inl.injEq, Ev.ask.injEq,
        Ev.ans.injEq] at h
      obtain ⟨rfl, ⟨-, hn⟩, h⟩ := h
      cases hn
      exact List.cons_prefix_cons.2 ⟨rfl, ih h⟩

end Calls

section Stream

variable {α : Type u}

@[simp] theorem length_streamTake (ω : ℕ → α) (k : ℕ) : (streamTake ω k).length = k := by
  simp [streamTake]

theorem getElem_streamTake (ω : ℕ → α) (k i : ℕ) (h : i < (streamTake ω k).length) :
    (streamTake ω k)[i] = ω i := by
  simp [streamTake]

theorem streamTake_succ (ω : ℕ → α) (k : ℕ) : streamTake ω (k + 1) = streamTake ω k ++ [ω k] := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  rw [getElem_streamTake]
  rcases Nat.lt_succ_iff_lt_or_eq.1 (by simpa using h₁) with h | rfl
  · rw [List.getElem_append_left (by simpa using h), getElem_streamTake]
  · simp

theorem streamTake_eq_append {ω : ℕ → α} {k : ℕ} {c₁ c₂ : List α} {x : α}
    (h : streamTake ω k = c₁ ++ x :: c₂) : streamTake ω c₁.length = c₁ ∧ ω c₁.length = x := by
  have hl : c₁.length < (streamTake ω k).length := by rw [h]; simp
  constructor
  · apply List.ext_getElem (by simp)
    intro i h₁ h₂
    have hi : i < (streamTake ω k).length := by simp at h₁; omega
    rw [getElem_streamTake, ← getElem_streamTake ω k i hi]
    simp only [h, List.getElem_append_left h₂]
  · rw [← getElem_streamTake ω k _ hl]
    simp [h]

theorem eq_of_streamTake_prefix {ω ω' : ℕ → α} {n k : ℕ}
    (h : streamTake ω n <+: streamTake ω' k) {j : ℕ} (hj : j < n) : ω j = ω' j := by
  have hj' : j < (streamTake ω n).length := by simpa using hj
  rw [← getElem_streamTake ω n j hj', h.getElem hj', getElem_streamTake]

end Stream

/-! ## Reading the calls of a round -/

section Read

variable {f : AFun E S A B} {P : Pending E S A}

theorem readCalls (q : S × A) {c₀ c : List (Call E)}
    (h : ∀ c₁ x c₂, c = c₁ ++ x :: c₂ → (c₀ ++ c₁, x.1) ∈ P q.1 q.2) :
    ARun f P (.run q c₀) (callMoves c) (.run q (c₀ ++ c)) := by
  induction c generalizing c₀ with
  | nil => simpa using ARun.nil _
  | cons x c ih =>
    have h₀ := h [] x c rfl
    simp only [List.append_nil] at h₀
    refine .cons (.call q c₀ x.1 h₀) (.cons (.reply q c₀ x.1 x.2) ?_)
    have := ih (c₀ := c₀ ++ [x]) fun c₁ y c₂ hc => by
      simpa using h (x :: c₁) y c₂ (by simp [hc])
    rw [show c₀ ++ x :: c = c₀ ++ [x] ++ c by simp]
    exact this

theorem readCalls_inv {q : S × A} {c₀ c : List (Call E)} {u : List (Move E (funSig S A B))}
    {y : St E S A} (h : ARun f P (.run q c₀) (callMoves c ++ u) y) :
    (∀ c₁ x c₂, c = c₁ ++ x :: c₂ → (c₀ ++ c₁, x.1) ∈ P q.1 q.2) ∧
      ARun f P (.run q (c₀ ++ c)) u y := by
  induction c generalizing c₀ with
  | nil => exact ⟨fun c₁ x c₂ h => by simp at h, by simpa using h⟩
  | cons x c ih =>
    obtain ⟨m, n⟩ := x
    simp only [callMoves_cons, List.cons_append] at h
    cases h with
    | cons h₁ h₂ =>
      cases h₁ with
      | call _ _ _ hP =>
        cases h₂ with
        | cons h₃ h₄ =>
          cases h₃ with
          | reply =>
            obtain ⟨ih₁, ih₂⟩ := ih h₄
            refine ⟨fun c₁ x c₂ hc => ?_, by simpa using ih₂⟩
            cases c₁ with
            | nil => simp at hc; obtain ⟨rfl, -⟩ := hc; simpa using hP
            | cons z c₁ =>
              simp only [List.cons_append, List.cons.injEq] at hc
              obtain ⟨rfl, hc⟩ := hc
              simpa using ih₁ c₁ x c₂ hc

/-- A nonempty run that ends idle contains an upper answer. -/
theorem exists_ans_of_idle {x y : St E S A} {p : List (Move E (funSig S A B))}
    (h : ARun f P x p y) (hy : y = .idle) (hp : p ≠ []) :
    ∃ q r, (.inr (.ans q r) : Move E (funSig S A B)) ∈ p := by
  induction h with
  | nil => exact absurd rfl hp
  | @cons x y z o s hs hr ih =>
    cases s with
    | nil =>
      cases hr
      subst hy
      cases hs with
      | ret q c r _ => exact ⟨q, r, List.mem_singleton_self _⟩
    | cons o' s =>
      obtain ⟨q, r, hm⟩ := ih hy (List.cons_ne_nil _ _)
      exact ⟨q, r, List.mem_cons_of_mem _ hm⟩

end Read

/-! ## Saturation -/

section Sat

variable {t : ObsTriple E S A B}

theorem satP_prefix {s : S} {a : A} {c c₁ : List (Call E)} {m m₁ : E.Op}
    (h : (c, m) ∈ satP t s a) (hc : CallPre c₁ m₁ c) : (c₁, m₁) ∈ satP t s a := by
  obtain ⟨n₁, c₂, rfl⟩ := hc
  rcases h with h | ⟨d, m', hd, n, c', rfl⟩ | ⟨d, e, hd, n, c', rfl⟩ | ⟨ω, hω, k, hk, -⟩
  · exact .inr (.inl ⟨_, m, h, n₁, c₂, rfl⟩)
  · exact .inr (.inl ⟨_, m', hd, n₁, c₂ ++ ⟨m, n⟩ :: c', by simp⟩)
  · exact .inr (.inr (.inl ⟨_, e, hd, n₁, c₂ ++ ⟨m, n⟩ :: c', by simp⟩))
  · obtain ⟨h₁, h₂⟩ := streamTake_eq_append hk
    exact .inr (.inr (.inr ⟨ω, hω, c₁.length, h₁, by simp [h₂]⟩))

theorem satP_of_beh {s : S} {a : A} {d c₁ c₂ : List (Call E)} {x : Call E} {e : End S B}
    (h : (d, e) ∈ t.1 s a) (hd : d = c₁ ++ x :: c₂) : (c₁, x.1) ∈ satP t s a :=
  .inr (.inr (.inl ⟨d, e, h, x.2, c₂, hd⟩))

theorem satP_of_stream {s : S} {a : A} {ω : ℕ → Call E} (hω : ω ∈ t.2.2 s a) {k : ℕ}
    {c₁ c₂ : List (Call E)} {x : Call E} (hk : streamTake ω k = c₁ ++ x :: c₂) :
    (c₁, x.1) ∈ satP t s a := by
  obtain ⟨h₁, h₂⟩ := streamTake_eq_append hk
  exact .inr (.inr (.inr ⟨ω, hω, c₁.length, h₁, by simp [h₂]⟩))

theorem satP_sat : satP (sat t) = satP t := by
  funext s a
  ext ⟨c, m⟩
  constructor
  · rintro (h | ⟨d, m', hd, hc⟩ | h | h)
    · exact h
    · exact satP_prefix hd hc
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))
  · exact .inl

theorem sat_idem : sat (sat t) = sat t := by
  show (t.1, satP (sat t), t.2.2) = _
  rw [satP_sat]; rfl

end Sat

/-! ## Characterisations -/

section Char

variable {t : ObsTriple E S A B}

theorem mem_round (q : S × A) (c : List (Call E)) (r : (B × S) ⊕ PUnit) :
    (.inr (.ask q) :: (callMoves c ++ [.inr (.ans q r)]) : List (Move E (funSig S A B))) ∈
      (toDStrat t).toStrategy ↔ (c, ansEnd r) ∈ t.1 q.1 q.2 := by
  constructor
  · rintro ⟨y, h⟩
    cases h with
    | cons h₁ h₂ =>
      cases h₁
      obtain ⟨-, h⟩ := readCalls_inv h₂
      cases h with
      | cons h₃ _ => cases h₃ with | ret _ _ _ h => simpa using h
  · intro h
    refine ⟨_, .cons (.ask q) ((readCalls q fun c₁ x c₂ hc => ?_).append
      (.cons (.ret q c r (by simpa using h)) (.nil _)))⟩
    simpa using satP_of_beh h hc

theorem mem_pending (q : S × A) (c : List (Call E)) (m : E.Op) :
    (.inr (.ask q) :: (callMoves c ++ [.inl (.ask m)]) : List (Move E (funSig S A B))) ∈
      (toDStrat t).toStrategy ↔ (c, m) ∈ satP t q.1 q.2 := by
  constructor
  · rintro ⟨y, h⟩
    cases h with
    | cons h₁ h₂ =>
      cases h₁
      obtain ⟨-, h⟩ := readCalls_inv h₂
      cases h with
      | cons h₃ _ => cases h₃ with | call _ _ _ h => simpa using h
  · intro h
    refine ⟨_, .cons (.ask q) ((readCalls q fun c₁ x c₂ hc => ?_).append
      (.cons (.call q c m (by simpa using h)) (.nil _)))⟩
    simpa using satP_prefix h ⟨x.2, c₂, hc⟩

theorem mem_div (q : S × A) (c : List (Call E)) :
    (.inr (.ask q) :: callMoves c : List (Move E (funSig S A B))) ∈ (toDStrat t).div ↔
      (c, .div) ∈ t.1 q.1 q.2 := by
  constructor
  · rintro ⟨q', c', h, hd⟩
    cases h with
    | cons h₁ h₂ =>
      cases h₁
      rw [← List.append_nil (callMoves c)] at h₂
      obtain ⟨-, h⟩ := readCalls_inv h₂
      cases h
      simpa using hd
  · intro h
    refine ⟨q, c, .cons (.ask q) ?_, h⟩
    simpa using readCalls (f := t.1) (P := satP t) q (c₀ := []) fun c₁ x c₂ hc => by
      simpa using satP_of_beh h hc

theorem isInfPlay_streamPlay (pre : List (Move E (funSig S A B))) (q : S × A) (ω : ℕ → Call E) :
    IsInfPlay (streamPlay pre q ω) := by
  refine Chain.isInfPlay_lim (c := fun k => pre ++ .inr (.ask q) :: callMoves (streamTake ω k))
    (fun k => ⟨callMoves [ω k], by simp [streamTake_succ]⟩) fun k => ⟨k, ?_⟩
  simp [length_callMoves]
  omega

theorem streamPlay_mem {pre : List (Move E (funSig S A B))} {q : S × A} {ω : ℕ → Call E}
    (hpre : ARun t.1 (satP t) .idle pre .idle) (hω : ω ∈ t.2.2 q.1 q.2) :
    streamPlay pre q ω ∈ (toDStrat t).inf := by
  refine ⟨isInfPlay_streamPlay pre q ω, ?_, .inl ⟨pre, q, ω, hpre, hω, rfl⟩⟩
  rintro p ⟨k, hp⟩
  refine (toDStrat t).toStrategy.of_prefix ?_ hp
  refine ⟨_, hpre.append (.cons (.ask q) (readCalls (c₀ := []) q fun c₁ x c₂ hc => ?_))⟩
  simpa using satP_of_stream hω hc

theorem no_ans_of_mem_streamPlay {q : S × A} {ω : ℕ → Call E}
    {p : List (Move E (funSig S A B))} (hp : p ∈ streamPlay [] q ω) (q' : S × A)
    (r : (B × S) ⊕ PUnit) : (.inr (.ans q' r) : Move E (funSig S A B)) ∉ p := by
  obtain ⟨k, hk⟩ := hp
  intro hm
  have := hk.subset hm
  simp only [List.nil_append, List.mem_cons, Sum.inr.injEq, reduceCtorEq, false_or] at this
  exact not_inr_mem_callMoves this

theorem mem_inf (q : S × A) (ω : ℕ → Call E) :
    streamPlay [] q ω ∈ (toDStrat t).inf ↔ ω ∈ t.2.2 q.1 q.2 := by
  refine ⟨?_, fun h => streamPlay_mem (.nil _) h⟩
  rintro ⟨-, -, ⟨pre, q', ω', hpre, hω', hI⟩ | h⟩
  · have hmem : pre ++ [.inr (.ask q')] ∈ streamPlay [] q ω :=
      hI ▸ ⟨0, by simp [streamTake]⟩
    have hpre0 : pre = [] := by
      by_contra hne
      obtain ⟨q'', r, hm⟩ := exists_ans_of_idle hpre rfl hne
      exact no_ans_of_mem_streamPlay hmem q'' r (List.mem_append_left _ hm)
    subst hpre0
    obtain ⟨k, hk⟩ := hmem
    simp only [List.nil_append, List.cons_prefix_cons, Sum.inr.injEq, Ev.ask.injEq] at hk
    obtain ⟨rfl, -⟩ := hk
    have hω : ω' = ω := by
      funext j
      have : (.inr (.ask q') :: callMoves (streamTake ω (j + 1)) : List (Move E (funSig S A B))) ∈
          streamPlay [] q' ω' := hI ▸ ⟨j + 1, by simp⟩
      obtain ⟨k, hk⟩ := this
      simp only [List.nil_append, List.cons_prefix_cons, true_and] at hk
      exact (eq_of_streamTake_prefix (prefix_of_callMoves hk) (Nat.lt_succ_self j)).symm
    exact hω ▸ hω'
  · obtain ⟨p', hp', hpre, hidle⟩ := h [.inr (.ask q)] ⟨0, by simp [streamTake]⟩
    obtain ⟨q'', r, hm⟩ :=
      exists_ans_of_idle hidle rfl (List.ne_nil_of_mem (hpre.subset (List.mem_singleton_self _)))
    exact (no_ans_of_mem_streamPlay hp' q'' r hm).elim

end Char

/-! ## Injection up to saturation -/

section Main

variable {t t' : ObsTriple E S A B}

theorem toDStrat_eq_of_sat (h : sat t = sat t') : toDStrat t = toDStrat t' := by
  simp only [sat, Prod.mk.injEq] at h
  obtain ⟨h₁, h₂, h₃⟩ := h
  unfold toDStrat
  rw [h₁, h₂, h₃]

theorem sat_eq_of_toDStrat (h : toDStrat t = toDStrat t') : sat t = sat t' := by
  have h₁ : t.1 = t'.1 := by
    funext s a
    ext ⟨c, e⟩
    cases e with
    | ret b s' =>
      have e₁ := mem_round (t := t) (s, a) c (.inl (b, s'))
      have e₂ := mem_round (t := t') (s, a) c (.inl (b, s'))
      rw [h] at e₁
      exact e₁.symm.trans e₂
    | trap =>
      have e₁ := mem_round (t := t) (s, a) c (.inr PUnit.unit)
      have e₂ := mem_round (t := t') (s, a) c (.inr PUnit.unit)
      rw [h] at e₁
      exact e₁.symm.trans e₂
    | div =>
      have e₁ := mem_div (t := t) (s, a) c
      have e₂ := mem_div (t := t') (s, a) c
      rw [h] at e₁
      exact e₁.symm.trans e₂
  have h₂ : satP t = satP t' := by
    funext s a
    ext ⟨c, m⟩
    have e₁ := mem_pending (t := t) (s, a) c m
    have e₂ := mem_pending (t := t') (s, a) c m
    rw [h] at e₁
    exact e₁.symm.trans e₂
  have h₃ : t.2.2 = t'.2.2 := by
    funext s a
    ext ω
    have e₁ := mem_inf (t := t) (s, a) ω
    have e₂ := mem_inf (t := t') (s, a) ω
    rw [h] at e₁
    exact e₁.symm.trans e₂
  simp only [sat, h₁, h₂, h₃]

end Main

end Silmaril.Proofs.Games.Abstract.StratObs
