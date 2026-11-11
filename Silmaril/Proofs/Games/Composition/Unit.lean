module

public import Silmaril.Games.Composition.Defs
import Silmaril.Proofs.Games.Composition.Copycat

/-!
# Copycat is a unit for composition: proofs

Proofs for the unit laws of `Silmaril.Games.Composition.Thms`.

* `σ ⊆ σ ; id` and `σ ⊆ id ; σ`: a play `s` interacts with the copycat play
  forwarding its upper (resp. lower) events and yields `s` itself
  (`zip_double_upper`, `zip_double_lower`).
* `σ ; id ⊆ σ` and `id ; σ ⊆ σ`: an interaction with a copycat play yields a
  prefix of the play of `σ`, or that play followed by one Opponent move that
  copycat has received but not yet forwarded (`comp_id_out`, `id_comp_out`);
  this is where receptiveness is needed.
-/

public section

namespace Silmaril.Proofs.Games.Composition

open Silmaril.Games

universe u

/-- A prefix of `a :: b :: rest` is empty, `[a]`, or `a :: b` followed by a prefix of `rest`. -/
private theorem prefix_pair_cases {α : Type u} {a b : α} {c rest : List α}
    (hc : c <+: a :: b :: rest) :
    c = [] ∨ c = [a] ∨ ∃ c', c = a :: b :: c' ∧ c' <+: rest := by
  rcases List.prefix_cons_iff.1 hc with h0 | ⟨c₁, hc₁, hp₁⟩
  · exact .inl h0
  rcases List.prefix_cons_iff.1 hp₁ with h1 | ⟨c₂, hc₂, hp₂⟩
  · exact .inr (.inl (by rw [hc₁, h1]))
  · exact .inr (.inr ⟨c₂, by rw [hc₁, hc₂], hp₂⟩)

variable {E F : Sig.{u}}

/-! ## Projections -/

@[simp] theorem upper_nil : upper ([] : List (Move E F)) = [] := rfl
@[simp] theorem upper_cons_inl (a : Ev E) (s : List (Move E F)) :
    upper (.inl a :: s) = upper s := rfl
@[simp] theorem upper_cons_inr (b : Ev F) (s : List (Move E F)) :
    upper (.inr b :: s) = b :: upper s := rfl
@[simp] theorem lower_nil : lower ([] : List (Move E F)) = [] := rfl
@[simp] theorem lower_cons_inl (a : Ev E) (s : List (Move E F)) :
    lower (.inl a :: s) = a :: lower s := rfl
@[simp] theorem lower_cons_inr (b : Ev F) (s : List (Move E F)) :
    lower (.inr b :: s) = lower s := rfl

theorem upper_alternating {a b : Pos E F} {s : List (Move E F)} (h : Path a s b) :
    (a = .idle → Ev.Alternating (upper s)) ∧
    (∀ q, (a = .run q ∨ ∃ m, a = .wait q m) →
      upper s = [] ∨ ∃ r w, upper s = .ans q r :: w ∧ Ev.Alternating w) := by
  induction h with
  | nil => exact ⟨fun _ => .nil, fun _ _ => .inl rfl⟩
  | @cons a b c o s st _ ih =>
    show (a = .idle → Ev.Alternating (upper (o :: s))) ∧
      (∀ q, (a = .run q ∨ ∃ m, a = .wait q m) →
        upper (o :: s) = [] ∨ ∃ r w, upper (o :: s) = .ans q r :: w ∧ Ev.Alternating w)
    cases st with
    | ask q =>
      refine ⟨fun _ => ?_, fun _ h => (by rcases h with h | ⟨_, h⟩ <;> cases h)⟩
      rcases ih.2 q (.inl rfl) with h | ⟨r, w, h, hw⟩
      · simp only [upper_cons_inr, h]; exact .ask q
      · simp only [upper_cons_inr, h]; exact .cons q r hw
    | call q m =>
      refine ⟨fun h => (by cases h), fun q' h => ?_⟩
      rcases h with h | ⟨_, h⟩ <;> cases h
      simpa using ih.2 q (.inr ⟨m, rfl⟩)
    | reply q m n =>
      refine ⟨fun h => (by cases h), fun q' h => ?_⟩
      rcases h with h | ⟨_, h⟩ <;> cases h
      simpa using ih.2 q (.inl rfl)
    | ret q r =>
      refine ⟨fun h => (by cases h), fun q' h => ?_⟩
      rcases h with h | ⟨_, h⟩ <;> cases h
      exact .inr ⟨r, _, rfl, ih.1 rfl⟩

theorem lower_alternating {a b : Pos E F} {s : List (Move E F)} (h : Path a s b) :
    ((a = .idle ∨ ∃ q, a = .run q) → Ev.Alternating (lower s)) ∧
    (∀ q m, a = .wait q m →
      lower s = [] ∨ ∃ n w, lower s = .ans m n :: w ∧ Ev.Alternating w) := by
  induction h with
  | nil => exact ⟨fun _ => .nil, fun _ _ _ => .inl rfl⟩
  | cons st _ ih =>
    cases st with
    | ask q =>
      refine ⟨fun _ => ?_, fun _ _ h => by cases h⟩
      simpa using ih.1 (.inr ⟨q, rfl⟩)
    | call q m =>
      refine ⟨fun _ => ?_, fun _ _ h => by cases h⟩
      rcases ih.2 q m rfl with h | ⟨n, w, h, hw⟩
      · simp only [lower_cons_inl, h]; exact .ask m
      · simp only [lower_cons_inl, h]; exact .cons m n hw
    | reply q m n =>
      refine ⟨fun h => (by rcases h with h | ⟨_, h⟩ <;> cases h), fun q' m' h => ?_⟩
      cases h
      exact .inr ⟨n, _, rfl, ih.1 (.inr ⟨q, rfl⟩)⟩
    | ret q r =>
      refine ⟨fun _ => ?_, fun _ _ h => by cases h⟩
      simpa using ih.1 (.inl rfl)

theorem zip_double_upper (s : List (Move E F)) : Zip s (Ev.double (upper s)) s := by
  induction s with
  | nil => exact .nil
  | cons x s ih =>
    rcases x with a | (q | ⟨q, r⟩)
    · exact .left a ih
    · simpa using Zip.right _ (Zip.sync _ ih)
    · simpa using Zip.sync _ (Zip.right _ ih)

theorem zip_double_lower (s : List (Move E F)) : Zip (Ev.double (lower s)) s s := by
  induction s with
  | nil => exact .nil
  | cons x s ih =>
    rcases x with (m | ⟨m, n⟩) | b
    · simpa using Zip.sync _ (Zip.left _ ih)
    · simpa using Zip.left _ (Zip.sync _ ih)
    · exact .right b ih

/-! ## Interactions with copycat plays -/

/-- The outcome of an interaction with copycat: a prefix of `s`, or `s`
followed by one Opponent move legal after it. -/
@[expose] def Out (s p : List (Move E F)) (x : Pos E F) : Prop :=
  p <+: s ∨ ∃ o y, p = s ++ [o] ∧ Step x o y ∧ o.IsO

theorem Out.lift (L : List (Move E F)) {s p : List (Move E F)} {x : Pos E F}
    (h : Out s p x) : Out (L ++ s) (L ++ p) x := by
  rcases h with h | ⟨o, y, rfl, hst, ho⟩
  · exact .inl ((List.prefix_append_right_inj L).2 h)
  · exact .inr ⟨o, y, by simp, hst, ho⟩

theorem no_inl_idle {as : List (Ev E)} {s : List (Move E F)} {x : Pos E F}
    (h : Path .idle (as.map .inl ++ s) x) : as = [] := by
  cases as with
  | nil => rfl
  | cons a as =>
    simp only [List.map_cons, List.cons_append] at h
    cases h with | cons h _ => cases h

theorem no_inr_wait {q : F.Op} {m : E.Op} {cs : List (Ev F)} {s : List (Move E F)}
    {x : Pos E F} (h : Path (.wait q m) (cs.map .inr ++ s) x) : cs = [] := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    simp only [List.map_cons, List.cons_append] at h
    cases h with | cons h _ => cases h

theorem after_ret {a : Pos E F} {as : List (Ev E)} {q : F.Op} {r : F.Ar q}
    {s : List (Move E F)} {x : Pos E F}
    (h : Path a (as.map .inl ++ .inr (.ans q r) :: s) x) : Path .idle s x := by
  obtain ⟨_, -, h⟩ := Path.of_append h
  cases h with | cons st h => cases st; exact h

theorem after_call {a : Pos E F} {cs : List (Ev F)} {m : E.Op}
    {s : List (Move E F)} {x : Pos E F}
    (h : Path a (cs.map .inr ++ .inl (.ask m) :: s) x) : ∃ q, Path (.wait q m) s x := by
  obtain ⟨_, -, h⟩ := Path.of_append h
  cases h with | cons st h => cases st; exact ⟨_, h⟩

theorem nil_of_zip_nil_idle {s p : List (Move E F)} {x : Pos E F}
    (h : Zip s ([] : List (Move F F)) p) (hs : Path .idle s x) : s = [] ∧ p = [] := by
  obtain ⟨as, rfl, rfl⟩ := Zip.nil_right_iff.1 h
  obtain rfl := no_inl_idle (s := []) (by simpa using hs)
  exact ⟨rfl, rfl⟩

theorem nil_of_nil_zip_wait {q : F.Op} {m : E.Op} {s p : List (Move E F)} {x : Pos E F}
    (h : Zip ([] : List (Move E E)) s p) (hs : Path (.wait q m) s x) : s = [] ∧ p = [] := by
  obtain ⟨cs, rfl, rfl⟩ := Zip.nil_left_iff.1 h
  obtain rfl := no_inr_wait (s := []) (by simpa using hs)
  exact ⟨rfl, rfl⟩

/-! ### Copycat on the right: one forwarded exchange at a time -/

private theorem ci_nil {s p : List (Move E F)} {x : Pos E F}
    (h : Zip s ([] : List (Move F F)) p) : Out s p x := by
  obtain ⟨as, hs, hp⟩ := Zip.nil_right_iff.1 h
  exact .inl (by rw [hs, hp]; exact List.prefix_refl _)

private theorem ci_single {m : F.Op} {s p : List (Move E F)} {x : Pos E F}
    (h : Zip s [.inr (.ask m)] p) (hs : Path .idle s x) : Out s p x := by
  obtain ⟨as, s₁, p₁, rfl, rfl, h₁⟩ := Zip.inr_right h
  obtain rfl := no_inl_idle hs
  obtain ⟨rfl, rfl⟩ := nil_of_zip_nil_idle h₁ hs
  cases hs
  exact .inr ⟨_, _, rfl, .ask m, trivial⟩

private theorem ci_ask_then {m : F.Op} {c : List (Move F F)} {s p : List (Move E F)}
    {x : Pos E F} (h : Zip s (.inr (.ask m) :: .inl (.ask m) :: c) p) (hs : Path .idle s x)
    (k : ∀ {s' p' : List (Move E F)}, Zip s' c p' → Path (.run m) s' x → Out s' p' x) :
    Out s p x := by
  obtain ⟨as, s₁, p₁, rfl, rfl, h₁⟩ := Zip.inr_right h
  obtain rfl := no_inl_idle hs
  obtain ⟨bs, s₂, p₂, rfl, rfl, h₂⟩ := Zip.inl_right h₁
  have hs₁ : Path .idle (bs.map .inl ++ .inr (.ask m) :: s₂) x := by simpa using hs
  obtain rfl := no_inl_idle hs₁
  have hs₂ : Path (.run m) s₂ x := by cases hs₁ with | cons st hs => cases st; exact hs
  simpa using (k h₂ hs₂).lift [.inr (.ask m)]

private theorem ci_ans_single {m : F.Op} {n : F.Ar m} {s p : List (Move E F)} {x : Pos E F}
    (h : Zip s [.inl (.ans m n)] p) (hs : Path (.run m) s x) : Out s p x := by
  obtain ⟨ds, s₃, p₃, rfl, rfl, h₃⟩ := Zip.inl_right h
  obtain ⟨rfl, rfl⟩ := nil_of_zip_nil_idle h₃ (after_ret hs)
  exact .inl (by simp)

private theorem ci_ans_then {m : F.Op} {n : F.Ar m} {c : List (Move F F)}
    {s p : List (Move E F)} {x : Pos E F}
    (h : Zip s (.inl (.ans m n) :: .inr (.ans m n) :: c) p) (hs : Path (.run m) s x)
    (k : ∀ {s' p' : List (Move E F)}, Zip s' c p' → Path .idle s' x → Out s' p' x) :
    Out s p x := by
  obtain ⟨ds, s₃, p₃, rfl, rfl, h₃⟩ := Zip.inl_right h
  have hs₃ : Path .idle s₃ x := after_ret hs
  obtain ⟨es, s₄, p₄, rfl, rfl, h₄⟩ := Zip.inr_right h₃
  obtain rfl := no_inl_idle hs₃
  have hs₄ : Path .idle s₄ x := by simpa using hs₃
  exact ((k h₄ hs₄).lift [.inr (.ans m n)]).lift (ds.map .inl)

theorem comp_id_out {w : List (Ev F)} (hw : Ev.Alternating w) :
    ∀ {c : List (Move F F)}, c <+: Ev.double w → ∀ {s p : List (Move E F)}, Zip s c p →
      ∀ {x : Pos E F}, Path .idle s x → Out s p x := by
  induction hw with
  | nil =>
    intro c hc s p h x _
    have hc0 : c = [] := List.prefix_nil.1 (by simpa only [double_nil] using hc)
    exact ci_nil (hc0 ▸ h)
  | ask m =>
    show ∀ {c : List (Move F F)}, c <+: Ev.double [.ask m] →
      ∀ {s p : List (Move E F)}, Zip s c p → ∀ {x : Pos E F}, Path .idle s x → Out s p x
    intro c hc s p h x hs
    have hc' : c <+: [.inr (.ask m), .inl (.ask m)] := by
      simpa only [double_cons, copy_ask, double_nil, List.cons_append, List.nil_append] using hc
    rcases prefix_pair_cases hc' with h0 | h1 | ⟨c₁, hcc₁, hc₁⟩
    · exact ci_nil (h0 ▸ h)
    · exact ci_single (h1 ▸ h) hs
    · have hc0 : c₁ = [] := List.prefix_nil.1 hc₁
      exact ci_ask_then (hcc₁ ▸ h) hs fun h₁ _ => ci_nil (hc0 ▸ h₁)
  | @cons m n w _ ih =>
    show ∀ {c : List (Move F F)}, c <+: Ev.double (.ask m :: .ans m n :: w) →
      ∀ {s p : List (Move E F)}, Zip s c p → ∀ {x : Pos E F}, Path .idle s x → Out s p x
    intro c hc s p h x hs
    have hc' : c <+: .inr (.ask m) :: .inl (.ask m) ::
        .inl (.ans m n) :: .inr (.ans m n) :: Ev.double w := by
      simpa only [double_cons, copy_ask, copy_ans, List.cons_append, List.nil_append] using hc
    rcases prefix_pair_cases hc' with h0 | h1 | ⟨c₁, hcc₁, hc₁⟩
    · exact ci_nil (h0 ▸ h)
    · exact ci_single (h1 ▸ h) hs
    refine ci_ask_then (hcc₁ ▸ h) hs fun {s₁ p₁} h₁ hs₁ => ?_
    show Out s₁ p₁ x
    rcases prefix_pair_cases hc₁ with h0 | h1 | ⟨c₂, hcc₂, hc₂⟩
    · exact ci_nil (h0 ▸ h₁)
    · exact ci_ans_single (h1 ▸ h₁) hs₁
    · exact ci_ans_then (hcc₂ ▸ h₁) hs₁ fun h₂ hs₂ => ih hc₂ h₂ hs₂

/-! ### Copycat on the left: one forwarded exchange at a time -/

private theorem ic_nil {s p : List (Move E F)} {x : Pos E F}
    (h : Zip ([] : List (Move E E)) s p) : Out s p x := by
  obtain ⟨cs, hs, hp⟩ := Zip.nil_left_iff.1 h
  exact .inl (by rw [hs, hp]; exact List.prefix_refl _)

private theorem ic_single {m : E.Op} {s p : List (Move E F)} {a x : Pos E F}
    (h : Zip [.inr (.ask m)] s p) (hs : Path a s x) : Out s p x := by
  obtain ⟨cs, s₁, p₁, rfl, rfl, h₁⟩ := Zip.inr_left h
  obtain ⟨q, hs₁⟩ := after_call hs
  obtain ⟨rfl, rfl⟩ := nil_of_nil_zip_wait h₁ hs₁
  exact .inl (by simp)

private theorem ic_ask_then {m : E.Op} {c : List (Move E E)} {s p : List (Move E F)}
    {a x : Pos E F} (h : Zip (.inr (.ask m) :: .inl (.ask m) :: c) s p) (hs : Path a s x)
    (k : ∀ {q : F.Op} {s' p' : List (Move E F)}, Zip c s' p' → Path (.wait q m) s' x →
      Out s' p' x) :
    Out s p x := by
  obtain ⟨cs, s₁, p₁, rfl, rfl, h₁⟩ := Zip.inr_left h
  obtain ⟨q, hs₁⟩ := after_call hs
  obtain ⟨ds, s₂, p₂, rfl, rfl, h₂⟩ := Zip.inl_left h₁
  obtain rfl := no_inr_wait hs₁
  have hs₂ : Path (.wait q m) s₂ x := by simpa using hs₁
  exact ((k h₂ hs₂).lift [.inl (.ask m)]).lift (cs.map .inr)

private theorem ic_ans_single {q : F.Op} {m : E.Op} {n : E.Ar m} {s p : List (Move E F)}
    {x : Pos E F} (h : Zip [.inl (.ans m n)] s p) (hs : Path (.wait q m) s x) :
    Out s p x := by
  obtain ⟨es, s₃, p₃, rfl, rfl, h₃⟩ := Zip.inl_left h
  obtain rfl := no_inr_wait hs
  have hs₃ : Path (.wait q m) s₃ x := by simpa using hs
  obtain ⟨rfl, rfl⟩ := nil_of_nil_zip_wait h₃ hs₃
  cases hs₃
  exact .inr ⟨_, _, by simp, .reply q m n, trivial⟩

private theorem ic_ans_then {q : F.Op} {m : E.Op} {n : E.Ar m} {c : List (Move E E)}
    {s p : List (Move E F)} {x : Pos E F}
    (h : Zip (.inl (.ans m n) :: .inr (.ans m n) :: c) s p) (hs : Path (.wait q m) s x)
    (k : ∀ {s' p' : List (Move E F)}, Zip c s' p' → Path (.run q) s' x → Out s' p' x) :
    Out s p x := by
  obtain ⟨es, s₃, p₃, rfl, rfl, h₃⟩ := Zip.inl_left h
  obtain rfl := no_inr_wait hs
  have hs₃ : Path (.wait q m) s₃ x := by simpa using hs
  obtain ⟨fs, s₄, p₄, rfl, rfl, h₄⟩ := Zip.inr_left h₃
  obtain rfl := no_inr_wait hs₃
  have hs₄ : Path (.run q) s₄ x := by
    cases hs₃ with | cons st hs => cases st; exact hs
  simpa using (k h₄ hs₄).lift [.inl (.ans m n)]

theorem id_comp_out {w : List (Ev E)} (hw : Ev.Alternating w) :
    ∀ {c : List (Move E E)}, c <+: Ev.double w → ∀ {s p : List (Move E F)}, Zip c s p →
      ∀ {a x : Pos E F}, (a = .idle ∨ ∃ q, a = .run q) → Path a s x → Out s p x := by
  induction hw with
  | nil =>
    intro c hc s p h a x _ _
    have hc0 : c = [] := List.prefix_nil.1 (by simpa only [double_nil] using hc)
    exact ic_nil (hc0 ▸ h)
  | ask m =>
    show ∀ {c : List (Move E E)}, c <+: Ev.double [.ask m] →
      ∀ {s p : List (Move E F)}, Zip c s p → ∀ {a x : Pos E F},
        (a = .idle ∨ ∃ q, a = .run q) → Path a s x → Out s p x
    intro c hc s p h a x _ hs
    have hc' : c <+: [.inr (.ask m), .inl (.ask m)] := by
      simpa only [double_cons, copy_ask, double_nil, List.cons_append, List.nil_append] using hc
    rcases prefix_pair_cases hc' with h0 | h1 | ⟨c₁, hcc₁, hc₁⟩
    · exact ic_nil (h0 ▸ h)
    · exact ic_single (h1 ▸ h) hs
    · have hc0 : c₁ = [] := List.prefix_nil.1 hc₁
      exact ic_ask_then (hcc₁ ▸ h) hs fun h₁ _ => ic_nil (hc0 ▸ h₁)
  | @cons m n w _ ih =>
    show ∀ {c : List (Move E E)}, c <+: Ev.double (.ask m :: .ans m n :: w) →
      ∀ {s p : List (Move E F)}, Zip c s p → ∀ {a x : Pos E F},
        (a = .idle ∨ ∃ q, a = .run q) → Path a s x → Out s p x
    intro c hc s p h a x _ hs
    have hc' : c <+: .inr (.ask m) :: .inl (.ask m) ::
        .inl (.ans m n) :: .inr (.ans m n) :: Ev.double w := by
      simpa only [double_cons, copy_ask, copy_ans, List.cons_append, List.nil_append] using hc
    rcases prefix_pair_cases hc' with h0 | h1 | ⟨c₁, hcc₁, hc₁⟩
    · exact ic_nil (h0 ▸ h)
    · exact ic_single (h1 ▸ h) hs
    refine ic_ask_then (hcc₁ ▸ h) hs fun {q s₁ p₁} h₁ hs₁ => ?_
    show Out s₁ p₁ x
    rcases prefix_pair_cases hc₁ with h0 | h1 | ⟨c₂, hcc₂, hc₂⟩
    · exact ic_nil (h0 ▸ h₁)
    · exact ic_ans_single (h1 ▸ h₁) hs₁
    · exact ic_ans_then (hcc₂ ▸ h₁) hs₁ fun h₂ hs₂ => ih hc₂ h₂ (.inr ⟨q, rfl⟩) hs₂

end Silmaril.Proofs.Games.Composition
