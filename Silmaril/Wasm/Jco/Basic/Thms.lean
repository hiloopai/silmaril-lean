module

public import Silmaril.Wasm.Jco.Basic.Defs

/-!
# jco-style toolchain, common layer: laws of the relational state monad

The monad laws hold as equations of relations (`pure_bind`, `bind_pure`, `bind_assoc`), traps
absorb continuations (`fail_bind`), and continuations that agree on every value a computation
can return give the same computation (`bind_congr_returns`). These are the rewriting rules the
behaviour theorems of the jco part use.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.RM

variable {σ α β γ : Type}

theorem bind_def (m : RM σ α) (k : α → RM σ β) :
    (m >>= k) = fun s o => (∃ a s', m s (.ok a s') ∧ k a s' o) ∨ (m s .trap ∧ o = .trap) :=
  rfl

theorem pure_def (a : α) : (pure a : RM σ α) = fun s o => o = .ok a s := rfl

theorem bind_apply (m : RM σ α) (k : α → RM σ β) (s : σ) (o : Out σ β) :
    (m >>= k) s o ↔ (∃ a s', m s (.ok a s') ∧ k a s' o) ∨ (m s .trap ∧ o = .trap) :=
  Iff.rfl

theorem pure_apply (a : α) (s : σ) (o : Out σ α) : (pure a : RM σ α) s o ↔ o = .ok a s :=
  Iff.rfl

@[simp] theorem pure_bind (a : α) (k : α → RM σ β) : (pure a >>= k) = k a := by
  funext s o
  simp [bind_apply, pure_apply]

@[simp] theorem bind_pure (m : RM σ α) : (m >>= fun a => pure a) = m := by
  funext s o
  cases o <;> simp [bind_apply, pure_apply]

theorem bind_assoc (m : RM σ α) (k : α → RM σ β) (k' : β → RM σ γ) :
    (m >>= k >>= k') = (m >>= fun a => k a >>= k') := by
  funext s o
  simp only [bind_apply, eq_iff_iff]
  constructor
  · rintro (⟨b, s', (⟨a, s1, h1, h2⟩ | ⟨_, h2⟩), h3⟩ | ⟨(⟨a, s1, h1, h2⟩ | ⟨h1, -⟩), rfl⟩)
    · exact .inl ⟨a, s1, h1, .inl ⟨b, s', h2, h3⟩⟩
    · cases h2
    · exact .inl ⟨a, s1, h1, .inr ⟨h2, rfl⟩⟩
    · exact .inr ⟨h1, rfl⟩
  · rintro (⟨a, s1, h1, (⟨b, s', h2, h3⟩ | ⟨h2, rfl⟩)⟩ | ⟨h1, rfl⟩)
    · exact .inl ⟨b, s', .inl ⟨a, s1, h1, h2⟩, h3⟩
    · exact .inr ⟨.inl ⟨a, s1, h1, h2⟩, rfl⟩
    · exact .inr ⟨.inr ⟨h1, trivial⟩, rfl⟩

@[simp] theorem fail_bind (k : α → RM σ β) : (fail >>= k) = fail := by
  funext s o
  simp only [bind_apply, fail, eq_iff_iff]
  constructor
  · rintro (⟨_, _, h, -⟩ | ⟨-, h⟩)
    · cases h
    · exact h
  · intro h
    exact .inr ⟨trivial, h⟩

@[simp] theorem ofOption_some (a : α) : (ofOption (some a) : RM σ α) = pure a := rfl

@[simp] theorem ofOption_none : (ofOption none : RM σ α) = fail := rfl

@[simp] theorem check_true : (check true : RM σ Unit) = pure () := rfl

@[simp] theorem check_false : (check false : RM σ Unit) = fail := rfl

/-- Continuations that agree on every value `m` returns give the same computation. -/
theorem bind_congr_returns {m : RM σ α} {P : α → Prop} (hm : Returns m P) {k k' : α → RM σ β}
    (h : ∀ a, P a → k a = k' a) : (m >>= k) = (m >>= k') := by
  funext s o
  simp only [bind_apply, eq_iff_iff]
  constructor
  · rintro (⟨a, s', h1, h2⟩ | h1)
    · exact .inl ⟨a, s', h1, h a (hm s a s' h1) ▸ h2⟩
    · exact .inr h1
  · rintro (⟨a, s', h1, h2⟩ | h1)
    · exact .inl ⟨a, s', h1, (h a (hm s a s' h1)).symm ▸ h2⟩
    · exact .inr h1

theorem bind_congr {m : RM σ α} {k k' : α → RM σ β} (h : ∀ a, k a = k' a) :
    (m >>= k) = (m >>= k') := by
  rw [show k = k' from funext h]

/-- What `m >>= k` returns: what `k` returns after a value of `m`. -/
theorem returns_bind {m : RM σ α} {P : α → Prop} (hm : Returns m P) {k : α → RM σ β}
    {Q : β → Prop} (hk : ∀ a, P a → Returns (k a) Q) : Returns (m >>= k) Q := by
  intro s b s' h
  rcases h with ⟨a, s1, h1, h2⟩ | ⟨-, h⟩
  · exact hk a (hm s a s1 h1) s1 b s' h2
  · cases h

theorem returns_pure {a : α} {P : α → Prop} (h : P a) : Returns (pure a : RM σ α) P := by
  intro s b s' hb
  cases hb
  exact h

theorem returns_fail {P : α → Prop} : Returns (fail : RM σ α) P := by
  intro s b s' hb
  cases hb

theorem returns_mono {m : RM σ α} {P Q : α → Prop} (hm : Returns m P) (h : ∀ a, P a → Q a) :
    Returns m Q := fun s a s' ha => h a (hm s a s' ha)

theorem returns_check {b : Bool} : Returns (check b : RM σ Unit) fun _ => True := by
  intro s a s' _
  trivial

theorem returns_true (m : RM σ α) : Returns m fun _ => True := fun _ _ _ _ => trivial

/-! ## Deterministic runs -/

theorem det_pure (a : α) (s : σ) : Det (pure a : RM σ α) s (.ok a s) := fun _ => Iff.rfl

theorem det_pure_eq {a b : α} (h : a = b) (s : σ) : Det (pure a : RM σ α) s (.ok b s) := by
  subst h
  exact det_pure a s

theorem det_fail (s : σ) : Det (fail : RM σ α) s .trap := fun _ => Iff.rfl

theorem det_get (s : σ) : Det (get : RM σ σ) s (.ok s s) := fun _ => Iff.rfl

theorem det_set (s s' : σ) : Det (set s' : RM σ Unit) s (.ok () s') := fun _ => Iff.rfl

theorem det_ofOption {x : Option α} {a : α} (h : x = some a) (s : σ) :
    Det (ofOption x : RM σ α) s (.ok a s) := by
  subst h
  exact det_pure a s

theorem det_ofOption_none {x : Option α} (h : x = none) (s : σ) :
    Det (ofOption x : RM σ α) s .trap := by
  subst h
  exact det_fail s

theorem det_check {b : Bool} (h : b = true) (s : σ) : Det (check b : RM σ Unit) s (.ok () s) := by
  subst h
  exact det_pure () s

theorem det_bind {m : RM σ α} {k : α → RM σ β} {s s' : σ} {a : α} {o : Out σ β}
    (hm : Det m s (.ok a s')) (hk : Det (k a) s' o) : Det (m >>= k) s o := by
  intro o'
  rw [bind_apply]
  constructor
  · rintro (⟨a1, s1, h1, h2⟩ | ⟨h1, -⟩)
    · obtain ⟨rfl, rfl⟩ : a1 = a ∧ s1 = s' := by simpa using (hm _).1 h1
      exact (hk o').1 h2
    · cases (hm _).1 h1
  · intro h
    exact .inl ⟨a, s', (hm _).2 rfl, (hk o').2 h⟩

theorem det_bind_trap {m : RM σ α} {k : α → RM σ β} {s : σ} (hm : Det m s .trap) :
    Det (m >>= k) s .trap := by
  intro o'
  rw [bind_apply]
  constructor
  · rintro (⟨a1, s1, h1, -⟩ | ⟨-, h⟩)
    · cases (hm _).1 h1
    · exact h
  · intro h
    exact .inr ⟨(hm _).2 rfl, h⟩

end Silmaril.Wasm.Jco.RM
